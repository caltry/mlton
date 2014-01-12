(* Copyright (C) 2013-2014 David Larsen.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

(*
 * For functions which scrutinize an argument in their first block, generate a
 * new entry point for each constructor in the datatype being scrutinized.
 *)
functor MeCaseEntries (S: ME_SSA_TRANSFORM_STRUCTS): ME_SSA_TRANSFORM =
struct

exception NoSuchBlock (* There is no block associated with that label. *)

open S

(* XXX Can we take in a Con.t option?  That way we can handle the default case (and
   any case where we don't use constructors!) *)
val {get = entryInfo: FuncEntry.t -> Con.t -> FunctionEntry.t,
     set = setEntryInfo: (FuncEntry.t * (Con.t -> FunctionEntry.t)) -> unit,
     destroy = destroyEntryInfo} =
   Property.destGetSetOnce
   (FuncEntry.plist,
    Property.initFun (fn e => fn _ => raise Fail ("no entryInfo for " ^
                                                   (FuncEntry.toString e))))

fun transformFun func =
   let
      val {blocks, entries, mayInline, name, raises, returns} =
         Function.dest func

      (*
       * Setup for maps.
       *)
      (* Get be basic block associated with a label. *)
      val {get = getBlock: Label.t -> Block.t,
           set = setLabelBlock: Label.t * Block.t -> unit,
           destroy = destroyGetBlock} =
         Property.destGetSetOnce
         (Label.plist, Property.initFun (fn _ => raise NoSuchBlock))
      val () = Vector.foreach (blocks, fn b =>
         setLabelBlock (Block.label b, b))

      (* Identify blocks which are used as entry points. *)
      val {get = isEntryBlock: Label.t -> bool,
           set = setIsEntryBlock: (Label.t * bool) -> unit,
           destroy = destroyIsEntryBlock} =
         Property.destGetSet (Label.plist, Property.initConst false)
      val () = Vector.foreach (entries, fn FunctionEntry.T{start, ...} =>
         setIsEntryBlock (start, true))

      (* We use this to determine if a variable is used in a function, this way
         we can see that we need a var to be present when trying to skip past
         entries.

         XXX: A better way to do this would be to look at the def-use chain or
         the dominator tree to see if a variable needs to be in scope.  It's
         possible that the simple (mapping) approach is ignoring some potential
         optimizations.
      *)
      val {get = isVarUsed: Var.t -> bool,
           set = varIsUsed: (Var.t * bool) -> unit,
           destroy = destroyVarUsageMap} =
         Property.destGetSet (Var.plist, Property.initConst false)
      fun foreachVar fx =
         Vector.foreach
         (blocks, fn Block.T {args, label, statements, transfer, ...} =>
            (* Don't count a variable as being used if it only appears in an
               entry block. *)
            if isEntryBlock label
               then ()
               else
                (Vector.foreach (args, fn (v, _) => fx v)
                 ; Vector.foreach (statements,
                                   fn Statement.T {var, ty = _, exp} => 
                                      (Option.app (var, fx)
                                      (* XXX: Why was Exp not included in
                                         Function.foreachVar ? *)
                                      ; Exp.foreachVar (exp, fx)))
                 ; Transfer.foreachVar (transfer, fx)))
      val () = foreachVar (fn v => varIsUsed (v, true))

      val (newEntries, newBlocks) =
         Vector.fold (entries, ([],[]), fn (entry, (newEntries, newBlocks)) =>
         let
            val FunctionEntry.T {args = entryArgs,
                                 name = entryName,
                                 start,
                                 ...}              = entry
            (* Find the start block for the entry.  If the only thing the block
             * does is scruitinize to argument into constructors, we're
             * insterested.  If it does more than that, it's likely creating
             * vars that are expected to be around later in the function. *)
            val constructors =
               case Vector.peek (blocks, fn Block.T {label, ...} => Label.equals (label, start)) of
                  SOME (Block.T {statements, transfer =
                     Transfer.Case {cases = Cases.Con v, ...}, ...}) =>
                        if Vector.length statements = 0
                           then v
                           else Vector.new0 ()
               |  _  => Vector.new0 ()
            (*
             * If the constructed value is used later in the function, we can't
             * create an entry that skips its definition.
             *
             * TODO: If it turns out that this happens often, it may be useful
             * to re-construct it on demand later.
             *)
            val constructors =
               if (not (Vector.exists (entryArgs, isVarUsed o #1)))
                  then constructors
                  else Vector.new0 ()
            val {get = caseEntry: Con.t -> FunctionEntry.t,
                 set = setCaseEntry: Con.t * FunctionEntry.t -> unit,
                 (* Referenced outside of this scope.  Be careful about
                    destroying it. *)
                 destroy = destroyCaseEntry} =
               Property.destGetSet
               (Con.plist,
                Property.initFun (fn _ => entry)
               )
            val (newEntries, newBlocks) = Vector.fold
               (constructors, (newEntries, newBlocks),
               fn ((constructor, label), (newEntries, newBlocks)) =>
               let
                  (* Create a new block for the entry point to jump to.
                   * The new block takes in no arguments (they were defined in
                   * the entry point), then passes the entry points' arguments
                   * off to the block that the case transfer would ultimately
                   * have jumped to for the current constructor.
                   *)
                  val newEntryName: FuncEntry.t = FuncEntry.new entryName
                  val destBlock = getBlock label
                  val blockArgs = Block.args destBlock
                  val entryArgs =
                     Vector.map (blockArgs, fn (x, ty) => (Var.new x, ty))
                  val entryArgsNoType = Vector.map (entryArgs, fn (x,_) => x)
                  val newJoin = Label.new label
                  val joinBlock = Block.T {args = Vector.new0 (),
                                           label = newJoin,
                                           statements = Vector.new0 (),
                                           transfer = (Transfer.Goto
                                                      {dst = label,
                                                       args = entryArgsNoType})}
                  (* args should be the arguments of the destination block. *)
                  val newEntry = FunctionEntry.T {args = entryArgs,
                                                  name = newEntryName,
                                                  start = newJoin}
                  val () = setCaseEntry (constructor, newEntry)
               in
                  (newEntry :: newEntries, joinBlock :: newBlocks)
               end)
            val () = setEntryInfo (entryName, caseEntry)
         in
            (newEntries, newBlocks)
         end)
      val newEntries = Vector.fromList newEntries
      val newBlocks = Vector.fromList newBlocks
      (* Add the new blocks and entry points to the function. *)
      val newFunction = Function.new {blocks = Vector.concat [blocks, newBlocks],
                                      entries = Vector.concat [entries, newEntries],
                                      mayInline = mayInline,
                                      name = name,
                                      raises = raises,
                                      returns = returns}

      val () = destroyGetBlock ()
      val () = destroyIsEntryBlock ()
      val () = destroyVarUsageMap ()
   in
      newFunction
   end

fun transform (Program.T {datatypes, globals, functions, main}) =
   let
      (* Add new entry points to functions which case immediately upon entry. *)
      val functions = List.map (functions, transformFun)

      (* Update the callers of those functions *)
      val functions = List.map (functions, fn func =>
         let
            val {blocks, entries, mayInline, name, raises, returns} =
               Function.dest func
            val blocks = Vector.map
               (blocks,
               fn Block.T {args, label, statements, transfer = transfer as
                  Transfer.Call{args = tr_args, entry, func, return}} =>
                  let
                     (* XXX: Right now, only handing calls with one argument,
                        so that we only have one constructor to search for. *)
                     val constructed_var =
                        if Vector.length tr_args > 0
                           then Vector.sub (tr_args, 0)
                           (* FIXME: Ugly hack.  My intent here is to make sure
                              that there is no match for constructed_var, but I
                              really just need to throw an exception or
                              re-think my flow control.  *)
                           else Var.newNoname ()
                     (* Grab the statement that creates this argument. *)
                     val stmt_o = Vector.peek (statements,
                        fn Statement.T{var = SOME var, ...} =>
                           Var.equals (var, constructed_var)
                        |  _ => false)
                     (* If yes, then use the contructor's arguments. *)
                     val (new_args, skipped_con) = case stmt_o of
                        SOME (Statement.T{exp = Exp.ConApp {args, con}, ...}) =>
                           (args, SOME con)
                     |  _ => (tr_args, NONE)
                     (* And update which entry we call. *)
                     val new_entry = case skipped_con of
                        NONE  => entry
                     |  SOME con => FunctionEntry.name (entryInfo entry con)
                     (* Make sure that the new entry was actually created! *)
                     val new_transfer = if FuncEntry.equals (entry, new_entry)
                        then transfer
                        else Transfer.Call {args = new_args,
                                            entry = new_entry,
                                            func = func,
                                            return = return}
                  in
                     Block.T {args = args,
                              label = label,
                              statements = statements,
                              transfer = new_transfer}
                  end
               |  origBlock => origBlock
               handle Subscript => origBlock
               )
         in
            Function.new {blocks = blocks,
                          entries = entries,
                          mayInline = mayInline,
                          name = name,
                          raises = raises,
                          returns = returns}
         end)

      val () = destroyEntryInfo ()
   in
      Program.T {datatypes = datatypes,
                 globals = globals,
                 functions = functions,
                 main = main}
   end
end
