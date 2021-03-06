(* Copyright (C) 2013-2015 David Larsen.
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


(* Since entryInfo is a mapping to a mapping, we need a good way of making sure
 * that we destroy the Con.t |-> FunctionEntry.t maps when we destroy the
 * entryInfo map.  To make sure that we don't forget about this later, override
 * the set and destroy methods to take care of the 2nd level maps.*)
local
   val conInfoMapDestructors = ref []
   val {get = entryInfo: FuncEntry.t -> Con.t -> FunctionEntry.t,
        set = setEntryInfo: (FuncEntry.t * (Con.t -> FunctionEntry.t)) -> unit,
        destroy = destroyEntryInfo} =
      Property.destGetSetOnce
      (FuncEntry.plist,
       Property.initFun (fn e => fn _ => raise Fail ("no entryInfo for " ^
                                                      (FuncEntry.toString e))))
in
   val entryInfo = entryInfo
   val setEntryInfo = fn (fe, conInfoMap, destructor: unit -> unit) =>
      let
         val () = conInfoMapDestructors := destructor :: !conInfoMapDestructors
      in
         setEntryInfo (fe, conInfoMap)
      end
   val destroyEntryInfo = fn () =>
      (List.foreach (!conInfoMapDestructors, fn destructor => destructor ());
       destroyEntryInfo ())
end

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

      (* Build a dictionary of Var.t -> Type.t to use when re-constructing the
         datatype in the new entry. *)
      val {get = varType: Var.t -> Type.t,
           set = varSetType: (Var.t * Type.t) -> unit,
           destroy = destroyVarTypeMap} =
         Property.destGetSet (Var.plist,
                              Property.initRaise ("varType", Var.layout))
      fun foreachVar fx =
         Vector.foreach
         (blocks, fn Block.T {args, label, statements, ...} =>
            (* Don't count a variable as being used if it only appears in an
               entry block. *)
            if isEntryBlock label
               then ()
               else
                (Vector.foreach (args, fn (v, t) => fx t v)
                 ; Vector.foreach (statements,
                                   fn Statement.T {var, ty, exp} =>
                                      (Option.app (var, fx ty)
                                      (* XXX: Why was Exp not included in
                                         Function.foreachVar ? *)
                                      ; Exp.foreachVar (exp, fx ty)))))
      val () = foreachVar (fn t => fn v => varSetType (v, t))
      fun foreachVar fx =
         Vector.foreach (entries, fn FunctionEntry.T {args, ...} =>
            Vector.foreach(args, fn (v,t) => fx t v))
      val () = foreachVar (fn t => fn v => varSetType (v, t))

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
            val constructorCase =
               case Vector.peek (blocks, fn Block.T {label, ...} => Label.equals (label, start)) of
                  SOME (Block.T {statements, transfer =
                     Transfer.Case {cases = Cases.Con v, test, ...}, ...}) =>
                        if Vector.length statements = 0
                           then SOME {scruineeName=test, constructors = v}
                           else NONE
               |  _  => NONE
            val {get = caseEntry: Con.t -> FunctionEntry.t,
                 set = setCaseEntry: Con.t * FunctionEntry.t -> unit,
                 (* Referenced outside of this scope.  Be careful about
                    destroying it. *)
                 destroy = destroyCaseEntry} =
               Property.destGetSetOnce
               (Con.plist,
                Property.initFun (fn _ => entry)
               )
            val (newEntries, newBlocks) = case constructorCase of
               SOME {constructors, scruineeName} =>
                  Vector.fold (constructors, (newEntries, newBlocks),
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
                     val origEntryArgs = entryArgs
                     val entryArgs =
                        Vector.map (blockArgs, fn (x, ty) => (Var.new x, ty))
                     val entryArgsNoType = Vector.map (entryArgs, fn (x,_) => x)

                     val recreatedConstructor = Statement.T
                        {var = SOME scruineeName,
                         exp = Exp.ConApp {args=Vector.map(entryArgs, #1),
                                           con=constructor},
                         ty = varType scruineeName}


                     val joinStatements = Vector.new1 recreatedConstructor

                     val newJoin = Label.new label
                     val joinBlock = Block.T {args = Vector.new0 (),
                                              label = newJoin,
                                              statements = joinStatements,
                                              transfer = (Transfer.Goto
                                                         {dst = label,
                                                          args = entryArgsNoType})}
                     (* args should be the arguments of the destination block. *)
                     (* FIXME: Ok, so the problem that I'm having with the
                       regression tests (see ugly hack below) is that we might
                       be replacing an entry that had arguments besides the
                       scruitnee.  We need to make sure that we can take in
                       those arguments as well. *)
                     val newEntry = FunctionEntry.T {args = entryArgs,
                                                     name = newEntryName,
                                                     start = newJoin}

                     (* FIXME: ugly hack to only take in entries that only had
                     one argument. *)
                     val () = if (Vector.size origEntryArgs) > 1
                        then ()
                        else setCaseEntry (constructor, newEntry)

                  in
                     (* FIXME: ugly hack to only take in entries that only had
                     one argument. *)
                     if (Vector.size origEntryArgs) > 1
                        then (newEntries, newBlocks)
                        else (newEntry :: newEntries, joinBlock :: newBlocks)
                  end)
            |  NONE  => (newEntries, newBlocks)
            val () = setEntryInfo (entryName, caseEntry, destroyCaseEntry)
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
      val () = destroyVarTypeMap ()
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
      restore(Program.T {datatypes = datatypes,
                         globals = globals,
                         functions = functions,
                         main = main})
   end
end
