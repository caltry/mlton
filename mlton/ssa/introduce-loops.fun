(* Copyright (C) 2013 Matthew Fluet.
 * Copyright (C) 1999-2005, 2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

(* Change any toplevel function that calls itself in tail position
 * into one with a local loop and no self tail-calls.
 *)
functor MeIntroduceLoops (S: ME_SSA_TRANSFORM_STRUCTS): ME_SSA_TRANSFORM =
struct

open S
datatype z = datatype Exp.t
datatype z = datatype Transfer.t

structure Return =
   struct
      open Return

      fun isTail (z: t): bool =
         case z of
            Dead => false
          | NonTail _ => false
          | Tail => true
   end

fun transform (Program.T {datatypes, globals, functions, main}) =
   let
      val functions =
         List.revMap
         (functions, fn f =>
          let
             val {blocks, entries, mayInline, name, raises, returns} =
                Function.dest f
             val selfTailCallEntries = ref []
             val _ =
                Vector.foreach
                (blocks, fn Block.T {transfer, ...} =>
                 case transfer of
                    Call {func, entry, return, ...} =>
                       if Func.equals (name, func)
                          andalso Return.isTail return
                          then List.push (selfTailCallEntries, entry)
                       else ()
                  | _ => ())
             val selfTailCallEntries =
                List.removeDuplicates (!selfTailCallEntries, FuncEntry.equals)
             val (entries, blocks) =
                if not (List.isEmpty selfTailCallEntries)
                   then
                      let
                         val _ = Control.diagnostics
                            (fn display =>
                             let open Layout
                             in
                                display (Func.layout name)
                             end)
                         val {get = entryToLoop : FuncEntry.t -> Label.t,
                              rem = remEntryToLoop,
                              set = setEntryToLoop} =
                            Property.getSetOnce
                            (FuncEntry.plist,
                             Property.initRaise ("IntroduceLoops.entryToLoop", FuncEntry.layout))
                         val (entries, newBlocks) =
                            Vector.mapAndFold
                            (entries, [], fn (entry as FunctionEntry.T {args, name, start}, newBlocks) =>
                             if List.contains (selfTailCallEntries, name, FuncEntry.equals)
                                then let
                                        val newArgs =
                                           Vector.map (args, fn (x, t) => (Var.new x, t))
                                        val loopName = Label.newString "loop"
                                        val loopSName = Label.newString "loopS"
                                        val () = setEntryToLoop (name, loopName)
                                     in
                                        (FunctionEntry.T
                                         {args = newArgs,
                                          name = name,
                                          start = loopSName},
                                         Block.T
                                         {label = loopSName,
                                          args = Vector.new0 (),
                                          statements = Vector.new0 (),
                                          transfer = Goto {dst = loopName,
                                                           args = Vector.map (newArgs, #1)}} ::
                                         Block.T
                                         {label = loopName,
                                          args = args,
                                          statements = Vector.new0 (),
                                          transfer = Goto {dst = start,
                                                           args = Vector.new0 ()}} ::
                                         newBlocks)
                                     end
                             else (entry, newBlocks))
                         val blocks = 
                            Vector.map
                            (blocks,
                             fn Block.T {label, args, statements, transfer} =>
                             let
                                val transfer =
                                   case transfer of
                                      Call {func, entry, args, return} =>
                                         if Func.equals (name, func)
                                            andalso Return.isTail return
                                            then Goto {dst = entryToLoop entry,
                                                       args = args}
                                         else transfer
                                    | _ => transfer
                             in
                                Block.T {label = label,
                                         args = args,
                                         statements = statements,
                                         transfer = transfer}
                             end)
                         val () = List.foreach (selfTailCallEntries, remEntryToLoop)
                      in
                         (entries, Vector.concat [Vector.fromList newBlocks, blocks])
                      end
                else (entries, blocks)
          in
             Function.new {blocks = blocks,
                           entries = entries,
                           mayInline = mayInline,
                           name = name,
                           raises = raises,
                           returns = returns}
          end)
   in
      Program.T {datatypes = datatypes,
                 globals = globals,
                 functions = functions,
                 main = main}
   end

end
