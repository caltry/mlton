(* Copyright (C) 2013 Matthew Fluet, David Larsen.
 * Copyright (C) 2009 Matthew Fluet.
 * Copyright (C) 1999-2007 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor MeSignalCheck (S: ME_RSSA_TRANSFORM_STRUCTS): ME_RSSA_TRANSFORM =
struct

open S
open Rssa

structure CFunction =
   struct
      open CFunction Type.BuiltInCFunction
   end

structure Graph = DirectedGraph
local
   open Graph
in
   structure Node = Node
   structure Forest = LoopForest
end

fun insertInFunction (f: Function.t): Function.t =
   let
      val {blocks, entries, name, raises, returns} =
         Function.dest f
      val {get = labelIndex: Label.t -> int, set = setLabelIndex, ...} =
         Property.getSetOnce
         (Label.plist, Property.initRaise ("index", Label.layout))
      val _ =
         Vector.foreachi (blocks, fn (i, Block.T {label, ...}) =>
                          setLabelIndex (label, i))
      val g = Graph.new ()
      val n = Vector.length blocks
      val {get = nodeIndex: unit Node.t -> int, set = setNodeIndex, ...} =
         Property.getSetOnce
         (Node.plist, Property.initRaise ("index", Node.layout))
      val nodes =
         Vector.tabulate (n, fn i =>
                          let
                             val n = Graph.newNode g
                             val _ = setNodeIndex (n, i)
                          in
                             n
                          end)
      val isHeader = Array.new (n, false)
      fun indexNode i = Vector.sub (nodes, i)
      val labelNode = indexNode o labelIndex
      val _ =
         Vector.foreachi
         (blocks, fn (i, Block.T {transfer, ...}) =>
          let
             val from = indexNode i
          in
             if (case transfer of
                    Transfer.CCall {func, ...} =>
                       CFunction.maySwitchThreads func
                  | _ => false)
                then ()
             else
                Transfer.foreachLabel
                (transfer, fn to =>
                 (ignore o Graph.addEdge) 
                 (g, {from = from, to = labelNode to}))
          end)
      val extra: Block.t list ref = ref []
      fun addSignalCheck (Block.T {args, kind, label, statements, transfer})
         : unit = 
         let
            val collect = Label.newNoname ()
            val collectReturn = Label.newNoname ()
            val dontCollect = Label.newNoname ()
            val res = Var.newNoname ()
            val compare =
               Vector.new1
               (Statement.PrimApp
                {args = (Vector.new2
                         (Operand.Runtime Runtime.GCField.Limit,
                          Operand.null)),
                 dst = SOME (res, Type.bool),
                 prim = Prim.cpointerEqual})
            val compareTransfer =
               Transfer.ifBool
               (Operand.Var {var = res, ty = Type.bool},
                {falsee = dontCollect,
                 truee = collect})
            val func = CFunction.gc {maySwitchThreads = true}
            val _ =
               extra :=
               Block.T {args = args,
                        kind = kind,
                        label = label,
                        statements = compare,
                        transfer = compareTransfer}
               :: (Block.T
                   {args = Vector.new0 (),
                    kind = Kind.Jump,
                    label = collect,
                    statements = Vector.new0 (),
                    transfer =
                    Transfer.CCall
                    {args = Vector.new3 (Operand.GCState,
                                         Operand.word (WordX.zero (WordSize.csize ())),
                                         Operand.bool false),
                     func = func,
                     return = SOME collectReturn}})
               :: (Block.T
                   {args = Vector.new0 (),
                    kind = Kind.CReturn {func = func},
                    label = collectReturn,
                    statements = Vector.new0 (),
                    transfer =
                    Transfer.Goto {dst = dontCollect,
                                   args = Vector.new0 ()}})
               :: Block.T {args = Vector.new0 (),
                           kind = Kind.Jump,
                           label = dontCollect,
                           statements = statements,
                           transfer = transfer}
               :: !extra
         in
            ()
         end
      (* Create extra blocks with signal checks for all blocks that are
       * loop headers.
       *)
      fun loop (f: unit Forest.t) =
         let
            val {loops, ...} = Forest.dest f
         in
            Vector.foreach
            (loops, fn {headers, child} =>
             let
                val _ =
                   Vector.foreach
                   (headers, fn n =>
                     if Array.sub (isHeader, nodeIndex n)
                        then ()
                        else
                          let
                             val i = nodeIndex n
                             val _ = Array.update (isHeader, i, true)
                          in
                             addSignalCheck (Vector.sub (blocks, i))
                          end)
                val _ = loop child
             in
                ()
             end)
         end
      (* Add a signal check at each function entry. *)
      val entries = Vector.map
         (entries,
          fn FunctionEntry.T {args, name, start} =>
            let
               val newStart = Label.newNoname ()
               val _ =
                  addSignalCheck
                  (Block.T {args = Vector.new0 (),
                            kind = Kind.Jump,
                            label = newStart,
                            statements = Vector.new0 (),
                            transfer = Transfer.Goto {args = Vector.new0 (),
                                                      dst = start}})
               val () = loop (Graph.loopForestSteensgaard (g, {root = labelNode start}))
            in
               FunctionEntry.T {args = args,
                                name = name,
                                start = newStart}
            end
         )
      val blocks =
         Vector.keepAllMap
         (blocks, fn b as Block.T {label, ...} =>
          if Array.sub (isHeader, labelIndex label)
             then NONE
          else SOME b)
      val blocks = Vector.concat [blocks, Vector.fromList (!extra)]
      val f = Function.new {blocks = blocks,
                            entries = entries,
                            name = name,
                            raises = raises,
                            returns = returns}
      val _ = Function.clear f
   in
      f
   end

fun transform p =
   let
      val Program.T {functions, handlesSignals, main, objectTypes} = p
   in
      if not handlesSignals
         then p
      else
         Program.T {functions = List.revMap (functions, insertInFunction),
                    handlesSignals = handlesSignals,
                    main = main,
                    objectTypes = objectTypes}
   end

end
