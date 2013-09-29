(* Copyright (C) 2013 David Larsen.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

(*
 * Takes functions that form a strongly connected component in the tail-call
 * graph an combines them into one function.
 *)
functor MeCombineTailcalls (S: ME_SSA_TRANSFORM_STRUCTS): ME_SSA_TRANSFORM =
struct

structure Graph = DirectedGraph

open S

fun transform (Program.T {datatypes, globals, functions, main}) =
   let
      (* Strategy:
         Build a graph of all of the tailcalls.
         Grab the strongly connected components and combine them into a
         function.
         Update the callers.
       *)
      val tailCallGraph = Graph.new ()
      val {get = nodeFunc, set = setNodeFunc, destroy = destroyNode} =
         Property.destGetSetOnce (Graph.Node.plist, Property.initFun
            (fn _ => raise Fail "Unset property for nodeFunc"))
      val {get = funcNode, destroy = destroyFunc} =
         Property.destGet (Func.plist, Property.initFun
            (fn f =>
               let
                  val node = Graph.newNode tailCallGraph
                  val () = setNodeFunc (node, f)
               in
                  node
               end))
      val {get = funcFunction,
           set = setFuncFunction,
           destroy = destroyFuncFunction} =
         Property.destGetSetOnce (Func.plist, Property.initFun
            (fn _ => Error.bug "funcFunction unset"))
      (* Used for updating calls to functions which were combined into bigger
         functions. *)
      val {get = updateFunc: Func.t -> Func.t,
           set = setNewFunc: Func.t * Func.t -> unit,
           destroy = destroyUpdateFunc} =
         Property.destGetSetOnce (Func.plist, Property.initFun
            (fn f => f))
      val () = List.foreach
         (functions,
          fn f => setFuncFunction (Function.name f, f))
      val () = List.foreach (functions, fn f =>
         Vector.foreach (Function.blocks f, fn block =>
            case Block.transfer block of
               Transfer.Call {func, return = Return.Tail, ...} =>
                  ignore (Graph.addEdge
                     (tailCallGraph, {from = (funcNode o Function.name) f,
                                      to= funcNode func}))
            |  _ => ()
            )
         )
      val components = Graph.stronglyConnectedComponents tailCallGraph
      val bigComponents = List.fold (components, [], fn (c, l) =>
         if (List.length c) > 1
            then c :: l
            else l
         )

      (* Take all of the functions' blocks, entries, etc. and combine them into
         one new large function. *)
      val (newFunctions, functionsToRemove) =
         List.fold (bigComponents, ([],[]), fn (c, (newFunctions, functionsToRemove)) =>
            let
               val funcsToBeCombined = List.map (c, nodeFunc)
               val functionsToBeCombined = List.map (c, funcFunction o nodeFunc)
               fun getFromFuncs a = (Vector.concat o List.map) (functionsToBeCombined, a)
               val blocks = getFromFuncs Function.blocks
               val entries = getFromFuncs Function.entries
               val mayInline = List.forall (functionsToBeCombined, Function.mayInline)
               val name = (Func.newString o String.concat o List.map)
                  (functionsToBeCombined, Func.toString o Function.name)
               (* Update the names of a combined function. *)
               val () = List.foreach (funcsToBeCombined, fn f => setNewFunc (f, name))
               (* XXX: All of these should raise/return the same type.  Is it
                  worth checking here to make sure that they do? *)
               val {raises, returns, ...} =
                  Function.dest (hd functionsToBeCombined)
               val combinedFunc = Function.new {blocks = blocks,
                                                entries = entries,
                                                mayInline = mayInline,
                                                name = name,
                                                raises = raises,
                                                returns = returns}
            in
               (combinedFunc :: newFunctions,
                functionsToBeCombined @ functionsToRemove)
            end)
      (* Remove the now-combined functions. *)
      val functions = List.fold (functions, [], fn (f, functions) =>
         if List.exists (functionsToRemove, fn ftr => Func.equals(Function.name ftr, Function.name f))
            then functions
            else f :: functions
         )
      val functions = newFunctions @ functions
      (* Update the callers of the now-combined functions. *)
      val functions = List.map (functions, fn f =>
         let
            val {blocks, entries, mayInline, name, raises, returns} =
               Function.dest f
            val blocks = Vector.map
               (blocks, fn Block.T {args, label, statements, transfer} =>
                  let
                     val transfer = case transfer of
                        Transfer.Call {args, entry, func, return} =>
                           Transfer.Call {args = args,
                                          entry = entry,
                                          func = updateFunc func,
                                          return = return}
                        |  _  => transfer
                  in
                     Block.T {args = args,
                              label = label,
                              statements = statements,
                              transfer = transfer}
                  end
               )
         in
            Function.new {blocks = blocks,
                          entries = entries,
                          mayInline = mayInline,
                          name = name,
                          raises = raises,
                          returns = returns}
         end)
      val () = (destroyNode ()
               ; destroyFunc ()
               ; destroyFuncFunction ()
               ; destroyUpdateFunc ())
   in
      Program.T {datatypes = datatypes,
                 functions = functions,
                 globals = globals,
                 main = main}
   end

end
