(* Copyright (C) 2013 Matthew Fluet, David Larsen.
 * Copyright (C) 2011 Matthew Fluet.
 * Copyright (C) 1999-2006 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor MeAnalyze (S: ME_ANALYZE_STRUCTS): ME_ANALYZE =
struct

open S
datatype z = datatype Exp.t
datatype z = datatype Transfer.t

fun 'a analyze
   {coerce, conApp, const,
    filter, filterWord,
    fromType, layout, primApp,
    program = Program.T {main, globals, functions, ...},
    select, tuple, useFromTypeOnBinds} =
   let
      val unit = fromType Type.unit
      fun coerces (msg, from, to) =
         if Vector.length from = Vector.length to
            then Vector.foreach2 (from, to, fn (from, to) =>
                                  coerce {from = from, to = to})
         else Error.bug (concat ["Analyze.coerces length mismatch: ", msg])
      val {get = value: Var.t -> 'a, set = setValue, ...} =
         Property.getSetOnce
         (Var.plist,
          Property.initRaise ("analyze var value", Var.layout))
      val value = Trace.trace ("Analyze.value", Var.layout, layout) value
      fun values xs = Vector.map (xs, value)
      val {get = func, set = setFunc, ...} =
         Property.getSetOnce
         (Func.plist, Property.initRaise ("analyze func name", Func.layout))
      val {get = entry, set = setEntry, ...} =
         Property.getSetOnce
         (FuncEntry.plist, Property.initRaise ("analyze entry name", FuncEntry.layout))
      val {get = labelInfo, set = setLabelInfo, ...} =
         Property.getSetOnce
         (Label.plist, Property.initRaise ("analyze label", Label.layout))
      val labelArgs = #args o labelInfo
      val labelValues = #values o labelInfo
      fun loopArgs args =
         Vector.map (args, fn (x, t) =>
                     let val v = fromType t
                     in setValue (x, v)
                        ; v
                     end)
      val _ =
         List.foreach
         (functions, fn f =>
          let
             val {entries, name, raises, returns, ...} = Function.dest f
          in
             setFunc (name, {raises = Option.map (raises, fn ts =>
                                                  Vector.map (ts, fromType)),
                             returns = Option.map (returns, fn ts =>
                                                   Vector.map (ts, fromType))})
             ; Vector.foreach (entries, fn FunctionEntry.T {args, name, ...} =>
                               setEntry (name, loopArgs args))
          end)
      fun loopTransfer (t: Transfer.t,
                        shouldReturns: 'a vector option,
                        shouldRaises: 'a vector option): unit =
        (case t of
            Arith {prim, args, overflow, success, ty} =>
               (coerces ("arith", Vector.new0 (), labelValues overflow)
                ; coerce {from = primApp {prim = prim,
                                          targs = Vector.new0 (),
                                          args = values args,
                                          resultType = ty,
                                          resultVar = NONE},
                          to = Vector.sub (labelValues success, 0)})
          | Bug => ()
          | Call {func = f, entry = e, args, return, ...} =>
               let
                  val {raises, returns} = func f
                  val formals = entry e
                  val _ = coerces ("formals", values args, formals)
                  fun noHandler () =
                     case (raises, shouldRaises) of
                        (NONE, NONE) => ()
                      | (NONE, SOME _) => ()
                      | (SOME _, NONE) => 
                           Error.bug "Analyze.loopTransfer: raise mismatch"
                      | (SOME vs, SOME vs') => coerces ("noHandler", vs, vs')
                  datatype z = datatype Return.t
               in
                  case return of
                     Dead =>
                        if isSome returns orelse isSome raises
                           then Error.bug "Analyze.loopTransfer: return mismatch at Dead"
                        else ()
                   | NonTail {cont, handler} => 
                        (Option.app (returns, fn vs =>
                                     coerces ("returns", vs, labelValues cont))
                         ; (case handler of
                               Handler.Caller => noHandler ()
                             | Handler.Dead =>
                                  if isSome raises
                                     then Error.bug "Analyze.loopTransfer: raise mismatch at NonTail"
                                  else ()
                             | Handler.Handle h =>
                                  let
                                     val _ =
                                        case raises of
                                           NONE => ()
                                         | SOME vs =>
                                              coerces ("handle", vs,
                                                       labelValues h)
                                  in
                                     ()
                                  end))
                   | Tail =>
                        let
                           val _ = noHandler ()
                           val _ =
                              case (returns, shouldReturns) of
                                 (NONE, NONE) => ()
                               | (NONE, SOME _) => ()
                               | (SOME _, NONE) =>
                                    Error.bug "Analyze.loopTransfer: return mismatch at Tail"
                               | (SOME vs, SOME vs') =>
                                    coerces ("tail", vs, vs')
                        in
                           ()
                        end

               end
          | Case {test, cases, default, ...} =>
               let
                  val test = value test
                  fun ensureNullary j =
                     if 0 = Vector.length (labelValues j)
                        then ()
                     else Error.bug (concat ["Analyze.loopTransfer: Case:",
                                             Label.toString j,
                                             " must be nullary"])
                  fun ensureSize (w, s) =
                     if WordSize.equals (s, WordX.size w)
                        then ()
                     else Error.bug (concat ["Analyze.loopTransfer: Case:",
                                             WordX.toString w,
                                             " must be size ",
                                             WordSize.toString s])
                  fun doitWord (s, cs) =
                     (ignore (filterWord (test, s))
                      ; Vector.foreach (cs, fn (w, j) =>
                                        (ensureSize (w, s)
                                         ; ensureNullary j)))
                  fun doitCon cs =
                     Vector.foreach (cs, fn (c, j) =>
                                     filter (test, c, labelValues j))
                  datatype z = datatype Cases.t
                  val _ =
                     case cases of
                        Con cs => doitCon cs
                      | Word (s, cs) => doitWord (s, cs)
                  val _ = Option.app (default, ensureNullary)
               in ()
               end
          | Goto {dst, args} => coerces ("goto", values args, labelValues dst)
          | Raise xs =>
               (case shouldRaises of
                   NONE => Error.bug "Analyze.loopTransfer: raise mismatch at Raise"
                 | SOME vs => coerces ("raise", values xs, vs))
          | Return xs =>
               (case shouldReturns of
                   NONE => Error.bug "Analyze.loopTransfer: return mismatch at Return"
                 | SOME vs => coerces ("return", values xs, vs))
          | Runtime {prim, args, return} =>
               let
                  val xts = labelArgs return
                  val (resultVar, resultType) =
                     if 0 = Vector.length xts
                        then (NONE, Type.unit)
                     else
                        let
                           val (x, t) = Vector.sub (xts, 0)
                        in
                           (SOME x, t)
                        end
                  val _ =
                     primApp {prim = prim,
                              targs = Vector.new0 (),
                              args = values args,
                              resultType = resultType,
                              resultVar = resultVar}
               in 
                  ()
               end)
      val loopTransfer =
         Trace.trace3
         ("Analyze.loopTransfer",
          Transfer.layout, 
          Option.layout (Vector.layout layout),
          Option.layout (Vector.layout layout),
          Layout.ignore)
         loopTransfer
      fun loopStatement (Statement.T {var, exp, ty}): unit =
         let
            val v =
               case exp of
                  ConApp {con, args} => conApp {con = con, args = values args}
                | Const c => const c
                | PrimApp {prim, targs, args, ...} =>
                     primApp {prim = prim,
                              targs = targs,
                              args = values args,
                              resultType = ty,
                              resultVar = var}
                | Profile _ => unit
                | Select {tuple, offset} =>
                     select {tuple = value tuple,
                             offset = offset,
                             resultType = ty}
                | Tuple xs =>
                     if 1 = Vector.length xs
                        then Error.bug "Analyze.loopStatement: unary tuple"
                     else tuple (values xs)
                | Var x => value x
         in
            Option.app
            (var, fn var =>
             if useFromTypeOnBinds
                then let
                        val v' = fromType ty
                        val _ = coerce {from = v, to = v'}
                        val _ = setValue (var, v')
                     in
                        ()
                     end
             else setValue (var, v))
         end
      val loopStatement =
         Trace.trace ("Analyze.loopStatement", Statement.layout, Unit.layout)
         loopStatement
      val _ = coerces ("main entry", Vector.new0 (), entry (#entry main))
      val _ = Vector.foreach (globals, loopStatement)
      val _ =
         List.foreach
         (functions, fn f =>
          let
             val {blocks, name, entries, ...} = Function.dest f
             val _ =
                Vector.foreach
                (blocks, fn b as Block.T {label, args, ...} =>
                 setLabelInfo (label, {args = args,
                                       block = b,
                                       values = loopArgs args,
                                       visited = ref false}))
             val {returns, raises, ...} = func name
             fun visit (l: Label.t) =
                let
                   val {block, visited, ...} = labelInfo l
                in
                   if !visited
                      then ()
                   else
                      let
                         val _ = visited := true
                         val Block.T {statements, transfer, ...} = block
                      in
                         Vector.foreach (statements, loopStatement)
                         ; loopTransfer (transfer, returns, raises)
                         ; Transfer.foreachLabel (transfer, visit)
                      end
                end
             val _ = Vector.foreach (entries, visit o FunctionEntry.start)
          in
             ()
          end)
   in
      {func = func,
       entry = entry,
       label = labelValues,
       value = value}
   end

end
