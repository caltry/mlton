(* Copyright (C) 2013 Matthew Fluet, David Larsen.
 * Copyright (C) 2011 Matthew Fluet.
 * Copyright (C) 1999-2007 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor MeAnalyze2 (S: ME_ANALYZE2_STRUCTS): ME_ANALYZE2 =
struct

open S
datatype z = datatype Exp.t
datatype z = datatype Statement.t
datatype z = datatype Transfer.t

fun 'a analyze
   {base, coerce, const, filter, filterWord, fromType, inject, layout, object, primApp,
    program = Program.T {functions, globals, main, ...},
    select, update, useFromTypeOnBinds} =
   let
      fun coerces (msg, from, to) =
         if Vector.length from = Vector.length to
            then Vector.foreach2 (from, to, fn (from, to) =>
                                  coerce {from = from, to = to})
         else Error.bug (concat ["Analyze2.coerces: length mismatch: ", msg])
      val {get = value: Var.t -> 'a, set = setValue, ...} =
         Property.getSetOnce
         (Var.plist,
          Property.initRaise ("analyze var value", Var.layout))
      val value = Trace.trace ("Analyze2.value", Var.layout, layout) value
      fun values xs = Vector.map (xs, value)
      val {get = funcEntry, set = setFuncEntry, ...} =
         Property.getSetOnce
         (FuncEntry.plist, Property.initRaise ("analyze funcEntry name",
         FuncEntry.layout))
      val {get = func, set = setFunc, ...} =
         Property.getSetOnce
         (Func.plist, Property.initRaise ("analyze func name", Func.layout))
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
             val entryNames = Vector.map
               (entries,
               fn FunctionEntry.T{args, name, ...} =>
                  (setFuncEntry (name, {args = loopArgs args});
                  name)
               )
          in
             setFunc (name, {entries = entryNames,
                             raises = Option.map (raises, fn ts =>
                                                  Vector.map (ts, fromType)),
                             returns = Option.map (returns, fn ts =>
                                                   Vector.map (ts, fromType))})
          end)
      fun loopTransfer (t: Transfer.t,
                        shouldReturns: 'a vector option,
                        shouldRaises: 'a vector option): unit =
        (case t of
            Arith {prim, args, overflow, success, ty} =>
               (coerces ("arith", Vector.new0 (), labelValues overflow)
                ; coerce {from = primApp {prim = prim,
                                          args = values args,
                                          resultType = ty,
                                          resultVar = NONE},
                          to = Vector.sub (labelValues success, 0)})
          | Bug => ()
          | Call {func = f, entry, args, return, ...} =>
               let
                  val {entries, raises, returns} = func f
                  val {args = formals, ...} = funcEntry entry
                  val _ = coerces ("formals", values args, formals)
                  fun noHandler () =
                     case (raises, shouldRaises) of
                        (NONE, NONE) => ()
                      | (NONE, SOME _) => ()
                      | (SOME _, NONE) => 
                           Error.bug "Analyze2.loopTransfer: raise mismatch"
                      | (SOME vs, SOME vs') => coerces ("noHandler", vs, vs')
                  datatype z = datatype Return.t
               in
                  case return of
                     Dead =>
                        if isSome returns orelse isSome raises
                           then Error.bug "Analyze2.loopTransfer: return mismatch at Dead"
                        else ()
                   | NonTail {cont, handler} => 
                        (Option.app (returns, fn vs =>
                                     coerces ("returns", vs, labelValues cont))
                         ; (case handler of
                               Handler.Caller => noHandler ()
                             | Handler.Dead =>
                                  if isSome raises
                                     then Error.bug "Analyze2.loopTransfer: raise mismatch at NonTail"
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
                                    Error.bug "Analyze2.loopTransfer: return mismatch at Tail"
                               | (SOME vs, SOME vs') =>
                                    coerces ("tail", vs, vs')
                        in
                           ()
                        end

               end
          | Case {test, cases, default, ...} =>
               let
                  val test = value test
                  fun ensureSize (w, s) =
                     if WordSize.equals (s, WordX.size w)
                        then ()
                     else Error.bug (concat ["Analyze.loopTransfer: Case:",
                                             WordX.toString w,
                                             " must be size ",
                                             WordSize.toString s])
                  fun ensureNullary j =
                     if 0 = Vector.length (labelValues j)
                        then ()
                     else Error.bug (concat ["Analyze2.loopTransfer: Case:",
                                             Label.toString j,
                                             " must be nullary"])
                  fun doitWord (s, cs) =
                     (ignore (filterWord (test, s))
                      ; Vector.foreach (cs, fn (w, j) =>
                                        (ensureSize (w, s)
                                         ; ensureNullary j)))
                  fun doitCon cs =
                     Vector.foreach
                     (cs, fn (c, j) =>
                      let
                         val v = labelValues j
                         val variant =
                            case Vector.length v of
                               0 => NONE
                             | 1 => SOME (Vector.sub (v, 0))
                             | _ => Error.bug "Analyze2.loopTransfer: Case:conApp with >1 arg"
                      in
                         filter {con = c,
                                 test = test,
                                 variant = variant}
                      end)
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
                   NONE => Error.bug "Analyze2.loopTransfer: raise mismatch at Raise"
                 | SOME vs => coerces ("raise", values xs, vs))
          | Return xs =>
               (case shouldReturns of
                   NONE => Error.bug "Analyze2.loopTransfer: return mismatch at Return"
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
                              args = values args,
                              resultType = resultType,
                              resultVar = resultVar}
               in 
                  ()
               end)
      val loopTransfer =
         Trace.trace3
         ("Analyze2.loopTransfer",
          Transfer.layout, 
          Option.layout (Vector.layout layout),
          Option.layout (Vector.layout layout),
          Layout.ignore)
         loopTransfer
      fun baseValue b = base (Base.map (b, value))
      fun loopBind {exp, ty, var}: 'a =
         case exp of
            Const c => const c
          | Inject {sum, variant} =>
               inject {sum = sum,
                       variant = value variant}
          | Object {args, con} =>
               let
                  val args =
                     case Type.dest ty of
                        Type.Object {args = ts, ...} =>
                           Prod.make
                           (Vector.map2
                            (args, Prod.dest ts,
                             fn (x, {isMutable, ...}) =>
                             {elt = value x,
                              isMutable = isMutable}))
                      | _ => Error.bug "Analyze2.loopBind: strange object"
               in
                  object {args = args,
                          con = con,
                          resultType = ty}
               end
          | PrimApp {prim, args, ...} =>
               primApp {prim = prim,
                        args = values args,
                        resultType = ty,
                        resultVar = var}
          | Select {base, offset} =>
               select {base = baseValue base,
                       offset = offset,
                       resultType = ty}
          | Var x => value x
      fun loopStatement (s: Statement.t): unit =
         (case s of
             Bind (b as {ty, var, ...}) =>
                let
                   val v = loopBind b
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
          | Profile _ => ()
          | Update {base, offset, value = v} =>
             update {base = baseValue base,
                     offset = offset,
                     value = value v})
      val loopStatement =
         Trace.trace ("Analyze2.loopStatement",
                      Statement.layout,
                      Unit.layout)
         loopStatement
      val _ = coerces ("main entry", Vector.new0 (), #args (funcEntry (#entry main)))
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
             val _ = Vector.foreach (entries,
                fn FunctionEntry.T{start, ...} => visit start
               )
          in
             ()
          end)
   in
      {func = func,
       funcEntry = funcEntry,
       label = labelValues,
       value = value}
   end

end
