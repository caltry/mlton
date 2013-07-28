(* Copyright (C) 2009,2013 Matthew Fluet.
 * Copyright (C) 1999-2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature HANDLER =
   sig
      structure Label: LABEL

      datatype t =
         Caller
       | Dead
       | Handle of Label.t

      val equals: t * t -> bool
      val foldLabel: t * 'a * (Label.t * 'a -> 'a) -> 'a
      val foreachLabel: t * (Label.t -> unit) -> unit
      val layout: t -> Layout.t
      val map: t * (Label.t -> Label.t) -> t
   end
