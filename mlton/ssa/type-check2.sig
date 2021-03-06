(* Copyright (C) 1999-2006 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ME_TYPE_CHECK2_STRUCTS =
   sig
      include ME_ANALYZE2
   end

signature ME_TYPE_CHECK2 =
   sig
      include ME_TYPE_CHECK2_STRUCTS

      val typeCheck: Program.t -> unit
   end
