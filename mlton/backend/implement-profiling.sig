(* Copyright (C) 2013 Matthew Fluet.
 * Copyright (C) 2009 Matthew Fluet.
 * Copyright (C) 2002-2007 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ME_IMPLEMENT_PROFILING_STRUCTS =
   sig
      structure Machine: MACHINE
      structure Rssa: ME_RSSA
      sharing Machine.ProfileLabel = Rssa.ProfileLabel
   end

signature ME_IMPLEMENT_PROFILING =
   sig
      include ME_IMPLEMENT_PROFILING_STRUCTS

      val doit:
         Rssa.Program.t
         -> Rssa.Program.t * ({frames: Rssa.Label.t vector}
                              -> Machine.ProfileInfo.t option)
   end
