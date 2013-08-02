(* Copyright (C) 2004-2006 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ME_SSA_TO_SSA2_STRUCTS =
   sig
      structure Ssa: ME_SSA
      structure Ssa2: ME_SSA2
      sharing Ssa.Atoms = Ssa2.Atoms
   end

signature ME_SSA_TO_SSA2 =
   sig
      include ME_SSA_TO_SSA2_STRUCTS

      val convert: Ssa.Program.t -> Ssa2.Program.t
   end
