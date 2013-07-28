(* Copyright (C) 2013 Matthew Fluet, David Larsen.
 * Copyright (C) 1999-2005 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ME_SSA_STRUCTS =
   sig
      include ME_SSA_TREE_STRUCTS
   end

signature ME_SSA = 
   sig
      include ME_SIMPLIFY
   end
