(* Small selected-path identity probes; no strengthening of shared posts. *)
Theory bodyPtrIntCallIdentityProbe
Ancestors
  exprSimNameValue loweringPosts exprLowering vyperAST
  vyperInterpreter vyperState finite_map venomState

(* This bridge is about the live machine state supplied by the consumer,
   not an independently chosen simulation run. *)
Theorem intcall_name_place_identity:
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME b /\
  cenv.ce_var_type id = SOME ann /\
  evaluate_type (get_tenv cx) ann = SOME tv ==>
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id [])) b
    (SOME LocMemory) (Type ann)
Proof
  strip_tac >>
  simp[place_ptr_rel_def, mem_path_offset_def, wordsTheory.WORD_ADD_0]
QED

val _ = export_theory ();
