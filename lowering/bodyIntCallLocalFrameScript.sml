(* Semantic live-local subvalues, including their dynamic headers. *)
Theory bodyIntCallLocalFrame
Ancestors
  compileEnv loweringStateRelDefs loweringPosts memoryValueEncoding

Theorem local_ptrs_rel_sub_layout:
  local_ptrs_rel func cenv scopes s /\
  lookup_scopes name scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\
  value_has_type entry.type entry.value /\
  sub_layout entry.type entry.value k tv v ==>
  val_in_memory tv v (w2n w + k) s.vs_memory
Proof
  simp[local_ptrs_rel_def, sub_layout_def] >> rpt strip_tac >>
  qpat_x_assum `!name entry p sz. _` drule_all >>
  strip_tac >> gvs[] >>
  `val_in_memory entry.type entry.value (w2n w) s.vs_memory` by
    (irule memory_value_rel_val_in_memory >> simp[]) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED
