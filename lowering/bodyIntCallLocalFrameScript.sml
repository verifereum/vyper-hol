(* Semantic live-local subvalues, including their dynamic headers. *)
Theory bodyIntCallLocalFrame
Ancestors
  compileEnv loweringPosts

Theorem local_ptrs_rel_sub_layout:
  local_ptrs_rel func cenv scopes s /\
  lookup_scopes name scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\
  sub_layout entry.type entry.value k tv v ==>
  val_in_memory tv v (w2n w + k) s.vs_memory
Proof
  simp[local_ptrs_rel_def, sub_layout_def] >> rpt strip_tac >>
  qpat_x_assum `!name entry p sz. _` drule_all >>
  strip_tac >> gvs[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED
