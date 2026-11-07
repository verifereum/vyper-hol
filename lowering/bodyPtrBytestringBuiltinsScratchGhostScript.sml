Theory bodyPtrBytestringBuiltinsScratchGhost
Ancestors
  bodyPtrBytestringBuiltinsWindowGhost exprSimPtrLiteralBuffer
  bodyPtrDefs compileEnv pred_set

(* A scratch write may remove taint anywhere, but cannot introduce it into
   old local windows.  The arbitrary write set records physical footprints. *)
Theorem ghost_inv_scratch_write_transport:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_rel fn cenv es.scopes s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
    lookup_var x s' = SOME w) /\
  (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  mem_agree_outside writes s.vs_memory s'.vs_memory /\
  (!name b len i. local_region cenv es.scopes s name b len /\
    b <= i /\ i < b+len ==> i NOTIN writes) /\
  (!i. i NOTIN writes /\ i IN tm.t_mem ==> i IN tn.t_mem) /\
  stor_taint_ok cx tm s' ==>
  ghost_inv d cenv cx es H tm s'
Proof
  strip_tac >> irule ghost_inv_local_window_transport >>
  simp[] >> qexistsl_tac [`G`, `fn`, `s`, `sa`, `tn`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (sym_tac >> irule literal_clean_window_agree >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  metis_tac[]
QED
