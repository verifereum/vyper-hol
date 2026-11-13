(* Ghost invariants across typed stores into a disjoint memory window. *)
Theory aggregateStorePtrFrame
Ancestors
  exprSimPtrLiteralBuffer typedMemoryCopy loweringStateRelDefs
  bodyPtrDefs compileEnv freshWrites venomState ptrDiscipline list pred_set

Theorem literal_typed_copy_ghost_frame:
  ghost_inv d ce cx es G tn s /\ stmt_state_rel ctx func ce cx es s /\
  local_ptrs_reserved ce sa /\ typed_copy_state_frame sa b k s t /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!name p n. local_region ce es.scopes s name p n ==>
    regions_disjoint b k p n) /\
  (!i. ~(b <= i /\ i < b+k) ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm ==>
  ghost_inv d ce cx es H tm t
Proof
  strip_tac >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient` by
    (fs[typed_copy_state_frame_def] >>
     qpat_x_assum `_ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  irule literal_ghost_inv_frame >>
  qexistsl_tac [`G`, `s`, `sa`, `tn`, `{i | b <= i /\ i < b+k}`] >>
  simp[] >> conj_tac
  >- (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`, `cenv` |-> `ce`,
        `cx` |-> `cx`, `es` |-> `es`, `s` |-> `s`, `b` |-> `b`, `n` |-> `k`]
        literal_ptr_local_footprint_exterior) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> fs[typed_copy_state_frame_def, typed_copy_frame_def] >>
  first_x_assum irule >> decide_tac
QED
