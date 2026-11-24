(* The typed widening store changes only its reserved destination window. *)
Theory bodyIfExpTypedGhostMods
Ancestors
  bodyFullShadowBodyInv robustCopyTransportPtr typedMemoryCopy
  assignTuplePtrCopyLen nameLoweringProps exprSimProps loweringStateRelDefs
  bodyPtrDefs ptrDiscipline venomState

Triviality ifexp_typed_copy_local_value:
  val_wf tv v /\ val_footprint tv v <= sz /\
  regions_disjoint dst n p sz /\ typed_copy_frame dst n mem mem' /\
  (!i. ~(dst <= i /\ i < dst + n) ==> (i IN tm' <=> i IN tm)) /\
  (!m. mem_agree_outside tm mem m ==> val_in_memory tv v p m) /\
  mem_agree_outside tm' mem' m ==>
  val_in_memory tv v p m
Proof
  strip_tac >> irule robust_val_in_memory_exterior_frame >> simp[] >>
  qexistsl_tac [`mem`, `mem'`, `tm`, `tm'`, `{i | dst <= i /\ i < dst + n}`] >>
  simp[] >> conj_tac
  >- (fs[typed_copy_frame_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qpat_x_assum `regions_disjoint _ _ _ _` mp_tac >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem ifexp_typed_copy_ghost_mods:
  ghost_inv_at_mods D lo d ce cx ee Ga ta q /\
  local_ptrs_rel func ce ee.scopes q /\ local_ptrs_reserved ce k /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  lo <= dst /\
  (!name b sz. local_region ce ee.scopes q name b sz ==>
               regions_disjoint dst n b sz) /\
  typed_copy_state_frame k dst n q f /\
  tf.t_imm = ta.t_imm /\ tf.t_stor = ta.t_stor /\ tf.t_trans = ta.t_trans /\
  (!i. ~(dst <= i /\ i < dst + n) ==> (i IN tf.t_mem <=> i IN ta.t_mem)) /\
  (!x. not_fresh_at k x ==>
       FLOOKUP Gf x = FLOOKUP Ga x /\ op_taint tf (Var x) = op_taint ta (Var x)) ==>
  ghost_inv_at_mods D lo d ce cx ee Gf tf f
Proof
  strip_tac >>
  qhdtm_x_assum `typed_copy_state_frame`
    (strip_assume_tac o SRULE [typed_copy_state_frame_def,venom_state_component_equality]) >>
  `!p sz. not_fresh_at k p /\ ptr_covers Ga ta p q sz ==> ptr_covers Gf tf p f sz` by
    (rpt strip_tac >> irule ptr_covers_lookup_frame >> metis_tac[]) >>
  rewrite_tac[ghost_inv_at_mods_def] >> conj_tac >- suspend "locals" >>
  `mem_bytes_at 0 lo f.vs_memory = mem_bytes_at 0 lo q.vs_memory` by
    (fs[typed_copy_frame_def] >> first_x_assum irule >> simp[]) >>
  `!i. i < lo ==> (i IN tf.t_mem <=> i IN ta.t_mem)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. ~(dst <= i /\ _) ==> _` irule >> decide_tac) >>
  fs[ghost_inv_at_mods_def,stor_taint_ok_at_def,allocas_from_def] >>
  rpt conj_tac
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[])
  >- metis_tac[] >>
  rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]
QED

Resume ifexp_typed_copy_ghost_mods[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at k p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qhdtm_x_assum `ghost_inv_at_mods`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  qpat_x_assum `!name e p sz. _ ==> ptr_covers _ _ _ _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p q = SOME w` by metis_tac[] >>
  drule_all_then strip_assume_tac local_ptrs_rel_value >>
  gvs[eval_operand_def] >>
  `local_region ce ee.scopes q name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  irule ifexp_typed_copy_local_value >>
  qpat_assum `typed_copy_frame _ _ _ _` (irule_at Any) >>
  qpat_assum `mem_agree_outside _ _ _` (irule_at Any) >>
  qexists_tac `ta.t_mem` >> qexists_tac `sz` >>
  simp[] >> metis_tac[val_footprint_le,arithmeticTheory.LESS_EQ_TRANS]
QED

Finalise ifexp_typed_copy_ghost_mods
