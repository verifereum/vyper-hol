Theory concretizePtrAllocationOwnership
Ancestors concretizePtrAllocationOrigins concretizePtrActivationSupport
  venomExecSemantics venomState
  venomMemProps venomExecProofs ptrDiscipline ptrDisciplineEmptyTaint venomWf
  venomInst finite_map words list

Definition ptr_alloc_table_ok_def:
  ptr_alloc_table_ok s <=>
    (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
      b + sz <= s.vs_alloca_next) /\
    (!aid aid' b sz b' sz' x.
      FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      FLOOKUP s.vs_allocas aid' = SOME (b',sz') /\
      b <= x /\ x < b + sz /\ b' <= x /\ x < b' + sz' ==> aid = aid')
End

Definition ptr_alloc_floor_def:
  ptr_alloc_floor q s <=>
    !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> q <= b
End

Definition ptr_active_alloc_geometry_def:
  (ptr_active_alloc_geometry [] <=> T) /\
  (ptr_active_alloc_geometry (s::ss) <=>
    ptr_alloc_table_ok s /\ ptr_active_alloc_geometry ss /\
    case ss of [] => T | p::ps =>
      p.vs_alloca_next <= s.vs_alloca_next /\ ptr_alloc_floor p.vs_alloca_next s)
End

Theorem ptr_active_alloc_geometry_nil[simp]:
  ptr_active_alloc_geometry []
Proof
  simp[ptr_active_alloc_geometry_def]
QED

Theorem ptr_active_alloc_geometry_singleton[simp]:
  ptr_active_alloc_geometry [s] <=> ptr_alloc_table_ok s
Proof
  simp[ptr_active_alloc_geometry_def]
QED

Theorem ptr_alloc_empty:
  s.vs_allocas = FEMPTY ==> ptr_alloc_table_ok s /\ ptr_alloc_floor q s
Proof
  simp[ptr_alloc_table_ok_def, ptr_alloc_floor_def]
QED

Theorem ptr_exec_alloca_table_ok:
  ptr_alloc_table_ok s /\ exec_alloca inst s n = OK s' ==>
  ptr_alloc_table_ok s'
Proof
  rw[exec_alloca_def, AllCaseEqs()] >>
  gvs[update_var_def, ptr_alloc_table_ok_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  Cases_on `inst.inst_id = aid` >> Cases_on `inst.inst_id = aid'` >> gvs[] >>
  qpat_assum `!aid b sz. FLOOKUP _ _ = _ ==> _`
    (fn th => imp_res_tac th) >> gvs[] >> metis_tac[]
QED

Theorem ptr_exec_alloca_floor:
  ptr_alloc_floor q s /\ q <= s.vs_alloca_next /\ exec_alloca inst s n = OK s' ==>
  ptr_alloc_floor q s' /\ q <= s'.vs_alloca_next
Proof
  rw[exec_alloca_def, AllCaseEqs()] >>
  gvs[update_var_def, ptr_alloc_floor_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `inst.inst_id = aid` >> gvs[] >> metis_tac[]
QED

Theorem ptr_exec_alloca_fresh_disjoint:
  ptr_alloc_table_ok s /\ exec_alloca inst s n = OK s' /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ b <= x /\ x < b + sz ==>
  ~(s.vs_alloca_next <= x /\ x < s.vs_alloca_next + w2n n)
Proof
  simp[ptr_alloc_table_ok_def] >> rpt strip_tac >>
  `b + sz <= s.vs_alloca_next` by metis_tac[] >> decide_tac
QED

Theorem ptr_active_alloc_frontier:
  !states n. ptr_active_alloc_geometry states /\ n < LENGTH states ==>
    (EL n states).vs_alloca_next <= (HD states).vs_alloca_next
Proof
  Induct >> simp[ptr_active_alloc_geometry_def] >> rpt gen_tac >>
  Cases_on `states` >> gvs[ptr_active_alloc_geometry_def] >>
  Cases_on `n` >> gvs[] >> strip_tac >>
  first_x_assum drule >> simp[] >>
  disch_then (qspec_then `n'` mp_tac) >> simp[] >> decide_tac
QED

Theorem ptr_active_alloc_tables:
  !states. ptr_active_alloc_geometry states ==> EVERY ptr_alloc_table_ok states
Proof
  Induct >> simp[ptr_active_alloc_geometry_def] >> metis_tac[]
QED

Theorem ptr_active_alloc_tail_bound:
  ptr_active_alloc_geometry (s::states) /\ n < LENGTH states /\
  FLOOKUP (EL n states).vs_allocas aid = SOME (b,sz) ==>
  b + sz <= (HD states).vs_alloca_next
Proof
  strip_tac >>
  `ptr_active_alloc_geometry states` by
    gvs[ptr_active_alloc_geometry_def] >>
  `ptr_alloc_table_ok (EL n states)` by
    (drule ptr_active_alloc_tables >> simp[EVERY_EL]) >>
  drule_all ptr_active_alloc_frontier >>
  fs[ptr_alloc_table_ok_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ptr_active_alloc_unique_owner:
  !states n m aid aid' b sz b' sz' x.
  ptr_active_alloc_geometry states /\ n < LENGTH states /\ m < LENGTH states /\
  FLOOKUP (EL n states).vs_allocas aid = SOME (b,sz) /\
  FLOOKUP (EL m states).vs_allocas aid' = SOME (b',sz') /\
  b <= x /\ x < b + sz /\ b' <= x /\ x < b' + sz' ==>
  n = m /\ aid = aid'
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `n` >> Cases_on `m` >> gvs[]
  >- (gvs[ptr_active_alloc_geometry_def, ptr_alloc_table_ok_def] >> metis_tac[])
  >- (drule_all ptr_active_alloc_tail_bound >>
      Cases_on `states` >>
      gvs[ptr_active_alloc_geometry_def, ptr_alloc_floor_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS, arithmeticTheory.NOT_LESS_EQUAL])
  >- (drule_all ptr_active_alloc_tail_bound >>
      Cases_on `states` >>
      gvs[ptr_active_alloc_geometry_def, ptr_alloc_floor_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS, arithmeticTheory.NOT_LESS_EQUAL]) >>
  first_x_assum irule >> gvs[ptr_active_alloc_geometry_def] >> metis_tac[]
QED

Theorem ptr_alloc_geometry_fields:
  s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next ==>
  (ptr_active_alloc_geometry (s'::ss) <=> ptr_active_alloc_geometry (s::ss))
Proof
  Cases_on `ss` >> simp[ptr_active_alloc_geometry_def,
    ptr_alloc_table_ok_def, ptr_alloc_floor_def]
QED

Theorem ptr_alloc_geometry_exec:
  ptr_active_alloc_geometry (s::ss) /\ exec_alloca inst s n = OK s' ==>
  ptr_active_alloc_geometry (s'::ss)
Proof
  Cases_on `ss` >> simp[ptr_active_alloc_geometry_def] >> strip_tac >>
  metis_tac[ptr_exec_alloca_table_ok, ptr_exec_alloca_floor]
QED

Theorem ptr_alloc_geometry_step:
  ptr_active_alloc_geometry (s::ss) /\ step_inst fuel ctx inst s = OK s' /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> DALLOCA ==>
  ptr_active_alloc_geometry (s'::ss)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[step_inst_non_invoke, step_inst_base_def,
        AllCaseEqs()] >> metis_tac[ptr_alloc_geometry_exec]) >>
  `s'.vs_allocas = s.vs_allocas` by
    (drule step_inst_non_alloca_preserves_allocas >>
     impl_tac >- (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]) >> simp[]) >>
  `s'.vs_alloca_next = s.vs_alloca_next` by
    (drule step_inst_non_invoke >> simp[] >> strip_tac >>
     irule step_inst_base_preserves_alloca_next >> metis_tac[]) >>
  metis_tac[ptr_alloc_geometry_fields]
QED

Theorem ptr_alloc_enters_fields:
  enters_block fn s s' ==>
  s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  simp[contextCodegenRelTheory.enters_block_def] >> rpt strip_tac >>
  drule eval_phis_preserves_alloca_fields >> simp[]
QED

Theorem ptr_alloc_setup_fields:
  setup_callee fn args s = SOME s' ==>
  s'.vs_allocas = FEMPTY /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  rw[setup_callee_def] >> gvs[]
QED

Theorem ptr_alloc_return_fields:
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state saved ended)) = SOME s' ==>
  s'.vs_allocas = saved.vs_allocas /\ s'.vs_alloca_next = saved.vs_alloca_next
Proof
  strip_tac >>
  `s'.vs_allocas = (adopt_return_fmp ret (merge_callee_state saved ended)).vs_allocas /\
   s'.vs_alloca_next = (adopt_return_fmp ret (merge_callee_state saved ended)).vs_alloca_next` by
    (conj_tac >> irule venomInstProofs1Theory.bind_outputs_preserves >>
     simp[update_var_def] >> metis_tac[]) >>
  Cases_on `ret.iret_adopt_fmp` >> gvs[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem ptr_frame_alloc_geometry_invariant[local]:
  !vs0 ctx stk PG G tn fn inst s.
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  vs0.vs_allocas = FEMPTY /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions ==>
  MEM fn ctx.ctx_functions /\ EVERY (\f. MEM f.cf_fn ctx.ctx_functions) stk /\
  ptr_active_alloc_geometry (s :: MAP (\f. f.cf_state) stk)
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> drule ptr_alloc_enters_fields >>
      simp[ptr_active_alloc_geometry_def, ptr_alloc_table_ok_def] >>
      metis_tac[lookup_function_MEM])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      qpat_x_assum `_ /\ _ ==> _ /\ _ /\ ptr_active_alloc_geometry _` mp_tac >>
      simp[] >> strip_tac >>
      `MEM inst (fn_insts fn)` by
        (gvs[contextCodegenRelTheory.active_inst_def, fn_insts_def,
          venomWfPropsTheory.fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
         metis_tac[MEM_EL]) >>
      `inst.inst_opcode <> DALLOCA` by (fs[EVERY_MEM] >> metis_tac[]) >>
      `ptr_active_alloc_geometry (s' :: MAP (\f. f.cf_state) stk)` by
        metis_tac[ptr_alloc_geometry_step] >>
      simp[] >> irule (iffRL ptr_alloc_geometry_fields) >> qexists `s'` >> simp[])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      qpat_x_assum `_ /\ _ ==> _ /\ _ /\ ptr_active_alloc_geometry _` mp_tac >>
      simp[] >> strip_tac >>
      `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> DALLOCA` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
      drule ptr_alloc_enters_fields >> strip_tac >>
      `ptr_active_alloc_geometry (s' :: MAP (\f. f.cf_state) stk)` by
        metis_tac[ptr_alloc_geometry_step] >>
      metis_tac[ptr_alloc_geometry_fields])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      qpat_x_assum `_ /\ _ ==> _ /\ _ /\ ptr_active_alloc_geometry _` mp_tac >>
      simp[] >> strip_tac >>
      drule ptr_alloc_setup_fields >> strip_tac >>
      drule ptr_alloc_enters_fields >> strip_tac >>
      gvs[ptr_active_alloc_geometry_def, ptr_alloc_table_ok_def, ptr_alloc_floor_def] >>
      metis_tac[lookup_function_MEM])
  >> rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_x_assum `_ /\ _ ==> _ /\ _ /\ ptr_active_alloc_geometry _` mp_tac >>
  simp[] >> strip_tac >>
  drule ptr_alloc_return_fields >> strip_tac >>
  `ptr_active_alloc_geometry (f.cf_state :: MAP (\f. f.cf_state) stk)` by
    gvs[ptr_active_alloc_geometry_def] >>
  simp[] >> irule (iffRL ptr_alloc_geometry_fields) >> qexists `f.cf_state` >> simp[]
QED

Theorem ptr_frame_alloc_geometry:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\ vs0.vs_allocas = FEMPTY /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions ==>
  ptr_active_alloc_geometry (s :: MAP (\f. f.cf_state) stk)
Proof
  metis_tac[ptr_frame_alloc_geometry_invariant]
QED

(* Uniqueness here is simultaneous ownership only. Retired activations can
   reuse the same numeric intervals. Relating a chronological writer's seed
   to an earlier allocation still requires temporal protection; non-revert
   coverage of that chronological theorem also remains to be discharged. *)
