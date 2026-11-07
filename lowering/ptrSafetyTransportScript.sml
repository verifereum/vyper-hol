(* Transporting ptrSafeRun's check and fragGasPathPtr's counted paths to a
 * higher lower bound: access_ok lo0 implies access_ok lo for lo0 <= lo,
 * and the remaining lo-dependent conjunct, allocas_from lo, holds along
 * any run that starts with every ALLOCA site and the frontier at or above
 * lo, since new sites are placed at the frontier, which never drops below
 * where it started.  With ctorDeployMemoryRunPtrMono's monotonicity in the
 * dead bytes, a runtime path checked at (D0, 0) is a path at (D, lo).
 *
 * TOP-LEVEL:
 *   ptr_inst_ok_lower_bound_transport -- one instruction
 *   step_inst_allocas_from, eval_phis_allocas_from, setup_callee_allocas_from
 *     -- allocas_from lo /\ lo <= frontier is kept by the runner's steps
 *   ptr_safe_lower_bound_transport, ptr_safe_run_lower_bound_transport --
 *     the check along a run
 *   gas_path_ptr_lower_bound_transport, gas_path_ptr_zero_to_lo -- counted
 *     paths
 *)
Theory ptrSafetyTransport
Ancestors
  ctorDeployMemoryRunPtrMono fragGasPathPtr allocaFrontierBound venomMemProps
  venomExecProofs venomExecSemantics ptrSafeRun ptrDiscipline venomState
  finite_map arithmetic

Theorem ptr_inst_ok_lower_bound_transport:
  lo0 <= lo /\ allocas_from lo s /\
  ptr_inst_ok D lo0 fuel ctx fn G tn inst s ==>
  ptr_inst_ok D lo fuel ctx fn G tn inst s
Proof
  pure_rewrite_tac [ptr_inst_ok_def] >> strip_tac >>
  `access_ok lo G fn inst s` by
    (qpat_x_assum `access_ok lo0 _ _ _ _` mp_tac >>
     qpat_x_assum `lo0 <= lo` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[access_ok_def] >> rpt strip_tac >>
     gvs[] >> metis_tac[LESS_EQ_LESS_TRANS]) >>
  asm_rewrite_tac[]
QED

(* ===== allocas_from lo along the runner ===== *)

Theorem exec_alloca_allocas_from[local]:
  exec_alloca inst s sz = OK s' /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  allocas_from lo s' /\ lo <= s'.vs_alloca_next
Proof
  rw[exec_alloca_def, AllCaseEqs(), update_var_def, allocas_from_def] >>
  gvs[AllCaseEqs()] >> qpat_x_assum `FLOOKUP _ aid = _` mp_tac >>
  simp[FLOOKUP_UPDATE] >> rw[] >> metis_tac[]
QED

Theorem step_inst_allocas_from:
  step_inst fuel ctx inst s = OK s' /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  allocas_from lo s' /\ lo <= s'.vs_alloca_next
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all step_inst_invoke_alloca_fields >> strip_tac >>
      gvs[allocas_from_def] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (`step_inst_base inst s = OK s'` by metis_tac[step_inst_non_invoke] >>
      qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      simp[step_inst_base_def] >>
      Cases_on `inst.inst_operands` >> simp[] >>
      Cases_on `t` >> simp[] >> Cases_on `h` >> simp[] >>
      metis_tac[exec_alloca_allocas_from]) >>
  `~is_alloca_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> gvs[venomInstTheory.is_alloca_op_def]) >>
  `s'.vs_allocas = s.vs_allocas` by
    metis_tac[step_inst_non_alloca_preserves_allocas] >>
  `step_inst_base inst s = OK s'` by metis_tac[step_inst_non_invoke] >>
  `s'.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[step_inst_base_preserves_alloca_next] >>
  gvs[allocas_from_def] >> metis_tac[]
QED

Theorem eval_phis_allocas_from:
  eval_phis s insts = OK s' /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  allocas_from lo s' /\ lo <= s'.vs_alloca_next
Proof
  strip_tac >> drule eval_phis_preserves_alloca_fields >> strip_tac >>
  gvs[allocas_from_def] >> metis_tac[]
QED

Theorem setup_callee_allocas_from:
  setup_callee callee args s = SOME cs /\ lo <= s.vs_alloca_next ==>
  allocas_from lo cs /\ lo <= cs.vs_alloca_next
Proof
  rw[setup_callee_def, allocas_from_def] >> gvs[]
QED

(* ===== The check along a run ===== *)

Theorem ptr_safe_lower_bound_transport:
  (!D lo0 fuel ctx fn PG G tn inst s lo.
     ptr_safe_step D lo0 fuel ctx fn PG G tn inst s /\ lo0 <= lo /\
     allocas_from lo s /\ lo <= s.vs_alloca_next ==>
     ptr_safe_step D lo fuel ctx fn PG G tn inst s) /\
  (!D lo0 fuel ctx fn PG G tn bb s lo.
     ptr_safe_block D lo0 fuel ctx fn PG G tn bb s /\ lo0 <= lo /\
     allocas_from lo s /\ lo <= s.vs_alloca_next ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s) /\
  (!D lo0 fuel ctx fn PG G tn s lo.
     ptr_safe_blocks D lo0 fuel ctx fn PG G tn s /\ lo0 <= lo /\
     allocas_from lo s /\ lo <= s.vs_alloca_next ==>
     ptr_safe_blocks D lo fuel ctx fn PG G tn s)
Proof
  ho_match_mp_tac ptr_safe_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      ONCE_REWRITE_TAC [ptr_safe_step_def] >> strip_tac >>
      conj_tac >- metis_tac[ptr_inst_ok_lower_bound_transport] >>
      Cases_on `inst.inst_opcode = INVOKE` >> gvs[] >>
      BasicProvers.every_case_tac >> gvs[] >>
      metis_tac[setup_callee_allocas_from])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `ptr_safe_block _ _ _ _ _ _ _ _ _ _` mp_tac >>
      ONCE_REWRITE_TAC [ptr_safe_block_def] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      Cases_on `step_inst fuel ctx inst s` >> simp[] >>
      rename1 `step_inst fuel ctx inst s = OK s'` >>
      `allocas_from lo s' /\ lo <= s'.vs_alloca_next` by
        metis_tac[step_inst_allocas_from] >>
      Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
      rpt strip_tac >> gvs[allocas_from_def] >> metis_tac[])
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `ptr_safe_blocks _ _ _ _ _ _ _ _ _` mp_tac >>
  ONCE_REWRITE_TAC [ptr_safe_blocks_def] >>
  BasicProvers.every_case_tac >> gvs[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  drule_all eval_phis_allocas_from >> strip_tac >>
  gvs[allocas_from_def] >> metis_tac[]
QED

Theorem ptr_safe_run_lower_bound_transport:
  ptr_safe_run D lo0 fuel ctx fn PG G tn s /\ lo0 <= lo /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  rw[ptr_safe_run_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[] >>
  metis_tac[ptr_safe_lower_bound_transport]
QED

(* ===== Counted paths ===== *)

Theorem gas_path_ptr_edge_lower_bound_transport:
  gas_path_ptr_edge D lo0 ctx fn PG G tn s n G' tn' r /\ lo0 <= lo /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' r /\
  !t. r = OK t ==> allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  rewrite_tac[gas_path_ptr_edge_def] >> strip_tac >>
  (conj_tac >- metis_tac[ptr_safe_lower_bound_transport]) >>
  rpt strip_tac >> gvs[fragExecTheory.exit_result_def] >>
  imp_res_tac step_inst_allocas_from >>
  imp_res_tac eval_phis_allocas_from >>
  gvs[allocas_from_def] >> metis_tac[]
QED

Theorem gas_path_ptr_lower_bound_transport:
  !D lo0 ctx fn PG G tn s n G' tn' r.
    gas_path_ptr D lo0 ctx fn PG G tn s n G' tn' r ==>
    !lo. lo0 <= lo /\ allocas_from lo s /\ lo <= s.vs_alloca_next ==>
         gas_path_ptr D lo ctx fn PG G tn s n G' tn' r
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt conj_tac
  >- simp[gas_path_ptr_rules]
  >- (rpt strip_tac >>
      drule_all gas_path_ptr_edge_lower_bound_transport >> strip_tac >>
      irule (cj 2 gas_path_ptr_rules) >> metis_tac[])
  >> rpt strip_tac >>
  drule_all gas_path_ptr_edge_lower_bound_transport >> strip_tac >>
  metis_tac[gas_path_ptr_rules]
QED

Theorem gas_path_ptr_edge_dead_mono:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' r /\
  (!a st. D.d_stor a st SUBSET D'.d_stor a st) /\
  (!a st. D.d_trans a st SUBSET D'.d_trans a st) /\
  (!i. D.d_imm i SUBSET D'.d_imm i) /\
  (!r. D.d_ret r SUBSET D'.d_ret r) ==>
  gas_path_ptr_edge D' lo ctx fn PG G tn s n G' tn' r
Proof
  rewrite_tac[gas_path_ptr_edge_def] >> strip_tac >> simp[] >>
  qexists_tac `fuel` >> gvs[] >>
  metis_tac[ptr_safe_dead_mono]
QED

Theorem gas_path_ptr_dead_mono:
  !D lo ctx fn PG G tn s n G' tn' r.
    gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
    !D'. (!a st. D.d_stor a st SUBSET D'.d_stor a st) /\
         (!a st. D.d_trans a st SUBSET D'.d_trans a st) /\
         (!i. D.d_imm i SUBSET D'.d_imm i) /\
         (!r. D.d_ret r SUBSET D'.d_ret r) ==>
         gas_path_ptr D' lo ctx fn PG G tn s n G' tn' r
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt conj_tac
  >- simp[gas_path_ptr_rules]
  >- (rpt strip_tac >>
      drule_all gas_path_ptr_edge_dead_mono >> strip_tac >>
      irule (cj 2 gas_path_ptr_rules) >> metis_tac[])
  >> rpt strip_tac >>
  drule_all gas_path_ptr_edge_dead_mono >> strip_tac >>
  metis_tac[gas_path_ptr_rules]
QED

(* A runtime path, checked at (D0, 0), is a path at (D, lo) when D holds
   D0's dead bytes and every ALLOCA site, and the frontier, is at or above
   lo where it starts. *)
Theorem gas_path_ptr_zero_to_lo:
  gas_path_ptr D0 0 ctx fn PG G tn s n G' tn' r /\
  (!a st. D0.d_stor a st SUBSET D.d_stor a st) /\
  (!a st. D0.d_trans a st SUBSET D.d_trans a st) /\
  (!i. D0.d_imm i SUBSET D.d_imm i) /\
  (!r. D0.d_ret r SUBSET D.d_ret r) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  gas_path_ptr D lo ctx fn PG G tn s n G' tn' r
Proof
  strip_tac >>
  drule gas_path_ptr_dead_mono >> disch_then (qspec_then `D` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  drule gas_path_ptr_lower_bound_transport >> simp[]
QED
