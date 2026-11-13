Theory lowerDloadPtrBackward
Ancestors
  lowerDloadPtrBytesTransport lowerDloadPtrExpansionTransport
  lowerDloadPtrRel lowerDloadPtrAggregate lowerDloadPtrCall ptrDiscipline
  venomExecSemantics venomState instIdxIndep lowerDloadDefs
  pointerConfinedDefs memLocDefs list pred_set words arithmetic finite_map

Theorem dload_offset_clean:
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\
  MEM i (fn_insts fn) /\ fn_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn i s ==>
  op_prov G off = NONE /\ op_taint tn off = {}
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) i` by metis_tac[fn_ptr_ok_def] >>
  `!v. off = Var v ==> v NOTIN fn_pv P fn` by
    (gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_write_ops_def, mem_read_ops_def] >>
     metis_tac[]) >>
  conj_tac
  >- (Cases_on `off` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]) >>
  gvs[taint_ok_def] >> metis_tac[]
QED

Theorem dload_replay_offset_defined:
  a.inst_opcode = ALLOCA /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  off <> Var av /\ step_inst fuel C a t = OK v1 /\
  step_inst fuel C b (v1 with vs_inst_idx := SUC t.vs_inst_idx) = OK v2 ==>
  ?x. eval_operand off t = SOME x
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ b _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >>
  qpat_x_assum `step_inst _ _ a _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_alloca_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `off` >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem dload_four_step_lookup:
  a.inst_opcode = ALLOCA /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_outputs = [cv] /\
  c.inst_opcode = CODECOPY /\ c.inst_outputs = [] /\
  d.inst_opcode = MLOAD /\ d.inst_outputs = [out] /\
  dload_prefix_match fuel C PH [a;b;c;d] 4 t H un t4 H4 un4 ==>
  !v. v <> out /\ v <> av /\ v <> cv ==> lookup_var v t4 = lookup_var v t
Proof
  strip_tac >> drule dload_four_step_replay >> strip_tac >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `H4 = _` kall_tac >> qpat_x_assum `un4 = _` kall_tac >>
  qpat_x_assum `H3 = _` kall_tac >> qpat_x_assum `un3 = _` kall_tac >>
  qpat_x_assum `H2 = _` kall_tac >> qpat_x_assum `un2 = _` kall_tac >>
  qpat_x_assum `H1 = _` kall_tac >> qpat_x_assum `un1 = _` kall_tac >>
  gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base d _ = _` mp_tac >>
  simp[step_inst_base_def, exec_read1_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base c _ = _` mp_tac >>
  simp[step_inst_base_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base b _ = _` mp_tac >>
  simp[step_inst_base_def, exec_pure2_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base a _ = _` mp_tac >>
  simp[step_inst_base_def, exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  simp[lookup_var_def, update_var_def, write_memory_with_expansion_def, FLOOKUP_UPDATE]
QED

Theorem dload_step_lookup:
  i.inst_opcode = DLOAD /\ i.inst_outputs = [out] /\
  step_inst fuel C i s = OK s1 ==>
  !v. v <> out ==> lookup_var v s1 = lookup_var v s
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem dload_supply_backward_boundary_fresh:
  dload_boundary_core lo (r::rs) V Ws PG PH G H tn un s t cs ds /\
  r.dr_scratch = FDOM t.vs_allocas DIFF orig /\
  FDOM s.vs_allocas SUBSET orig /\ (EL 0 xs).inst_id NOTIN orig /\
  (FLOOKUP t.vs_allocas (EL 0 xs).inst_id = NONE ==> t.vs_alloca_next + 32 < dimword (:256)) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  lower_dload_inst_supply supply i = (xs,next) /\
  (EL 0 xs).inst_outputs = [av] /\ (EL 1 xs).inst_outputs = [cv] /\
  av <> cv /\ av NOTIN V /\ cv NOTIN V /\ off <> Var av /\
  code_layout_valid s /\ dload_offset_ok C fn i s /\
  MEM i (fn_insts fn) /\ fn_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn i s /\ (!v. off = Var v ==> v IN V) /\
  dload_prefix_match fuel Ct PH xs 4 t H un t4 H4 un4 ==>
  ?s1 r1. step_inst fuel C i s = OK s1 /\
    r1.dr_source = r.dr_source /\
    r1.dr_scratch = (EL 0 xs).inst_id INSERT r.dr_scratch /\
    dload_boundary_core lo (r1::rs) V Ws PG PH
      (step_prov PG G i s1) H4 (step_taint i s s1 tn) un4
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) t4 cs ds /\
    (!v. v <> out ==> lookup_var v s1 = lookup_var v s) /\
    (!v. v <> out /\ v <> av /\ v <> cv ==> lookup_var v t4 = lookup_var v t)
Proof
  strip_tac >>
  drule_all dload_supply_expansion >> strip_tac >> gvs[] >>
  `?x. eval_operand off t = SOME x` by
    (drule dload_four_step_replay >> strip_tac >>
     irule dload_replay_offset_defined >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     qpat_x_assum `t1 = _` (fn th =>
       qpat_x_assum `step_inst _ _ _ t1 = _` (mp_tac o REWRITE_RULE [th])) >>
     rpt (pop_assum kall_tac) >> strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
  suspend "offset_equal"
QED

Resume dload_supply_backward_boundary_fresh[offset_equal]:
  `dload_vars_match (r::rs) V G H tn un s t` by metis_tac[dload_boundary_vars] >>
  `s.vs_labels = t.vs_labels` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `eval_operand off s = NONE <=> eval_operand off t = NONE` by
    (irule dload_matched_operand_defined >> simp[] >>
     qexistsl [`G`,`H`,`V`,`r::rs`,`tn`,`un`] >> simp[]) >>
  drule_all dload_offset_clean >> strip_tac >>
  `eval_operand off s = eval_operand off t` by
    (irule scalar_operand_equal >> simp[] >>
     qexistsl [`G`,`H`,`V`,`r::rs`,`tn`,`un`] >> simp[]) >>
  `eval_operand off s = SOME x` by metis_tac[] >>
  suspend "replay_finish"
QED

Resume dload_supply_backward_boundary_fresh[replay_finish]:
  drule_at (Pat `lower_dload_inst_supply _ _ = _`) dload_supply_replay_boundary_fresh >>
  simp[] >> disch_then drule >> simp[] >>
  disch_then (drule_at (Pat `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `dload_offset_ok _ _ _ _`)) >>
  disch_then (qspec_then `orig` mp_tac) >> simp[] >> strip_tac >>
  `!v. v <> out /\ v <> av /\ v <> cv ==> lookup_var v t4 = lookup_var v t` by
    (drule_at (Pat `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _`)
       dload_four_step_lookup >> simp[]) >>
  qexistsl [`s1`,`r1`] >> simp[] >>
  match_mp_tac dload_step_lookup >> goal_assum (drule_at Any) >> simp[]
QED

Finalise dload_supply_backward_boundary_fresh

Theorem dload_supply_backward_boundary:
  dload_boundary_core lo (r::rs) V Ws PG PH G H tn un s t cs ds /\
  r.dr_scratch = FDOM t.vs_allocas DIFF orig /\
  FDOM s.vs_allocas SUBSET orig /\ (EL 0 xs).inst_id NOTIN orig /\
  t.vs_alloca_next + 32 < dimword (:256) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  lower_dload_inst_supply supply i = (xs,next) /\
  (EL 0 xs).inst_outputs = [av] /\ (EL 1 xs).inst_outputs = [cv] /\
  av <> cv /\ av NOTIN V /\ cv NOTIN V /\ off <> Var av /\
  code_layout_valid s /\ dload_offset_ok C fn i s /\
  MEM i (fn_insts fn) /\ fn_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn i s /\ (!v. off = Var v ==> v IN V) /\
  dload_prefix_match fuel Ct PH xs 4 t H un t4 H4 un4 ==>
  ?s1 r1. step_inst fuel C i s = OK s1 /\
    r1.dr_source = r.dr_source /\
    r1.dr_scratch = (EL 0 xs).inst_id INSERT r.dr_scratch /\
    dload_boundary_core lo (r1::rs) V Ws PG PH
      (step_prov PG G i s1) H4 (step_taint i s s1 tn) un4
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) t4 cs ds /\
    (!v. v <> out ==> lookup_var v s1 = lookup_var v s) /\
    (!v. v <> out /\ v <> av /\ v <> cv ==> lookup_var v t4 = lookup_var v t)
Proof
  strip_tac >> irule dload_supply_backward_boundary_fresh >> metis_tac[]
QED
