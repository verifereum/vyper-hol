Theory readonlyInvokeCopyFwdExecutionEffects
Ancestors
  allocaFrontierBound
  venomWf
  readonlyInvokeCopyFwdExecutionFields readonlyInvokeCopyFwdExecutionOrdinary
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdStepsEffects readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdOperationalSupport
  o1LowerDloadJointScalar o1LowerDloadPtrDiscipline o1LowerDloadGhost
  o1LowerDloadRelocationKernel o1LowerDloadOccurrence
  internalReturnCopyFwdSim frameViewFacts frameRel unitShapeDefs o1PassContract
  ptrDiscipline taintAgree pointerConfinedDefs memLocDefs
  venomExecSemantics venomState venomInst contextCodegenRel codegenRel
  finite_map list pred_set words

Theorem ricf_opaque_frame_sstore[local]:
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  word_agree_except m x y ==>
  ricf_opaque_frame_agree fn D X sites PG G
    (tn with t_stor := key_update tn.t_stor key m)
    (sstore key x s) (sstore key y t)
Proof
  simp[ricf_opaque_frame_agree_def] >> strip_tac >>
  drule_all ricf_frame_sstore >> disch_then (qspec_then `key` mp_tac) >>
  simp[ricf_opaque_view_def, sstore_def]
QED

Theorem ricf_opaque_frame_tstore[local]:
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  word_agree_except m x y ==>
  ricf_opaque_frame_agree fn D X sites PG G
    (tn with t_trans := key_update tn.t_trans key m)
    (tstore key x s) (tstore key y t)
Proof
  simp[ricf_opaque_frame_agree_def] >> strip_tac >>
  drule_all ricf_frame_tstore >> disch_then (qspec_then `key` mp_tac) >>
  simp[ricf_opaque_view_def, tstore_def]
QED

Theorem ricf_execution_store_operands[local]:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ssa_form fn /\ opaque_use_ok fn /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SSTORE;TSTORE] /\ inst.inst_operands = [kop;vop] /\
  eval_operand kop s = SOME key /\ eval_operand vop s = SOME x ==>
  ?y. eval_operand kop t = SOME key /\ eval_operand vop t = SOME y /\
    word_agree_except (op_taint tn vop) x y
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    metis_tac[frame_reachable_prov_support] >>
  `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `!op. MEM op inst.inst_operands ==> op_prov G op = NONE` by
    (rpt strip_tac >> irule ld_scalar_no_provenance >>
     qexistsl_tac [`P`,`inst`,`fn_pv P fn`] >>
     fs[MEM] >> simp[is_pointer_preserving_op_def,
       mem_read_ops_def, mem_write_ops_def]) >>
  `op_taint tn kop = {}` by
    (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[]) >>
  `eval_operand kop t = SOME key` by
    (drule ricf_execution_scalar_operand >> disch_then irule >>
     fs[MEM] >> simp[is_pointer_preserving_op_def, mem_read_ops_def,
       mem_write_ops_def] >> metis_tac[MEM]) >>
  `!name. vop = Var name ==> ~retpc_var fn name` by
    (rpt gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> fs[MEM] >>
     metis_tac[active_inst_mem_fn_insts]) >>
  `op_prov G vop = NONE` by metis_tac[MEM] >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  drule_all (Q.INST [`op` |-> `vop`] ricf_opaque_frame_operand) >> strip_tac >>
  rename1 `eval_operand vop t = SOME y` >>
  qexists_tac `y` >>
  gvs[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
    ricf_value_agree_def, ld_value_agree_def, MEM]
QED

Theorem ricf_execution_storage_store_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  o1_fn_shape C fn /\ wf_ssa fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SSTORE;TSTORE] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `ssa_form fn /\ opaque_use_ok fn /\ fn_inst_wf fn` by
    fs[o1_fn_shape_def, fn_shape_ok_def, wf_ssa_def] >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `inst.inst_outputs = []` by gvs[MEM, inst_wf_def] >>
  `t.vs_call_ctx = s.vs_call_ctx` by
    fs[ricf_execution_invariant_def, ricf_opaque_frame_agree_def,
      ricf_frame_agree_def, taint_agree_def, ricf_opaque_view_def,
      venom_state_component_equality] >>
  `?kop vop key x. inst.inst_operands = [kop;vop] /\
    eval_operand kop s = SOME key /\ eval_operand vop s = SOME x /\
    ~s.vs_call_ctx.cc_static /\
    u = if inst.inst_opcode = SSTORE then sstore key x s else tstore key x s` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >> fs[MEM] >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def,
       eval_operands_def, AllCaseEqs()] >>
     strip_tac >> gvs[eval_operands_def] >> metis_tac[]) >>
  drule_all ricf_execution_store_operands >> strip_tac >>
  rename1 `eval_operand vop t = SOME y` >>
  qexists_tac `if inst.inst_opcode = SSTORE then sstore key y t else tstore key y t` >>
  conj_asm1_tac
  >- (fs[MEM] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
        exec_write2_def, eval_operands_def]) >>
  `!j. j < LENGTH stk ==>
    (EL j stk).cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
    (EL j targets).vs_call_ctx.cc_address = t.vs_call_ctx.cc_address` by
    metis_tac[ricf_execution_stack_addresses] >>
  `step_taint inst s u tn =
    if inst.inst_opcode = SSTORE then
      tn with t_stor := key_update tn.t_stor key (op_taint tn vop)
    else tn with t_trans := key_update tn.t_trans key (op_taint tn vop)` by
    (fs[MEM] >>
     gvs[step_taint_def, mem_taint_def, new_site_bytes_def,
       written_taint_def, step_writes_def, source_memory_write_ranges_def,
       store_taint_def, imm_taint_def, adopt_reset_def, set_var_taint_def,
       DRESTRICT_UNIV, range_bytes_def, taint_component_equality,
       sstore_def, tstore_def, FLOOKUP_DEF] >> SET_TAC[]) >>
  mp_tac (Q.INST [`rt` |-> `tn`, `v` |->
    `if inst.inst_opcode = SSTORE then sstore key y t else tstore key y t`]
    ricf_execution_next) >>
  impl_tac >- (simp[] >> fs[MEM] >>
  (simp[is_terminator_def, occurrence_sites_step_def, step_prov_def,
    set_prov_def, DRESTRICT_UNIV] >>
  fs[ricf_execution_invariant_def] >> gvs[] >> rpt conj_tac
  >- (mp_tac (Q.INST [`X` |-> `ircf_dead (ricf_original_copy_ids C) s stk`,
        `PG` |-> `ricf_complete_params PG s.vs_params`, `m` |-> `op_taint tn vop`]
        ricf_opaque_frame_sstore) >>
      mp_tac (Q.INST [`X` |-> `ircf_dead (ricf_original_copy_ids C) s stk`,
        `PG` |-> `ricf_complete_params PG s.vs_params`, `m` |-> `op_taint tn vop`]
        ricf_opaque_frame_tstore) >>
      simp[] >> simp[sstore_def, tstore_def, ircf_dead_def])
  >- (fs[ricf_opaque_live_stack_agree_def] >> rpt strip_tac >>
      qpat_x_assum `!j. _ ==> ricf_opaque_frame_agree _ _ _ _ _ _ _ _ _`
        (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
      first_x_assum (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
      mp_tac (Q.INST [`fn` |-> `(EL j stk).cf_fn`,
        `X` |-> `ircf_dead (ricf_original_copy_ids C) (EL j stk).cf_state (DROP (SUC j) stk)`,
        `sites` |-> `EL j maps`, `PG` |-> `ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params`,
        `G` |-> `(EL j stk).cf_prov`, `tn` |-> `tn with t_var := (EL j stk).cf_tvar`,
        `s` |-> `merge_callee_state (EL j stk).cf_state s`,
        `t` |-> `merge_callee_state (EL j targets) t`,
        `m` |-> `op_taint tn vop`] ricf_opaque_frame_sstore) >>
      mp_tac (Q.INST [`fn` |-> `(EL j stk).cf_fn`,
        `X` |-> `ircf_dead (ricf_original_copy_ids C) (EL j stk).cf_state (DROP (SUC j) stk)`,
        `sites` |-> `EL j maps`, `PG` |-> `ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params`,
        `G` |-> `(EL j stk).cf_prov`, `tn` |-> `tn with t_var := (EL j stk).cf_tvar`,
        `s` |-> `merge_callee_state (EL j stk).cf_state s`,
        `t` |-> `merge_callee_state (EL j targets) t`,
        `m` |-> `op_taint tn vop`] ricf_opaque_frame_tstore) >>
      simp[] >> simp[merge_callee_state_def, sstore_def, tstore_def])
  >- (gvs[ircf_cross_def, sstore_def, tstore_def] >> metis_tac[])
  >- (gvs[ricf_cert_crosses_def, ircf_cross_def, sstore_def, tstore_def] >> metis_tac[])
  >> gvs[ricf_support_agree_def, sstore_def, tstore_def] >> metis_tac[])) >> simp[]
QED
