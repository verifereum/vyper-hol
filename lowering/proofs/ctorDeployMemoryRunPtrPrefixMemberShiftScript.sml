(* Shifted resources and ambient fields at the supplied member setup cut. *)
Theory ctorDeployMemoryRunPtrPrefixMemberShift
Ancestors
  ctorDeployMemoryRunPtrPrefixMemberFloor ctorDeployMemoryRunPtrPrefixMemberSetup
  ctorDeployLoweringEntryCompleteScalar ctorDeployLoweringEntryRegistration
  ctorDeployLoweringEntryAllocation ctorAbiActualFrame abiDecoderReentry
  abiDecoderContract abiDecoderVarSequence ctorDeployMemoryFrontier venomMemDefs
  allocaFrontierBound allocaBudgetProps compileEnv
  venomState venomInst venomExecSemantics ptrDiscipline ptrSafeRun
  words list arithmetic

Theorem prefix_member_setup_pair_shift:
  abi_decode_member_setup (Var dst) src DLOAD (Lit 0w) dyn ao vo st = (ops,middle) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand (Var dst) s = SOME (n2w d) /\
  (dyn ==> abi_decode_load DLOAD (n2w (sb+ao) : bytes32) s = n2w payload_off /\
           sb+payload_off < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,sz) /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  lo <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts st middle) s = OK t /\
  fn_has_code st middle fn /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  ctor_actual_scratch fn ids scratch_base N s /\ scratch_base+N <= s.vs_alloca_next ==>
  ?H qt child_dst.
    let prepared = t with vs_inst_idx := LENGTH middle.cs_current_insts in
    SND ops = Var child_dst /\ FLOOKUP H child_dst = SOME (b,sz) /\
    op_taint qt (FST ops) = {} /\ op_taint qt (SND ops) = {} /\
    eval_operand (FST ops) prepared = SOME (n2w (sb + if dyn then payload_off else ao)) /\
    eval_operand (SND ops) prepared = SOME (n2w (d+vo)) /\
    abi_decoder_operand_live middle.cs_next_var (FST ops) /\
    abi_decoder_operand_live middle.cs_next_var (SND ops) /\
    fresh_vars_wrt limit_st prepared /\
    abi_decoder_address_frame st.cs_next_var s prepared /\ inst_extends st middle /\
    prepared.vs_allocas = s.vs_allocas /\ prepared.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\
    prepared.vs_current_bb = middle.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==>
       FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt prepared) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    alloca_inv prepared /\ alloca_frontier_inv_from k ctx fn site prepared /\
    ctor_actual_scratch fn ids scratch_base N prepared /\
    scratch_base+N <= prepared.vs_alloca_next /\
    prepared.vs_outcomes = s.vs_outcomes /\ prepared.vs_tx_ctx = s.vs_tx_ctx /\
    prepared.vs_block_ctx = s.vs_block_ctx /\ prepared.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st middle)` by
    (drule prefix_member_setup_code >> simp[LET_THM] >> strip_tac >>
     Cases_on `dyn` >> gvs[abi_decoder_reentry_opcode_def, mk_inst_def]) >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  drule_all prefix_member_setup_pair_floor >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
  simp[LET_THM] >> strip_tac >>
  qexistsl [`H`,`qt`,`child_dst`] >> simp[] >>
  conj_tac >-
    (qpat_x_assum `alloca_inv s` mp_tac >>
     simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]) >>
  conj_tac >-
    (irule deploy_ctor_alloca_frontier_fields >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `ctor_actual_scratch fn ids scratch_base N s` mp_tac >>
  simp[ctor_actual_scratch_def]
QED
