Theory ctorDeployMemoryRunPtrPrefixChildShift
Ancestors
  loweringStateRelDefs
  ctorDeployMemoryRunPtrPrefixScalarClamps
  ctorDeployMemoryRunPtrPrefixExecutionAttach ctorDeployMemoryRunPtrPrefixMemberShift
  ctorDeployLoweringEntryRegistration ctorDeployLoweringEntryAllocation
  ctorDeployMemoryFrontier allocaFrontierBound allocaBudgetProps
  ptrDiscipline ctorAbiActualFrame
  abiDecoderClampedWord abiDecoderContract abiDecoderReentry abiDecoderDynamicLoopSetup compileEnv
  venomState venomExecSemantics venomMemDefs venomMemProps words list arithmetic finite_map

Theorem prefix_read_byte_mstore_below[local]:
  a < d ==> read_byte a (mstore d w s).vs_memory = read_byte a s.vs_memory
Proof
  strip_tac >>
  simp[mstore_def, LET_THM] >>
  qabbrev_tac `expanded = if d + 32 > LENGTH s.vs_memory then
    s.vs_memory ++ REPLICATE (d + 32 - LENGTH s.vs_memory) 0w
    else s.vs_memory` >>
  `d <= LENGTH expanded` by
    (simp[Abbr `expanded`] >> IF_CASES_TAC >> simp[] >> decide_tac) >>
  simp[codegenRelTheory.read_byte_def, LENGTH_TAKE, EL_APPEND_EQN, EL_TAKE] >>
  Cases_on `a < LENGTH s.vs_memory` >>
  simp[Abbr `expanded`] >> Cases_on `d + 32 > LENGTH s.vs_memory` >>
  simp[EL_APPEND_EQN, rich_listTheory.EL_REPLICATE] >>
  `F` by decide_tac
QED

Theorem prefix_execution_int_fields:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (DecPrimWord (IntClamp bits signed)) st = ((),st') /\
  run_inst_seq (emitted_insts st st') initial = OK actual /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst) initial = SOME (n2w d) /\ d < dimword (:256) /\
  (!v. src = Var v \/ Var dst = Var v \/ Lit 0w = Var v ==> not_fresh_at st v) /\
  lo <= d ==>
  actual.vs_allocas = initial.vs_allocas /\
  actual.vs_alloca_next = initial.vs_alloca_next /\
  actual.vs_gas_readings = initial.vs_gas_readings /\
  (!v. not_fresh_at st v ==> lookup_var v actual = lookup_var v initial) /\
  (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory)
Proof
  strip_tac >>
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (mp_then Any mp_tac prefix_scalar_checked_layout) >>
  disch_then (qspecl_then [`signed`,`n2w (if signed then bits DIV 8-1 else bits):bytes32`,`0`,`F`,`bits`] mp_tac) >>
  simp[LET_THM] >> strip_tac >>
  qabbrev_tac `x = "%" ++ toString st.cs_next_var` >>
  qabbrev_tac `y = "%" ++ toString (st.cs_next_var+1)` >>
  qabbrev_tac `z = "%" ++ toString (st.cs_next_var+2)` >>
  `x <> dst /\ y <> dst /\ z <> dst /\ x <> y /\ x <> z /\ y <> z` by
    gvs[Abbr `x`, Abbr `y`, Abbr `z`, not_fresh_at_def] >>
  qpat_assum `eval_operand src initial = _`
    (mp_then Any mp_tac prefix_scalar_word_execution) >>
  disch_then (qspecl_then [`z`,`y`,`x`,`signed`,`n2w d:bytes32`,`n2w (if signed then bits DIV 8-1 else bits):bytes32`,`F`,`st.cs_next_id`,`dst`] mp_tac) >>
  simp[LET_THM] >>
  simp[Abbr `x`, Abbr `y`, Abbr `z`] >>
  qpat_assum `emitted_insts st st' = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  asm_rewrite_tac[] >>
  qmatch_goalsub_abbrev_tac `if valid then OK _ else _` >>
  Cases_on `valid` >> simp[] >> strip_tac >>
  gvs[] >>
  reverse conj_tac >-
    (rpt strip_tac >>
     `a < d` by decide_tac >>
     simp[prefix_read_byte_mstore_below, update_var_def]) >>
  simp[update_var_def, mstore_def] >>
  rpt strip_tac >>
     `v <> STRING #"%" (toString st.cs_next_var) /\
      v <> STRING #"%" (toString (st.cs_next_var+1)) /\
      v <> STRING #"%" (toString (st.cs_next_var+2))` by
       (qpat_x_assum `not_fresh_at st v` mp_tac >>
        simp[not_fresh_at_def] >> strip_tac >>
        rpt conj_tac >> first_x_assum irule >> decide_tac) >>
     simp[lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem prefix_execution_int_attach_shift:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (DecPrimWord (IntClamp bits signed)) st = ((),st') /\
  run_inst_seq (emitted_insts st st') initial = OK actual /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst) initial = SOME (n2w d) /\ d < dimword (:256) /\
  (!v. src = Var v \/ Var dst = Var v \/ Lit 0w = Var v ==> not_fresh_at st v) /\
  fn_has_code st st' func /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= d /\ d+32 <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo initial /\ ~ctx_has_dalloca ctx /\ lo <= d /\
  lo <= initial.vs_alloca_next /\ alloca_inv initial /\
  alloca_frontier_inv_from k ctx func site initial /\
  ctor_actual_scratch func ids scratch_base N initial /\
  scratch_base+N <= initial.vs_alloca_next ==>
  ?H qt.
    let final = actual with vs_inst_idx := LENGTH st'.cs_current_insts in
    final.vs_outcomes = initial.vs_outcomes /\
    final.vs_tx_ctx = initial.vs_tx_ctx /\ final.vs_block_ctx = initial.vs_block_ctx /\
    final.vs_gas_readings = initial.vs_gas_readings /\
    final.vs_allocas = initial.vs_allocas /\
    final.vs_alloca_next = initial.vs_alloca_next /\
    allocas_from lo final /\ lo <= final.vs_alloca_next /\
    alloca_inv final /\ alloca_frontier_inv_from k ctx func site' final /\
    ctor_actual_scratch func ids scratch_base N final /\
    scratch_base+N <= final.vs_alloca_next /\
    (!a. a < lo ==> read_byte a final.vs_memory = read_byte a initial.vs_memory) /\
    qt.t_mem = tn.t_mem DIFF range_bytes [(d,32)] /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==> lookup_var v final = lookup_var v initial /\
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt final) ==>
     !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
  strip_tac >>
  drule_all prefix_execution_int_fields >> strip_tac >>
  drule_all prefix_execution_int_attach >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >> strip_tac >>
  qexistsl [`H`,`qt`] >> simp[LET_THM, lookup_var_def] >>
  conj_tac >-
    (qpat_x_assum `allocas_from lo initial` mp_tac >> simp[allocas_from_def]) >>
  conj_tac >-
    (qpat_x_assum `alloca_inv initial` mp_tac >>
     simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]) >>
  conj_tac >-
    (irule deploy_ctor_alloca_frontier_fields >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `ctor_actual_scratch func ids scratch_base N initial` mp_tac >>
  simp[ctor_actual_scratch_def] >> strip_tac >> simp[] >>
  qpat_x_assum `!v. not_fresh_at st v ==> lookup_var v actual = _` mp_tac >>
  simp[lookup_var_def] >> metis_tac[]
QED

Theorem prefix_member_int_attach_shift:
  abi_decode_member_setup (Var dst) src DLOAD (Lit 0w) dyn ao vo st = (ops,middle) /\
  SND ops = Var child_dst /\
  compile_abi_decode_to_buf (Var child_dst) (FST ops) DLOAD (Lit 0w)
    (DecPrimWord (IntClamp bits signed)) middle = ((),end_st) /\
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
  fn_has_code st middle func /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
  ctor_actual_scratch func ids scratch_base N s /\ scratch_base+N <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts middle end_st)
    (t with vs_inst_idx := LENGTH middle.cs_current_insts) = OK actual /\
  fn_has_code middle end_st func /\
  lo <= d+vo /\ d+vo < dimword (:256) /\ b <= d+vo /\ d+vo+32 <= b+sz ==>
  ?K rt.
    let final = actual with vs_inst_idx := LENGTH end_st.cs_current_insts in
    final.vs_outcomes = s.vs_outcomes /\
    final.vs_tx_ctx = s.vs_tx_ctx /\ final.vs_block_ctx = s.vs_block_ctx /\
    final.vs_gas_readings = s.vs_gas_readings /\
    final.vs_allocas = s.vs_allocas /\ final.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo final /\ lo <= final.vs_alloca_next /\
    alloca_inv final /\ alloca_frontier_inv_from k ctx func site' final /\
    ctor_actual_scratch func ids scratch_base N final /\
    scratch_base+N <= final.vs_alloca_next /\
    (!a. a < lo ==> read_byte a final.vs_memory = read_byte a s.vs_memory) /\
    rt.t_mem = tn.t_mem DIFF range_bytes [(d+vo,32)] /\
    rt.t_stor = tn.t_stor /\ rt.t_trans = tn.t_trans /\ rt.t_imm = tn.t_imm /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG K rt final) ==>
     !fuel. ptr_safe_run D lo fuel ctx func PG G tn s)
Proof
  strip_tac >>
  drule_all prefix_member_setup_pair_shift >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
  simp[LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts middle end_st) prepared` >>
  `(!v. FST ops = Var v \/ Var child_dst = Var v \/ Lit 0w = Var v ==>
       not_fresh_at middle v)` by
    (rpt strip_tac >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `eval_operand (FST ops) prepared = SOME (n2w (sb + if dyn then payload_off else ao)) /\
   eval_operand (Var child_dst) prepared = SOME (n2w (d+vo))` by
    simp[Abbr `prepared`] >>
  qpat_assum `compile_abi_decode_to_buf (Var child_dst) _ _ _ _ _ = _`
    (mp_then Any mp_tac prefix_execution_int_attach_shift) >>
  disch_then (drule_at (Pat `run_inst_seq _ prepared = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP H _ = _`)) >>
  disch_then (drule_at (Pat `op_taint qt (FST ops) = _`)) >>
  disch_then (drule_at (Pat `eval_operand (FST ops) prepared = _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var child_dst) prepared = _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv_from k ctx func site prepared`)) >>
  disch_then (drule_at (Pat `ctor_actual_scratch func ids scratch_base N prepared`)) >>
  disch_then (drule_at (Pat `allocas_from lo prepared`)) >>
  disch_then (qspecl_then [`site'`,`PG`,`D`] mp_tac) >>
  (impl_tac >- (simp[Abbr `prepared`] >> metis_tac[])) >>
  simp[LET_THM] >> strip_tac >>
  qexistsl [`H'`,`qt'`] >> simp[LET_THM] >>
  `prepared.vs_memory = s.vs_memory` by
    gvs[Abbr `prepared`, abi_decoder_address_frame_def] >>
  simp[Abbr `prepared`]
QED
