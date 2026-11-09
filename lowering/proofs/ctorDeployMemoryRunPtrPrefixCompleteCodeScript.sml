(* Code framing comes from concrete sequence witnesses, not continuation inclusion. *)
Theory ctorDeployMemoryRunPtrPrefixCompleteCode
Ancestors
  ctorDeployMemoryRunPtrPrefixCompleteMembers
  ctorDeployMemoryRunPtrPrefixCompleteMemberSetup
  ctorDeployMemoryRunPtrPrefixCompleteScalar
  ctorDeployLoweringEntryRegistration abiDecoderClampedWord abiDecoderReentry
  abiDecoderReentryPointer
  ctorAbiActualObservations ctorAbiActualMemberSetup abiDecoderMemberSetup abiDecoderContract
  abiDecoderMemberInfos abiDecoderMembers abiDecoderCoherence abiDecoderTypedContract
  abiDecoderEmpty ctorDeployMemoryRunPtrPrefixEmptyFloor abiEncoderRegisteredEffect
  abiEncoder abiDecoderLoop allocaFrontierBound valueEncoding exprLoweringProps
  abiDecoderWordTyped abiDecoderLayout ctorDeployMemoryFrontier
  compileEnv venomState venomInst venomExecSemantics
  ptrDiscipline ptrSafeRun words list arithmetic
  ctorDeployMemoryRunPtrPrefixMembersCons ctorAbiActualWorld ctorAbiActualAlloc
  abiDecoderDynamicLoopSetup abiDecoderMemberCode abiDecoderMemberCons abiDecoderMemberBody
  ctorAbiActualMemberInputs abiEncoderProps ctorDeployMemoryRunPtrPrefixMembers
  ctorAbiActualChildFrame fragExec ctorAbiActualSites allocaBudgetProps
  finite_map pred_set contractABI venomMemDefs

Theorem prefix_scalar_sequence_code:
  compile_abi_decode_to_buf dst src DLOAD hi (DecPrimWord clamp) st = ((),st') /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  t.vs_code = s.vs_code
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> simp[]
QED

Theorem prefix_member_setup_sequence_code:
  abi_decode_member_setup dst src DLOAD (Lit 0w) dyn ao vo st = (ops,middle) /\
  run_inst_seq (emitted_insts st middle) s = OK t ==>
  t.vs_code = s.vs_code
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule ctor_actual_member_setup_opcodes >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> simp[]
QED

Theorem prefix_scalar_complete_execution_code:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst) initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual.
    run_inst_seq (emitted_insts st st') initial = OK actual /\
    let final = actual with vs_inst_idx := LENGTH st'.cs_current_insts in
    val_in_memory tv v d final.vs_memory /\ fresh_vars_wrt limit_st final /\
    abi_decode_frame d 32 initial final /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op final = SOME w) /\
    final.vs_allocas = initial.vs_allocas /\
    final.vs_alloca_next = initial.vs_alloca_next /\
    final.vs_outcomes = initial.vs_outcomes /\
    final.vs_tx_ctx = initial.vs_tx_ctx /\ final.vs_block_ctx = initial.vs_block_ctx /\
    final.vs_gas_readings = initial.vs_gas_readings /\
    final.vs_code = initial.vs_code /\
    abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
      [(d,32)] initial final
Proof
  strip_tac >> drule_all prefix_scalar_complete_execution >>
  disch_then (qspec_then `func` mp_tac) >> simp[LET_THM] >> strip_tac >>
  drule_all prefix_scalar_sequence_code >> disch_tac >>
  qexists `actual` >> simp[LET_THM]
QED

Theorem prefix_scalar_complete_shift_code:
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst) initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= d /\ d+32 <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo initial /\ ~ctx_has_dalloca ctx /\ lo <= d /\
  lo <= initial.vs_alloca_next /\ alloca_inv initial /\
  alloca_frontier_inv_from k ctx func site initial /\
  ctor_actual_scratch func ids scratch_base N initial /\
  scratch_base+N <= initial.vs_alloca_next ==>
  ?actual H qt.
    run_inst_seq (emitted_insts st st') initial = OK actual /\
    let final = actual with vs_inst_idx := LENGTH st'.cs_current_insts in
    val_in_memory tv v d final.vs_memory /\ fresh_vars_wrt limit_st final /\
    abi_decode_frame d 32 initial final /\
    abi_decode_sim ctx func initial final /\
    ~final.vs_halted /\ final.vs_current_bb = st'.cs_current_bb /\
    final.vs_inst_idx = LENGTH st'.cs_current_insts /\
    final.vs_data_section = initial.vs_data_section /\
    final.vs_call_ctx = initial.vs_call_ctx /\ final.vs_labels = initial.vs_labels /\
    final.vs_outcomes = initial.vs_outcomes /\
    final.vs_tx_ctx = initial.vs_tx_ctx /\ final.vs_block_ctx = initial.vs_block_ctx /\
    final.vs_gas_readings = initial.vs_gas_readings /\
    final.vs_code = initial.vs_code /\
    final.vs_allocas = initial.vs_allocas /\
    final.vs_alloca_next = initial.vs_alloca_next /\
    allocas_from lo final /\ lo <= final.vs_alloca_next /\
    alloca_inv final /\ alloca_frontier_inv_from k ctx func site' final /\
    ctor_actual_scratch func ids scratch_base N final /\
    scratch_base+N <= final.vs_alloca_next /\
    (!a. a < lo ==> read_byte a final.vs_memory = read_byte a initial.vs_memory) /\
    qt.t_mem = tn.t_mem DIFF range_bytes [(d,32)] /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x final = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x)) /\
    abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
      [(d,32)] initial final /\
    (?B. FINITE B /\ B SUBSET range_bytes [(d,32)] /\ DISJOINT B qt.t_mem /\
      (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 final.vs_memory) ==>
        val_in_memory tv v d mem)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt final) ==>
     !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
  strip_tac >> drule_all prefix_scalar_complete_shift >>
  disch_then (qspecl_then [`site'`,`PG`,`D`] mp_tac) >>
  simp[LET_THM] >> strip_tac >>
  drule_all prefix_scalar_sequence_code >> disch_tac >>
  qexistsl [`actual`,`H`,`qt`] >> simp[LET_THM] >> metis_tac[]
QED

Theorem prefix_member_setup_complete_shift_code:
  abi_decode_member_setup (Var dst) src DLOAD (Lit 0w) dyn ao vo st = (ops,middle) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand (Var dst) s = SOME (n2w d) /\
  (dyn ==> abi_decode_load DLOAD (n2w (sb+ao) : bytes32) s = n2w payload_off /\
           sb+payload_off < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,sz) /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  lo <= s.vs_alloca_next /\ ~s.vs_halted /\
  fn_has_code st middle fn /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  ctor_actual_scratch fn ids scratch_base N s /\ scratch_base+N <= s.vs_alloca_next ==>
  ?t H qt child_dst.
    run_inst_seq (emitted_insts st middle) s = OK t /\
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
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\ ~prepared.vs_halted /\
    prepared.vs_memory = s.vs_memory /\ prepared.vs_data_section = s.vs_data_section /\
    prepared.vs_call_ctx = s.vs_call_ctx /\ prepared.vs_labels = s.vs_labels /\
    (!v. not_fresh_at st v ==> lookup_var v prepared = lookup_var v s) /\
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
    prepared.vs_block_ctx = s.vs_block_ctx /\ prepared.vs_gas_readings = s.vs_gas_readings /\
    prepared.vs_code = s.vs_code
Proof
  strip_tac >> drule_all prefix_member_setup_complete_shift >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >> simp[LET_THM] >> strip_tac >>
  drule_all prefix_member_setup_sequence_code >> disch_tac >>
  qexistsl [`t`,`H`,`qt`,`child_dst`] >> simp[LET_THM]
QED

Theorem prefix_canonical_member_setup_complete_shift_code:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) s.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) /\
  abi_decode_member_setup (Var dst) src DLOAD (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = (ops,middle) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand (Var dst) s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (b,sz) /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  lo <= s.vs_alloca_next /\ ~s.vs_halted /\
  fn_has_code st middle fn /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  ctor_actual_scratch fn ids scratch_base N s /\ scratch_base+N <= s.vs_alloca_next ==>
  ?t H qt child_dst.
    run_inst_seq (emitted_insts st middle) s = OK t /\
    let prepared = t with vs_inst_idx := LENGTH middle.cs_current_insts in
    SND ops = Var child_dst /\ FLOOKUP H child_dst = SOME (b,sz) /\
    op_taint qt (FST ops) = {} /\ op_taint qt (SND ops) = {} /\
    eval_operand (FST ops) prepared = SOME (n2w (sb +
      if type_to_abi_dec_info sf ce ty = DecComplex T [] then
        SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))
      else abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
        (preavs ++ av::avs) (LENGTH pretys))) /\
    eval_operand (SND ops) prepared = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) /\
    abi_decoder_operand_live middle.cs_next_var (FST ops) /\
    abi_decoder_operand_live middle.cs_next_var (SND ops) /\
    fresh_vars_wrt limit_st prepared /\
    abi_decoder_address_frame st.cs_next_var s prepared /\ inst_extends st middle /\
    prepared.vs_allocas = s.vs_allocas /\ prepared.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\
    prepared.vs_current_bb = middle.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\ ~prepared.vs_halted /\
    prepared.vs_memory = s.vs_memory /\ prepared.vs_data_section = s.vs_data_section /\
    prepared.vs_call_ctx = s.vs_call_ctx /\ prepared.vs_labels = s.vs_labels /\
    (!x. not_fresh_at st x ==> lookup_var x prepared = lookup_var x s) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
       FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt prepared) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    alloca_inv prepared /\ alloca_frontier_inv_from k ctx fn site prepared /\
    ctor_actual_scratch fn ids scratch_base N prepared /\
    scratch_base+N <= prepared.vs_alloca_next /\
    prepared.vs_outcomes = s.vs_outcomes /\ prepared.vs_tx_ctx = s.vs_tx_ctx /\
    prepared.vs_block_ctx = s.vs_block_ctx /\ prepared.vs_gas_readings = s.vs_gas_readings /\
    prepared.vs_code = s.vs_code
Proof
  strip_tac >> drule_all prefix_canonical_member_setup_complete_shift >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >> simp[LET_THM] >> strip_tac >>
  drule_all prefix_member_setup_sequence_code >> disch_tac >>
  qexistsl [`t`,`H`,`qt`,`child_dst`] >> simp[LET_THM]
QED

val CshiftCode = ``\ty tv.
 !dst src st st' ctx func site initial limit_st sb d D N ids av v root_di
  G tn b sz Ddead lo PG.
 compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
   (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand (Var dst) initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
   initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb.
    lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
 d + type_memory_bytes ce ty <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
 lo <= initial.vs_alloca_next /\ lo <= d ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory) /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\
 DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
    val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
                           op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

val MshiftCode = ``\tys tvs.
 !dst src st final ctx func site initial limit_st sb d D N ids
   pretys pretvs preavs prevs avs vs G tn b sz Ddead lo PG.
 compile_abi_decode_complex_elems (Var dst) src DLOAD (Lit 0w)
   (abi_decoder_member_infos sf ce tys)
   (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
   (SUM (MAP (type_memory_bytes ce) pretys)) st = ((),final) /\
 abi_decoder_members ce env sf pretys pretvs preavs prevs /\
 abi_decoder_members ce env sf tys tvs avs vs /\
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand (Var dst) initial = SOME (n2w d) /\
 sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs))) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs)))) initial.vs_data_section =
   enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs)) /\
 (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
 final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st final func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = final.cs_blocks \/ !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ tys)) <= D+N /\
 D+N <= initial.vs_alloca_next /\ frag_ids st final SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
 d + SUM (MAP (type_memory_bytes ce) (pretys ++ tys)) <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\ lo <= initial.vs_alloca_next /\ lo <= d ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final))
   [(d + SUM (MAP (type_memory_bytes ce) pretys), SUM (MAP (type_memory_bytes ce) tys))] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial) /\
 ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory) /\
 FINITE B /\ B SUBSET range_bytes
   [(d + SUM (MAP (type_memory_bytes ce) pretys), SUM (MAP (type_memory_bytes ce) tys))] /\
 DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
   tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
                           op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

Theorem prefix_members_complete_code_nil:
  (^MshiftCode) [] []
Proof
  BETA_TAC >> rpt gen_tac >>
  simp[abi_decoder_member_infos_def, Once compile_abi_decode_to_buf_def,
    comp_return_def, Excl "enc_def"] >> strip_tac >>
  drule abi_decoder_members_lengths >> strip_tac >> gvs[Excl "enc_def"] >>
  qexistsl [`initial`,`G`,`tn`,`{}`] >>
  simp[val_in_memory_def, abi_encoder_registered_effect_refl, abi_decode_sim_refl]
QED

Theorem prefix_scalar_complete_code_contract:
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==> (^CshiftCode) ty tv
Proof
  disch_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` by
    (qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
      (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
     drule_all abi_decoder_descended_encoding_length >> simp[]) >>
  `sb < dimword (:256) /\ d < dimword (:256)` by
    (qpat_x_assum `alloca_frontier_inv_from _ _ _ _ _` mp_tac >>
     simp[alloca_frontier_inv_from_def] >> strip_tac >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var (Var dst)` by
    (Cases_on `src` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
     (DecPrimWord clamp) st = ((),st')` by metis_tac[] >>
  `mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
   d+32 <= b+sz` by metis_tac[] >>
  drule_all prefix_scalar_complete_shift_code >>
  disch_then (qspecl_then [`site`,`PG`,`Ddead`] mp_tac) >>
  simp[LET_THM, Excl "enc_def"] >> strip_tac >>
  qexistsl [`actual with vs_inst_idx := LENGTH st'.cs_current_insts`,`H`,`qt`,`B`] >>
  simp[Excl "enc_def"]
QED

Theorem prefix_empty_complete_code_contract:
  type_to_abi_dec_info sf ce ty = DecComplex T [] ==> (^CshiftCode) ty tv
Proof
  disch_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (DecComplex T []) st = ((),st')` by metis_tac[] >>
  drule prefix_empty_inline_code >> strip_tac >>
  drule_all abi_decoder_empty_metadata_value >> strip_tac >>
  qexistsl [`initial`,`G`,`tn`,`{}`] >>
  simp[abi_encoder_registered_effect_refl, abi_decode_sim_refl]
QED

val HshiftCode = ``\ctx func site ids D N limit_st tv v d sz st st' initial G tn actual H qt B Ddead lo PG.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,sz)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\
 actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx /\
 actual.vs_gas_readings = initial.vs_gas_readings /\
 (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory) /\
 FINITE B /\ B SUBSET range_bytes [(d,sz)] /\ DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
   val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\ qt.t_stor = tn.t_stor /\
 qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
   op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

Theorem prefix_members_complete_code_cons:
  (^CshiftCode) ty tv /\ (^MshiftCode) tys tvs ==>
  (^MshiftCode) (ty::tys) (tv::tvs)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (mk_asm "tail")) >>
  BETA_TAC >> rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_members_lengths >> strip_tac >>
  Cases_on `avs` >- gvs[] >> Cases_on `vs` >- gvs[] >>
  rename1 `abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs') (v::vs')` >>
  drule abi_decoder_member_cons_trace >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule_all abi_decoder_members_child_phi >> disch_then assume_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var (Var dst)` by
    (asm_x "child" kall_tac >> asm_x "tail" kall_tac >> Cases_on `src` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `fn_has_code st middle func` by
    (mp_tac (Q.SPECL [`st`,`middle`,`final`,`func`] fn_has_code_split) >> simp[]) >>
  drule_all prefix_canonical_member_setup_complete_shift_code >>
  disch_then (qspecl_then [`PG`,`Ddead`] strip_assume_tac) >>
  qpat_x_assum `LET _ _` (strip_assume_tac o SIMP_RULE bool_ss [LET_THM]) >>
  qmatch_asmsub_abbrev_tac `allocas_from lo prepared` >>
  `abi_decode_sim ctx func initial prepared /\
   abi_encoder_registered_effect {} [] initial prepared` by
    (qunabbrev_tac `prepared` >>
     drule_all prefix_member_setup_shift_execution_frame >> simp[]) >>
  `fn_has_code middle end_st func` by
    (mp_tac (Q.SPECL [`middle`,`end_st`,`final`,`func`] fn_has_code_split) >> simp[]) >>
  `?after_head Hh qh Bh. (^HshiftCode) ctx func site ids D N limit_st tv v
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty)
    middle end_st prepared H qt after_head Hh qh Bh Ddead lo PG` by
    suspend "head" >>
  pop_assum (strip_assume_tac o BETA_RULE) >>
  suspend "tail_and_compose"
QED

Resume prefix_members_complete_code_cons[head]:
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- suspend "empty_head" >>
  mp_tac (Q.INST [`childsrc` |-> `FST (ops:operand # operand)`,
    `childdst` |-> `SND (ops:operand # operand)`, `hi` |-> `Lit (0w:256 word)`,
    `avs` |-> `avs':abi_value list`, `vs` |-> `vs':value list`]
    ctor_actual_member_child_inputs) >>
  (impl_tac >- asm_simp_tac bool_ss
    [MAP_APPEND, MAP, abi_decoder_operand_live_def, operand_case_def]) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `SND ops = Var child_dst` SUBST_ALL_TAC >>
  BETA_TAC >>
  asm "child" (fn th =>
    qpat_assum `compile_abi_decode_to_buf (Var child_dst) _ _ _ _ _ = _`
      (mp_then Any mp_tac (BETA_RULE th))) >>
  disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv_from _ _ _ _ prepared`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ prepared`)) >>
  disch_then (drule_at (Pat `FLOOKUP H child_dst = _`)) >>
  disch_then (drule_at (Pat `op_taint qt (FST ops) = _`)) >>
  disch_then (drule_at (Pat `ctor_actual_scratch _ _ _ _ prepared`)) >>
  disch_then (qspecl_then
    [`sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
       (preavs ++ av::avs') (LENGTH pretys)`,
     `d + SUM (MAP (type_memory_bytes ce) pretys)`, `Ddead`,`lo`,`PG`] mp_tac) >>
  (impl_tac >-
    (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
     asm_simp_tac bool_ss [] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- decide_tac >>
     conj_tac >- (qpat_x_assum `frag_ids st final SUBSET ids` mp_tac >>
       simp_tac (srw_ss()) [frag_ids_def, SUBSET_DEF, IN_DIFF, IN_COUNT] >>
       strip_tac >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
     full_simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM] >> decide_tac)) >>
  simp_tac bool_ss []
QED

Resume prefix_members_complete_code_cons[empty_head]:
  asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
  qpat_assum `abi_decoder_members ce env sf pretys pretvs preavs prevs`
    (mp_then Any mp_tac abi_decoder_members_child_facts) >>
  disch_then drule >> strip_tac >>
  `compile_abi_decode_to_buf (SND ops) (FST ops) DLOAD (Lit 0w)
    (DecComplex T []) middle = ((),end_st)` by metis_tac[] >>
  drule prefix_empty_inline_code >> strip_tac >>
  drule_all abi_decoder_empty_metadata_value >> strip_tac >>
  qexistsl [`prepared`,`H`,`qt`,`{}`] >> BETA_TAC >>
  simp[abi_encoder_registered_effect_refl, abi_decode_sim_refl]
QED

Resume prefix_members_complete_code_cons[tail_and_compose]:
  asm_x "child" kall_tac >>
  `abi_decoder_members ce env sf (pretys ++ [ty]) (pretvs ++ [tv])
     (preavs ++ [av]) (prevs ++ [v]) /\
   abi_decoder_members ce env sf tys tvs avs' vs'` by
    (asm_x "tail" kall_tac >>
     qpat_assum `abi_decoder_members _ _ _ (_::_) _ _ _`
       (mp_tac o PURE_REWRITE_RULE [abi_decoder_members_def]) >>
     strip_tac >> conj_tac
     >- (irule abi_decoder_members_join >> simp[abi_decoder_members_def]) >>
     first_assum ACCEPT_TAC) >>
  `compile_abi_decode_complex_elems (Var dst) src DLOAD (Lit 0w)
    (abi_decoder_member_infos sf ce tys)
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (pretys ++ [ty]))))
    (SUM (MAP (type_memory_bytes ce) (pretys ++ [ty]))) end_st = ((),final)` by
    (asm_x "tail" kall_tac >>
     qpat_assum `abi_decoder_members _ _ _ (_::_) _ _ _`
       (mp_tac o PURE_REWRITE_RULE [abi_decoder_members_def]) >> strip_tac >>
     drule abi_decoder_coherent_header >>
     simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
     qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ end_st = _` mp_tac >>
     qpat_x_assum `abi_embedded_static_size _ ty = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0]) >>
  `!x. not_fresh_at st x ==> not_fresh_at middle x` by
    (asm_x "tail" kall_tac >> simp_tac bool_ss [not_fresh_at_def] >>
     metis_tac[LESS_EQ_TRANS]) >>
  `!x. not_fresh_at st x ==> lookup_var x after_head = lookup_var x initial /\
     FLOOKUP Hh x = FLOOKUP G x /\ op_taint qh (Var x) = op_taint tn (Var x)` by
    (asm_x "tail" kall_tac >> metis_tac[]) >>
  `eval_operand src after_head = SOME (n2w sb) /\
   eval_operand (Var dst) after_head = SOME (n2w d)` by
    (asm_x "tail" kall_tac >>
     rpt conj_tac >> irule ctor_actual_old_operand >>
     qexistsl [`initial`,`st`] >> asm_rewrite_tac[] >> metis_tac[]) >>
  drule_all abi_decoder_members_tail_phi >> disch_then assume_tac >>
  asm "tail" (fn th =>
    qpat_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ end_st = _`
      (mp_then Any mp_tac (BETA_RULE th))) >>
  disch_then (drule_at (Pat `abi_decoder_members _ _ _ (pretys ++ [ty]) _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_members _ _ _ tys tvs avs' vs'`)) >>
  disch_then (drule_at (Pat `eval_operand src after_head = _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv_from _ _ _ _ after_head`)) >>
  disch_then (drule_at (Pat `ctor_actual_scratch _ _ _ _ after_head`)) >>
  disch_then (qspecl_then [`limit_st`,`sb`,`Hh`,`qh`,`b`,`sz`,`Ddead`,`lo`,`PG`] mp_tac) >>
  (impl_tac >- suspend "tail_inputs") >>
  disch_then (qx_choose_then `actual` (qx_choose_then `Ht`
    (qx_choose_then `qtail` (qx_choose_then `Bt` strip_assume_tac)))) >>
  asm_x "tail" kall_tac >> suspend "compose"
QED

Resume prefix_members_complete_code_cons[tail_inputs]:
  asm_x "tail" kall_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0, ADD_ASSOC]) >>
  asm_simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0, ADD_ASSOC,
    GSYM APPEND_ASSOC, APPEND] >>
  conj_tac >- (rpt strip_tac >> fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  conj_tac >-
    (qpat_x_assum `frag_ids st final SUBSET ids` mp_tac >>
     simp_tac (srw_ss()) [frag_ids_def, SUBSET_DEF, IN_DIFF, IN_COUNT] >>
     strip_tac >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  Cases_on `src` >> fs[op_taint_def] >> metis_tac[]
QED

Resume prefix_members_complete_code_cons[compose]:
  `actual.vs_code = initial.vs_code` by metis_tac[] >>
  `!a. a IN Bh ==> mem_bytes_at a 1 actual.vs_memory =
       mem_bytes_at a 1 after_head.vs_memory` by
    (qpat_assum `abi_encoder_registered_effect _ _ after_head actual`
       (mp_then Any mp_tac prefix_member_support_frame) >>
     disch_then (drule_at (Pat `ctor_actual_scratch _ _ _ _ actual`)) >>
     disch_then (fn th => qpat_assum `Bh SUBSET _` (mp_then Any mp_tac th)) >>
     `frag_ids end_st final SUBSET ids` by
       (qpat_x_assum `frag_ids st final SUBSET ids` mp_tac >>
        simp_tac (srw_ss()) [frag_ids_def, SUBSET_DEF, IN_DIFF, IN_COUNT] >>
        strip_tac >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
     `D <= d + SUM (MAP (type_memory_bytes ce) pretys) /\
      d + SUM (MAP (type_memory_bytes ce) pretys) + type_memory_bytes ce ty <= D+N /\
      regions_disjoint (d + SUM (MAP (type_memory_bytes ce) pretys),type_memory_bytes ce ty)
        (d + SUM (MAP (type_memory_bytes ce) (pretys ++ [ty])),
         SUM (MAP (type_memory_bytes ce) tys))` by
       (fs[MAP_APPEND, MAP, SUM_APPEND, SUM, venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
     simp[]) >>
  `val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory` by
    (qpat_assum `!mem. _ ==> val_in_memory tv v _ mem` irule >> simp[]) >>
  `type_memory_size tv = type_memory_bytes ce ty` by
    (qpat_assum `abi_decoder_members ce env sf pretys pretvs preavs prevs`
      (mp_then Any mp_tac abi_decoder_members_child_facts) >>
     disch_then drule >> simp[]) >>
  qexistsl [`actual`,`Ht`,`qtail`,`Bh UNION Bt`] >>
  asm_simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0, ADD_ASSOC,
    FINITE_UNION, DISJOINT_UNION, SUBSET_UNION] >>
  conj_tac >-
    (asm_simp_tac bool_ss [val_in_memory_def] >>
     qpat_x_assum `tuple_in_memory vs' tvs _ actual.vs_memory` mp_tac >>
     qpat_x_assum `val_in_memory tv v _ actual.vs_memory` mp_tac >>
     qpat_x_assum `type_memory_size tv = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [LET_DEF, pairTheory.UNCURRY_DEF,
       MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0, ADD_ASSOC]) >>
  conj_tac >- suspend "effects" >>
  conj_tac >-
    (rpt strip_tac >>
     `not_fresh_at end_st x` by (fs[not_fresh_at_def] >> decide_tac) >> metis_tac[]) >>
  conj_tac >-
    (qpat_assum `abi_decode_sim ctx func initial prepared` mp_tac >>
     qpat_assum `abi_decode_sim ctx func prepared after_head` mp_tac >>
     qpat_assum `abi_decode_sim ctx func after_head actual` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[abi_decode_sim_trans]) >>
  suspend "support_and_ghost"
QED

Resume prefix_members_complete_code_cons[support_and_ghost]:
  conj_tac >-
    (qpat_assum `Bh SUBSET _` mp_tac >> qpat_assum `Bt SUBSET _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[SUBSET_DEF, IN_UNION, range_bytes_def, MAP_APPEND, MAP, SUM_APPEND, SUM] >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  conj_tac >-
    (qpat_assum `DISJOINT Bh qh.t_mem` mp_tac >>
     qpat_assum `qtail.t_mem SUBSET qh.t_mem` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> SET_TAC[]) >>
  conj_tac >- suspend "support" >>
  conj_tac >-
    (qpat_assum `qtail.t_mem SUBSET qh.t_mem` mp_tac >>
     qpat_assum `qh.t_mem SUBSET qt.t_mem` mp_tac >>
     qpat_assum `qt.t_mem = tn.t_mem` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> SET_TAC[]) >>
  rpt strip_tac >>
  `not_fresh_at end_st x` by (fs[not_fresh_at_def] >> decide_tac) >> metis_tac[]
QED

Resume prefix_members_complete_code_cons[effects]:
  `frag_ids middle end_st SUBSET frag_ids st final /\
   frag_ids end_st final SUBSET frag_ids st final` by
    (qpat_x_assum `st.cs_next_id < middle.cs_next_id` mp_tac >>
     qpat_x_assum `middle.cs_next_id <= end_st.cs_next_id` mp_tac >>
     qpat_x_assum `end_st.cs_next_id <= final.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[frag_ids_def, SUBSET_DEF, IN_COUNT, IN_DIFF] >> decide_tac) >>
  qmatch_goalsub_abbrev_tac `abi_encoder_registered_effect allsites out initial actual` >>
  `abi_encoder_registered_effect allsites out initial prepared` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{}`, `[]`] >> asm_simp_tac (srw_ss()) []) >>
  `abi_encoder_registered_effect allsites out prepared after_head` by
    (simp_tac bool_ss [Abbr `allsites`, Abbr `out`] >>
     irule ctor_actual_child_narrow_effect >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_encoder_registered_effect allsites out after_head actual` by
    (simp_tac bool_ss [Abbr `allsites`, Abbr `out`] >>
     irule ctor_actual_child_narrow_effect >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
     asm_simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0] >> decide_tac) >>
  qpat_assum `abi_encoder_registered_effect allsites out initial prepared` mp_tac >>
  qpat_assum `abi_encoder_registered_effect allsites out prepared after_head` mp_tac >>
  qpat_assum `abi_encoder_registered_effect allsites out after_head actual` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[abi_encoder_registered_effect_trans]
QED

Resume prefix_members_complete_code_cons[support]:
  qpat_assum `!mem. _ ==> val_in_memory tv v _ mem` mp_tac >>
  qpat_assum `!mem. _ ==> tuple_in_memory vs' tvs _ mem` mp_tac >>
  qpat_assum `!a. a IN Bh ==> mem_bytes_at a 1 actual.vs_memory = _` mp_tac >>
  qpat_assum `type_memory_size tv = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  `val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) mem` by
    (first_x_assum irule >> rpt strip_tac >> metis_tac[IN_UNION]) >>
  `tuple_in_memory vs' tvs (d + SUM (MAP (type_memory_bytes ce) (pretys ++ [ty]))) mem` by
    (first_x_assum irule >> metis_tac[IN_UNION]) >>
  qpat_assum `val_in_memory tv v _ mem` mp_tac >>
  qpat_assum `tuple_in_memory vs' tvs _ mem` mp_tac >>
  qpat_assum `type_memory_size tv = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac (srw_ss()) [val_in_memory_def, LET_DEF, pairTheory.UNCURRY_DEF,
     MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0, ADD_ASSOC]
QED

Finalise prefix_members_complete_code_cons

Theorem prefix_members_complete_code:
  !tys tvs. LIST_REL (^CshiftCode) tys tvs ==> (^MshiftCode) tys tvs
Proof
  Induct_on `tys` >> rpt gen_tac >> Cases_on `tvs` >>
  simp_tac bool_ss [LIST_REL_def, prefix_members_complete_code_nil] >> strip_tac >>
  rename1 `LIST_REL _ tys rest` >>
  mp_tac (Q.INST [`ty` |-> `h`, `tv` |-> `h'`, `tvs` |-> `rest`]
    prefix_members_complete_code_cons) >>
  (impl_tac >- (conj_tac >- (BETA_TAC >> first_assum ACCEPT_TAC) >>
    first_x_assum irule >> first_assum ACCEPT_TAC)) >>
  simp_tac bool_ss []
QED
