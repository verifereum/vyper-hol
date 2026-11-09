(* Execution-producing member setup, with the ghost at the same cutpoint. *)
Theory ctorDeployMemoryRunPtrPrefixCompleteMemberSetup
Ancestors
  loweringStateRelDefs
  ctorDeployMemoryRunPtrPrefixMemberShift ctorDeployMemoryRunPtrPrefixMemberSetup
  abiDecoderMemberSetup abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderContract abiDecoderVarSequence ctorAbiActualAlloc ctorAbiActualObservations
  compileEnv exprLoweringProps venomState venomInst venomExecSemantics
  ptrDiscipline ptrSafeRun words list arithmetic
  abiDecoderMemberBody abiDecoderCoherence abiDecoderTypedContract abiEncoder abiDecoderDynamic
  abiDecoderOffset

Theorem prefix_member_setup_var_frame:
  abi_decode_member_setup (Var dst) src DLOAD (Lit 0w) (Lit 0w) dyn ao vo st = (ops,middle) /\
  run_inst_seq (emitted_insts st middle) s = OK t /\ not_fresh_at st v ==>
  lookup_var v t = lookup_var v s
Proof
  strip_tac >>
  drule prefix_member_setup_code >> simp[LET_THM] >> strip_tac >>
  irule ctor_actual_sequence_var_frame >> goal_assum (drule_at Any) >>
  Cases_on `dyn` >> gvs[mk_inst_def, is_terminator_def] >>
  qpat_x_assum `not_fresh_at st v` mp_tac >>
  simp[not_fresh_at_def] >> strip_tac >> rpt conj_tac >>
  spose_not_then assume_tac >> gvs[] >> first_x_assum (qspec_then `st.cs_next_var` mp_tac) >>
  simp[]
QED

Theorem prefix_member_setup_complete_shift:
  abi_decode_member_setup (Var dst) src DLOAD (Lit 0w) (Lit 0w) dyn ao vo st = (ops,middle) /\
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
    prepared.vs_block_ctx = s.vs_block_ctx /\ prepared.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  `abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    simp[abi_decoder_operand_live_def] >>
  `dyn ==> eval_operand (Lit 0w) s = SOME (n2w 0) /\
    abi_decode_load DLOAD (n2w (0 + (sb + ao)) : bytes32) s = n2w payload_off /\
    sb + payload_off < dimword (:256)` by
    (asm_rewrite_tac[eval_operand_def, ADD]) >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  drule_all prefix_member_setup_pair_shift >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
  simp[LET_THM] >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st middle)` by
    (drule prefix_member_setup_code >> simp[LET_THM] >> strip_tac >>
     Cases_on `dyn` >> gvs[abi_decoder_reentry_opcode_def, mk_inst_def]) >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  qexistsl [`H`,`qt`,`child_dst`] >> simp[LET_THM] >>
  `t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_data_section = s.vs_data_section /\ t.vs_halted = s.vs_halted` by
    gvs[abi_decoder_address_frame_def] >>
  simp[] >> rpt strip_tac >> simp[lookup_var_def] >>
  irule (SRULE [lookup_var_def] prefix_member_setup_var_frame) >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem prefix_canonical_member_setup_inputs:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) s.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) ==>
  ?payload_off.
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty) ==>
      abi_decode_load DLOAD
        (n2w (sb + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) : bytes32)
        s = n2w payload_off /\ sb+payload_off < dimword (:256)) /\
    (if dec_info_needs_offset (type_to_abi_dec_info sf ce ty) then payload_off
     else SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) =
    (if type_to_abi_dec_info sf ce ty = DecComplex T [] then
       SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))
     else abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
       (preavs ++ av::avs) (LENGTH pretys))
Proof
  strip_tac >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- (qexists `0` >> simp[dec_info_needs_offset_def]) >>
  mp_tac abi_decoder_members_child_facts >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  `LENGTH (MAP (vyper_to_abi_type env) pretys) = LENGTH preavs` by simp[] >>
  fs[MAP_APPEND, Excl "enc_def"] >>
  drule (SIMP_RULE bool_ss [abi_decode_source_def]
    (Q.INST [`opc` |-> `DLOAD`] abi_decoder_canonical_member_inputs)) >>
  disch_then (qspecl_then [`sb`, `s`] mp_tac) >>
  (impl_tac >- gvs[Excl "enc_def"]) >> strip_tac >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    is_dynamic (vyper_to_abi_type env ty)` by simp[abi_decoder_needs_offset_iff] >>
  gvs[MAP_APPEND, Excl "enc_def"] >>
  qexists `SUM (MAP2 abi_member_tail_size (MAP (vyper_to_abi_type env) pretys) preavs) +
    head_lengths (MAP (vyper_to_abi_type env) pretys ++
      vyper_to_abi_type env ty::MAP (vyper_to_abi_type env) tys) 0` >>
  simp[ADD_COMM]
QED

Theorem prefix_canonical_member_setup_complete_shift:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) s.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) /\
  abi_decode_member_setup (Var dst) src DLOAD (Lit 0w) (Lit 0w)
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
    prepared.vs_block_ctx = s.vs_block_ctx /\ prepared.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >>
  drule_all prefix_canonical_member_setup_inputs >> strip_tac >>
  drule_all prefix_member_setup_complete_shift >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
  asm_simp_tac bool_ss []
QED
