Theory ctorDeployLoweringEntryCompleteMemberBoundary
Ancestors
 ctorDeployLoweringEntryMember ctorDeployLoweringEntryCompleteScalar
 ctorDeployLoweringEntryArrayFrame ctorDeployLoweringEntryRegistration
 ctorAbiActualLabelMember ctorAbiActualObservations ctorAbiActualWorld
 ctorAbiActualMemberSetup ctorAbiActualNarrowWord
 ctorAbiActualMemberInputs ctorAbiActualChildFrame ctorAbiActualEmpty
 abiDecoderMemberCons abiDecoderMemberBody ctorAbiActualMembers
 abiDecoderMemberInfos abiDecoderMembers abiDecoderAppend
 valueEncoding contractABI rich_list pred_set
 abiDecoderEmpty abiDecoderComplexGuard abiDecoderComplexHead abiDecoderGuard
 ctorAbiActualNarrow abiDecoderComplexExecute abiDecoderTupleInputs abiDecodeRanges
 abiDecoderTypedContract vyperTypeABI vyperABI valueEncodingProps
 abiDecoderMemberCode abiDecoderDynamic abiDecoderOffset
 abiDecoderMemberSetup abiDecoderDynamicLoopSetup abiDecoderVarSequence
 abiDecoderReentry abiDecoderContract abiDecoderLoop abiEncoderRegisteredEffect
 abiEncoderProps abiEncoder fragExec instIdxIndep compileEnv
 emitHelperProps fragGasStraight fragGasPath
 exprLoweringProps venomExecSemantics venomState venomInst words list arithmetic

Theorem deploy_ctor_member_setup_complete_frame_fragment:
  abi_decode_member_setup dst src DLOAD hi dyn ao vo st = (ops,st') /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  (dyn ==> abi_decode_load DLOAD (n2w (sb + ao) : bytes32) initial = n2w payload_off /\
    sb + payload_off < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. eval_operand (FST ops) t = SOME (n2w (sb + if dyn then payload_off else ao)) /\
      eval_operand (SND ops) t = SOME (n2w (d + vo)) /\
      fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
      abi_encoder_registered_effect (frag_ids st st') [] initial t /\
      t.vs_labels = initial.vs_labels /\
      t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code /\
      t.vs_outcomes = initial.vs_outcomes /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
      t.vs_block_ctx = initial.vs_block_ctx) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule ctor_actual_member_setup_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  qexists `t` >>
  gvs[abi_decoder_address_frame_def, abi_encoder_registered_effect_def,
    eval_op_inst_idx, fresh_vars_wrt_def]
QED

Theorem deploy_ctor_complex_guard_complete_frame_fragment:
  abi_decode_complex_head_guard src hi head_sz st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + head_sz <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
      abi_encoder_registered_effect {} [] initial t /\ t.vs_labels = initial.vs_labels /\
      t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code /\
      t.vs_outcomes = initial.vs_outcomes /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
      t.vs_block_ctx = initial.vs_block_ctx) (K F)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_complex_guard_reentry >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  `abi_encoder_registered_effect {} [] initial actual` by
    (irule ctor_actual_empty_effect >> gvs[abi_decoder_address_frame_def]) >>
  qexists `actual` >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx,
      abi_encoder_registered_effect_def]
QED

Theorem deploy_ctor_empty_complex_complete_frame_reach:
  compile_abi_decode_to_buf dst src opc hi (DecComplex dynamic []) st = ((),st') /\
  fn_has_code st st' func /\ eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    abi_encoder_registered_effect {} [] initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\ actual.vs_labels = initial.vs_labels /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
    actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
    actual.vs_block_ctx = initial.vs_block_ctx
Proof
  simp_tac bool_ss [abi_decode_empty_complex_phases] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`head_sz` |-> `0:num`] deploy_ctor_complex_guard_complete_frame_fragment) >>
  (impl_tac >- simp[]) >> disch_then assume_tac >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qexists `actual` >> gvs[abi_decoder_address_frame_def]
QED

Theorem deploy_ctor_member_setup_complete_frame:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) /\
  abi_decode_member_setup dst src DLOAD hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = (ops,middle) /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st middle (\s. s = initial)
    (\t. eval_operand (FST ops) t = SOME (n2w (sb +
        if type_to_abi_dec_info sf ce ty = DecComplex T [] then
          SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))
        else abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
          (preavs ++ av::avs) (LENGTH pretys))) /\
      eval_operand (SND ops) t = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) /\
      fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
      abi_encoder_registered_effect (frag_ids st middle) [] initial t /\
      t.vs_labels = initial.vs_labels /\
      t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code /\
      t.vs_outcomes = initial.vs_outcomes /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
      t.vs_block_ctx = initial.vs_block_ctx) (K F)
Proof
  strip_tac >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- (gvs[dec_info_needs_offset_def, Excl "enc_def"] >>
      drule_all (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`, `payload_off` |-> `0:num`]
        deploy_ctor_member_setup_complete_frame_fragment)) >> simp[]) >>
  mp_tac abi_decoder_members_child_facts >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  `LENGTH (MAP (vyper_to_abi_type env) pretys) = LENGTH preavs` by simp[] >>
  fs[MAP_APPEND, Excl "enc_def"] >>
  drule (SIMP_RULE bool_ss [abi_decode_source_def]
    (Q.INST [`opc` |-> `DLOAD`] abi_decoder_canonical_member_inputs)) >>
  disch_then (qspecl_then [`sb`, `initial`] mp_tac) >>
  impl_tac >- gvs[Excl "enc_def"] >> strip_tac >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    is_dynamic (vyper_to_abi_type env ty)` by simp[abi_decoder_needs_offset_iff] >>
  gvs[MAP_APPEND, Excl "enc_def"] >>
  irule deploy_ctor_member_setup_complete_frame_fragment >> simp[] >>
  qexistsl [`dst`, `hi`, `src`] >> simp[]
QED

Theorem deploy_ctor_member_setup_complete_frame_narrow:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) /\
  abi_decode_member_setup dst src DLOAD hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = (ops,middle) /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st middle (\s. s = initial)
    (\t. eval_operand (FST ops) t = SOME (n2w (sb +
        if type_to_abi_dec_info sf ce ty = DecComplex T [] then
          SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))
        else abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
          (preavs ++ av::avs) (LENGTH pretys))) /\
      eval_operand (SND ops) t = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) /\
      fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
      abi_encoder_registered_effect {} [] initial t /\
      t.vs_memory = initial.vs_memory /\ t.vs_allocas = initial.vs_allocas /\
      t.vs_alloca_next = initial.vs_alloca_next /\ t.vs_labels = initial.vs_labels /\
      t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code /\
      t.vs_outcomes = initial.vs_outcomes /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
      t.vs_block_ctx = initial.vs_block_ctx) (K F)
Proof
  strip_tac >> drule_all deploy_ctor_member_setup_complete_frame >>
  disch_then (qspec_then `ctx` assume_tac) >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[Excl "enc_def"] >>
  rpt strip_tac >>
  `abi_encoder_registered_effect {} [] initial s` by
    (irule ctor_actual_address_empty_effect >> conj_tac >>
     goal_assum (drule_at Any)) >>
  gvs[abi_decoder_address_frame_def, Excl "enc_def"]
QED

Theorem deploy_ctor_member_setup_complete_gas_path:
  abi_decode_member_setup dst src DLOAD hi dyn ao vo st = (ops,st') /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  (dyn ==> abi_decode_load DLOAD (n2w (sb + ao) : bytes32) initial = n2w payload_off /\
    sb + payload_off < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. gas_path ctx func initial 0 (OK actual) /\
    eval_operand (FST ops) actual = SOME (n2w (sb + if dyn then payload_off else ao)) /\
    eval_operand (SND ops) actual = SOME (n2w (d + vo)) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_address_frame st.cs_next_var initial actual /\
    abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
    actual.vs_labels = initial.vs_labels /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
    actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
    actual.vs_block_ctx = initial.vs_block_ctx
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule ctor_actual_member_setup_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st') = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `EVERY (\i. abi_decoder_reentry_opcode _) _` mp_tac >>
     pure_rewrite_tac[EVERY_MEM] >> disch_then (qspec_then `i` mp_tac) >>
     simp[abi_decoder_reentry_opcode_def]) >>
  `st'.cs_current_bb = st.cs_current_bb /\
   st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'` by
    gvs[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND, DROP_APPEND] >>
  drule_all concat_straight_gas_path >> strip_tac >>
  `abi_decode_sim ctx func initial
    (t with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    metis_tac[gas_path_normal, abi_decode_sim_def] >>
  qexists `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[abi_decoder_address_frame_def, abi_encoder_registered_effect_def,
    eval_op_inst_idx, fresh_vars_wrt_def]
QED

Theorem deploy_ctor_complex_guard_complete_gas_path:
  abi_decode_complex_head_guard src hi head_sz st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + head_sz <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. gas_path ctx func initial 0 (OK actual) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_address_frame st.cs_next_var initial actual /\
    abi_encoder_registered_effect {} [] initial actual /\ actual.vs_labels = initial.vs_labels /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
    actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
    actual.vs_block_ctx = initial.vs_block_ctx
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_decoder_complex_guard_reentry >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  `abi_encoder_registered_effect {} [] initial actual` by
    (irule ctor_actual_empty_effect >> gvs[abi_decoder_address_frame_def]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st') = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `EVERY (\i. abi_decoder_reentry_opcode _) _` mp_tac >>
     pure_rewrite_tac[EVERY_MEM] >> disch_then (qspec_then `i` mp_tac) >>
     simp[abi_decoder_reentry_opcode_def]) >>
  `st'.cs_current_bb = st.cs_current_bb /\
   st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'` by
    gvs[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND, DROP_APPEND] >>
  drule_all concat_straight_gas_path >> strip_tac >>
  `abi_decode_sim ctx func initial
    (actual with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    metis_tac[gas_path_normal, abi_decode_sim_def] >>
  qexists `actual with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx,
      abi_encoder_registered_effect_def]
QED

Theorem deploy_ctor_empty_complex_complete_gas_path:
  compile_abi_decode_to_buf dst src opc hi (DecComplex dynamic []) st = ((),st') /\
  fn_has_code st st' func /\ eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. gas_path ctx func initial 0 (OK actual) /\ fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    abi_encoder_registered_effect {} [] initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\ actual.vs_labels = initial.vs_labels /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
    actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
    actual.vs_block_ctx = initial.vs_block_ctx
Proof
  simp_tac bool_ss [abi_decode_empty_complex_phases] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE bool_ss [ADD_0]
    (Q.INST [`head_sz` |-> `0:num`] deploy_ctor_complex_guard_complete_gas_path)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem deploy_ctor_member_setup_complete_frame_gas_path:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) /\
  abi_decode_member_setup dst src DLOAD hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = (ops,middle) /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st middle func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. gas_path ctx func initial 0 (OK t) /\
      eval_operand (FST ops) t = SOME (n2w (sb +
        if type_to_abi_dec_info sf ce ty = DecComplex T [] then
          SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))
        else abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
          (preavs ++ av::avs) (LENGTH pretys))) /\
      eval_operand (SND ops) t = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) /\
      fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
      abi_encoder_registered_effect (frag_ids st middle) [] initial t /\
      t.vs_labels = initial.vs_labels /\
      ~t.vs_halted /\ t.vs_current_bb = middle.cs_current_bb /\
      t.vs_inst_idx = LENGTH middle.cs_current_insts /\
      abi_decode_sim ctx func initial t /\
      t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code /\
      t.vs_outcomes = initial.vs_outcomes /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
      t.vs_block_ctx = initial.vs_block_ctx
Proof
  strip_tac >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- (gvs[dec_info_needs_offset_def, Excl "enc_def"] >>
      drule_all (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`, `payload_off` |-> `0:num`]
        deploy_ctor_member_setup_complete_gas_path)) >> simp[]) >>
  mp_tac abi_decoder_members_child_facts >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  `LENGTH (MAP (vyper_to_abi_type env) pretys) = LENGTH preavs` by simp[] >>
  fs[MAP_APPEND, Excl "enc_def"] >>
  drule (SIMP_RULE bool_ss [abi_decode_source_def]
    (Q.INST [`opc` |-> `DLOAD`] abi_decoder_canonical_member_inputs)) >>
  disch_then (qspecl_then [`sb`, `initial`] mp_tac) >>
  impl_tac >- gvs[Excl "enc_def"] >> strip_tac >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    is_dynamic (vyper_to_abi_type env ty)` by simp[abi_decoder_needs_offset_iff] >>
  gvs[MAP_APPEND, Excl "enc_def"] >>
  irule deploy_ctor_member_setup_complete_gas_path >> simp[] >>
  qexistsl [`dst`, `hi`, `src`] >> simp[]
QED
