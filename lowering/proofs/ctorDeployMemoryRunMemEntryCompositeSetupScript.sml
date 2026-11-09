Theory ctorDeployMemoryRunMemEntryCompositeSetup
Ancestors
  loweringStateRelDefs
  ctorDeployMemoryRunMemEntryCompositeEdges ctorAbiActualComplex
  ctorAbiActualLabelMember ctorAbiActualLabelEmpty ctorAbiActualMemberInputs
  abiDecoderComplexGuard abiDecoderComplexHead abiDecoderGuard
  fragExecMem instMemFrontier unitTransformDefs emitHelperProps
  venomInst venomExecSemantics venomState list rich_list arithmetic
  compileEnv exprLoweringProps abiDecoderContract abiEncoder context emitHelper memSafeRun fragExec
  abiDecoderReentry abiDecoderVarSequence ctorAbiActualObservations ctorAbiActualWorld
  abiEncoderRegisteredEffect instIdxIndep words ctorAbiActualNarrow abiDecoderDynamicLoopSetup
  entrySinkExtraction abiDecoderEmpty ctorDeployMemoryRunMemEntryWord
  abiDecoderMemberBody abiDecoderMembers abiDecodeRanges contractABI vyperABI abiDecoderMemberSetup
  abiDecoderMemberCode ctorAbiActualMemberSetup abiDecoderDynamic abiDecoderOffset

Theorem ctor_complex_guard_mem_ok:
  abi_decode_complex_head_guard src hi head_sz st = ((),st') ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  Cases_on `hi = Lit 0w` >>
  simp[abi_decode_complex_head_guard_def, abi_decode_le_guard_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  irule run_inst_seq_mem_ok_every >>
  simp[mk_inst_def, inst_dload_in_section_def] >> rpt conj_tac >>
  rpt gen_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem ctor_checked_emitted_endpoint:
  fn_has_code st st' func /\ inst_extends st st' /\
  st'.cs_current_bb = st.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts st st') /\
  run_inst_seq_mem_ok (emitted_insts st st') s /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb /\
  alloca_history func s ==>
  gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
  t.vs_gas_readings = s.vs_gas_readings /\
  alloca_history func (t with vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  strip_tac >>
  `?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def, inst_extends_def] >> metis_tac[]) >>
  `?code. st'.cs_current_insts = st.cs_current_insts ++ code /\
          emitted_insts st st' = code` by
    (fs[inst_extends_def, IS_PREFIX_APPEND] >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >> simp[IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  irule ctor_checked_sequence_endpoint >> simp[] >>
  qexists `code` >> gvs[]
QED

Theorem ctor_checked_complex_guard_labels:
  abi_decode_complex_head_guard src hi head_sz st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + head_sz <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ alloca_history func initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
    abi_encoder_registered_effect {} [] initial t /\ t.vs_labels = initial.vs_labels /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    gas_path_mem ctx func initial 0 (OK t) /\
    t.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_complex_guard_reentry >> strip_tac >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    fs[EVERY_CONJ] >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  `abi_encoder_registered_effect {} [] initial actual` by
    (irule ctor_actual_empty_effect >> gvs[abi_decoder_address_frame_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts st st')` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!e. MEM e _ ==> abi_decoder_reentry_opcode _` drule >>
     simp[abiDecoderVarSequenceTheory.abi_decoder_reentry_opcode_def] >>
     fs[EVERY_MEM] >> metis_tac[is_alloca_op_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st st') initial` by
    (irule ctor_complex_guard_mem_ok >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `actual.vs_allocas = initial.vs_allocas` by fs[abi_decoder_address_frame_def] >>
  drule_all ctor_checked_emitted_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists `actual with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[abi_decoder_address_frame_def, abi_encoder_registered_effect_def,
      fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem ctor_checked_empty_complex_labels_reach:
  compile_abi_decode_to_buf dst src opc (Lit 0w) hi (DecComplex dynamic []) st = ((),st') /\
  fn_has_code st st' func /\ eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  alloca_history func initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
    abi_encoder_registered_effect {} [] initial t /\ t.vs_labels = initial.vs_labels /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func initial t /\
    gas_path_mem ctx func initial 0 (OK t) /\
    t.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func t
Proof
  simp_tac bool_ss [abi_decode_empty_complex_phases] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_at (Pos hd) ctor_checked_complex_guard_labels >>
  simp[] >> disch_then drule_all >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all ctor_word_path_sim >> strip_tac >> metis_tac[]
QED

Theorem ctor_member_child_section:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) <= LENGTH initial.vs_data_section /\
  prepared.vs_data_section = initial.vs_data_section ==>
  sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
    (preavs ++ av::avs) (LENGTH pretys) + LENGTH (enc (vyper_to_abi_type env ty) av)
    <= LENGTH prepared.vs_data_section
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`opc` |-> `DLOAD`, `s` |-> `initial:venom_state`]
    abi_decoder_member_source) >>
  (impl_tac >- gvs[abi_decode_source_def, Excl "enc_def"]) >>
  strip_tac >> gvs[Excl "enc_def"] >> decide_tac
QED


Theorem ctor_arithmetic_tail_mem_ok:
  EVERY (\i. MEM i.inst_opcode [ADD; LT; ISZERO; ASSERT]) code ==>
  run_inst_seq_mem_ok code s
Proof
  strip_tac >> irule run_inst_seq_mem_ok_every >>
  fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
  simp[] >> strip_tac >> gvs[inst_dload_in_section_def] >>
  irule below_frontier_no_ranges >> simp[]
QED

Theorem ctor_add_dload_prefix_mem_ok:
  eval_operand src s = SOME (n2w sb) /\
  sb + ao < dimword (:256) /\ sb + ao + 32 <= LENGTH s.vs_data_section /\
  (!t. run_inst_seq_mem_ok tail t) ==>
  run_inst_seq_mem_ok
    (mk_inst id ADD [src; Lit (n2w ao)] [var] ::
     mk_inst id2 DLOAD [Var var] [valvar] :: tail) s
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [src; Lit (n2w ao)] [var]) s =
    OK (update_var var (n2w (sb + ao)) s)` by
    simp[Once step_inst_base_def, exec_pure2_def,
         mk_inst_def, eval_operand_def, word_add_n2w] >>
  rewrite_tac[Once run_inst_seq_mem_ok_cons] >>
  simp[mk_inst_def, inst_dload_in_section_def] >>
  conj_tac >- (irule below_frontier_no_ranges >> simp[]) >>
  Cases_on `tail` >- (
    simp[run_inst_seq_mem_ok_last, mk_inst_def, inst_dload_in_section_def,
         eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE, w2n_n2w, ADD_COMM] >>
    irule below_frontier_no_ranges >> simp[]) >>
  rewrite_tac[Once run_inst_seq_mem_ok_cons] >>
  simp[mk_inst_def, inst_dload_in_section_def, eval_operand_def,
       lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE, w2n_n2w, ADD_COMM] >>
  conj_tac >- (irule below_frontier_no_ranges >> simp[]) >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Theorem ctor_member_setup_mem_ok:
  abi_decode_member_setup dst src DLOAD hi dyn ao vo st = (ops,st') /\
  eval_operand src s = SOME (n2w sb) /\
  (dyn ==> sb + ao < dimword (:256) /\
           sb + ao + 32 <= LENGTH s.vs_data_section) ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >>
  simp[abi_decode_member_setup_def, compile_getelemptr_abi_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  FIRST [irule ctor_arithmetic_tail_mem_ok >> simp[mk_inst_def] >> NO_TAC,
         irule ctor_add_dload_prefix_mem_ok >> simp[] >>
         conj_tac >- (gen_tac >> irule ctor_arithmetic_tail_mem_ok >> simp[mk_inst_def]) >>
         qexists `sb` >> `sb < dimword (:256)` by decide_tac >> simp[]]
QED

Theorem ctor_checked_member_setup_labels_fragment:
  abi_decode_member_setup dst src DLOAD hi dyn ao vo st = (ops,st') /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  (dyn ==> abi_decode_load DLOAD (n2w (sb + ao) : bytes32) initial = n2w payload_off /\
    sb + payload_off < dimword (:256) /\ sb + ao < dimword (:256) /\
    sb + ao + 32 <= LENGTH initial.vs_data_section) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ alloca_history func initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. eval_operand (FST ops) t = SOME (n2w (sb + if dyn then payload_off else ao)) /\
    eval_operand (SND ops) t = SOME (n2w (d + vo)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
    abi_encoder_registered_effect {} [] initial t /\ t.vs_labels = initial.vs_labels /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    gas_path_mem ctx func initial 0 (OK t) /\
    t.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func t
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule ctor_actual_member_setup_opcodes >> strip_tac >>
  `dyn ==> abi_decode_load DLOAD (n2w (sb + ao) : bytes32) initial = n2w payload_off /\
    sb + payload_off < dimword (:256)` by metis_tac[] >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  `abi_encoder_registered_effect {} [] initial t` by
    (irule ctor_actual_empty_effect >> gvs[abi_decoder_address_frame_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts st st')` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!e. MEM e _ ==> abi_decoder_reentry_opcode _` drule >>
     simp[abiDecoderVarSequenceTheory.abi_decoder_reentry_opcode_def] >>
     fs[EVERY_MEM] >> metis_tac[is_alloca_op_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st st') initial` by
    (drule ctor_member_setup_mem_ok >> disch_then irule >>
     qexists `sb` >> simp[] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `t.vs_allocas = initial.vs_allocas` by fs[abi_decoder_address_frame_def] >>
  drule_all ctor_checked_emitted_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[abi_decoder_address_frame_def, abi_encoder_registered_effect_def,
      fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem ctor_checked_member_setup_labels_narrow:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) <= LENGTH initial.vs_data_section /\
  abi_decode_member_setup dst src DLOAD hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = (ops,middle) /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st middle func /\ alloca_history func initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. eval_operand (FST ops) t = SOME (n2w (sb +
        if type_to_abi_dec_info sf ce ty = DecComplex T [] then
          SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))
        else abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
          (preavs ++ av::avs) (LENGTH pretys))) /\
    eval_operand (SND ops) t = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
    abi_encoder_registered_effect {} [] initial t /\
    t.vs_memory = initial.vs_memory /\ t.vs_allocas = initial.vs_allocas /\
    t.vs_alloca_next = initial.vs_alloca_next /\ t.vs_labels = initial.vs_labels /\
    ~t.vs_halted /\ t.vs_current_bb = middle.cs_current_bb /\
    t.vs_inst_idx = LENGTH middle.cs_current_insts /\
    gas_path_mem ctx func initial 0 (OK t) /\
    t.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func t
Proof
  strip_tac >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- (gvs[dec_info_needs_offset_def, Excl "enc_def"] >>
      drule_all (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`, `payload_off` |-> `0:num`]
        ctor_checked_member_setup_labels_fragment)) >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      qexists `t` >> gvs[abi_decoder_address_frame_def, Excl "enc_def"]) >>
  mp_tac abi_decoder_members_child_facts >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  `LENGTH (MAP (vyper_to_abi_type env) pretys) = LENGTH preavs` by simp[] >>
  mp_tac (Q.INST [`pre` |-> `MAP (vyper_to_abi_type env) pretys`,
    `aty` |-> `vyper_to_abi_type env ty`, `post` |-> `MAP (vyper_to_abi_type env) tys`,
    `pvs` |-> `preavs`, `opc` |-> `DLOAD`, `s` |-> `initial:venom_state`] abi_decoder_canonical_member_inputs) >>
  (impl_tac >- gvs[MAP_APPEND, abi_decode_source_def, Excl "enc_def"]) >> strip_tac >>
  drule canonical_tuple_length >> disch_then assume_tac >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    is_dynamic (vyper_to_abi_type env ty)` by simp[abi_decoder_needs_offset_iff] >>
  `is_dynamic (vyper_to_abi_type env ty) ==>
    sb + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)) < dimword (:256) /\
    sb + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)) + 32 <=
      LENGTH initial.vs_data_section` by
    (strip_tac >> fs[MAP_APPEND, SUM_APPEND, abi_member_head_size_def, Excl "enc_def"] >> decide_tac) >>
  gvs[MAP_APPEND, Excl "enc_def"] >>
  drule ctor_checked_member_setup_labels_fragment >>
  disch_then (qspecl_then [`sb`,
    `SUM (MAP2 abi_member_tail_size (MAP (vyper_to_abi_type env) pretys) preavs) +
     head_lengths (MAP (vyper_to_abi_type env) pretys ++
       vyper_to_abi_type env ty::MAP (vyper_to_abi_type env) tys) 0`] mp_tac) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`d`, `ctx`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  strip_tac >> qexists `t` >> gvs[abi_decoder_address_frame_def, Excl "enc_def"]
QED
