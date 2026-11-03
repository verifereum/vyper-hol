Theory ctorAbiActualMemberSetup
Ancestors
  abiEncoderProps ctorAbiActualWorld abiDecoderMemberBody abiDecoderMemberCode
  abiDecoderDynamic abiDecoderOffset
  abiDecoderMemberSetup abiDecoderDynamicLoopSetup abiDecoderVarSequence
  abiDecoderReentry abiDecoderContract abiDecoderLoop abiEncoderRegisteredEffect
  abiEncoder fragExec instIdxIndep compileEnv emitHelper emitHelperProps
  exprLoweringProps venomExecSemantics venomState venomInst words list rich_list arithmetic

Theorem ctor_actual_member_setup_opcodes:
  abi_decode_member_setup dst src DLOAD hi dyn ao vo st = (ops,st') ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >>
  simp[abi_decode_member_setup_def, compile_getelemptr_abi_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  strip_tac >> gvs[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem ctor_actual_member_setup_fragment:
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
      abi_encoder_registered_effect (frag_ids st st') [] initial t) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule ctor_actual_member_setup_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  qexists `t` >>
  gvs[abi_decoder_address_frame_def, abi_encoder_registered_effect_def,
    eval_op_inst_idx, fresh_vars_wrt_def]
QED

Theorem ctor_actual_member_setup:
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
      abi_encoder_registered_effect (frag_ids st middle) [] initial t) (K F)
Proof
  strip_tac >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- (gvs[dec_info_needs_offset_def, Excl "enc_def"] >>
      drule_all (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`, `payload_off` |-> `0:num`]
        ctor_actual_member_setup_fragment)) >> simp[]) >>
  mp_tac abi_decoder_members_child_facts >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  `LENGTH (MAP (vyper_to_abi_type env) pretys) = LENGTH preavs` by simp[] >>
  mp_tac (Q.INST [`pre` |-> `MAP (vyper_to_abi_type env) pretys`,
    `aty` |-> `vyper_to_abi_type env ty`, `post` |-> `MAP (vyper_to_abi_type env) tys`,
    `pvs` |-> `preavs`, `opc` |-> `DLOAD`, `s` |-> `initial:venom_state`] abi_decoder_canonical_member_inputs) >>
  impl_tac >- gvs[MAP_APPEND, abi_decode_source_def, Excl "enc_def"] >> strip_tac >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    is_dynamic (vyper_to_abi_type env ty)` by simp[abi_decoder_needs_offset_iff] >>
  gvs[MAP_APPEND, Excl "enc_def"] >>
  irule ctor_actual_member_setup_fragment >> simp[] >>
  qexistsl [`dst`, `hi`, `src`] >> simp[]
QED
