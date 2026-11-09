(* Same-witness observations for heterogeneous member setup. *)
Theory ctorDeployLoweringEntryMember
Ancestors
  loweringStateRelDefs valueEncodingDefs
  ctorDeployLoweringEntryArrayFrame ctorDeployLoweringEntryRegistration
  ctorAbiActualLabelMember ctorAbiActualObservations ctorAbiActualWorld
  ctorAbiActualMemberSetup ctorAbiActualNarrowWord
  ctorAbiActualMemberInputs ctorAbiActualChildFrame ctorAbiActualEmpty
  abiDecoderMemberCons abiDecoderMemberBody ctorAbiActualMembers
  abiDecoderMemberInfos abiDecoderMembers abiDecoderAppend
  ctorDeployMemoryFrontier allocaFrontierBound allocaBudgetProps
  valueEncoding contractABI rich_list pred_set
  abiDecoderEmpty abiDecoderComplexGuard abiDecoderComplexHead abiDecoderGuard
  ctorAbiActualNarrow abiDecoderComplexExecute abiDecoderTupleInputs abiDecodeRanges
  abiDecoderStruct abiStaticDynarrayLayout vyperTyping finite_map valueEncodingTyping
  abiDecoderFixedInputs abiDecoderFixedMemory abiCanonicalHeadSize
  abiDecoderTypedContract vyperTypeABI vyperABI valueEncodingProps
  abiDecoderMemberBody abiDecoderMemberCode abiDecoderDynamic abiDecoderOffset
  abiDecoderMemberSetup abiDecoderDynamicLoopSetup abiDecoderVarSequence
  abiDecoderReentry abiDecoderContract abiDecoderLoop abiEncoderRegisteredEffect
  abiEncoderProps abiEncoder fragExec instIdxIndep compileEnv
  exprLoweringProps venomExecSemantics venomState venomInst words list arithmetic

Theorem deploy_ctor_member_setup_frame_fragment:
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
      t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule ctor_actual_member_setup_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  qexists `t` >>
  gvs[abi_decoder_address_frame_def, abi_encoder_registered_effect_def,
    eval_op_inst_idx, fresh_vars_wrt_def]
QED

Theorem deploy_ctor_member_setup_frame:
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
      t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code) (K F)
Proof
  strip_tac >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- (gvs[dec_info_needs_offset_def, Excl "enc_def"] >>
      drule_all (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`, `payload_off` |-> `0:num`]
        deploy_ctor_member_setup_frame_fragment)) >> simp[]) >>
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
  irule deploy_ctor_member_setup_frame_fragment >> simp[] >>
  qexistsl [`dst`, `hi`, `src`] >> simp[]
QED

Theorem deploy_ctor_member_setup_frame_narrow:
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
      t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code) (K F)
Proof
  strip_tac >> drule_all deploy_ctor_member_setup_frame >>
  disch_then (qspec_then `ctx` assume_tac) >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[Excl "enc_def"] >>
  rpt strip_tac >>
  `abi_encoder_registered_effect {} [] initial s` by
    (irule ctor_actual_address_empty_effect >> conj_tac >>
     goal_assum (drule_at Any)) >>
  gvs[abi_decoder_address_frame_def, Excl "enc_def"]
QED

Theorem deploy_ctor_complex_guard_frame_fragment:
  abi_decode_complex_head_guard src hi head_sz st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + head_sz <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
      abi_encoder_registered_effect {} [] initial t /\ t.vs_labels = initial.vs_labels /\
      t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code) (K F)
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
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  `abi_encoder_registered_effect {} [] initial actual` by
    (irule ctor_actual_empty_effect >> gvs[abi_decoder_address_frame_def]) >>
  qexists `actual` >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx,
      abi_encoder_registered_effect_def]
QED

Theorem deploy_ctor_empty_complex_frame_reach:
  compile_abi_decode_to_buf dst src opc (Lit 0w) hi (DecComplex dynamic []) st = ((),st') /\
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
    actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code
Proof
  simp_tac bool_ss [abi_decode_empty_complex_phases] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`head_sz` |-> `0:num`] deploy_ctor_complex_guard_frame_fragment) >>
  (impl_tac >- simp[]) >> disch_then assume_tac >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qexists `actual` >> gvs[abi_decoder_address_frame_def]
QED

(* Contracts are ML quotations only: k remains fixed across recursive calls. *)
val Ck = ``\ty tv.
 !dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\ k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code``;

val Mk = ``\tys tvs.
 !dst src hi st final ctx func site initial limit_st sb d D N ids
   pretys pretvs preavs prevs avs vs.
 compile_abi_decode_complex_elems dst src DLOAD (Lit 0w) hi (abi_decoder_member_infos sf ce tys)
   (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
   (SUM (MAP (type_memory_bytes ce) pretys)) st = ((),final) /\
 abi_decoder_members ce env sf pretys pretvs preavs prevs /\
 abi_decoder_members ce env sf tys tvs avs vs /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs))) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs)))) initial.vs_data_section =
   enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs)) /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
   sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ tys))) (ListV (preavs ++ avs))) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st final func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = final.cs_blocks \/ !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\ k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ tys)) <= D+N /\
 D+N <= initial.vs_alloca_next /\ frag_ids st final SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final))
   [(d + SUM (MAP (type_memory_bytes ce) pretys), SUM (MAP (type_memory_bytes ce) tys))] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code``;

Theorem deploy_ctor_members_run_nil:
  (^Mk) [] []
Proof
  BETA_TAC >> rpt gen_tac >>
  simp[abi_decoder_member_infos_def, Once compile_abi_decode_to_buf_def,
    comp_return_def, Excl "enc_def"] >> strip_tac >>
  drule abi_decoder_members_lengths >> strip_tac >> gvs[Excl "enc_def"] >>
  qexists `initial` >>
  simp[val_in_memory_def, abi_encoder_registered_effect_refl, abi_decode_sim_refl]
QED

(* Shared head postcondition, including observations of the actual witness. *)
val Hk = ``\ctx func site ids D N limit_st tv v d sz st st' initial actual.
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,sz)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 actual.vs_code = initial.vs_code``;

Theorem deploy_ctor_member_child_run:
  (^Ck) ty tv /\
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))) <= h /\ h < dimword (:256)) /\
  abi_decoder_address_frame st.cs_next_var initial prepared /\
  abi_decoder_operand_live st.cs_next_var hi /\ st.cs_next_var <= middle.cs_next_var /\
  eval_operand childsrc prepared = SOME (n2w (sb + abi_tuple_child_offset
    (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) (preavs ++ av::avs) (LENGTH pretys))) /\
  eval_operand childdst prepared = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var childdst /\
  D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys)) <= D+N /\
  compile_abi_decode_to_buf childdst childsrc DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st prepared /\
  fn_has_code middle end_st func /\ fn_inst_ids_distinct func /\
  (middle.cs_blocks = end_st.cs_blocks \/ !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv prepared /\ alloca_frontier_inv_from k ctx func site prepared /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D+N <= prepared.vs_alloca_next /\ frag_ids middle end_st SUBSET ids /\
  ctor_actual_scratch func ids D N prepared /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?actual. (^Hk) ctx func site ids D N limit_st tv v
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty)
    middle end_st prepared actual
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all ctor_actual_member_child_inputs >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  BETA_TAC >> asm "child" (drule o BETA_RULE) >>
  disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
  disch_then irule >> asm_simp_tac bool_ss [] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
    (preavs ++ av::avs) (LENGTH pretys)` >> asm_simp_tac bool_ss []
QED

Theorem deploy_ctor_member_child_run_elim:
  (^Ck) ty tv ==>
  !pretys pretvs preavs prevs.
  abi_decoder_members ce env sf pretys pretvs preavs prevs ==>
  !tys tvs av avs v vs.
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) ==>
  !st initial prepared.
  abi_decoder_address_frame st.cs_next_var initial prepared ==>
  !childdst childsrc hi middle end_st.
  compile_abi_decode_to_buf childdst childsrc DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) middle = ((),end_st) ==>
  !sb d D N ctx func site limit_st ids.
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))) <= h /\ h < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var hi /\ st.cs_next_var <= middle.cs_next_var /\
  eval_operand childsrc prepared = SOME (n2w (sb + abi_tuple_child_offset
    (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) (preavs ++ av::avs) (LENGTH pretys))) /\
  eval_operand childdst prepared = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var childdst /\
  D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys)) <= D+N /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st prepared /\
  fn_has_code middle end_st func /\ fn_inst_ids_distinct func /\
  (middle.cs_blocks = end_st.cs_blocks \/ !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv prepared /\ alloca_frontier_inv_from k ctx func site prepared /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D+N <= prepared.vs_alloca_next /\ frag_ids middle end_st SUBSET ids /\
  ctor_actual_scratch func ids D N prepared /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?actual. (^Hk) ctx func site ids D N limit_st tv v
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty)
    middle end_st prepared actual
Proof
  disch_tac >> rpt gen_tac >> disch_tac >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >> disch_tac >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all deploy_ctor_member_child_run >> simp[]
QED

(* Application with renamed live tails; later parameters stay quantified
   until the source membership and prepared-state premises have selected them. *)
Theorem deploy_ctor_member_child_run_application:
  (^Ck) ty tv /\
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs') (v::vs') /\
  abi_decoder_address_frame st.cs_next_var initial prepared /\
  compile_abi_decode_to_buf childdst childsrc DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs')))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs')) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs'))) < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs'))) <= h /\ h < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var hi /\ st.cs_next_var <= middle.cs_next_var /\
  eval_operand childsrc prepared = SOME (n2w (sb + abi_tuple_child_offset
    (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) (preavs ++ av::avs') (LENGTH pretys))) /\
  eval_operand childdst prepared = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var childdst /\
  D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys)) <= D+N /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st prepared /\
  fn_has_code middle end_st func /\ fn_inst_ids_distinct func /\
  (middle.cs_blocks = end_st.cs_blocks \/ !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv prepared /\ alloca_frontier_inv_from k ctx func site prepared /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D+N <= prepared.vs_alloca_next /\ frag_ids middle end_st SUBSET ids /\
  ctor_actual_scratch func ids D N prepared /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?actual. (^Hk) ctx func site ids D N limit_st tv v
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty)
    middle end_st prepared actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule deploy_ctor_member_child_run_elim >>
  qpat_assum `abi_decoder_members ce env sf pretys pretvs preavs prevs`
    (fn premise => disch_then (fn rule => mp_then Any mp_tac rule premise)) >>
  qpat_assum `abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs') (v::vs')`
    (fn premise => disch_then (fn rule => mp_then Any mp_tac rule premise)) >>
  qpat_assum `abi_decoder_address_frame st.cs_next_var initial prepared`
    (fn premise => disch_then (fn rule => mp_then Any mp_tac rule premise)) >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
  disch_then drule_all >> simp[]
QED

Theorem deploy_ctor_member_empty_run:
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] /\
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecComplex T []) st = ((),st') /\
  fn_has_code st st' func /\ eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb <= h /\ h < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. (^Hk) ctx func site ids D N limit_st tv v d (type_memory_bytes ce ty)
    st st' initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_empty_metadata_value >> strip_tac >>
  drule_all deploy_ctor_empty_complex_frame_reach >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `actual.vs_allocas = initial.vs_allocas /\
   actual.vs_alloca_next = initial.vs_alloca_next` by
    fs[abi_decoder_address_frame_def] >>
  drule_all deploy_ctor_array_allocation_state >> strip_tac >>
  qexists `actual` >> BETA_TAC >> asm_simp_tac bool_ss [] >>
  conj_tac
  >- (irule abi_encoder_registered_effect_enlarge >>
      qexistsl [`{}`, `[]`] >> simp[]) >>
  qpat_assum `abi_decoder_address_frame _ initial actual`
    (mp_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  first_x_assum (qspec_then `Var x` mp_tac) >>
  qpat_x_assum `lookup_var x initial = SOME w` mp_tac >>
  qpat_x_assum `not_fresh_at st x` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    not_fresh_at_def, eval_operand_def]
QED



Theorem deploy_ctor_member_tuple_join:
  val_in_memory tv v p s.vs_memory /\ val_wf tv v /\ type_memory_size tv = h /\
  tuple_in_memory vs tvs (p+h) t.vs_memory /\
  abi_encoder_registered_effect (ctor_actual_sites func child) [(p+h,n)] s t /\
  child SUBSET ids /\ ctor_actual_scratch func ids D N t /\
  D <= p /\ p+h <= D+N ==>
  tuple_in_memory (v::vs) (tv::tvs) p t.vs_memory
Proof
  strip_tac >>
  `val_in_memory tv v p t.vs_memory` by
    (irule ctor_actual_child_preserves_value >>
     conj_tac >- first_assum ACCEPT_TAC >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
     qexistsl [`D`, `N`, `ids`] >>
     asm_simp_tac bool_ss [] >>
     simp[venomMemDefsTheory.regions_disjoint_def, ADD_COMM]) >>
  asm_simp_tac (srw_ss()) [val_in_memory_def, LET_DEF, pairTheory.UNCURRY_DEF]
QED

Theorem deploy_ctor_member_effect_join:
  abi_encoder_registered_effect {} [] initial prepared /\
  abi_encoder_registered_effect (ctor_actual_sites func headids) [(p,h)] prepared head /\
  abi_encoder_registered_effect (ctor_actual_sites func tailids) [(p+h,n)] head actual /\
  headids SUBSET allids /\ tailids SUBSET allids ==>
  abi_encoder_registered_effect (ctor_actual_sites func allids) [(p,h+n)] initial actual
Proof
  strip_tac >>
  `abi_encoder_registered_effect (ctor_actual_sites func allids) [(p,h+n)] initial prepared` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{}`, `[]`] >> asm_simp_tac (srw_ss()) []) >>
  `abi_encoder_registered_effect (ctor_actual_sites func allids) [(p,h+n)] prepared head` by
    (irule ctor_actual_child_narrow_effect >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_encoder_registered_effect (ctor_actual_sites func allids) [(p,h+n)] head actual` by
    (irule ctor_actual_child_narrow_effect >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  metis_tac[abi_encoder_registered_effect_trans]
QED

(* The tail consumes the same head witness, retaining the shifted credit. *)
Theorem deploy_ctor_member_tail_run:
  (^Mk) tys tvs ==>
  !pretys pretvs preavs prevs ty tv av avs v vs.
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) ==>
  !st initial prepared middle end_st after_head ctx func site ids D N limit_st sb d.
  abi_decoder_address_frame st.cs_next_var initial prepared /\
  prepared.vs_labels = initial.vs_labels /\
  (^Hk) ctx func site ids D N limit_st tv v
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty)
    middle end_st prepared after_head /\
  st.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var <= end_st.cs_next_var ==>
  !dst src hi final.
  compile_abi_decode_complex_elems dst src DLOAD (Lit 0w) hi (abi_decoder_member_infos sf ce tys)
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (pretys ++ [ty]))))
    (SUM (MAP (type_memory_bytes ce) (pretys ++ [ty]))) end_st = ((),final) /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))) <= h /\ h < dimword (:256)) /\
  (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
  final.cs_next_var <= limit_st.cs_next_var /\
  fn_has_code end_st final func /\ fn_inst_ids_distinct func /\
  (end_st.cs_blocks = final.cs_blocks \/ !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys)) <= D+N /\
  frag_ids end_st final SUBSET ids ==>
  ?actual. tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) (pretys ++ [ty]))) actual.vs_memory /\
  abi_encoder_registered_effect (ctor_actual_sites func (frag_ids end_st final))
    [(d + SUM (MAP (type_memory_bytes ce) (pretys ++ [ty])), SUM (MAP (type_memory_bytes ce) tys))]
    after_head actual /\
  alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
  ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
  actual.vs_data_section = after_head.vs_data_section /\ actual.vs_call_ctx = after_head.vs_call_ctx /\
  (!x w. not_fresh_at end_st x /\ lookup_var x after_head = SOME w ==> lookup_var x actual = SOME w) /\
  ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
  actual.vs_inst_idx = LENGTH final.cs_current_insts /\
  abi_decode_sim ctx func after_head actual /\ fresh_vars_wrt limit_st actual /\
  actual.vs_labels = after_head.vs_labels /\ actual.vs_gas_readings = after_head.vs_gas_readings /\
  actual.vs_code = after_head.vs_code
Proof
  disch_then (mk_asm "tail") >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `(^Hk) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
  `abi_decoder_members ce env sf (pretys ++ [ty]) (pretvs ++ [tv])
    (preavs ++ [av]) (prevs ++ [v]) /\ abi_decoder_members ce env sf tys tvs avs vs` by
    (qpat_assum `abi_decoder_members _ _ _ (_::_) _ _ _`
      (mp_tac o PURE_REWRITE_RULE [abi_decoder_members_def]) >> strip_tac >>
     conj_tac >- (irule abi_decoder_members_join >> simp[abi_decoder_members_def]) >>
     first_assum ACCEPT_TAC) >>
  `!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
    lookup_var x after_head = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at middle x` by
       (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
     `lookup_var x prepared = SOME w` by
       (qpat_assum `abi_decoder_address_frame _ initial prepared`
         (mp_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
        disch_then (mp_tac o CONJUNCT1) >>
        disch_then (qspec_then `Var x` mp_tac) >>
        qpat_x_assum `lookup_var x initial = SOME w` mp_tac >>
        qpat_x_assum `not_fresh_at st x` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
          eval_operand_def, not_fresh_at_def]) >> metis_tac[]) >>
  `eval_operand src after_head = SOME (n2w sb) /\
   eval_operand dst after_head = SOME (n2w d) /\
   (!h. eval_operand hi initial = SOME (n2w h) ==> eval_operand hi after_head = SOME (n2w h))` by
    (rpt conj_tac >> rpt strip_tac >> irule ctor_actual_old_operand >>
     qexistsl [`initial`, `st`] >> simp[] >> metis_tac[]) >>
  `!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at end_st x` by
    (rpt strip_tac >> `not_fresh_at st x` by metis_tac[] >>
     fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `after_head.vs_data_section = initial.vs_data_section` by
    fs[abi_decoder_address_frame_def] >>
  asm "tail" (drule o BETA_RULE) >>
  disch_then (drule_at (Pat `ctor_actual_scratch _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv_from _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_members _ _ _ (_ ++ [_]) _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_members _ _ _ tys _ _ _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  (impl_tac >- (asm_x "tail" kall_tac >>
    asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND] >> metis_tac[])) >> simp[]
QED

Theorem deploy_ctor_members_run_cons:
  (^Ck) ty tv /\ (^Mk) tys tvs ==> (^Mk) (ty::tys) (tv::tvs)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (mk_asm "tail")) >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
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
   abi_decoder_operand_live st.cs_next_var dst /\
   abi_decoder_operand_live st.cs_next_var hi` by
    (qpat_x_assum `!x. src = Var x \/ dst = Var x \/ hi = Var x ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `src` >> Cases_on `dst` >> Cases_on `hi` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `fn_has_code st middle func` by
    (mp_tac (Q.SPECL [`st`, `middle`, `final`, `func`] fn_has_code_split) >> simp[]) >>
  drule_all deploy_ctor_member_setup_frame_narrow >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[Excl "enc_def"] >>
  strip_tac >> rename1 `abi_decode_sim ctx func initial prepared` >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` kall_tac >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  `fn_has_code middle end_st func` by
    (mp_tac (Q.SPECL [`middle`, `end_st`, `final`, `func`] fn_has_code_split) >> simp[]) >>
  `frag_ids middle end_st SUBSET ids` by
    (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
     gvs[frag_ids_def, SUBSET_DEF, IN_COUNT, IN_DIFF] >> decide_tac) >>
  `alloca_inv prepared /\ alloca_frontier_inv_from k ctx func site prepared /\
   ctor_actual_scratch func ids D N prepared /\ D+N <= prepared.vs_alloca_next` by
    (drule_all deploy_ctor_array_allocation_state >> strip_tac >> asm_simp_tac bool_ss []) >>
  `end_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `prepared.vs_current_bb = middle.cs_current_bb /\
   prepared.vs_inst_idx = LENGTH middle.cs_current_insts` by simp[] >>
  `?after_head. (^Hk) ctx func site ids D N limit_st tv v
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty)
    middle end_st prepared after_head` by
    (reverse (Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`)
     >- (qpat_assum `type_to_abi_dec_info sf ce ty <> DecComplex T []` (fn flag =>
           qpat_x_assum `eval_operand (FST ops) prepared = _`
             (assume_tac o PURE_REWRITE_RULE [flag, COND_CLAUSES])) >>
         asm "child" (mp_tac) >>
         disch_then (mp_tac o MATCH_MP deploy_ctor_member_child_run_elim) >>
         qpat_assum `abi_decoder_members ce env sf pretys pretvs preavs prevs`
           (fn premise => disch_then (fn rule => mp_then Any mp_tac rule premise)) >>
         qpat_assum `abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs') (v::vs')`
           (fn premise => disch_then (fn rule => mp_then Any mp_tac rule premise)) >>
         qpat_assum `abi_decoder_address_frame st.cs_next_var initial prepared`
           (fn premise => disch_then (fn rule => mp_then Any mp_tac rule premise)) >>
         disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
         BETA_TAC >> disch_then irule >>
         asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
         asm_simp_tac bool_ss [] >> qexists `sb` >>
         qpat_x_assum `mem_bytes_at _ _ _ = _`
           (assume_tac o PURE_REWRITE_RULE [MAP_APPEND, MAP, GSYM APPEND_ASSOC, APPEND]) >>
         qpat_x_assum `sb + LENGTH _ < dimword (:256)`
           (assume_tac o PURE_REWRITE_RULE [MAP_APPEND, MAP, GSYM APPEND_ASSOC, APPEND]) >>
         qpat_x_assum `hi = Lit 0w \/ _`
           (assume_tac o PURE_REWRITE_RULE [MAP_APPEND, MAP, GSYM APPEND_ASSOC, APPEND]) >>
         asm_simp_tac bool_ss [MAP_APPEND, MAP, GSYM APPEND_ASSOC, APPEND]) >>
     drule_all ctor_actual_member_inline_guard >> disch_then assume_tac >>
     `abi_decoder_operand_live middle.cs_next_var hi` by
       (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
     qpat_assum `type_to_abi_dec_info sf ce ty = DecComplex T []` (fn flag =>
       qpat_x_assum `compile_abi_decode_to_buf (SND ops) _ _ _ _ _ _ = _`
         (assume_tac o PURE_REWRITE_RULE [flag]) >>
       qpat_x_assum `eval_operand (FST ops) prepared = _`
         (assume_tac o PURE_REWRITE_RULE [flag, COND_CLAUSES])) >>
     `abi_decoder_coherent ce env sf ty tv /\
      abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v` by
       (qpat_assum `abi_decoder_members _ _ _ (_::_) _ _ _`
          (mp_tac o PURE_REWRITE_RULE [abi_decoder_members_def]) >>
        simp_tac bool_ss [] >> metis_tac[]) >>
     drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`) deploy_ctor_member_empty_run >>
     disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
     BETA_TAC >> disch_then irule >>
     asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
     asm_simp_tac bool_ss [] >>
     reverse conj_tac >- (qexists `sf` >> asm_simp_tac bool_ss []) >>
     qexists `sb + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))` >>
     asm_simp_tac bool_ss []) >>
  rename1 `(^Hk) ctx func site ids D N limit_st tv v _ _ middle end_st prepared after_head` >>
  `compile_abi_decode_complex_elems dst src DLOAD (Lit 0w) hi (abi_decoder_member_infos sf ce tys)
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (pretys ++ [ty]))))
    (SUM (MAP (type_memory_bytes ce) (pretys ++ [ty]))) end_st = ((),final)` by
    (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
     qpat_assum `abi_decoder_members _ _ _ (_::_) _ _ _`
       (mp_tac o PURE_REWRITE_RULE [abi_decoder_members_def]) >> strip_tac >>
     drule abiDecoderCoherenceTheory.abi_decoder_coherent_header >>
     simp_tac bool_ss [abiDecoderCoherenceTheory.abi_decoder_header_def] >> strip_tac >>
     qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ end_st = _` mp_tac >>
     qpat_x_assum `abi_embedded_static_size _ ty = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0]) >>
  `frag_ids end_st final SUBSET ids` by
    (qpat_x_assum `frag_ids st final SUBSET ids` mp_tac >>
     qpat_x_assum `st.cs_next_id < middle.cs_next_id` mp_tac >>
     qpat_x_assum `middle.cs_next_id <= end_st.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[frag_ids_def, SUBSET_DEF, IN_COUNT, IN_DIFF] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  drule_all abi_decoder_members_tail_phi >> disch_then assume_tac >>
  asm "tail" (mp_tac) >>
  disch_then (mp_tac o MATCH_MP deploy_ctor_member_tail_run) >>
  qpat_assum `abi_decoder_members ce env sf pretys pretvs preavs prevs`
    (fn premise => disch_then (fn rule => mp_then Any mp_tac rule premise)) >>
  qpat_assum `abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs') (v::vs')`
    (fn premise => disch_then (fn rule => mp_then Any mp_tac rule premise)) >>
  disch_then (drule_at (Pat `abi_decoder_address_frame _ initial prepared`)) >>
  disch_then (drule_at (Pat `(^Hk) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ end_st = _`)) >>
  disch_then (drule_at (Pat `eval_operand src initial = SOME (n2w sb)`)) >>
  (impl_tac >- (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
    asm_simp_tac bool_ss [] >> metis_tac[])) >>
  disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
  qpat_x_assum `(^Hk) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
  `type_memory_size tv = type_memory_bytes ce ty /\ val_wf tv v` by
    (qpat_assum `abi_decoder_members _ _ _ (_::_) _ _ _`
       (mp_tac o PURE_REWRITE_RULE [abi_decoder_members_def]) >> strip_tac >>
     qpat_x_assum `abi_decoder_metadata _ _ ty tv _ av v`
       (mp_tac o PURE_REWRITE_RULE [abiDecoderTypedContractTheory.abi_decoder_metadata_def]) >> strip_tac >>
     metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>
  `frag_ids middle end_st SUBSET frag_ids st final /\
   frag_ids end_st final SUBSET frag_ids st final` by
    (qpat_x_assum `st.cs_next_id < middle.cs_next_id` mp_tac >>
     qpat_x_assum `middle.cs_next_id <= end_st.cs_next_id` mp_tac >>
     qpat_x_assum `end_st.cs_next_id <= final.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[frag_ids_def, SUBSET_DEF, IN_COUNT, IN_DIFF] >> decide_tac) >>
  qpat_x_assum `tuple_in_memory vs' tvs _ actual.vs_memory`
    (assume_tac o PURE_REWRITE_RULE [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0, ADD_ASSOC]) >>
  qpat_x_assum `abi_encoder_registered_effect _ _ after_head actual`
    (assume_tac o PURE_REWRITE_RULE [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0, ADD_ASSOC]) >>
  qexists `actual` >> asm_simp_tac bool_ss [] >>
  conj_tac
  >- (drule_at (Pat `val_in_memory _ _ _ _`) deploy_ctor_member_tuple_join >>
      disch_then (drule_at (Pat `type_memory_size tv = _`)) >>
      disch_then (drule_at (Pat `abi_encoder_registered_effect _ _ after_head actual`)) >>
      disch_then irule >> asm_simp_tac bool_ss [] >> qexistsl [`D`, `N`, `ids`] >>
      asm_simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM, ADD_0, ADD_ASSOC] >>
      qpat_x_assum `d + SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys)) <= D+N` mp_tac >>
      qpat_x_assum `D <= d` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[MAP_APPEND, MAP, SUM_APPEND, SUM] >> decide_tac) >>
  conj_tac
  >- (`abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final))
        [(d + SUM (MAP (type_memory_bytes ce) pretys),
          type_memory_bytes ce ty + SUM (MAP (type_memory_bytes ce) tys))] initial actual` suffices_by
        simp_tac bool_ss [ADD_COMM] >>
      drule_at (Pat `abi_encoder_registered_effect {} [] _ _`) deploy_ctor_member_effect_join >>
      disch_then (drule_at (Pat `abi_encoder_registered_effect _ _ prepared after_head`)) >>
      disch_then (drule_at (Pat `abi_encoder_registered_effect _ _ after_head actual`)) >>
      disch_then irule >> asm_simp_tac bool_ss []) >>
  `prepared.vs_data_section = initial.vs_data_section /\
   prepared.vs_call_ctx = initial.vs_call_ctx` by
    (qpat_assum `abi_decoder_address_frame _ initial prepared`
       (mp_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
     simp_tac bool_ss [] >> metis_tac[]) >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at middle x /\ not_fresh_at end_st x` by
        (qpat_x_assum `not_fresh_at st x` mp_tac >>
         qpat_x_assum `st.cs_next_var <= middle.cs_next_var` mp_tac >>
         qpat_x_assum `middle.cs_next_var <= end_st.cs_next_var` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp[not_fresh_at_def] >> decide_tac) >>
      `lookup_var x prepared = SOME w` by
        (qpat_assum `abi_decoder_address_frame _ initial prepared`
           (mp_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
         disch_then (mp_tac o CONJUNCT1) >>
         disch_then (qspec_then `Var x` mp_tac) >>
         qpat_x_assum `lookup_var x initial = SOME w` mp_tac >>
         qpat_x_assum `not_fresh_at st x` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
           not_fresh_at_def, eval_operand_def]) >> metis_tac[]) >>
  metis_tac[abi_decode_sim_trans]
QED

Theorem deploy_ctor_members_run:
  !tys tvs. LIST_REL (^Ck) tys tvs ==> (^Mk) tys tvs
Proof
  Induct_on `tys` >> rpt gen_tac >> Cases_on `tvs` >>
  simp_tac bool_ss [LIST_REL_def, deploy_ctor_members_run_nil] >> strip_tac >>
  rename1 `LIST_REL _ tys rest` >>
  mp_tac (Q.INST [`ty` |-> `h`, `tv` |-> `h'`, `tvs` |-> `rest`]
    deploy_ctor_members_run_cons) >>
  (impl_tac >- (conj_tac >- (BETA_TAC >> first_assum ACCEPT_TAC) >>
     first_x_assum irule >> first_assum ACCEPT_TAC)) >>
  simp_tac bool_ss []
QED

Theorem deploy_ctor_complex_head_bound[local]:
  abi_decoder_members ce env sf tys tvs avs vs ==>
  FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys) <=
    LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs))
Proof
  strip_tac >> drule abi_decoder_members_relations >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  `has_types (MAP (vyper_to_abi_type env) tys) avs` by fs[has_types_LIST_REL] >>
  drule canonical_tuple_length >> strip_tac >>
  gvs[Excl "enc_def"] >> decide_tac
QED

Theorem deploy_ctor_complex_execute:
  LIST_REL (^Ck) tys tvs /\
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecComplex dyn (abi_decoder_member_infos sf ce tys)) st = ((),final) /\
  abi_decoder_members ce env sf tys tvs avs vs /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs))) initial.vs_data_section = enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\ sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) <= h /\ h < dimword (:256)) /\
  (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  (st.cs_blocks = final.cs_blocks \/ !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\ k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + SUM (MAP (type_memory_bytes ce) tys) <= D+N /\ D+N <= initial.vs_alloca_next /\
  frag_ids st final SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. tuple_in_memory vs tvs d actual.vs_memory /\
  abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final)) [(d,SUM (MAP (type_memory_bytes ce) tys))] initial actual /\
  alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
  ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
  actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
  (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
  ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
  abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\ actual.vs_labels = initial.vs_labels /\
  actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_complex_trace >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_complex_code >> strip_tac >>
  rename1 `abi_decode_complex_head_guard src hi _ st = ((),middle)` >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst /\
   abi_decoder_operand_live st.cs_next_var hi` by
    (qpat_x_assum `!x. _ ==> not_fresh_at st x` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `src` >> Cases_on `dst` >> Cases_on `hi` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def] >> metis_tac[]) >>
  drule deploy_ctor_complex_head_bound >> strip_tac >>
  mp_tac (Q.INST [`st'` |-> `middle`, `head_sz` |->
    `FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys)`]
    deploy_ctor_complex_guard_frame_fragment) >>
  (impl_tac >- (qpat_x_assum `LIST_REL _ _ _` kall_tac >>
    asm_simp_tac bool_ss [] >>
    Cases_on `hi = Lit 0w` >- simp[] >>
    qpat_x_assum `hi = Lit 0w \/ _` mp_tac >>
    asm_simp_tac bool_ss [] >> strip_tac >> qexists `h` >> asm_simp_tac bool_ss [] >> decide_tac)) >>
  disch_then assume_tac >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[Excl "enc_def"] >>
  strip_tac >> rename1 `abi_decode_sim ctx func initial prepared` >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` kall_tac >>
  qpat_assum `abi_decoder_address_frame _ initial prepared`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  drule_all deploy_ctor_array_allocation_state >> strip_tac >>
  `eval_operand src prepared = SOME (n2w sb) /\
   eval_operand dst prepared = SOME (n2w d)` by
    (qpat_x_assum `LIST_REL _ _ _` kall_tac >>
     conj_tac >> first_x_assum irule >> simp[]) >>
  `!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at middle x` by
    (qpat_x_assum `!x. src = Var x \/ dst = Var x \/ hi = Var x ==> _` mp_tac >>
     qpat_x_assum `st.cs_next_var <= middle.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `frag_ids middle final SUBSET ids` by
    (qpat_x_assum `LIST_REL _ _ _` kall_tac >>
     gvs[frag_ids_def, SUBSET_DEF, IN_COUNT, IN_DIFF] >> decide_tac) >>
  drule deploy_ctor_members_run >>
  disch_then (mp_tac o SIMP_RULE bool_ss [MAP, SUM, APPEND, ADD_CLAUSES] o
    Q.INST [`st` |-> `middle`, `initial` |-> `prepared:venom_state`,
      `pretys` |-> `[]`, `pretvs` |-> `[]`, `preavs` |-> `[]`, `prevs` |-> `[]`] o SPEC_ALL o BETA_RULE) >>
  (impl_tac >- (qpat_x_assum `LIST_REL _ _ _` kall_tac >>
    asm_simp_tac (srw_ss()) [Once abi_decoder_members_def, Excl "enc_def"] >>
    metis_tac[])) >>
  strip_tac >> rename1 `tuple_in_memory vs tvs d actual.vs_memory` >>
  qpat_x_assum `LIST_REL _ _ _` kall_tac >>
  `frag_ids middle final SUBSET frag_ids st final` by
    (qpat_x_assum `st.cs_next_id <= middle.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[frag_ids_def, SUBSET_DEF, IN_COUNT, IN_DIFF] >> decide_tac) >>
  `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final))
    [(d,SUM (MAP (type_memory_bytes ce) tys))] prepared actual` by
    (irule ctor_actual_child_narrow_effect >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >> simp[]) >>
  `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st final))
    [(d,SUM (MAP (type_memory_bytes ce) tys))] initial prepared` by
    (irule abi_encoder_registered_effect_enlarge >> qexistsl [`{}`, `[]`] >> simp[]) >>
  qexists `actual` >> asm_simp_tac bool_ss [] >>
  conj_tac >- metis_tac[abi_encoder_registered_effect_trans] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at middle x` by
        (qpat_x_assum `not_fresh_at st x` mp_tac >>
         qpat_x_assum `st.cs_next_var <= middle.cs_next_var` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
      `lookup_var x prepared = SOME w` by
        (qpat_x_assum `!op w. abi_decoder_operand_live _ _ /\ _ ==> _`
          (qspec_then `Var x` mp_tac) >>
         simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
           eval_operand_def, GSYM not_fresh_at_def]) >> metis_tac[]) >>
  irule abi_decode_sim_trans >> qexists `prepared` >> simp[]
QED

Theorem deploy_ctor_tuple:
  LIST_REL (^Ck) tys tvs ==> (^Ck) (TupleT tys) (TupleTV tvs)
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_to_vyper env (TupleT tys) av = SOME v` by
    fs[abi_decoder_metadata_def] >>
  drule abi_decoder_tuple_values >> strip_tac >>
  qpat_x_assum `av = ListV _` SUBST_ALL_TAC >>
  qpat_x_assum `v = ArrayV _` SUBST_ALL_TAC >>
  drule_all abi_decoder_tuple_members >> strip_tac >>
  `type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys)` by
    (simp[Once type_memory_bytes_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_tuple_infos]) >>
  `vyper_to_abi_type env (TupleT tys) = Tuple (MAP (vyper_to_abi_type env) tys)` by
    simp[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
  mp_tac (Q.INST [`final` |-> `st'`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields) tys`] deploy_ctor_complex_execute) >>
  (impl_tac >- (NO_STRIP_FULL_SIMP_TAC bool_ss [vyper_to_abi_types_MAP] >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists `actual` >> asm_simp_tac bool_ss [val_in_memory_tuple]
QED

val Ckdesc = ``(\env sf. ^Ck) (env \\ nsid) (sf \\ nsid_to_string nsid)``;

Theorem deploy_ctor_struct:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  LIST_REL (^Ckdesc) (MAP SND args) tvs ==>
  (^Ck) (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_to_vyper env (StructT nsid) av = SOME v` by fs[abi_decoder_metadata_def] >>
  drule abi_decoder_struct_values >> strip_tac >>
  qpat_x_assum `av = ListV _` SUBST_ALL_TAC >>
  qpat_x_assum `v = StructV _` SUBST_ALL_TAC >>
  drule_all abi_decoder_struct_members_at >> strip_tac >>
  drule abi_decoder_members_relations >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (irule type_memory_size_fields_zip >> simp[]) >>
  `type_memory_bytes ce (StructT nsid) = SUM (MAP (type_memory_bytes ce) (MAP SND args))` by
    fs[abi_decoder_metadata_def, Once type_memory_size_def, Excl "enc_def"] >>
  drule_all abi_decoder_struct_field_types >> strip_tac >>
  drule abi_decoder_struct_infos >> strip_tac >>
  `vyper_to_abi_type env (StructT nsid) =
    Tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))` by
    simp[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
  mp_tac (Q.INST [`final` |-> `st'`,
    `env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`,
    `tys` |-> `MAP SND (args:(string # vyperAST$type) list)`,
    `vs` |-> `MAP SND (fields:(string # value) list)`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields)
      (MAP SND (args:(string # vyperAST$type) list))`] deploy_ctor_complex_execute) >>
  (impl_tac >- (NO_STRIP_FULL_SIMP_TAC bool_ss [vyper_to_abi_types_MAP] >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `fields_in_memory fields (ZIP (MAP FST args,tvs)) d actual.vs_memory` by
    (irule static_fields_memory_zip >> fs[abi_decoder_metadata_def, Once value_has_type_def]) >>
  qexists `actual` >> asm_simp_tac bool_ss [val_in_memory_struct]
QED

Theorem deploy_ctor_fixed_array_run:
 (^Ck) ty tv ==> (^Ck) (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
 strip_tac >> simp_tac bool_ss [] >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule_all abi_decoder_fixed_array_values >> strip_tac >>
 gnvs[Once vyper_to_abi_type_def, canonical_array_tuple, Excl "enc_def"] >>
 qpat_assum `LENGTH vs = LENGTH avs`
   (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th]) >> assume_tac th) >>
 `type_memory_bytes ce (ArrayT ty (Fixed (LENGTH vs))) =
   LENGTH vs * type_memory_bytes ce ty` by simp[Once type_memory_bytes_def] >>
 qpat_assum `type_memory_bytes ce (ArrayT ty (Fixed (LENGTH vs))) = _`
   (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
 `LIST_REL (^Ck) (REPLICATE (LENGTH vs) ty) (REPLICATE (LENGTH vs) tv)` by
   (simp_tac bool_ss [LIST_REL_REPLICATE_same] >> BETA_TAC >>
    strip_tac >> first_assum ACCEPT_TAC) >>
 qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
   (assume_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
 drule_all (SIMP_RULE bool_ss [map_replicate, SUM_REPLICATE]
   (Q.INST [`tys` |-> `REPLICATE (LENGTH vs) ty`,
     `tvs` |-> `REPLICATE (LENGTH vs) tv`] (BETA_RULE deploy_ctor_complex_execute))) >>
 disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 qexists `actual` >>
 qpat_x_assum `LENGTH vs = LENGTH avs` (fn th => rewrite_tac[GSYM th]) >>
 asm_simp_tac bool_ss [Once type_memory_bytes_def] >>
 irule abi_decoder_fixed_array_memory >> asm_simp_tac bool_ss []
QED
