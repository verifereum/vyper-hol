(* Counted interpretation of the shared operational member certificate. *)
Theory bodyIntCallEncoderCountedSpine
Ancestors
  bodyIntCallEncoderCountedPhases bodyIntCallDecoderCountedPrimitive
  abiEncoder abiEncoderMemberSpine abiEncoderMemberPhaseRaw abiEncoderChildContext abiEncoderChildCode
  abiEncoderAddressReach abiDecoderContract abiDecoderLoop entrySinkExtraction
  fragGasPath fragExec compileEnv emitHelperProps venomState venomInst
  venomExecSemantics emitHelper instIdxIndep words list rich_list arithmetic

Theorem intcall_encoder_raw_phase_control:
  final.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final) /\
  abi_encoder_member_phase_raw st final initial ready /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb ==>
  ~ready.vs_halted /\ ready.vs_current_bb = final.cs_current_bb /\
  ready.vs_inst_idx = LENGTH final.cs_current_insts
Proof
  strip_tac >> gvs[abi_encoder_member_phase_raw_def] >>
  drule_all run_inst_seq_preserves_entry_control >> simp[]
QED

Theorem intcall_encoder_binary_raw_path:
  emit_op opc ops st = (out,final) /\ (opc = ADD \/ opc = MUL) /\
  fn_has_code st final func /\ abi_encoder_member_phase_raw st final initial ready /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?n. gas_path ctx func initial n (OK ready)) /\
  ~ready.vs_halted /\ ready.vs_current_bb = final.cs_current_bb /\
  ready.vs_inst_idx = LENGTH final.cs_current_insts
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)` by
    (drule emitted_insts_emit_op >> strip_tac >> gvs[mk_inst_def, is_terminator_def]) >>
  conj_tac >- (irule intcall_encoder_phase_raw_path >> simp[] >>
    goal_assum (drule_at Any) >> simp[]) >>
  drule_all intcall_encoder_raw_phase_control >> simp[]
QED

Theorem intcall_encoder_prefix_raw_path:
  abi_encode_child_prefix dst ho dp st = (ops,final) /\
  fn_has_code st final func /\ abi_encoder_member_phase_raw st final initial ready /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?n. gas_path ctx func initial n (OK ready)) /\
  ~ready.vs_halted /\ ready.vs_current_bb = final.cs_current_bb /\
  ready.vs_inst_idx = LENGTH final.cs_current_insts
Proof
  strip_tac >> drule abi_encode_child_prefix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)` by fs[EVERY_CONJ] >>
  `isPREFIX st.cs_current_insts final.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  conj_tac >- (drule_all intcall_encoder_phase_raw_path >> simp[]) >>
  drule_all intcall_encoder_raw_phase_control >> simp[]
QED

Theorem intcall_encoder_suffix_raw_path:
  abi_encode_child_suffix head dp off len st = (out,final) /\
  fn_has_code st final func /\ abi_encoder_member_phase_raw st final initial ready /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?n. gas_path ctx func initial n (OK ready)) /\
  ~ready.vs_halted /\ ready.vs_current_bb = final.cs_current_bb /\
  ready.vs_inst_idx = LENGTH final.cs_current_insts
Proof
  strip_tac >> drule abi_encode_child_suffix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)` by fs[EVERY_CONJ] >>
  `isPREFIX st.cs_current_insts final.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  conj_tac >- (drule_all intcall_encoder_phase_raw_path >> simp[]) >>
  drule_all intcall_encoder_raw_phase_control >> simp[]
QED

Theorem intcall_encoder_spine_static_path:
  (!ei dst src st en out s t. core_run (ei,dst,src,st,en,out) s t ==>
    (?n. gas_path ctx func s n (OK t)) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts) /\
  abi_encoder_spine_child core_run (ei,F,dst,src,ho,dp,st,en,out) s t /\
  fn_has_code st en func /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?n. gas_path ctx func s n (OK t)) /\
  ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
  t.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  strip_tac >> drule abi_encoder_spine_child_compile >> strip_tac >>
  drule_all abi_encoder_static_child_structural_context >> strip_tac >>
  gvs[abi_encoder_spine_child_def, abi_encoder_spine_call_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] intcall_encoder_binary_raw_path)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  first_x_assum (drule_then strip_assume_tac) >>
  simp[] >> metis_tac[gas_path_then]
QED

Theorem intcall_encoder_spine_dynamic_path:
  (!ei dst src st en out s t. core_run (ei,dst,src,st,en,out) s t ==>
    (?n. gas_path ctx func s n (OK t)) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts) /\
  abi_encoder_spine_child core_run (ei,T,dst,src,ho,dp,st,en,out) s t /\
  fn_has_code st en func /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?n. gas_path ctx func s n (OK t)) /\
  ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
  t.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  strip_tac >> drule abi_encoder_spine_child_compile >> strip_tac >>
  drule_all abi_encoder_dynamic_child_context >> strip_tac >>
  gvs[abi_encoder_spine_child_def, abi_encoder_spine_call_def] >>
  drule_all intcall_encoder_prefix_raw_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  first_x_assum (drule_then strip_assume_tac) >>
  drule_all intcall_encoder_suffix_raw_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  simp[] >> metis_tac[gas_path_then]
QED

Theorem intcall_encoder_spine_child_path:
  (!ei dst src st en out s t. core_run (ei,dst,src,st,en,out) s t ==>
    (?n. gas_path ctx func s n (OK t)) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts) /\
  abi_encoder_spine_child core_run (ei,dyn,dst,src,ho,dp,st,en,out) s t /\
  fn_has_code st en func /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?n. gas_path ctx func s n (OK t)) /\
  ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
  t.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  Cases_on `dyn` >> strip_tac
  >- (drule_all intcall_encoder_spine_dynamic_path >> simp[]) >>
  drule_all intcall_encoder_spine_static_path >> simp[]
QED

Theorem intcall_encoder_member_spine_path:
  (!ei dst src st en out s t. core_run (ei,dst,src,st,en,out) s t ==>
    (?n. gas_path ctx func s n (OK t)) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts) ==>
  !infos st so ho out en s t.
    abi_encoder_spine_code func limit_st last (dst,src,dp) infos (st,so,ho) (out,en) /\
    abi_encoder_member_spine core_run (dst,src,dp) infos (st,so,ho) (out,en) s t /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    (?n. gas_path ctx func s n (OK t)) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  strip_tac >> Induct
  >- (simp[abi_encoder_member_spine_def, abi_encoder_spine_code_def,
      Once compile_abi_encode_child_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[gas_path_rules]) >>
  qx_gen_tac `entry` >> PairCases_on `entry` >> rpt gen_tac >> strip_tac >>
  drule abi_encoder_spine_cons_layout >> strip_tac >>
  gvs[abi_encoder_member_spine_def] >>
  drule abi_encoder_spine_child_compile >> strip_tac >>
  qpat_assum `abi_encoder_spine_cons_layout _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_spine_cons_layout_def]) >>
  gvs[] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] intcall_encoder_binary_raw_path)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all intcall_encoder_spine_child_path >> strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  simp[] >> metis_tac[gas_path_then]
QED

(* The recursive runner exposes execution and the compiler endpoint together. *)
Definition intcall_encoder_core_path_def:
  intcall_encoder_core_path ctx func (ei:abi_enc_info,dst:operand,src:operand,st:compile_state,en:compile_state,out:operand) s t <=>
    (?n. gas_path ctx func s n (OK t)) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts
End

Theorem intcall_encoder_core_path_endpoint:
  intcall_encoder_core_path ctx func (ei,dst,src,st,en,out) s t ==>
  (?n. gas_path ctx func s n (OK t)) /\
  ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
  t.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  simp[intcall_encoder_core_path_def]
QED

Theorem intcall_encoder_counted_member_spine:
  abi_encoder_spine_code func limit_st last (dst,src,dp) infos (st,so,ho) (out,en) /\
  abi_encoder_member_spine (intcall_encoder_core_path ctx func)
    (dst,src,dp) infos (st,so,ho) (out,en) s t /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?n. gas_path ctx func s n (OK t)) /\
  ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
  t.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  strip_tac >>
  mp_tac (Q.INST [`core_run` |-> `intcall_encoder_core_path ctx func`]
    intcall_encoder_member_spine_path) >>
  impl_tac >- simp[intcall_encoder_core_path_def] >>
  disch_then drule_all >> simp[]
QED
