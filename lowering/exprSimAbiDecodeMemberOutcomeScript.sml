(* Concrete dynamic primitive member execution, without source-validity premises. *)
Theory exprSimAbiDecodeMemberOutcome
Ancestors
  exprSimAbiDecodeCompositePrefix abiDecoderMemberSetup abiDecoderMemberBound
  abiDecoderBytesBound abiDecoderRange abiDecoderReservation abiDecoderDynamicLoopSetup
  abiDecoderPrimitiveFetched abiDecoderSiteEffect abiDecoderFiniteControl
  abiDecoderBytestringOutcome abiDecoderWordOutcome abiDecoderBytesPhases fragExec
  exprSimAbiDecodeChildBounds abiDecoderClampedWord
  abiDecoderSequenceReach abiDecoderContract abiEncoder compileEnv emitHelper emitHelperProps
  exprLoweringProps venomState venomExecSemantics venomInst instIdxIndep
  words list rich_list arithmetic

Theorem abi_decode_member_setup_sequence:
  abi_decode_member_setup dst src MLOAD base_op hi T ao vo st = (ops,middle) /\
  eval_operand src s = SOME(n2w p) /\ eval_operand dst s = SOME(n2w d) /\
  eval_operand base_op s = SOME(n2w B) /\
  abi_decode_load MLOAD (n2w(B+(p+ao)):bytes32) s = n2w delta /\
  p+delta < dimword(:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st middle) s = OK t /\
    eval_operand (FST ops) t = SOME(n2w(p+delta)) /\
    eval_operand (SND ops) t = SOME(n2w(d+vo)) /\
    fresh_vars_wrt middle t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st middle
Proof
  simp[abi_decode_member_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src T ao MLOAD base_op hi st = (child_src,c1)` >>
  rename1 `emit_op ADD [dst; Lit(n2w vo)] c1 = (child_dst,middle)` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  mp_tac (Q.INST [`off` |-> `ao`, `sb` |-> `p`, `src_base` |-> `B`,
    `payload_off` |-> `delta`, `opc` |-> `MLOAD`, `member_op` |-> `child_src`,
    `st'` |-> `c1`] abi_decode_dynamic_member_pointer) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand dst s1 = SOME(n2w d)` by metis_tac[] >>
  `eval_operand (Lit(n2w vo)) s1 = SOME(n2w vo)` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 middle) s1 = OK t` >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> gvs[word_add_n2w] >> metis_tac[]
QED

Theorem abi_decode_member_mload_setup_shape:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,middle) ==>
  middle.cs_blocks = st.cs_blocks /\ middle.cs_current_bb = st.cs_current_bb /\
  inst_extends st middle /\
  EVERY (\i. abi_bytes_opcode i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st middle)
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_member_setup_def, compile_getelemptr_abi_def, compile_abi_dec_addr_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def,
    inst_extends_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, is_terminator_def, is_alloca_op_def, mk_inst_def,
    abi_bytes_opcode_def, abi_word_opcode_def]
QED

Theorem abi_decode_member_setup_sequence_effect:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,middle) /\
  run_inst_seq (emitted_insts st middle) s = OK t /\
  t.vs_memory = s.vs_memory /\ decode_site_resources ctx fn s /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) ==>
  decode_site_effect ctx fn next writes s t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_halted = s.vs_halted
Proof
  strip_tac >> drule abi_decode_member_mload_setup_shape >> strip_tac >>
  `EVERY (\i. abi_bytes_opcode i.inst_opcode) (emitted_insts st middle)`
    by fs[EVERY_MEM] >>
  drule_all abi_bytes_sequence_static >> strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_fmp = s.vs_fmp /\ t.vs_halted = s.vs_halted /\ decode_static_frame s t` by
    fs[decode_static_frame_def, venom_state_component_equality] >>
  `decode_site_resources ctx fn t` by metis_tac[decode_site_resources_fields] >>
  simp[decode_site_effect_def, decode_memory_frame_def]
QED

Theorem abi_decode_member_setup_fetched_success:
  abi_decode_member_setup dst src MLOAD base_op hi T ao vo st = (ops,middle) /\
  eval_operand src s = SOME(n2w p) /\ eval_operand dst s = SOME(n2w d) /\
  eval_operand base_op s = SOME(n2w B) /\
  abi_decode_load MLOAD (n2w(B+(p+ao)):bytes32) s = n2w delta /\
  p+delta < dimword(:256) /\ fresh_vars_wrt st s /\
  decode_site_resources ctx fn s /\ fn_has_code st middle func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. decoder_straight_prefix func s t /\
    t.vs_current_bb = middle.cs_current_bb /\ t.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST ops) t = SOME(n2w(p+delta)) /\
    eval_operand (SND ops) t = SOME(n2w(d+vo)) /\ fresh_vars_wrt middle t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ decode_site_effect ctx fn next writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\ ~t.vs_halted
Proof
  strip_tac >> drule_all abi_decode_member_setup_sequence >> strip_tac >>
  drule_all abi_decode_member_setup_sequence_effect >>
  disch_then (qspecl_then [`writes`,`next`] strip_assume_tac) >>
  drule abi_decode_member_mload_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st middle)` by fs[EVERY_MEM] >>
  drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
  qexists_tac `t'` >> gvs[fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem member_straight_prefix_run_from[local]:
  decoder_straight_prefix func s t ==>
  run_from fuel ctx func s = run_from fuel ctx func t
Proof
  simp[decoder_straight_prefix_def] >>
  map_every qid_spec_tac [`t`,`s`] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT_RIGHT1 >>
  simp[] >> metis_tac[decoder_straight_step_run_from]
QED

Theorem abi_decode_member_setup_revert:
  abi_decode_member_setup dst src MLOAD base_op hi T ao vo st = (ops,middle) /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w p) /\ eval_operand base_op s = SOME(n2w B) /\
  eval_operand hi s = SOME(n2w H) /\ p+ao+32 <= H /\ B+H < dimword(:256) /\
  delta = w2n(abi_decode_load MLOAD (n2w(B+p+ao):bytes32) s) /\
  dimword(:256) <= p+delta /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st middle) s = Abort Revert_abort t
Proof
  simp_tac bool_ss [abi_decode_member_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `p < dimword(:256)` by decide_tac >>
  qmatch_asmsub_abbrev_tac `dimword(:256) <= p+offset` >>
  `offset < dimword(:256)` by simp[Abbr `offset`, w2n_lt] >>
  `abi_decode_load MLOAD (n2w(B+(p+ao)):bytes32) s = n2w offset` by
    (`p+ao = ao+p` by decide_tac >>
     asm_simp_tac bool_ss [Abbr `offset`, n2w_w2n]) >>
  drule_all abi_decode_dynamic_member_pointer_revert >> strip_tac >>
  drule abi_decode_member_pointer_prefix_shape >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  `!u. run_inst_seq (emitted_insts st cs') s <> OK u` by simp[] >>
  drule_all run_inst_seq_emit_extend_err >> simp[]
QED

Theorem abi_decode_bytes_member_fetched_outcome:
  abi_decode_member_setup dst src MLOAD base_op hi T ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) MLOAD base_op hi (DecBytestring n)
    middle = ((),end_st) /\
  (bt = BytesT (Dynamic n) \/ bt = StringT n) /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w p) /\ eval_operand dst s = SOME(n2w d) /\
  eval_operand base_op s = SOME(n2w B) /\ eval_operand hi s = SOME(n2w H) /\
  p+ao+32 <= H /\ B+H < dimword(:256) /\
  d+vo+abi_decode_bytes_copy_size n < dimword(:256) /\
  (B+H <= d+vo \/ d+vo+abi_decode_bytes_copy_size n <= B) /\
  {a | d+vo <= a /\ a < d+vo+abi_decode_bytes_copy_size n} SUBSET writes /\
  delta = w2n(abi_decode_load MLOAD (n2w(B+p+ao):bytes32) s) /\
  bs = mem_bytes_at (B+(p+delta)) (H-(p+delta)) s.vs_memory /\
  fresh_vars_wrt st s /\ decode_site_resources ctx fn s /\
  fn_has_code st end_st func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (p+delta < dimword(:256) /\ ?t v. decoder_straight_prefix func s t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    vyper_decode_valid_enc (vyper_to_abi_type env (BaseT bt)) bs /\
    abi_to_vyper env (BaseT bt) (dec (vyper_to_abi_type env (BaseT bt)) bs) = SOME v /\
    val_in_memory (BaseTV bt) v (d+vo) t.vs_memory /\ fresh_vars_wrt end_st t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    decode_site_effect ctx fn st.cs_next_var writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) \/
  (?t. run_from 0 ctx func s = Abort Revert_abort t /\
    (dimword(:256) <= p+delta \/
     ~(vyper_decode_valid_enc (vyper_to_abi_type env (BaseT bt)) bs /\
       ?v. abi_to_vyper env (BaseT bt) (dec (vyper_to_abi_type env (BaseT bt)) bs) = SOME v)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decode_member_mload_setup_shape >> strip_tac >>
  drule_all abi_decode_bytes_position_shape >> strip_tac >>
  `cs_extends st middle /\ cs_extends middle end_st` by
    fs[inst_extends_def, cs_extends_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  Cases_on `p+delta < dimword(:256)`
  >- suspend "child" >>
  `dimword(:256) <= p+delta` by decide_tac >>
  drule_all abi_decode_member_setup_revert >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st middle)` by fs[EVERY_MEM] >>
  drule_all abi_decoder_run_sequence_abort >> strip_tac >>
  disj2_tac >> metis_tac[]
QED

Resume abi_decode_bytes_member_fetched_outcome[child]:
  `abi_decode_load MLOAD (n2w(B+(p+ao)):bytes32) s = n2w delta` by
    asm_simp_tac bool_ss [ADD_ASSOC, n2w_w2n] >>
  drule_all abi_decode_member_setup_fetched_success >>
  disch_then (qspecl_then [`writes`,`st.cs_next_var`] strip_assume_tac) >>
  `eval_operand base_op t = SOME(n2w B) /\ eval_operand hi t = SOME(n2w H)`
    by metis_tac[] >>
  `bs = mem_bytes_at (B+(p+delta)) (H-(p+delta)) t.vs_memory` by metis_tac[] >>
  qpat_x_assum `EVERY _ (emitted_insts st middle)` kall_tac >>
  qpat_x_assum `EVERY _ (emitted_insts middle end_st)` kall_tac >>
  `decode_site_resources ctx fn t` by metis_tac[decode_site_effect_resources] >>
  `w2n(abi_decode_load MLOAD (n2w(B+(p+delta)):bytes32) t) =
   w2n(abi_decode_load MLOAD (n2w(B+(p+delta)):bytes32) t)` by rewrite_tac[] >>
  drule_all abi_decoder_bytestring_fetched_outcome >>
  ntac 35 (pop_last_assum kall_tac) >>
  qpat_x_assum `abi_decode_load _ _ _ = _` kall_tac >>
  disch_then (qspecl_then [`st.cs_next_var`,`env`] strip_assume_tac)
  >- (qpat_x_assum `mem_bytes_at _ _ t'.vs_memory = mem_bytes_at _ _ _` kall_tac >>
      qpat_x_assum `mem_bytes_at _ _ t'.vs_memory = REPLICATE _ _` kall_tac >>
      `decoder_straight_prefix func s t'` by metis_tac[decoder_straight_prefix_trans] >>
      `decode_site_effect ctx fn st.cs_next_var writes s t'` by
        metis_tac[decode_site_effect_trans, pred_setTheory.UNION_IDEMPOT] >>
      disj1_tac >> simp[] >> qexists_tac `t'` >> simp[] >> metis_tac[]) >>
  `run_from 0 ctx func s = run_from 0 ctx func t` by
    metis_tac[member_straight_prefix_run_from] >>
  disj2_tac >> metis_tac[]
QED

Finalise abi_decode_bytes_member_fetched_outcome

Theorem abi_decode_static_member_setup_sequence:
  abi_decode_member_setup dst src MLOAD base_op hi F ao vo st = (ops,middle) /\
  eval_operand src s = SOME(n2w p) /\ eval_operand dst s = SOME(n2w d) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st middle) s = OK t /\
    eval_operand (FST ops) t = SOME(n2w(p+ao)) /\
    eval_operand (SND ops) t = SOME(n2w(d+vo)) /\ fresh_vars_wrt middle t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory
Proof
  simp[abi_decode_member_setup_def, compile_getelemptr_abi_def,
    comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [src; Lit(n2w ao)] st = (child_src,c1)` >>
  rename1 `emit_op ADD [dst; Lit(n2w vo)] c1 = (child_dst,middle)` >>
  `eval_operand (Lit(n2w ao)) s = SOME(n2w ao)` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  qpat_x_assum `emit_op ADD [src; Lit(n2w ao)] st = _` kall_tac >>
  `eval_operand dst s1 = SOME(n2w d)` by metis_tac[] >>
  `eval_operand (Lit(n2w vo)) s1 = SOME(n2w vo)` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 middle) s1 = OK t` >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> gvs[word_add_n2w] >> metis_tac[]
QED

Theorem abi_decode_static_member_setup_fetched_success:
  abi_decode_member_setup dst src MLOAD base_op hi F ao vo st = (ops,middle) /\
  eval_operand src s = SOME(n2w p) /\ eval_operand dst s = SOME(n2w d) /\
  fresh_vars_wrt st s /\ decode_site_resources ctx fn s /\ fn_has_code st middle func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. decoder_straight_prefix func s t /\
    t.vs_current_bb = middle.cs_current_bb /\ t.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST ops) t = SOME(n2w(p+ao)) /\
    eval_operand (SND ops) t = SOME(n2w(d+vo)) /\ fresh_vars_wrt middle t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ decode_site_effect ctx fn next writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\ ~t.vs_halted
Proof
  strip_tac >> drule_all abi_decode_static_member_setup_sequence >> strip_tac >>
  drule_all abi_decode_member_setup_sequence_effect >>
  disch_then (qspecl_then [`writes`,`next`] strip_assume_tac) >>
  drule abi_decode_member_mload_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st middle)` by fs[EVERY_MEM] >>
  drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
  qexists_tac `t'` >> gvs[fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_decode_scalar_member_fetched_outcome:
  abi_decode_member_setup dst src MLOAD base_op hi F ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) MLOAD base_op hi (DecPrimWord clamp)
    middle = ((),end_st) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\ abi_decoder_clamp_wf clamp /\
  eval_operand src s = SOME(n2w p) /\ eval_operand dst s = SOME(n2w d) /\
  eval_operand base_op s = SOME(n2w B) /\ eval_operand hi s = SOME(n2w H) /\
  ao + abi_embedded_static_size ce.ce_struct_fields ty <= heads /\ p+heads <= H /\
  B+H < dimword(:256) /\ d+vo+32 < dimword(:256) /\
  {a | d+vo <= a /\ a < d+vo+32} SUBSET writes /\
  bs = mem_bytes_at (B+(p+ao)) 32 s.vs_memory /\
  fresh_vars_wrt st s /\ decode_site_resources ctx fn s /\
  fn_has_code st end_st func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?t v. decoder_straight_prefix func s t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
    abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v /\
    val_in_memory tv v (d+vo) t.vs_memory /\ fresh_vars_wrt end_st t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    decode_site_effect ctx fn st.cs_next_var writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) \/
  (?t. run_from 0 ctx func s = Abort Revert_abort t /\
     ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
       ?v. abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decode_scalar_child_readable >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decode_member_mload_setup_shape >> strip_tac >>
  drule_all abi_decoder_word_inst_extends >> strip_tac >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `cs_extends st middle /\ cs_extends middle end_st` by
    fs[inst_extends_def, cs_extends_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all abi_decode_static_member_setup_fetched_success >>
  disch_then (qspecl_then [`writes`,`st.cs_next_var`] strip_assume_tac) >>
  `eval_operand base_op t = SOME(n2w B) /\ eval_operand hi t = SOME(n2w H)` by metis_tac[] >>
  `decode_site_resources ctx fn t` by metis_tac[decode_site_effect_resources] >>
  `bs = mem_bytes_at (B+(p+ao)) 32 (abi_decode_source MLOAD t)` by
    gvs[abi_decode_source_def] >>
  `p+ao+32 <= H /\ d+vo+32 < dimword(:256)` by decide_tac >>
  drule_all abi_decoder_scalar_fetched_outcome >>
  qpat_x_assum `decoder_straight_prefix func s t` mp_tac >>
  qpat_x_assum `decode_site_effect _ _ _ _ s t` mp_tac >>
  qpat_x_assum `!op w. eval_operand op s = SOME w ==> _` mp_tac >>
  qpat_x_assum `t.vs_allocas = s.vs_allocas` mp_tac >>
  qpat_x_assum `t.vs_alloca_next = s.vs_alloca_next` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> ntac 5 strip_tac >>
  disch_then (qspec_then `st.cs_next_var` strip_assume_tac)
  >- (`decoder_straight_prefix func s t'` by metis_tac[decoder_straight_prefix_trans] >>
      `decode_site_effect ctx fn st.cs_next_var writes s t'` by
        metis_tac[decode_site_effect_trans, pred_setTheory.UNION_IDEMPOT] >>
      disj1_tac >> qexistsl_tac [`t'`,`v`] >> simp[] >> metis_tac[]) >>
  `run_from 0 ctx func s = run_from 0 ctx func t` by
    metis_tac[member_straight_prefix_run_from] >>
  disj2_tac >> metis_tac[]
QED
