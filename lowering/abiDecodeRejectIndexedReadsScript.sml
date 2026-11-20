(* Execute the nonbulk array body's reads before testing an element offset. *)
Theory abiDecodeRejectIndexedReads
Ancestors
  abiDecoderDynamicLoopSetup abiDecoderStaticLoopSetup abiDecoderReentryAddress
  decoderNavigationPtr decoderMemberPrefixPtr abiDecodePtrMemberFrame
  abiEncoderPathProps instIdxIndep fragGasOriginPtrLoop emitHelperProps
  compileEnv emitHelper venomExecSemantics venomState venomInst words
  loweringStateRelDefs fragExec ptrDiscipline finite_map
  abiDecoderContract exprLoweringProps abiDecoderReentry fragGasOriginPtr
  externalEntryShape arithmetic pred_set abiEncoder abiMalformedNavigation
  exprSimAbiDecodeArrayRuntimeSetup appendStorageGhostPtr exprSimConvertFromBytes
  freshWrites abiDecoderArrayBound

Theorem indexed_pc_frame_trans[local]:
  m = (s with <|vs_vars := m.vs_vars; vs_inst_idx := i|>) /\
  t = (m with <|vs_vars := t.vs_vars; vs_inst_idx := j|>) ==>
  t = (s with <|vs_vars := t.vs_vars; vs_inst_idx := j|>)
Proof
  strip_tac >>
  qpat_x_assum `t = _` (fn th => CONV_TAC (LAND_CONV (REWR_CONV th))) >>
  qpat_x_assum `m = _` (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[venom_state_component_equality]
QED

Theorem reject_indexed_mload[local]:
  emit_op MLOAD [Var q] sa = (out,sb) /\
  lookup_var q s = SOME a /\ ptr_covers G tn q s 32 /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  w2n a + 32 <= s.vs_alloca_next /\
  sb.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  fn_has_code sa sb func /\ allocas_from lower s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u. t = (s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|>) /\
    eval_operand out t = SOME (mload (w2n a) s) /\
    op_taint u out = {} /\ op_prov H out = NONE /\
    fresh_vars_wrt ceiling t /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_immutables = s.vs_immutables /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_halted = s.vs_halted /\
    t.vs_labels = s.vs_labels /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lower t /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ FLOOKUP u.t_var v = FLOOKUP tn.t_var v /\
      op_taint u (Var v) = op_taint tn (Var v)) /\
    !D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
      (OK t,H,u)
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD /\ eval_operand (Var q) s = SOME a` by
    simp[abi_decode_source_opcode_def, eval_operand_def] >>
  drule_all abi_decoder_read_reentry >> strip_tac >>
  drule_all emit_mload_clean_endpoint_ptr_origin_core_exact_frame >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`,`ARB`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK raw` >>
  rename1 `op_prov H out = NONE` >>
  rename1 `op_taint u out = {}` >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH sb.cs_current_insts`,`H`,`u`] >>
  conj_tac >- fs[update_var_def] >>
  simp[eval_op_inst_idx, fresh_vars_wrt_inst_idx, lookup_var_def] >>
  rpt conj_tac
  >> fs[abi_decode_load_def, update_var_def, allocas_from_def, lookup_var_def]
  >> TRY (first_assum ACCEPT_TAC)
  >> rw[FLOOKUP_UPDATE]
  >> fs[not_fresh_at_def]
QED

Theorem reject_indexed_scalar[local]:
  emit_op opc [lhs;rhs] sa = (out,sb) /\ (opc = ADD \/ opc = MUL) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  op_taint tn lhs = {} /\ op_taint tn rhs = {} /\
  op_prov G lhs = NONE /\ op_prov G rhs = NONE /\
  sb.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  fn_has_code sa sb func /\ allocas_from lower s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u. t = (s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|>) /\
    eval_operand out t = SOME (if opc = ADD then a + b else a * b) /\
    op_taint u out = {} /\ op_prov H out = NONE /\
    fresh_vars_wrt ceiling t /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_immutables = s.vs_immutables /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_halted = s.vs_halted /\
    t.vs_labels = s.vs_labels /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lower t /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ FLOOKUP u.t_var v = FLOOKUP tn.t_var v /\
      op_taint u (Var v) = op_taint tn (Var v)) /\
    !D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
      (OK t,H,u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_binary_reentry >> strip_tac >>
  drule_all emit_scalar_binop_endpoint_ptr_origin_core_exact_frame >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`,`ARB`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK raw` >>
  rename1 `op_prov H out = NONE` >>
  rename1 `op_taint u out = {}` >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH sb.cs_current_insts`,`H`,`u`] >>
  conj_tac >- fs[update_var_def] >>
  simp[eval_op_inst_idx, fresh_vars_wrt_inst_idx, lookup_var_def] >>
  rpt conj_tac
  >> fs[update_var_def, allocas_from_def, lookup_var_def]
  >> TRY (first_assum ACCEPT_TAC)
  >> rw[FLOOKUP_UPDATE]
  >> fs[not_fresh_at_def]
QED

Theorem indexed_live_values_frame[local]:
  abi_decoder_operand_live sa.cs_next_var op /\ t.vs_labels = s.vs_labels /\
  (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
    FLOOKUP H v = FLOOKUP G v /\ FLOOKUP u.t_var v = FLOOKUP tn.t_var v /\
    op_taint u (Var v) = op_taint tn (Var v)) ==>
  eval_operand op t = eval_operand op s /\ op_prov H op = op_prov G op /\
  op_taint u op = op_taint tn op
Proof
  Cases_on `op` >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    not_fresh_at_def, eval_operand_def, op_prov_def] >>
  rw[op_taint_def]
QED

Theorem indexed_frame_trans[local]:
  !M m sm tm.
  sa.cs_next_var <= sm.cs_next_var /\
  (!v. not_fresh_at sa v ==> lookup_var v m = lookup_var v s /\
    FLOOKUP M v = FLOOKUP G v /\ FLOOKUP tm.t_var v = FLOOKUP tn.t_var v /\
    op_taint tm (Var v) = op_taint tn (Var v)) /\
  (!v. not_fresh_at sm v ==> lookup_var v t = lookup_var v m /\
    FLOOKUP H v = FLOOKUP M v /\ FLOOKUP u.t_var v = FLOOKUP tm.t_var v /\
    op_taint u (Var v) = op_taint tm (Var v)) ==>
  !v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
    FLOOKUP H v = FLOOKUP G v /\ FLOOKUP u.t_var v = FLOOKUP tn.t_var v /\
    op_taint u (Var v) = op_taint tn (Var v)
Proof
  rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem indexed_compile_four[local]:
  abi_decode_array_head_setup (Var ip) src stride sa = (ops,sb) /\
  fn_has_code sa sb func ==>
  ?c1 c2 c3 idx data off head.
    emit_op MLOAD [Var ip] sa = (idx,c1) /\
    emit_op ADD [src;Lit 32w] c1 = (data,c2) /\
    emit_op MUL [idx;Lit (n2w stride)] c2 = (off,c3) /\
    emit_op ADD [data;off] c3 = (head,sb) /\ ops = (idx,data,head) /\
    fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
    fn_has_code c2 c3 func /\ fn_has_code c3 sb func
Proof
  simp[abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
    comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op MLOAD [Var ip] sa = (idx,c1)` >>
  rename1 `emit_op ADD [src;Lit 32w] c1 = (data,c2)` >>
  rename1 `emit_op MUL [idx;Lit (n2w stride)] c2 = (off,c3)` >>
  rename1 `emit_op ADD [data;off] c3 = (head,sb)` >>
  imp_res_tac exprSimAccountsTheory.emit_op_extends_next_var >>
  `cs_extends c1 sb /\ cs_extends c2 sb` by metis_tac[cs_extends_trans] >>
  metis_tac[fn_has_code_split]
QED

Theorem indexed_read_coordinates_joint[local]:
  abi_decode_array_head_setup (Var ip) src stride sa = ((idx,data,head),sb) /\
  lookup_var ip s = SOME slot /\ ptr_covers G tn ip s 32 /\
  (!i. w2n slot <= i /\ i < w2n slot + 32 ==> i NOTIN tn.t_mem) /\
  w2n slot + 32 <= s.vs_alloca_next /\ mload (w2n slot) s = n2w j /\
  eval_operand src s = SOME (n2w p) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  sb.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  fn_has_code sa sb func /\ allocas_from lower s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u. t = (s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|>) /\
    eval_operand idx t = SOME (n2w j) /\
    eval_operand data t = SOME (n2w (p+32)) /\
    eval_operand head t = SOME (n2w (p+32+j*stride)) /\
    op_taint u idx = {} /\ op_prov H idx = NONE /\
    op_taint u data = {} /\ op_prov H data = NONE /\
    op_taint u head = {} /\ op_prov H head = NONE /\
    abi_decoder_operand_live sb.cs_next_var idx /\
    abi_decoder_operand_live sb.cs_next_var data /\
    abi_decoder_operand_live sb.cs_next_var head /\
    sa.cs_next_var <= sb.cs_next_var /\
    fresh_vars_wrt ceiling t /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_immutables = s.vs_immutables /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_halted = s.vs_halted /\
    t.vs_labels = s.vs_labels /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lower t /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ FLOOKUP u.t_var v = FLOOKUP tn.t_var v /\
      op_taint u (Var v) = op_taint tn (Var v)) /\
    !D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
      (OK t,H,u)
Proof
  strip_tac >> drule_all indexed_compile_four >> strip_tac >> gvs[] >>
  imp_res_tac exprSimAccountsTheory.emit_op_extends_next_var >>
  imp_res_tac abi_decoder_operand_live_emit >>
  `c1.cs_next_var <= ceiling.cs_next_var /\ c2.cs_next_var <= ceiling.cs_next_var /\
   c3.cs_next_var <= ceiling.cs_next_var` by decide_tac >>
  drule_all reject_indexed_mload >> disch_then (qspec_then `PG`
    (qx_choose_then `s1` (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac)))) >>
  `eval_operand src s1 = SOME (n2w p) /\ op_prov G1 src = NONE /\
   op_taint tn1 src = {}` by
    (drule_all indexed_live_values_frame >> simp[]) >>
  `eval_operand (Lit 32w) s1 = SOME 32w /\ op_taint tn1 (Lit 32w) = {} /\
   op_prov G1 (Lit 32w) = NONE` by simp[eval_operand_def,op_taint_def,op_prov_def] >>
  `~s1.vs_halted` by simp[] >>
  `allocas_below_fmp s1 = allocas_below_fmp s` by
    (qpat_assum `s1 = s with <|vs_vars := s1.vs_vars; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >>
     simp[NoAsms,allocas_below_fmp_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by metis_tac[] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `sa` |-> `c1`] reject_indexed_scalar)) >>
  disch_then (qspec_then `PG`
    (qx_choose_then `s2` (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac)))) >>
  `eval_operand idx s2 = SOME (n2w j) /\ op_prov G2 idx = NONE /\
   op_taint tn2 idx = {}` by
    (drule_all (Q.INST [`op` |-> `idx`, `sa` |-> `c1`] indexed_live_values_frame) >> simp[]) >>
  `eval_operand (Lit (n2w stride)) s2 = SOME (n2w stride) /\
   op_taint tn2 (Lit (n2w stride)) = {} /\ op_prov G2 (Lit (n2w stride)) = NONE`
    by simp[eval_operand_def,op_taint_def,op_prov_def] >>
  `allocas_below_fmp s2 = allocas_below_fmp s1` by
    (qpat_assum `s2 = s1 with <|vs_vars := s2.vs_vars; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >>
     simp[NoAsms,allocas_below_fmp_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s2` by metis_tac[] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `MUL`, `sa` |-> `c2`] reject_indexed_scalar)) >>
  disch_then (qspec_then `PG`
    (qx_choose_then `s3` (qx_choose_then `G3` (qx_choose_then `tn3` strip_assume_tac)))) >>
  `eval_operand data s3 = SOME (n2w p + 32w) /\ op_prov G3 data = NONE /\
   op_taint tn3 data = {}` by
    (`eval_operand data s3 = eval_operand data s2 /\
      op_prov G3 data = op_prov G2 data /\ op_taint tn3 data = op_taint tn2 data`
      by (irule indexed_live_values_frame >> simp[] >> qexists `c2` >> simp[]) >> simp[]) >>
  `~s3.vs_halted` by simp[] >>
  `allocas_below_fmp s3 = allocas_below_fmp s2` by
    (qpat_assum `s3 = s2 with <|vs_vars := s3.vs_vars; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >>
     simp[NoAsms,allocas_below_fmp_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s3` by metis_tac[] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `sa` |-> `c3`] reject_indexed_scalar)) >>
  disch_then (qspec_then `PG`
    (qx_choose_then `s4` (qx_choose_then `G4` (qx_choose_then `tn4` strip_assume_tac)))) >>
  `c1.cs_next_var <= c3.cs_next_var /\ c1.cs_next_var <= sb.cs_next_var /\
   c2.cs_next_var <= sb.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live sb.cs_next_var idx /\
   abi_decoder_operand_live sb.cs_next_var data` by metis_tac[abi_decoder_operand_live_mono] >>
  `!v. not_fresh_at c2 v ==> lookup_var v s4 = lookup_var v s2 /\
    FLOOKUP G4 v = FLOOKUP G2 v /\ FLOOKUP tn4.t_var v = FLOOKUP tn2.t_var v /\
    op_taint tn4 (Var v) = op_taint tn2 (Var v)` by
    (MATCH_MP_TAC indexed_frame_trans >>
     qexistsl_tac [`G3`,`s3`,`c3`,`tn3`] >> simp[]) >>
  `abi_decoder_operand_live c2.cs_next_var idx` by metis_tac[abi_decoder_operand_live_mono] >>
  `eval_operand idx s4 = eval_operand idx s2 /\ op_prov G4 idx = op_prov G2 idx /\
   op_taint tn4 idx = op_taint tn2 idx` by
    (irule indexed_live_values_frame >> simp[] >> qexists `c2` >> simp[]) >>
  `eval_operand data s4 = eval_operand data s2 /\ op_prov G4 data = op_prov G2 data /\
   op_taint tn4 data = op_taint tn2 data` by
    (irule indexed_live_values_frame >> simp[] >> qexists `c2` >> simp[]) >>
  qexistsl_tac [`s4`,`G4`,`tn4`] >>
  conj_tac
  >- (irule indexed_pc_frame_trans >> qexistsl [`LENGTH c3.cs_current_insts`,`s3`] >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      irule indexed_pc_frame_trans >> qexistsl [`LENGTH c2.cs_current_insts`,`s2`] >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      irule indexed_pc_frame_trans >> qexistsl [`LENGTH c1.cs_current_insts`,`s1`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[word_add_n2w,word_mul_n2w,AC ADD_ASSOC ADD_COMM] >>
  conj_tac
  >- (MATCH_MP_TAC indexed_frame_trans >> qexistsl_tac [`G2`,`s2`,`c2`,`tn2`] >>
      simp[] >> MATCH_MP_TAC indexed_frame_trans >>
      qexistsl_tac [`G1`,`s1`,`c1`,`tn1`] >> simp[]) >>
  rpt gen_tac >>
  irule gas_origin_ptr_path_trans >> qexistsl_tac [`G3`,`s3`,`tn3`] >> simp[] >>
  irule gas_origin_ptr_path_trans >> qexistsl_tac [`G2`,`s2`,`tn2`] >> simp[] >>
  irule gas_origin_ptr_path_trans >> qexistsl_tac [`G1`,`s1`,`tn1`] >> simp[]
QED

Theorem reject_indexed_pointer_add[local]:
  emit_op ADD [Var bp;pos] sa = (out,sb) /\
  abi_decode_ptr_window G tn s bp (n2w B) L /\
  eval_operand pos s = SOME (n2w h) /\ op_taint tn pos = {} /\
  op_prov G pos = NONE /\ h + 32 <= L /\ B + L < dimword(:256) /\
  sb.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  fn_has_code sa sb func /\ allocas_from lower s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q t H u. t = (s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|>) /\
    out = Var q /\ lookup_var q t = SOME (n2w (B+h)) /\
    ptr_covers H u q t 32 /\
    fresh_vars_wrt ceiling t /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_immutables = s.vs_immutables /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_halted = s.vs_halted /\
    t.vs_labels = s.vs_labels /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lower t /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ FLOOKUP u.t_var v = FLOOKUP tn.t_var v /\
      op_taint u (Var v) = op_taint tn (Var v)) /\
    !D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
      (OK t,H,u)
Proof
  strip_tac >> fs[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def] >>
  `eval_operand (Var bp) s = SOME (n2w B)` by simp[eval_operand_def] >>
  `B < dimword(:256) /\ B + h < dimword(:256)` by decide_tac >>
  `w2n (n2w B : bytes32) + h < dimword(:256)` by simp[w2n_n2w] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_decoder_binary_reentry)) >>
  strip_tac >> rename1 `run_inst_seq (emitted_insts sa sb) s = OK raw` >>
  drule_all (Q.SPECL [`32`] (Q.GEN `n` (SPEC_ALL emit_ptr_offset_endpoint_ptr_origin_core_exact_frame))) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`,`ARB`] strip_assume_tac) >>
  rename1 `out = Var q` >> rename1 `ptr_covers H u q _ 32` >>
  `raw = update_var (STRING #"%" (toString sa.cs_next_var)) (n2w B + n2w h) s` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  qexistsl_tac [`q`,`raw with vs_inst_idx := LENGTH sb.cs_current_insts`,`H`,`u`] >>
  conj_tac >- fs[update_var_def] >>
  simp[fresh_vars_wrt_inst_idx, lookup_var_def] >>
  rpt conj_tac
  >> fs[update_var_def, allocas_from_def, lookup_var_def, w2n_n2w, LESS_MOD,
        word_add_n2w, AC ADD_COMM ADD_ASSOC]
  >> TRY (first_assum ACCEPT_TAC)
  >> TRY (FIRST_PROVE [fs[bodyPtrDefsTheory.ptr_covers_def, lookup_var_def]])
  >> rpt strip_tac >> first_assum irule >> simp[]
QED

(* Stop at the loaded offset, before the potentially failing scalar tests. *)
Theorem indexed_offset_read_joint[local]:
  emit_op ADD [Var bp;head] sa = (addr,sm) /\
  emit_op MLOAD [addr] sm = (off,sb) /\
  abi_decode_ptr_window G tn s bp (n2w B) L /\
  eval_operand head s = SOME (n2w h) /\ op_taint tn head = {} /\
  op_prov G head = NONE /\ h + 32 <= L /\ B + L < dimword(:256) /\
  B + L <= s.vs_alloca_next /\ mem_bytes_at B L s.vs_memory = xs /\
  sb.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  allocas_from lower s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u. t = (s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|>) /\
    eval_operand off t = SOME (n2w (abi_head_word (DROP h xs))) /\
    op_taint u off = {} /\ op_prov H off = NONE /\
    abi_decoder_operand_live sb.cs_next_var off /\
    sa.cs_next_var <= sb.cs_next_var /\
    fresh_vars_wrt ceiling t /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_immutables = s.vs_immutables /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_halted = s.vs_halted /\
    t.vs_labels = s.vs_labels /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lower t /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ FLOOKUP u.t_var v = FLOOKUP tn.t_var v /\
      op_taint u (Var v) = op_taint tn (Var v)) /\
    !D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
      (OK t,H,u)
Proof
  strip_tac >> imp_res_tac exprSimAccountsTheory.emit_op_extends_next_var >>
  `sm.cs_next_var <= ceiling.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var`
    by decide_tac >>
  drule_all reject_indexed_pointer_add >>
  disch_then (qspec_then `PG` (qx_choose_then `q`
    (qx_choose_then `m` (qx_choose_then `M` (qx_choose_then `z` strip_assume_tac))))) >>
  `B < dimword(:256) /\ B+h < dimword(:256)` by decide_tac >>
  `!i. B+h <= i /\ i < B+h+32 ==> i NOTIN z.t_mem` by
    (fs[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def, w2n_n2w, LESS_MOD] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `w2n (n2w (B+h):bytes32) + 32 <= m.vs_alloca_next /\ ~m.vs_halted` by
    simp[w2n_n2w, LESS_MOD] >>
  qpat_x_assum `addr = Var q` SUBST_ALL_TAC >>
  `!i. w2n (n2w (B+h):bytes32) <= i /\ i < w2n (n2w (B+h):bytes32) + 32 ==>
      i NOTIN z.t_mem` by simp[w2n_n2w, LESS_MOD] >>
  `allocas_below_fmp m = allocas_below_fmp s` by
    (qpat_assum `m = s with <|vs_vars := m.vs_vars; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac[th]) >>
     simp[NoAsms,allocas_below_fmp_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp m` by metis_tac[] >>
  drule_all (Q.INST [`sa` |-> `sm`] reject_indexed_mload) >>
  disch_then (qspec_then `PG`
    (qx_choose_then `t` (qx_choose_then `H` (qx_choose_then `u` strip_assume_tac)))) >>
  `abi_decode_load MLOAD (n2w (B+h):bytes32) m =
      n2w (abi_head_word (DROP h xs))` by
    (irule (cj 1 abi_checked_offset_load) >> simp[abi_decode_source_def] >>
     qexists `L` >> simp[]) >>
  qexistsl_tac [`t`,`H`,`u`] >>
  conj_tac
  >- (irule indexed_pc_frame_trans >> qexistsl [`LENGTH sm.cs_current_insts`,`m`] >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  fs[abi_decode_load_def, w2n_n2w, LESS_MOD] >>
  conj_tac >- metis_tac[abi_decoder_operand_live_emit] >>
  conj_tac
  >- (MATCH_MP_TAC indexed_frame_trans >> qexistsl_tac [`M`,`m`,`sm`,`z`] >> simp[]) >>
  rpt gen_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`M`,`m`,`z`] >> simp[]
QED

Theorem indexed_compile_grows[local]:
  (abi_decode_array_head_setup (Var ip) src stride sa = (ops,sb) \/
   abi_decode_indexed_address dst idx memsz sa = (dstop,sb) \/
   abi_decode_array_pointer_guard child data hi stride sa = ((),sb)) ==>
  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  `dynamic_straight_fresh (abi_decode_array_head_setup (Var ip) src stride) /\
   dynamic_straight_fresh (abi_decode_indexed_address dst idx memsz) /\
   dynamic_straight_fresh (abi_decode_array_pointer_guard child data hi stride)` by
    (simp[abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
          abiDecoderIndexedAddressTheory.abi_decode_indexed_address_def,
          abi_decode_array_pointer_guard_def, abiDecoderGuardTheory.abi_decode_ge_guard_def,
          compile_abi_decode_range_check_def] >>
     rpt (FIRST [CHANGED_TAC BETA_TAC,
                 irule dynamic_straight_fresh_bind,
                 irule dynamic_straight_fresh_ignore_bind,
                 gen_tac, conj_tac]) >>
     simp[dynamic_straight_fresh_return, dynamic_straight_fresh_emit_op,
          dynamic_straight_fresh_emit_void, fresh_write_op_def]) >>
  strip_tac >> fs[dynamic_straight_fresh_def] >>
  first_x_assum drule >> simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem indexed_compile_offset[local]:
  compile_abi_decode_dyn_elem_ptr MLOAD (Var bp) head data hi stride mid = (child,nav) /\
  hi <> Lit 0w ==>
  ?addr sm off cut cmp.
    emit_op ADD [Var bp;head] mid = (addr,sm) /\
    emit_op MLOAD [addr] sm = (off,cut) /\
    emit_op ADD [data;off] cut = (child,cmp) /\
    abi_decode_array_pointer_guard child data hi stride cmp = ((),nav)
Proof
  strip_tac >> qhdtm_x_assum `compile_abi_decode_dyn_elem_ptr` mp_tac >>
  simp[abi_decode_bounded_array_pointer_phases, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  qhdtm_x_assum `compile_abi_decode_dyn_elem_ptr` mp_tac >>
  simp[compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[]
QED

Theorem indexed_element_setup_cut[local]:
  abi_decode_array_element_setup (Var ip) src dst MLOAD (Var bp) hi di stride memsz sa =
    ((idx,child,dstop),sb) /\ hi <> Lit 0w /\ fn_has_code sa sb func ==>
  ?data head mid cut.
    abi_decode_array_head_setup (Var ip) src stride sa = ((idx,data,head),mid) /\
    fn_has_code sa mid func /\ mid.cs_next_var <= cut.cs_next_var /\
    cut.cs_next_var <= sb.cs_next_var /\ fn_has_code cut sb func /\
    (if dec_info_needs_offset di then
       ?addr sm off cmp nav.
         emit_op ADD [Var bp;head] mid = (addr,sm) /\
         emit_op MLOAD [addr] sm = (off,cut) /\
         fn_has_code mid sm func /\ fn_has_code sm cut func /\
         emit_op ADD [data;off] cut = (child,cmp) /\
         abi_decode_array_pointer_guard child data hi stride cmp = ((),nav) /\
         fn_has_code cut nav func /\ fn_has_code nav sb func /\
         abi_decode_indexed_address dst idx memsz nav = (dstop,sb)
     else cut = mid /\ child = head /\
       abi_decode_indexed_address dst idx memsz cut = (dstop,sb))
Proof
  strip_tac >> Cases_on `dec_info_needs_offset di` >> simp[]
  >- (drule_all abi_decode_dynamic_element_setup_split >> simp[] >> strip_tac >>
      drule abi_decode_array_source_setup_split >> strip_tac >>
      PairCases_on `head_ops` >> simp[] >> gvs[] >>
      drule_all indexed_compile_offset >> strip_tac >>
      rename1 `abi_decode_array_head_setup _ _ _ sa = ((idx,data,head),mid)` >>
      rename1 `abi_decode_indexed_address dst idx memsz nav = (dstop,sb)` >>
      rename1 `emit_op ADD [Var bp;head] mid = (addr,sm)` >>
      rename1 `emit_op MLOAD [addr] sm = (off,cut)` >>
      rename1 `emit_op ADD [data;off] cut = (child,cmp)` >>
      `cs_extends sa mid /\ sa.cs_next_var <= mid.cs_next_var /\
       cs_extends cmp nav /\ cmp.cs_next_var <= nav.cs_next_var /\
       cs_extends nav sb /\ nav.cs_next_var <= sb.cs_next_var` by
        metis_tac[indexed_compile_grows] >>
      imp_res_tac exprSimAccountsTheory.emit_op_extends_next_var >>
      `cs_extends cut nav /\ cs_extends cut sb /\ cs_extends mid cut /\ cs_extends mid sb` by
        metis_tac[cs_extends_trans] >>
      map_every (fn sts =>
        qspecl_then (sts @ [`func`]) mp_tac fn_has_code_split >>
        (impl_tac >- simp[]) >> strip_tac)
        [[`sa`,`mid`,`sb`], [`mid`,`cut`,`sb`], [`mid`,`sm`,`cut`],
         [`cut`,`nav`,`sb`]] >>
      qexists `cut` >> simp[] >>
      rpt (conj_tac >- decide_tac) >> metis_tac[]) >>
  drule_all abi_array_static_element_setup_split >> simp[] >> strip_tac >>
  PairCases_on `head_ops` >> gvs[] >>
  rename1 `abi_decode_array_head_setup _ _ _ sa = ((idx,data,head),mid)` >>
  `cs_extends sa mid /\ cs_extends mid sb /\ mid.cs_next_var <= sb.cs_next_var`
    by metis_tac[indexed_compile_grows] >>
  drule_all fn_has_code_split >> strip_tac >>
  (simp[])
QED

(* Run the common read slice at the physical body entry. The offset arm
   stops immediately before adding the loaded delta to the data origin. *)
Theorem malformed_indexed_reads_joint_frame:
  abi_decode_array_element_setup (Var ip) src dst MLOAD (Var bp) hi di stride memsz sa =
    ((idx,child,dstop),sb) /\ hi <> Lit 0w /\ fn_has_code sa sb func /\
  j < n /\ p+32+n*stride <= L /\ (dec_info_needs_offset di ==> 32 <= stride) /\
  lookup_var ip s = SOME slot /\ ptr_covers G tn ip s 32 /\ not_fresh_at sa ip /\
  (!i. w2n slot <= i /\ i < w2n slot+32 ==> i NOTIN tn.t_mem) /\
  w2n slot+32 <= s.vs_alloca_next /\ mload (w2n slot) s = n2w j /\
  eval_operand src s = SOME (n2w p) /\ abi_decoder_operand_live sa.cs_next_var src /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  abi_decode_ptr_window G tn s bp (n2w B) L /\ not_fresh_at sa bp /\
  B+L < dimword(:256) /\ B+L <= s.vs_alloca_next /\ mem_bytes_at B L s.vs_memory = xs /\
  sb.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  allocas_from lower s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?data head cut t H u.
    t = (s with <|vs_vars := t.vs_vars; vs_inst_idx := LENGTH cut.cs_current_insts|>) /\
    sa.cs_next_var <= cut.cs_next_var /\ cut.cs_next_var <= sb.cs_next_var /\
    fn_has_code cut sb func /\
    eval_operand idx t = SOME (n2w j) /\ op_taint u idx = {} /\ op_prov H idx = NONE /\
    eval_operand data t = SOME (n2w (p+32)) /\ op_taint u data = {} /\ op_prov H data = NONE /\
    eval_operand head t = SOME (n2w (p+32+j*stride)) /\ op_taint u head = {} /\ op_prov H head = NONE /\
    EVERY (abi_decoder_operand_live cut.cs_next_var) [idx;data;head] /\
    fresh_vars_wrt ceiling t /\ t.vs_current_bb = cut.cs_current_bb /\
    t.vs_inst_idx = LENGTH cut.cs_current_insts /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_immutables = s.vs_immutables /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
    t.vs_labels = s.vs_labels /\ t.vs_halted = s.vs_halted /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lower t /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    abi_decode_ptr_window H u t bp (n2w B) L /\ ptr_covers H u ip t 32 /\
    (!v sz. not_fresh_at sa v /\ ptr_covers G tn v s sz ==> ptr_covers H u v t sz) /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ FLOOKUP u.t_var v = FLOOKUP tn.t_var v /\
      op_taint u (Var v) = op_taint tn (Var v)) /\
    (if dec_info_needs_offset di then
       ?off cmp nav.
         eval_operand off t = SOME (n2w (abi_head_word (DROP (p+32+j*stride) xs))) /\
         op_taint u off = {} /\ op_prov H off = NONE /\
         abi_decoder_operand_live cut.cs_next_var off /\
         emit_op ADD [data;off] cut = (child,cmp) /\
         abi_decode_array_pointer_guard child data hi stride cmp = ((),nav) /\
         fn_has_code cut nav func /\ fn_has_code nav sb func /\
         abi_decode_indexed_address dst idx memsz nav = (dstop,sb)
     else child = head /\ abi_decode_indexed_address dst idx memsz cut = (dstop,sb)) /\
    !D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
      (OK t,H,u)
Proof
  strip_tac >> drule_all indexed_element_setup_cut >> strip_tac >>
  `mid.cs_next_var <= ceiling.cs_next_var /\ cut.cs_next_var <= ceiling.cs_next_var`
    by decide_tac >>
  drule_all indexed_read_coordinates_joint >>
  disch_then (qspec_then `PG`
    (qx_choose_then `m` (qx_choose_then `M` (qx_choose_then `z` strip_assume_tac)))) >>
  `abi_decode_ptr_window M z m bp (n2w B) L` by
    (irule abi_decode_ptr_window_frame >> metis_tac[]) >>
  `allocas_below_fmp m = allocas_below_fmp s` by
    (qpat_assum `m = s with <|vs_vars := m.vs_vars; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac[th]) >>
     simp[NoAsms,allocas_below_fmp_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp m` by metis_tac[] >>
  Cases_on `dec_info_needs_offset di` >> fs[]
  >- (`SUC j*stride <= n*stride` by (irule LESS_MONO_MULT2 >> decide_tac) >>
      `p+(j*stride+32)+32 <= L` by
        (qpat_x_assum `SUC j*stride <= _` mp_tac >>
         simp_tac bool_ss [MULT_CLAUSES] >> decide_tac) >>
      `B+L <= m.vs_alloca_next /\ mem_bytes_at B L m.vs_memory = xs /\ ~m.vs_halted`
        by simp[] >>
      drule_all indexed_offset_read_joint >>
      disch_then (qspec_then `PG`
        (qx_choose_then `t` (qx_choose_then `H` (qx_choose_then `u` strip_assume_tac)))) >>
      `!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
         FLOOKUP H v = FLOOKUP G v /\ FLOOKUP u.t_var v = FLOOKUP tn.t_var v /\
         op_taint u (Var v) = op_taint tn (Var v)` by
        (MATCH_MP_TAC indexed_frame_trans >> qexistsl_tac [`M`,`m`,`mid`,`z`] >> simp[]) >>
      map_every (fn opn =>
        `eval_operand ^opn t = eval_operand ^opn m /\
         op_prov H ^opn = op_prov M ^opn /\ op_taint u ^opn = op_taint z ^opn` by
          (irule indexed_live_values_frame >> simp[] >> qexists `mid` >> simp[]))
        [``idx:operand``,``data:operand``,``head:operand``] >>
      qexistsl_tac [`data`,`head`,`cut`,`t`,`H`,`u`] >>
      conj_tac
      >- (irule indexed_pc_frame_trans >> qexistsl [`LENGTH mid.cs_current_insts`,`m`] >>
          conj_tac >> first_assum ACCEPT_TAC) >>
      simp[] >>
      conj_tac >- metis_tac[abi_decoder_operand_live_mono] >>
      conj_tac >- (irule abi_decode_ptr_window_frame >> metis_tac[]) >>
      conj_tac >- (irule ptr_covers_old_transport >> qexistsl [`G`,`s`,`sa`,`tn`] >> simp[]) >>
      conj_tac >- (rpt strip_tac >> irule ptr_covers_old_transport >>
                   qexistsl [`G`,`s`,`sa`,`tn`] >> simp[]) >>
      conj_tac >- (qexistsl_tac [`off`,`cmp`,`nav`] >> simp[]) >>
      rpt gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`M`,`m`,`z`] >> simp[]) >>
  qpat_x_assum `cut = mid` SUBST_ALL_TAC >>
  qexistsl_tac [`data`,`mid`,`m`,`M`,`z`] >>
  conj_tac >- first_assum ACCEPT_TAC >> simp[] >>
  conj_tac >- (irule ptr_covers_old_transport >> qexistsl [`G`,`s`,`sa`,`tn`] >> simp[]) >>
  rpt strip_tac >> irule ptr_covers_old_transport >> qexistsl [`G`,`s`,`sa`,`tn`] >> simp[]
QED

Theorem malformed_indexed_reads_joint:
  abi_decode_array_element_setup (Var ip) src dst MLOAD (Var bp) hi di stride memsz sa =
    ((idx,child,dstop),sb) /\ hi <> Lit 0w /\ fn_has_code sa sb func /\
  j < n /\ p+32+n*stride <= L /\ (dec_info_needs_offset di ==> 32 <= stride) /\
  lookup_var ip s = SOME slot /\ ptr_covers G tn ip s 32 /\ not_fresh_at sa ip /\
  (!i. w2n slot <= i /\ i < w2n slot+32 ==> i NOTIN tn.t_mem) /\
  w2n slot+32 <= s.vs_alloca_next /\ mload (w2n slot) s = n2w j /\
  eval_operand src s = SOME (n2w p) /\ abi_decoder_operand_live sa.cs_next_var src /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  abi_decode_ptr_window G tn s bp (n2w B) L /\ not_fresh_at sa bp /\
  B+L < dimword(:256) /\ B+L <= s.vs_alloca_next /\ mem_bytes_at B L s.vs_memory = xs /\
  sb.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  allocas_from lower s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?data head cut t H u.
    sa.cs_next_var <= cut.cs_next_var /\ cut.cs_next_var <= sb.cs_next_var /\
    fn_has_code cut sb func /\
    eval_operand idx t = SOME (n2w j) /\ op_taint u idx = {} /\ op_prov H idx = NONE /\
    eval_operand data t = SOME (n2w (p+32)) /\ op_taint u data = {} /\ op_prov H data = NONE /\
    eval_operand head t = SOME (n2w (p+32+j*stride)) /\ op_taint u head = {} /\ op_prov H head = NONE /\
    EVERY (abi_decoder_operand_live cut.cs_next_var) [idx;data;head] /\
    fresh_vars_wrt ceiling t /\ t.vs_current_bb = cut.cs_current_bb /\
    t.vs_inst_idx = LENGTH cut.cs_current_insts /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_immutables = s.vs_immutables /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
    t.vs_labels = s.vs_labels /\ t.vs_halted = s.vs_halted /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lower t /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    abi_decode_ptr_window H u t bp (n2w B) L /\ ptr_covers H u ip t 32 /\
    (!v sz. not_fresh_at sa v /\ ptr_covers G tn v s sz ==> ptr_covers H u v t sz) /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ FLOOKUP u.t_var v = FLOOKUP tn.t_var v /\
      op_taint u (Var v) = op_taint tn (Var v)) /\
    (if dec_info_needs_offset di then
       ?off cmp nav.
         eval_operand off t = SOME (n2w (abi_head_word (DROP (p+32+j*stride) xs))) /\
         op_taint u off = {} /\ op_prov H off = NONE /\
         abi_decoder_operand_live cut.cs_next_var off /\
         emit_op ADD [data;off] cut = (child,cmp) /\
         abi_decode_array_pointer_guard child data hi stride cmp = ((),nav) /\
         fn_has_code cut nav func /\ fn_has_code nav sb func /\
         abi_decode_indexed_address dst idx memsz nav = (dstop,sb)
     else child = head /\ abi_decode_indexed_address dst idx memsz cut = (dstop,sb)) /\
    !D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
      (OK t,H,u)
Proof
  strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all malformed_indexed_reads_joint_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl [`data`,`head`,`cut`,`t`,`H`,`u`] >> simp[]
QED
