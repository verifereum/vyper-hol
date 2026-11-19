(* The nonbulk allocated-array header reloads both index and count before branching. *)
Theory abiDecodeRejectFiniteHeader
Ancestors
  abiDecoderRecursiveLoopLayout abiDecoderLoopEmit abiDecoderLoopCode abiDecoderContract
  abiMalformedNavigation abiDecodePtrMemberFrame abiDecoderExecution
  abiEncoderWindowSequence decoderNavigationPtr decoderMemberPrefixPtr
  decoderArraySetupPtr decoderGhostFramePtr typedCopyOriginPtrBase
  actualAllocaReplayPtr fragGasOriginPtrLoop
  venomState venomInst venomExecSemantics fragExec compileEnv emitHelperProps
  bodyPtrDefs ptrDiscipline exprLoweringProps loweringStateRelDefs
  emitHelper abiEncoder words finite_map list arithmetic

Theorem finite_header_emit_extends[local]:
  emit_op opc ops a = (out,b) ==>
  cs_extends a b /\ b.cs_current_bb = a.cs_current_bb
Proof
  strip_tac >> drule exprLoweringPropsTheory.emit_op_same_blocks >> drule emitted_insts_emit_op >>
  simp[exprLoweringPropsTheory.same_blocks_def] >> rpt strip_tac >>
  irule cs_extends_same_block >> simp[]
QED

Theorem finite_header_emits[local]:
  abi_decode_loop_prefix (Var slotvar) pos MLOAD (Var source) ls = (labels,body_st) /\
  fn_has_code ls body_st func ==>
  ?a a1 a2 a3 a4 a5 a6 idx addr cnt lt done.
    emit_op MLOAD [Var slotvar] a = (idx,a1) /\
    emit_op ADD [Var source;pos] a1 = (addr,a2) /\
    emit_op MLOAD [addr] a2 = (cnt,a3) /\
    emit_op LT [idx;cnt] a3 = (lt,a4) /\
    emit_op ISZERO [lt] a4 = (done,a5) /\
    emit_inst JNZ [done;Label (SND (SND labels));Label (FST (SND labels))] [] a5 = ((),a6) /\
    fn_has_code a a1 func /\ fn_has_code a1 a2 func /\ fn_has_code a2 a3 func /\
    fn_has_code a3 a6 func /\
    a.cs_current_bb = FST labels /\ a.cs_current_insts = [] /\
    a.cs_next_var = ls.cs_next_var
Proof
  simp[abi_decode_loop_prefix_def, compile_abi_dec_addr_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  rename1 `new_block hdr after_jump = (_,a)` >>
  rename1 `emit_op MLOAD [Var slotvar] a = (idx,a1)` >>
  rename1 `emit_op ADD [Var source;pos] a1 = (addr,a2)` >>
  rename1 `emit_op MLOAD [addr] a2 = (cnt,a3)` >>
  rename1 `emit_op LT [idx;cnt] a3 = (lt,a4)` >>
  rename1 `emit_op ISZERO [lt] a4 = (done,a5)` >>
  rename1 `new_block _ a6 = (_,body_st)` >>
  qexistsl_tac [`a`,`a1`,`a2`,`a3`,`a4`,`a5`,`a6`,`idx`,`addr`,`cnt`,`lt`,`done`] >>
  simp[] >>
  `cs_extends a a1 /\ cs_extends a1 a2 /\ cs_extends a2 a3 /\
   cs_extends a3 a4 /\ cs_extends a4 a5 /\ cs_extends a5 a6 /\
   cs_extends a6 body_st` by metis_tac[finite_header_emit_extends, cs_extends_emit_inst, cs_extends_new_block] >>
  `cs_extends ls a` by
    (imp_res_tac cs_extends_fresh_label >> imp_res_tac cs_extends_emit_inst >>
     imp_res_tac cs_extends_new_block >> metis_tac[cs_extends_trans]) >>
  `cs_extends a3 a6 /\ cs_extends a3 body_st /\ cs_extends a2 body_st /\
   cs_extends a1 body_st /\ cs_extends a body_st` by metis_tac[cs_extends_trans] >>
  `fn_has_code a body_st func` by metis_tac[fn_has_code_split] >>
  `fn_has_code a a1 func /\ fn_has_code a1 a2 func /\ fn_has_code a2 a3 func /\
   fn_has_code a3 a6 func` by metis_tac[fn_has_code_split] >>
  gvs[new_block_def, fresh_label_def, emit_inst_def, comp_bind_def,
      fresh_id_def, emit_def]
QED

Theorem finite_header_load[local]:
  emit_op MLOAD [Var q] a = (out,b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ allocas_from lo s /\
  ~ctx_has_dalloca ctx /\ lookup_var q s = SOME w /\
  ptr_covers G tn q s 32 /\ w2n w + 32 <= s.vs_alloca_next /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) ==>
  ?G' tn'.
    out = Var (STRING #"%" (toString a.cs_next_var)) /\
    op_taint tn' out = {} /\ op_prov G' out = NONE /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    b.cs_current_bb = a.cs_current_bb /\
    LENGTH b.cs_current_insts = SUC s.vs_inst_idx /\
    (!x. not_fresh_at a x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (update_var (STRING #"%" (toString a.cs_next_var)) (mload (w2n w) s) s
             with vs_inst_idx := LENGTH b.cs_current_insts),G',tn')
Proof
  strip_tac >>
  `eval_operand (Var q) s = SOME (n2w (w2n w))` by simp[eval_operand_def] >>
  `w2n w < dimword(:256)` by simp[w2n_lt] >>
  drule_all abiEncoderWindowLeavesTheory.window_emit_load_run >> strip_tac >>
  drule_all emit_mload_clean_endpoint_ptr_origin_core_exact_frame >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`,`ARB`] strip_assume_tac) >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexistsl_tac [`HG`,`u`] >> gvs[] >> metis_tac[]
QED

Theorem finite_header_address[local]:
  emit_op ADD [Var source;pos] a = (out,b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ allocas_from lo s /\
  ~ctx_has_dalloca ctx /\ lookup_var source s = SOME (n2w B) /\
  ptr_covers G tn source s L /\ eval_operand pos s = SOME (n2w p) /\
  op_taint tn pos = {} /\ op_prov G pos = NONE /\
  p + 32 <= L /\ B + L < dimword(:256) ==>
  ?G' tn'.
    out = Var (STRING #"%" (toString a.cs_next_var)) /\
    b.cs_current_bb = a.cs_current_bb /\
    LENGTH b.cs_current_insts = SUC s.vs_inst_idx /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at a x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    ptr_covers G' tn' (STRING #"%" (toString a.cs_next_var)) (update_var (STRING #"%" (toString
      a.cs_next_var)) (n2w (B + p)) s with vs_inst_idx := LENGTH b.cs_current_insts) 32 /\
      !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (update_var (STRING #"%" (toString a.cs_next_var)) (n2w (B + p)) s with vs_inst_idx :=
          LENGTH b.cs_current_insts),G',tn')
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule finite_header_emit_extends >> strip_tac >>
  `B < dimword(:256) /\ B + p < dimword(:256)` by decide_tac >>
  qabbrev_tac `x = STRING #"%" (toString a.cs_next_var)` >>
  `run_inst_seq (emitted_insts a b) s = OK (update_var x (n2w (B+p)) s)` by
    (simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
          eval_operand_def, word_add_n2w, Abbr `x`]) >>
  `w2n (n2w B:bytes32) = B` by simp[w2n_n2w, LESS_MOD] >>
  `w2n (n2w B:bytes32) + p < dimword(:256)` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all member_navigation_emit_pointer_pc_uniform_origin >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`H`,`u`] >>
  gvs[ptr_covers_def, lookup_var_def, w2n_n2w, LESS_MOD] >>
  `(s with vs_inst_idx := LENGTH a.cs_current_insts) = s` by
    simp[venom_state_component_equality] >>
  fs[]
QED

Theorem finite_header_branch[local]:
  emit_op LT [Var ix;cnt] a = (lt,b) /\ emit_op ISZERO [lt] b = (done,c) /\
  emit_inst JNZ [done;Label exit_lbl;Label body_lbl] [] c = ((),d) /\ fn_has_code a d func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ allocas_from lo s /\
  ~ctx_has_dalloca ctx /\ lookup_var ix s = SOME (n2w j) /\
  eval_operand cnt s = SOME (n2w n) /\ j < n /\ n < dimword(:256) /\
  op_taint tn (Var ix) = {} /\ op_prov G (Var ix) = NONE /\
  op_taint tn cnt = {} /\ op_prov G cnt = NONE ==>
  ?G' tn'.
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at a x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (jump_to body_lbl
        (update_var (STRING #"%" (toString (a.cs_next_var + 1))) 0w
          (update_var (STRING #"%" (toString a.cs_next_var)) 1w s))),G',tn')
Proof
  strip_tac >>
  `j <= n /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s)` by simp[] >>
  `FLOOKUP G ix = NONE` by fs[op_prov_def] >>
  `lt = Var (STRING #"%" (toString a.cs_next_var))` by
    metis_tac[emitted_insts_emit_op] >>
  `done = Var (STRING #"%" (toString (a.cs_next_var + 1)))` by
    metis_tac[emitted_insts_emit_op] >>
  qabbrev_tac `x = STRING #"%" (toString a.cs_next_var)` >>
  qabbrev_tac `y = STRING #"%" (toString (a.cs_next_var + 1))` >>
  qexistsl_tac [`DRESTRICT (DRESTRICT G (COMPL {x})) (COMPL {y})`,
    `tn with t_var := (tn.t_var |+ (x,{})) |+ (y,{})`] >>
  rpt conj_tac >- simp[] >- simp[] >- simp[] >- simp[]
  >- (simp[not_fresh_at_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
      metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
  rpt gen_tac >> drule_all typed_copy_origin_ptr_header_branch_path >>
  disch_then (qspecl_then [`explicit`,`PG`,`D`] strip_assume_tac) >>
  `j <> n` by decide_tac >> gvs[]
QED

Theorem malformed_finite_header_body_joint:
  compile_abi_decode_dyn_loop (Var dst) pos MLOAD (Var source) hi di asz msz
    (Var slotvar) initial_count ls = ((),en) /\ fn_has_code ls en func /\
  ~s.vs_halted /\ s.vs_current_bb = fresh_label_output "dec_dyn_hdr" ls.cs_next_label /\
  s.vs_inst_idx = 0 /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  mem_bytes_at B L s.vs_memory = xs /\ p + 32 <= L /\
  B + L < dimword(:256) /\ B + L <= s.vs_alloca_next /\
  n = abi_head_word (DROP p xs) /\ j < n /\
  lookup_var slotvar s = SOME slot /\ ptr_covers G tn slotvar s 32 /\
  w2n slot + 32 <= s.vs_alloca_next /\ mload (w2n slot) s = n2w j /\
  (!i. w2n slot <= i /\ i < w2n slot + 32 ==> i NOTIN tn.t_mem) /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\ op_prov G pos = NONE /\
  ptr_covers G tn dst s cap /\
  not_fresh_at ls slotvar /\ not_fresh_at ls source /\ not_fresh_at ls dst /\
  (!x. pos = Var x \/ hi = Var x ==> not_fresh_at ls x) /\
  ls.cs_next_var + 5 <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s ==>
  ?b Gb tb.
    b = jump_to (fresh_label_output "dec_dyn_body" (ls.cs_next_label + 1))
      (abi_decode_position_header_state (Var source) ls.cs_next_var B p j n s) /\
    ~b.vs_halted /\ b.vs_current_bb = fresh_label_output "dec_dyn_body" (ls.cs_next_label + 1) /\
    b.vs_inst_idx = 0 /\ b.vs_memory = s.vs_memory /\ b.vs_allocas = s.vs_allocas /\
    b.vs_alloca_next = s.vs_alloca_next /\ b.vs_fmp = s.vs_fmp /\ allocas_from lo b /\
    b.vs_accounts = s.vs_accounts /\ b.vs_transient = s.vs_transient /\
    b.vs_call_ctx = s.vs_call_ctx /\ b.vs_immutables = s.vs_immutables /\
    b.vs_labels = s.vs_labels /\ fresh_vars_wrt ceiling b /\
    tb.t_mem = tn.t_mem /\ tb.t_stor = tn.t_stor /\
    tb.t_trans = tn.t_trans /\ tb.t_imm = tn.t_imm /\
    (!x. not_fresh_at ls x ==> lookup_var x b = lookup_var x s /\
      FLOOKUP Gb x = FLOOKUP G x /\ op_taint tb (Var x) = op_taint tn (Var x)) /\
    lookup_var slotvar b = SOME slot /\ mload (w2n slot) b = n2w j /\
    ptr_covers Gb tb slotvar b 32 /\ abi_decode_ptr_window Gb tb b source (n2w B) L /\
    ptr_covers Gb tb dst b cap /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK b,Gb,tb)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_dyn_loop_trace >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_loop_phase_containment >> strip_tac >>
  drule abi_decoder_loop_prefix_extends >> strip_tac >>
  drule abiDecoderArraySetupCodeTheory.abi_decoder_array_setup_head >> strip_tac >>
  `cs_extends st1 en` by
    (irule abi_decoder_loop_suffix_extends >>
     qpat_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >> asm_simp_tac bool_ss [] >>
     metis_tac[]) >>
  `cs_extends st0 en` by metis_tac[cs_extends_trans] >>
  `fn_has_code ls st0 func` by
    (qspecl_then [`ls`,`st0`,`en`,`func`] mp_tac fn_has_code_split >> simp[]) >>
  drule_all finite_header_emits >> strip_tac >>
  `FST labels = fresh_label_output "dec_dyn_hdr" ls.cs_next_label /\
   FST (SND labels) = fresh_label_output "dec_dyn_body" (ls.cs_next_label+1)` by
    gvs[abi_decode_loop_prefix_shape] >>
  `s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts` by simp[] >>
  `B < dimword(:256) /\ B + p < dimword(:256)` by decide_tac >>
  `mem_bytes_at B L (abi_decode_source MLOAD s) = xs` by simp[abi_decode_source_def] >>
  drule_all abi_checked_offset_load >> strip_tac >>
  `w2n (n2w (B+p):bytes32) = B+p` by
    (rewrite_tac[w2n_n2w] >> irule LESS_MOD >> simp[]) >>
  `mload (B+p) s = n2w n /\ n < dimword(:256)` by
    (conj_tac >-
       (qpat_assum `w2n (n2w (B+p):bytes32) = B+p` (fn h =>
          qpat_assum `abi_decode_load MLOAD _ s = _`
            (mp_tac o REWRITE_RULE[abi_decode_load_def,h])) >> simp[]) >>
     simp[]) >>
  qpat_x_assum `compile_abi_decode_dyn_loop _ _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` kall_tac >>
  suspend "loads"
QED

Resume malformed_finite_header_body_joint[loads]:
  drule_all finite_header_load >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `op_prov G1 idx = NONE` >> rename1 `op_taint tn1 idx = {}` >>
  qabbrev_tac `ix = STRING #"%" (toString a.cs_next_var)` >>
  qabbrev_tac `s1 = update_var ix (mload (w2n slot) s) s with vs_inst_idx := LENGTH a1.cs_current_insts` >>
  `lookup_var source s = SOME (n2w B) /\ ptr_covers G tn source s L` by
    fs[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def] >>
  `!x. not_fresh_at a x ==> lookup_var x s1 = lookup_var x s` by
    (rpt strip_tac >>
     `x <> ix` by (simp[Abbr `ix`] >> fs[not_fresh_at_def]) >>
     simp[Abbr `s1`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `not_fresh_at a source` by fs[not_fresh_at_def] >>
  `!x. pos = Var x ==> not_fresh_at a x` by fs[not_fresh_at_def] >>
  `lookup_var source s1 = SOME (n2w B)` by metis_tac[] >>
  `ptr_covers G1 tn1 source s1 L` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `eval_operand pos s1 = SOME (n2w p) /\ op_taint tn1 pos = {} /\ op_prov G1 pos = NONE` by
    (`s1.vs_labels = s.vs_labels` by simp[Abbr `s1`,update_var_def] >>
     Cases_on `pos` >> fs[eval_operand_def,op_taint_def,op_prov_def] >> metis_tac[]) >>
  `~s1.vs_halted /\ s1.vs_current_bb = a1.cs_current_bb /\
   s1.vs_inst_idx = LENGTH a1.cs_current_insts /\ allocas_from lo s1` by
    (conj_tac >- simp[Abbr `s1`,update_var_def] >>
     conj_tac >- simp[Abbr `s1`,update_var_def] >>
     conj_tac >- simp[Abbr `s1`] >>
     simp[Abbr `s1`,update_var_def,allocas_from_def,NoAsms] >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  drule_all finite_header_address >>
  disch_then (qspec_then `PG` (strip_assume_tac o BETA_RULE o REWRITE_RULE[LET_THM])) >>
  rename1 `tn2.t_mem = tn1.t_mem` >>
  qabbrev_tac `ax = STRING #"%" (toString a1.cs_next_var)` >>
  qabbrev_tac `s2 = update_var ax (n2w (B+p)) s1 with vs_inst_idx := LENGTH a2.cs_current_insts` >>
  `lookup_var ax s2 = SOME (n2w (B+p))` by
    simp[Abbr `s2`,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
  `~s2.vs_halted /\ s2.vs_current_bb = a2.cs_current_bb /\
   s2.vs_inst_idx = LENGTH a2.cs_current_insts /\ s2.vs_memory = s.vs_memory /\
   s2.vs_alloca_next = s.vs_alloca_next` by
    simp[Abbr `s2`,Abbr `s1`,update_var_def] >>
  `allocas_from lo s2` by
    (qpat_assum `allocas_from lo s1` (mp_tac o REWRITE_RULE[allocas_from_def]) >>
     simp[Abbr `s2`,update_var_def,allocas_from_def]) >>
  `w2n (n2w (B+p):bytes32) + 32 <= s2.vs_alloca_next` by
    (pure_asm_rewrite_tac[] >> decide_tac) >>
  `!i. w2n (n2w (B+p):bytes32) <= i /\ i < w2n (n2w (B+p):bytes32) + 32 ==>
    i NOTIN tn2.t_mem` by
    (qpat_assum `abi_decode_ptr_window G tn s source _ L`
       (mp_tac o REWRITE_RULE[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def]) >>
     `w2n (n2w B:bytes32) = B` by simp[w2n_n2w,LESS_MOD] >>
     pure_asm_rewrite_tac[] >> rpt strip_tac >>
     qpat_assum `!k. B <= k /\ k < B + L ==> k NOTIN tn.t_mem`
       (qspec_then `i` mp_tac) >> (impl_tac >- decide_tac) >> simp[]) >>
  `a1.cs_next_var = a.cs_next_var + 1 /\ a2.cs_next_var = a1.cs_next_var + 1 /\
   a3.cs_next_var = a2.cs_next_var + 1` by metis_tac[emitted_insts_emit_op] >>
  qpat_x_assum `emit_op MLOAD [Var slotvar] a = _` kall_tac >>
  `emit_op MLOAD [Var ax] a2 = (cnt,a3)` by metis_tac[] >>
  drule_all finite_header_load >> disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `op_prov G3 cnt = NONE` >> rename1 `op_taint tn3 cnt = {}` >>
  qabbrev_tac `cv = STRING #"%" (toString a2.cs_next_var)` >>
  qabbrev_tac `s3 = update_var cv (mload (w2n (n2w (B+p):bytes32)) s2) s2
    with vs_inst_idx := LENGTH a3.cs_current_insts` >>
  `mload (w2n (n2w (B+p):bytes32)) s2 = n2w n` by
    (pure_asm_rewrite_tac[] >>
     qpat_assum `mload (B+p) s = _` (mp_tac o REWRITE_RULE[mload_def]) >> simp[mload_def]) >>
  `ix <> ax /\ ix <> cv` by simp[Abbr `ix`,Abbr `ax`,Abbr `cv`,ASCIInumbersTheory.toString_inj] >>
  `lookup_var ix s3 = SOME (n2w j) /\ eval_operand cnt s3 = SOME (n2w n)` by
    simp[Abbr `s3`,Abbr `s2`,Abbr `s1`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
  `not_fresh_at a1 ix /\ not_fresh_at a2 ix` by
    (simp[Abbr `ix`,not_fresh_at_def,ASCIInumbersTheory.toString_inj] >> decide_tac) >>
  `op_taint tn3 (Var ix) = {} /\ op_prov G3 (Var ix) = NONE` by
    (simp[op_prov_def] >>
     qpat_assum `op_prov G1 idx = NONE` (mp_tac o REWRITE_RULE[op_prov_def]) >>
     simp[] >> metis_tac[]) >>
  `~s3.vs_halted /\ s3.vs_current_bb = a3.cs_current_bb /\ s3.vs_inst_idx = LENGTH a3.cs_current_insts` by
    simp[Abbr `s3`,update_var_def] >>
  `allocas_from lo s3` by
    (qpat_assum `allocas_from lo s2` (mp_tac o REWRITE_RULE[allocas_from_def]) >>
     simp[Abbr `s3`,update_var_def,allocas_from_def]) >>
  `emit_op LT [Var ix;cnt] a3 = (lt,a4)` by metis_tac[] >>
  drule_all finite_header_branch >> disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `tn4.t_mem = tn3.t_mem` >>
  rename1 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s3,G3,tn3) [] (OK (jump_to _ _),G4,tn4)` >>
  qabbrev_tac `b = jump_to (FST (SND labels))
    (update_var (STRING #"%" (toString (a3.cs_next_var + 1))) 0w
       (update_var (STRING #"%" (toString a3.cs_next_var)) 1w s3))` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK b,G4,tn4)` by
    (rpt gen_tac >>
     metis_tac[SIMP_RULE (srw_ss()) []
       (Q.SPECL [`cx`,`st`,`[]`] fragGasOriginPtrTheory.gas_origin_ptr_path_append)]) >>
  `b = jump_to (fresh_label_output "dec_dyn_body" (ls.cs_next_label + 1))
      (abi_decode_position_header_state (Var source) ls.cs_next_var B p j n s)` by
    (simp[Abbr `b`, Abbr `s3`, Abbr `cv`] >>
     simp[Abbr `s2`, Abbr `s1`, Abbr `ix`, Abbr `ax`,
          abi_decode_position_header_state_def, abi_decode_position_header_delta_def,
          bool_to_word_def, jump_to_def, update_var_def, arithmeticTheory.ADD_ASSOC]) >>
  `!x. not_fresh_at ls x ==> lookup_var x b = lookup_var x s /\
       FLOOKUP G4 x = FLOOKUP G x /\ op_taint tn4 (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at a x /\ not_fresh_at a1 x /\ not_fresh_at a2 x /\ not_fresh_at a3 x` by
       (rpt conj_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
        qexists_tac `ls` >> simp[]) >>
     reverse conj_tac >- metis_tac[] >>
     `!k. ls.cs_next_var <= k ==> x <> STRING #"%" (toString k)` by
       fs[not_fresh_at_def] >>
     simp[abi_decode_position_header_state_def, abi_decode_position_header_delta_def,
          lookup_var_def, jump_to_def, update_var_def, FLOOKUP_UPDATE]) >>
  `tn4.t_mem = tn.t_mem` by simp[] >>
  `ptr_covers G4 tn4 slotvar b 32 /\ ptr_covers G4 tn4 dst b cap` by
    (conj_tac >> irule ptr_covers_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `abi_decode_ptr_window G4 tn4 b source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `fresh_vars_wrt ceiling b` by
    (simp[abi_decode_position_header_state_def, abi_decode_position_header_delta_def,
          jump_to_def, update_var_def, fresh_vars_wrt_def, FDOM_FUPDATE,
          ASCIInumbersTheory.toString_inj] >>
     qpat_assum `fresh_vars_wrt ceiling s` (ACCEPT_TAC o REWRITE_RULE[fresh_vars_wrt_def])) >>
  `allocas_from lo b` by
    (simp[abi_decode_position_header_state_def, abi_decode_position_header_delta_def,
          jump_to_def, update_var_def, allocas_from_def] >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `b.vs_memory = s.vs_memory` by
    simp[abi_decode_position_header_state_def, abi_decode_position_header_delta_def,
         jump_to_def, update_var_def] >>
  `mload (w2n slot) b = n2w j` by
    (qpat_assum `mload (w2n slot) s = n2w j` (mp_tac o REWRITE_RULE[mload_def]) >>
     simp[mload_def]) >>
  qexistsl_tac [`b`,`G4`,`tn4`] >> simp[] >>
  simp[abi_decode_position_header_state_def, abi_decode_position_header_delta_def,
       jump_to_def, update_var_def]
QED

Finalise malformed_finite_header_body_joint
