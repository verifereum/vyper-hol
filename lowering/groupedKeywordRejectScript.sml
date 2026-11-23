(* The rejecting branches of a supplied keyword's decoder. *)
Theory groupedKeywordReject
Ancestors
  groupedKeywordAddress groupedInternalLabels registrationGuardRejectOrigin
  calldataNoneDecoder abiDecoderCoherence abiDecoderReentry fragGasOriginPtr
  fragGasOriginPtrLoop fragExec ptrDiscipline loweringStateRelDefs
  compileEnv finite_map words list arithmetic venomState
  registrationGuardPtr calldataRegistrationRawAddress calldataRegistrationExec
  entryPtrSeamRegister moduleLoweringProps abiDecoderCounters loweringShapeDefs
  groupedKeywordSupplied calldataSourceSize calldataSourceCorrespondence vyperCalldata bodyPtrDefs
  calldataDynOwned exprLoweringProps exprSimWordBuiltins emitHelperProps pair
  groupedDispatchPath selectedAcceptedFold rich_list

Theorem grouped_keyword_decoder_reject:
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  compile_abi_decode_to_buf (Var dst) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) sa = ((),sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  (!bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\ unit_alloca_budget ctx < dimword (:256) /\
  eval_operand src s = SOME p /\ eval_operand (Var dst) s = SOME (n2w d) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var (Var dst) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> id < sa.cs_next_id) /\
  FLOOKUP s.vs_allocas oid = SOME (d,type_memory_size tv) /\
  d+type_memory_size tv < dimword (:256) /\ ptr_covers G tn dst s (type_memory_size tv) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  fresh_vars_wrt sb s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  cd_decode F s.vs_call_ctx.cc_calldata tv (w2n p) = NONE ==>
  ?z H u. z.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort z,H,u)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule (BETA_RULE none_coherent_decode_paths) >>
  disch_then (qspecl_then
    [`sa`,`sb`,`sb`,`ctx`,`fn`,`site`,`src`,`dst`,`s`,`p`,`d`,`oid`,`d`,
     `type_memory_size tv`,`G`,`tn`,`lo`,`PG`] mp_tac) >>
  impl_tac >-
    (`oid < sa.cs_next_id` by metis_tac[] >>
     simp[] >> rpt strip_tac >>
     qpat_assum `!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> _`
       (qspecl_then [`id`,`(q,k)`] (drule_then assume_tac)) >>
     `F` by
       (qpat_assum `id < sa.cs_next_id` mp_tac >>
        qpat_assum `sa.cs_next_id <= id` mp_tac >> decide_tac)) >>
  simp[]
QED

Theorem grouped_keyword_pointer_wrap_reject:
  compile_getelemptr_abi (Lit 4w) T off CALLDATALOAD (Lit 0w) (Lit 0w)
    sa = (src,sm) /\
  compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) sm = ((),sb) /\
  fn_has_code sa sm fn /\ fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  fresh_vars_wrt sa s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (4w + abi_decode_load CALLDATALOAD (n2w (4+off):bytes32) s) <+ 4w ==>
  ?z H u. z.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort z,H,u)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  mp_tac (Q.INST [`se` |-> `sm`] grouped_keyword_dynamic_address) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then strip_assume_tac >>
  rename1 `fresh_vars_wrt sm addr` >>
  rename1 `op_prov Ha src = NONE` >>
  rename1 `op_taint ta src = {}` >>
  `addr.vs_allocas = s.vs_allocas /\ addr.vs_initial_fmp = s.vs_initial_fmp /\
   addr.vs_fmp = s.vs_fmp` by
    (qpat_assum `addr = s with <|vs_vars := _; vs_inst_idx := _|>` (pure_once_rewrite_tac o single) >> simp[]) >>
  `allocas_from lo addr /\ (ctx_has_dalloca ctx ==> allocas_below_fmp addr)` by
    (pure_rewrite_tac[allocas_from_def, allocas_below_fmp_def] >>
     qpat_assum `addr.vs_allocas = s.vs_allocas` (pure_once_rewrite_tac o single) >>
     qpat_assum `addr.vs_initial_fmp = s.vs_initial_fmp` (pure_once_rewrite_tac o single) >>
     qpat_assum `addr.vs_fmp = s.vs_fmp` (pure_once_rewrite_tac o single) >>
     conj_tac
     >- qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def]) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
       (ACCEPT_TAC o REWRITE_RULE [allocas_below_fmp_def])) >>
  pop_assum strip_assume_tac >>
  drule_at (Pat `compile_abi_arg_ptr_guard _ _ _ sm = _`) registration_ptr_guard_reject_origin >>
  disch_then (drule_at (Pat `eval_operand src addr = SOME _`)) >>
  disch_then (drule_at (Pat `op_taint ta src = {}`)) >>
  disch_then (drule_at (Pat `op_prov Ha src = NONE`)) >>
  disch_then (qspecl_then [`lo`,`fn`,`ctx`,`PG`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`z`,`Hz`,`uz`] strip_assume_tac) >>
  qexistsl_tac [`z`,`Hz`,`uz`] >> simp[] >> rpt gen_tac >>
  metis_tac[gas_origin_ptr_path_append, APPEND]
QED

Theorem grouped_keyword_reject_singleton:
  0 < k /\
  compile_init_kwargs ce ((name,Var dst,ty,e)::vars) (4+off) k hi sa = ((),sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  is_abi_dynamic ce.ce_struct_fields ty = tv_abi_dynamic tv /\
  4+off < dimword (:256) /\
  calldata_decode_args s.vs_call_ctx.cc_calldata [tv] off = NONE /\
  fresh_vars_wrt sa s /\ not_fresh_at sa dst /\
  lookup_var dst s = SOME (n2w d) /\ ptr_covers G tn dst s (type_memory_size tv) /\
  FLOOKUP s.vs_allocas oid = SOME (d,type_memory_size tv) /\
  d+type_memory_size tv < dimword (:256) /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> id < sa.cs_next_id) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z H u. z.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort z,H,u)
Proof
  strip_tac >> drule_all compile_init_kwargs_supplied_intervals >> strip_tac >>
  qabbrev_tac `dyn = is_abi_dynamic ce.ce_struct_fields ty` >>
  qabbrev_tac `delta = w2n (cd_word s.vs_call_ctx.cc_calldata (4+off))` >>
  qabbrev_tac `srcpos = if dyn then (4+delta) MOD dimword (:256) else 4+off` >>
  mp_tac (Q.INST [`cd` |-> `s.vs_call_ctx.cc_calldata`, `s` |-> `s`,
    `delta` |-> `delta`, `ofs` |-> `off`, `p` |-> `srcpos`,
    `tv` |-> `tv`, `tvs` |-> `[]`] calldata_decode_args_step_exact) >>
  impl_tac >- simp[Abbr `srcpos`, Abbr `delta`, Abbr `dyn`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `4 + off - 4 = off` by decide_tac >>
  qpat_assum `4 + off - 4 = off` (fn eq =>
    qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ sa = _`
      (assume_tac o REWRITE_RULE [eq])) >>
  Cases_on `srcpos < 4`
  >- (`dyn` by (Cases_on `dyn` >> fs[Abbr `srcpos`]) >>
      `4w + abi_decode_load CALLDATALOAD (n2w (4+off):bytes32) s <+ 4w` by
        fs[Abbr `srcpos`, word_add_n2w, word_lo_n2w, dimword_def] >>
      qpat_assum `dyn` (fn dyn_true =>
        qpat_assum `if dyn then _ else _`
          (assume_tac o SIMP_RULE bool_ss [dyn_true]) >>
        qpat_assum `compile_getelemptr_abi _ dyn _ _ _ _ sa = _`
          (assume_tac o SIMP_RULE bool_ss [dyn_true])) >>
      mp_tac (Q.INST [`sm` |-> `mid`,`sb` |-> `first`] grouped_keyword_pointer_wrap_reject) >>
      impl_tac >- (asm_rewrite_tac[] >> metis_tac[]) >>
      simp[]) >>
  `4 <= srcpos` by decide_tac >>
  `cd_decode F s.vs_call_ctx.cc_calldata tv srcpos = NONE` by
    (qpat_assum `calldata_decode_args _ [tv] _ = NONE <=> _` (fn eq =>
       qpat_assum `calldata_decode_args _ [tv] _ = NONE` (mp_tac o EQ_MP eq)) >>
     qpat_assum `~(srcpos < 4)` (fn above =>
       qpat_assum `4 <= srcpos` (fn bound =>
         simp_tac bool_ss [above,bound,calldata_decode_args_def, optionTheory.NOT_NONE_SOME]))) >>
  qpat_assum `4 <= srcpos ==> _` (drule_then strip_assume_tac) >>
  `srcpos < dimword (:256)` by
    (Cases_on `dyn` >> fs[Abbr `srcpos`, MOD_LESS]) >>
  mp_tac (Q.INST [`s` |-> `s`, `sa` |-> `sa`, `se` |-> `mid`,
    `dyn` |-> `dyn`, `off` |-> `off`, `delta` |-> `delta`, `src` |-> `src`,
    `lo` |-> `lo`, `ctx` |-> `ctx`, `fn` |-> `fn`, `PG` |-> `PG`,
    `G` |-> `G`, `tn` |-> `tn`] (SPEC_ALL grouped_keyword_source_address)) >>
  impl_tac >- simp[Abbr `dyn`] >>
  strip_tac >>
  rename1 `eval_operand src addr = SOME _` >>
  rename1 `fresh_vars_wrt mid addr` >>
  rename1 `op_prov Ga src = NONE` >>
  rename1 `op_taint ta src = {}` >>
  `eval_operand src addr = SOME (n2w srcpos)` by
    (qpat_assum `srcpos = _` (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
     qpat_assum `eval_operand src addr = SOME _` mp_tac >>
     asm_simp_tac bool_ss [ADD_COMM]) >>
  `dyn ==> ~(n2w srcpos : bytes32 <+ 4w)` by
    (strip_tac >>
     `4 <= srcpos` by
       (qpat_assum `srcpos = _` (fn th => PURE_ONCE_REWRITE_TAC[th]) >> decide_tac) >>
     simp_tac bool_ss [word_lo_n2w] >>
     `srcpos MOD dimword (:256) = srcpos` by simp[LESS_MOD] >>
     rewrite_tac[NOT_LESS] >>
     irule LESS_EQ_TRANS >> qexists_tac `4` >>
     asm_rewrite_tac[] >> simp[MOD_LESS_EQ]) >>
  `allocas_from lo addr /\ (ctx_has_dalloca ctx ==> allocas_below_fmp addr)` by
    (conj_tac
     >- (rewrite_tac[allocas_from_def] >>
         qpat_assum `addr.vs_allocas = _` (fn eq => PURE_REWRITE_TAC[eq]) >>
         qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
     strip_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> _` (drule_then strip_assume_tac) >>
     rewrite_tac[allocas_below_fmp_def] >>
     qpat_assum `addr.vs_allocas = _` (fn th => PURE_REWRITE_TAC[th]) >>
     qpat_assum `addr.vs_initial_fmp = _` (fn th => PURE_REWRITE_TAC[th]) >>
     qpat_assum `addr.vs_fmp = _` (fn th => PURE_REWRITE_TAC[th]) >>
     qpat_assum `allocas_below_fmp s`
       (ACCEPT_TAC o REWRITE_RULE[allocas_below_fmp_def])) >>
  mp_tac (Q.INST [`dyn` |-> `dyn`, `sa` |-> `mid`, `sb` |-> `first`,
    `s` |-> `addr`, `G` |-> `Ga`, `tn` |-> `ta`, `ctx` |-> `ctx`,
    `fn` |-> `fn`, `lo` |-> `lo`, `PG` |-> `PG`,
    `src` |-> `src`, `w` |-> `n2w srcpos`] (SPEC_ALL grouped_keyword_pointer_guard)) >>
  impl_tac >-
    (conj_tac
     >- (qpat_assum `if dyn then _ else _` mp_tac >>
         Cases_on `dyn` >> simp_tac bool_ss [EQ_SYM_EQ]) >>
     asm_rewrite_tac[]) >>
  strip_tac >>
  rename1 `fresh_vars_wrt first ready` >>
  rename1 `op_prov Gr src = NONE` >>
  rename1 `op_taint tr src = {}` >>
  `sa.cs_next_id <= mid.cs_next_id /\ sa.cs_next_var <= mid.cs_next_var` by
    (qpat_assum `compile_getelemptr_abi _ _ _ _ _ _ sa = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `dyn` >>
     simp[abiEncoderTheory.compile_getelemptr_abi_def, abiEncoderTheory.compile_abi_dec_addr_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
          fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  `mid.cs_next_id <= first.cs_next_id /\ mid.cs_next_var <= first.cs_next_var` by
    (qpat_assum `if dyn then _ else _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `dyn` >> simp[] >>
     strip_tac >> drule registration_ptr_guard_code >> simp[]) >>
  `sa.cs_next_id <= first.cs_next_id` by decide_tac >>
  `not_fresh_at mid dst` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `lookup_var dst ready = lookup_var dst s /\
   FLOOKUP Gr dst = FLOOKUP G dst /\ op_taint tr (Var dst) = op_taint tn (Var dst)` by
    (qpat_assum `!p. not_fresh_at sa p ==> lookup_var p addr = lookup_var p s /\ _`
       (qspec_then `dst` (drule_then strip_assume_tac)) >>
     qpat_assum `!p. not_fresh_at mid p ==> lookup_var p ready = lookup_var p addr /\ _`
       (qspec_then `dst` (drule_then strip_assume_tac)) >>
     asm_rewrite_tac[]) >>
  `lookup_var dst ready = SOME (n2w d) /\
    ptr_covers Gr tr dst ready (type_memory_size tv)` by
    (conj_tac >- asm_rewrite_tac[] >>
     pure_rewrite_tac[ptr_covers_def] >>
     qpat_assum `lookup_var dst ready = _` (pure_rewrite_tac o single) >>
     qpat_assum `FLOOKUP Gr dst = _` (pure_rewrite_tac o single) >>
     qpat_assum `op_taint tr (Var dst) = _` (pure_rewrite_tac o single) >>
     qpat_assum `ptr_covers G tn dst s _` (ACCEPT_TAC o REWRITE_RULE[ptr_covers_def])) >>
  `ready.vs_allocas = s.vs_allocas /\ ready.vs_alloca_next = s.vs_alloca_next /\
   ready.vs_initial_fmp = s.vs_initial_fmp /\ ready.vs_fmp = s.vs_fmp /\
   ready.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `vars_pc_only addr ready` mp_tac >>
     simp_tac (srw_ss()) [vars_pc_only_def, venom_state_component_equality] >>
     strip_tac >> asm_rewrite_tac[]) >>
  `alloca_inv ready /\ alloca_frontier_inv ctx fn site ready` by
    (mp_tac (Q.INST [`s` |-> `s`,`t` |-> `ready`,`fn` |-> `fn`,
       `ctx` |-> `ctx`,`site` |-> `site`] calldata_alloca_invariants_fields) >> simp[]) >>
  `allocas_from lo ready /\ lo <= ready.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp ready /\
      ready.vs_alloca_next + pending_alloca_size fn ready <= w2n ready.vs_initial_fmp)` by
    (conj_tac
     >- (pure_rewrite_tac[allocas_from_def] >>
         qpat_assum `ready.vs_allocas = s.vs_allocas` (pure_rewrite_tac o single) >>
         qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
     conj_tac >- asm_rewrite_tac[] >>
     strip_tac >> qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s /\ _` drule >>
     asm_rewrite_tac[allocas_below_fmp_def, pending_alloca_size_def]) >>
  `!id entry. FLOOKUP ready.vs_allocas id = SOME entry ==> id < first.cs_next_id` by
    (qpat_assum `ready.vs_allocas = s.vs_allocas` (pure_rewrite_tac o single) >>
     rpt strip_tac >> qpat_assum `!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> _`
      drule >> decide_tac) >>
  `first.cs_next_var <= last.cs_next_var` by
    metis_tac[abi_decoder_vars_mono_mutual, abi_decoder_vars_mono_def, SND] >>
  `fresh_vars_wrt last ready` by
    (irule fresh_vars_wrt_mono >> qexists_tac `first` >> simp[]) >>
  `abi_decoder_operand_live first.cs_next_var (Var dst)` by
    (simp[calldata_operand_live_not_fresh] >>
     irule not_fresh_at_mono >> qexists_tac `mid` >> simp[]) >>
  `!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `!label bb. lookup_block label fn.fn_blocks = SOME bb ==> _`
       (qspec_then `last.cs_current_bb` ACCEPT_TAC)) >>
  `oid < first.cs_next_id` by
    (qpat_assum `!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> _`
       drule >> decide_tac) >>
  `w2n (n2w srcpos : bytes32) = srcpos` by
    (rewrite_tac[wordsTheory.w2n_n2w] >>
     irule arithmeticTheory.LESS_MOD >> first_assum ACCEPT_TAC) >>
  `cd_decode F ready.vs_call_ctx.cc_calldata tv (w2n (n2w srcpos : bytes32)) = NONE` by
    (qpat_assum `w2n (n2w srcpos : bytes32) = srcpos` (pure_once_rewrite_tac o single) >>
     qpat_assum `ready.vs_call_ctx = s.vs_call_ctx` (pure_once_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`sa` |-> `first`, `sb` |-> `last`, `s` |-> `ready`,
    `p` |-> `n2w srcpos : bytes32`, `G` |-> `Gr`, `tn` |-> `tr`]
    grouped_keyword_decoder_reject) >>
  impl_tac >- simp[eval_operand_def] >>
  disch_then (qx_choosel_then [`z`,`Hz`,`uz`] strip_assume_tac) >>
  qexistsl_tac [`z`,`Hz`,`uz`] >> simp[] >> rpt gen_tac >>
  metis_tac[gas_origin_ptr_path_append, APPEND]
QED

(* Every still-supplied argument already has an allocated buffer. *)
Definition supplied_keyword_owner_def:
  supplied_keyword_owner ce env st s G tn (name,op,ty,e) tv <=>
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    is_abi_dynamic ce.ce_struct_fields ty = tv_abi_dynamic tv /\
    ?dst d oid.
      op = Var dst /\ not_fresh_at st dst /\ lookup_var dst s = SOME (n2w d) /\
      ptr_covers G tn dst s (type_memory_size tv) /\
      FLOOKUP s.vs_allocas oid = SOME (d,type_memory_size tv) /\
      d + type_memory_size tv < dimword (:256)
End

Theorem supplied_keyword_owner_frame[local]:
  supplied_keyword_owner ce env sa s G tn arg tv /\ fresh_vars_wrt sb t /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
    FLOOKUP H p = FLOOKUP G p /\ op_taint u (Var p) = op_taint tn (Var p)) /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> FLOOKUP t.vs_allocas id = SOME entry) ==>
  supplied_keyword_owner ce env sb t H u arg tv
Proof
  PairCases_on `arg` >> simp[supplied_keyword_owner_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `?dst d oid. _` (qx_choosel_then [`dst`,`d`,`oid`] strip_assume_tac) >>
  qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `dst` (drule_then strip_assume_tac)) >>
  `not_fresh_at sb dst` by
    (mp_tac (Q.SPECL [`sb`,`t`,`Var dst`,`n2w d`] fresh_vars_wrt_not_fresh_at) >>
     simp[eval_operand_def]) >>
  `ptr_covers H u dst t (type_memory_size tv)` by
    (pure_once_rewrite_tac [ptr_covers_def] >>
     qpat_assum `lookup_var dst t = _` (pure_once_rewrite_tac o single) >>
     qpat_assum `FLOOKUP H dst = _` (pure_once_rewrite_tac o single) >>
     qpat_assum `op_taint u (Var dst) = _` (pure_once_rewrite_tac o single) >>
     qpat_assum `ptr_covers G tn dst s _` (ACCEPT_TAC o REWRITE_RULE [ptr_covers_def])) >>
  qexistsl_tac [`dst`,`d`,`oid`] >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem grouped_supplied_keywords_reject:
  !tvs vars off k sa s G tn.
    LENGTH tvs = k /\
    LIST_REL (supplied_keyword_owner ce env sa s G tn) (TAKE k vars) tvs /\
    4 + off + SUM (MAP tv_abi_size tvs) < dimword (:256) /\
    calldata_decode_args s.vs_call_ctx.cc_calldata tvs off = NONE /\
    compile_init_kwargs ce vars (4+off) k hi sa = ((),sb) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> id < sa.cs_next_id) /\
    alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
    unit_alloca_budget ctx < dimword (:256) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
      s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) /\
    fresh_vars_wrt sa s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?z H u. z.vs_returndata = [] /\
      !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (Abort Revert_abort z,H,u)
Proof
  Induct_on `tvs` >- simp[calldata_decode_args_def] >>
  qx_genl_tac [`tv`,`vars`] >> Cases_on `vars` >- simp[TAKE_def] >> PairCases_on `h` >>
  simp_tac bool_ss [LENGTH] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `LIST_REL _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [TAKE_def, LIST_REL_def]) >>
  qpat_x_assum `supplied_keyword_owner _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [supplied_keyword_owner_def]) >>
  `4 + off < dimword (:256) /\
   4 + (off + tv_abi_size tv) + SUM (MAP tv_abi_size tvs) < dimword (:256)` by
    (qpat_assum `4 + off + SUM _ < _` (mp_tac o REWRITE_RULE [MAP,SUM]) >> decide_tac) >>
  Cases_on `calldata_decode_args s.vs_call_ctx.cc_calldata [tv] off` >> gvs[]
  >- (irule grouped_keyword_reject_singleton >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (qexists_tac `site` >> first_assum ACCEPT_TAC) >>
      qexistsl_tac [`ce`,`d`,`dst`,`h3`,`env`,`hi`,`SUC (LENGTH tvs)`,
        `h0`,`off`,`oid`,`sa`,`sb`,`tv`,`h2`,`t`] >>
      asm_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM, SUC_POS] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `off + (SUM _ + _) < _` mp_tac >> decide_tac) >>
  rename1 `calldata_decode_args s.vs_call_ctx.cc_calldata [tv] off = SOME decoded` >>
  `?x. decoded = [x]` by
    (qpat_x_assum `calldata_decode_args _ [tv] _ = SOME decoded` mp_tac >>
     simp_tac (srw_ss()) [calldata_decode_args_def, LET_THM, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `decoded = _` SUBST_ALL_TAC >>
  `calldata_decode_args s.vs_call_ctx.cc_calldata tvs (off + tv_abi_size tv) = NONE` by
    (qpat_x_assum `calldata_decode_args _ [tv] _ = SOME _` mp_tac >>
     qpat_x_assum `calldata_decode_args _ (tv::tvs) _ = NONE` mp_tac >>
     simp_tac (srw_ss()) [calldata_decode_args_def, LET_THM, AllCaseEqs()] >>
     metis_tac[optionTheory.NOT_NONE_SOME]) >>
  mp_tac (Q.INST [`tvs` |-> `[]`,`xs` |-> `[]`,`k` |-> `SUC (LENGTH tvs)`,
    `name` |-> `h0`,`ty` |-> `h2`,`e` |-> `h3`,`vars` |-> `t`]
    (SPEC_ALL groupedKeywordSuppliedTheory.grouped_keyword_decode_supplied)) >>
  impl_tac >- (simp[AC ADD_COMM ADD_ASSOC] >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  rename1 `compile_init_kwargs ce t _ _ hi last = ((),sb)` >>
  rename1 `fresh_vars_wrt last tail_state` >>
  `abi_embedded_static_size ce.ce_struct_fields h2 = tv_abi_size tv` by
    metis_tac[calldata_coherent_embedded_size] >>
  `LIST_REL (supplied_keyword_owner ce env last tail_state G' tn') (TAKE (LENGTH tvs) t) tvs` by
    (qpat_assum `LIST_REL _ _ _` mp_tac >> ho_match_mp_tac LIST_REL_mono >>
     rpt strip_tac >> irule supplied_keyword_owner_frame >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`G`,`s`,`sa`,`tn`] >> asm_rewrite_tac[]) >>
  first_x_assum (qspecl_then [`t`,`off + tv_abi_size tv`,`last`,`tail_state`,`G'`,`tn'`] mp_tac) >>
  impl_tac
  >- (asm_rewrite_tac[GSYM ADD_ASSOC] >> conj_tac
      >- (qpat_assum `off + (SUM _ + _) < _` mp_tac >> decide_tac) >>
      conj_tac
      >- (`off + (tv_abi_size tv + 4) = 4 + off + abi_embedded_static_size ce.ce_struct_fields h2`
            by (asm_rewrite_tac[] >> decide_tac) >>
          `SUC (LENGTH tvs) - 1 = LENGTH tvs` by decide_tac >>
          qpat_assum `SUC (LENGTH tvs) - 1 = _` (fn count =>
            qpat_assum `off + (tv_abi_size tv + 4) = _` (fn offset =>
              qpat_assum `compile_init_kwargs ce t _ _ hi last = _`
                (ACCEPT_TAC o PURE_REWRITE_RULE [count, SYM offset])))) >>
      decide_tac) >>
  disch_then (qx_choosel_then [`z`,`Hz`,`uz`] strip_assume_tac) >>
  qexistsl_tac [`z`,`Hz`,`uz`] >> simp[] >> rpt gen_tac >>
  metis_tac[gas_origin_ptr_path_append, APPEND]
QED

Theorem grouped_supplied_owners:
  LIST_REL (\(n,ty) tv. abi_decoder_coherent ce env ce.ce_struct_fields ty tv)
    args tvs /\
  LENGTH defaults <= LENGTH args /\
  n = LENGTH args - LENGTH defaults /\ k <= LENGTH defaults /\
  MAP (\(name,_,ty,e). (name,ty,e)) vars =
    MAP (\((name,ty),e). (name,ty,e)) (ZIP (DROP n args,defaults)) /\
  (!name op ty e. MEM (name,op,ty,e) vars ==>
    ?dst d oid.
      op = Var dst /\ not_fresh_at init dst /\ lookup_var dst s = SOME (n2w d) /\
      ptr_covers G tn dst s (type_memory_bytes ce ty) /\
      FLOOKUP s.vs_allocas oid = SOME (d,type_memory_bytes ce ty) /\
      d + type_memory_bytes ce ty < dimword (:256)) ==>
  LENGTH (TAKE k (DROP n tvs)) = k /\
  LIST_REL (supplied_keyword_owner ce env init s G tn) (TAKE k vars)
    (TAKE k (DROP n tvs))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `LENGTH args = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  `LENGTH (DROP n args) = LENGTH defaults /\ LENGTH (DROP n tvs) = LENGTH defaults` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  `LENGTH vars = LENGTH defaults` by
    (qpat_assum `MAP (\(name,_,ty,e). (name,ty,e)) vars = _`
       (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[LENGTH_ZIP]) >>
  `n + LENGTH defaults = LENGTH args` by decide_tac >>
  qpat_x_assum `n = _` kall_tac >>
  simp[LIST_REL_EL_EQN, LENGTH_TAKE_EQ, EL_TAKE] >>
  qx_gen_tac `j` >> strip_tac >>
  `j < LENGTH vars /\ n+j < LENGTH args` by decide_tac >>
  Cases_on `EL j vars` >> PairCases_on `r` >>
  rename1 `EL j vars = (name,op,ty,e)` >>
  `MEM (name,op,ty,e) vars` by metis_tac[EL_MEM] >>
  `EL (n+j) args = (name,ty)` by
    (qpat_assum `MAP (\(name,_,ty,e). (name,ty,e)) vars = _` (mp_tac o Q.AP_TERM `EL j`) >>
     simp[EL_MAP, EL_ZIP, EL_DROP] >>
     Cases_on `EL (j+n) args` >> asm_rewrite_tac[] >> simp[]) >>
  `abi_decoder_coherent ce env ce.ce_struct_fields ty (EL (n+j) tvs)` by
    (qpat_assum `LIST_REL _ args tvs`
       (qspec_then `n+j` mp_tac o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     simp[]) >>
  `is_abi_dynamic ce.ce_struct_fields ty = tv_abi_dynamic (EL (n+j) tvs)` by
    metis_tac[calldata_coherent_dynamic] >>
  `type_memory_size (EL (n+j) tvs) = type_memory_bytes ce ty` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  qpat_assum `!name op ty e. MEM _ vars ==> _` (drule_then strip_assume_tac) >>
  `EL j (DROP n tvs) = EL (n+j) tvs` by simp[EL_DROP, ADD_COMM] >>
  `d < dimword (:256)` by decide_tac >>
  simp[supplied_keyword_owner_def] >>
  SUBGOAL_THEN ``j+n = n+j`` SUBST1_TAC >- decide_tac >>
  asm_rewrite_tac[] >>
  qexistsl_tac [`d`,`oid`] >> simp[]
QED

(* A selected group rejects before executing any omitted default if one
   of the supplied keyword arguments has no source ABI value. *)
Theorem grouped_bad_supplied_origin:
  compile_group_dispatch_linear groups fallback sa = (jobs,sb) /\
  fn_has_code sa sb fn /\ EVERY group_entry_labels_ok groups /\
  groups = pre ++ ExternalDefaults common entries specs (4+off)::post /\
  EVERY (\group. case group of
    ExternalSingle (sel,_,_) _ => calldata_method_id s.vs_call_ctx.cc_calldata <> n2w sel
  | ExternalDefaults comp es sp _ =>
      FIND (\(sel,_,_,_). calldata_method_id s.vs_call_ctx.cc_calldata = n2w sel) es = NONE /\
      EVERY (\(_,ty,_). type_memory_bytes comp.ec_env ty < dimword (:256)) sp) pre /\
  FIND (\(n,_,_,_). calldata_method_id s.vs_call_ctx.cc_calldata = n2w n) entries =
    SOME (sel,lbl,mincd,k) /\
  EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs /\
  4 <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  mincd <= LENGTH s.vs_call_ctx.cc_calldata /\
  (common.ec_payable \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  selected_registration_resources ctx fn site lo sa s /\ s.vs_allocas = FEMPTY /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) /\
  LENGTH kw = k /\
  4+off+SUM (MAP tv_abi_size kw) < dimword (:256) /\
  calldata_decode_args s.vs_call_ctx.cc_calldata kw off = NONE /\
  (!vars st t H u.
    MAP (\(n,_,ty,e). (n,ty,e)) vars = specs /\
    (!name op ty e. MEM (name,op,ty,e) vars ==>
      ?dst d oid. op = Var dst /\ not_fresh_at st dst /\ lookup_var dst t = SOME (n2w d) /\
        ptr_covers H u dst t (type_memory_bytes common.ec_env ty) /\
        FLOOKUP t.vs_allocas oid = SOME (d,type_memory_bytes common.ec_env ty) /\
        d + type_memory_bytes common.ec_env ty < dimword (:256)) ==>
    LIST_REL (supplied_keyword_owner common.ec_env env st t H u) (TAKE k vars) kw) ==>
  ?z H u. z.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort z,H,u)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all grouped_dispatch_long_prelude >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  rename1 `compile_external_groups (Var mid) groups prep = (jobs,cut)` >>
  rename1 `selected_registration_resources ctx fn site lo prep before` >>
  rename1 `selected_registration_frame s tn before tb` >>
  rename1 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK before,Gb,tb)` >>
  qpat_x_assum `groups = pre ++ _` SUBST_ALL_TAC >>
  drule_all compile_external_groups_selected_default_origin >>
  disch_then (qspecl_then [`PG`,`Gb`] strip_assume_tac) >>
  rename1 `compile_entry_point_kwargs common.ec_env vars (4+off) k _ init = ((),done)` >>
  rename1 `compile_entry_checks mincd common.ec_payable checks = ((),init)` >>
  rename1 `selected_registration_frame before tb hit th` >>
  rename1 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (before,Gb,tb) [] (OK hit,Gh,th)` >>
  `hit.vs_call_ctx = s.vs_call_ctx` by fs[selected_registration_frame_def] >>
  mp_tac (Q.INST [`m` |-> `mincd`,`pay` |-> `common.ec_payable`,
      `sa` |-> `checks`,`sb` |-> `init`,`s` |-> `hit`,
      `tn` |-> `th`,`G` |-> `Gh`] (SPEC_ALL grouped_default_checks_pass_origin)) >>
  impl_tac >- asm_rewrite_tac[] >>
  strip_tac >>
  rename1 `selected_registration_resources ctx fn site lo init at_init` >>
  rename1 `selected_registration_frame hit th at_init ti` >>
  rename1 `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (hit,Gh,th) [] (OK at_init,Gi,ti)` >>
  `at_init.vs_call_ctx = s.vs_call_ctx` by fs[selected_registration_frame_def] >>
  `LIST_REL (supplied_keyword_owner common.ec_env env init at_init Gi ti) (TAKE k vars) kw` by
    (qpat_assum `!vars st t H u. _`
       (qspecl_then [`vars`,`init`,`at_init`,`Gi`,`ti`] mp_tac) >>
     impl_tac >- (asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
       qpat_assum `!name op ty e. MEM _ vars ==> _`
         (drule_then (qx_choosel_then [`owner_id`,`owner_var`,`owner_addr`] strip_assume_tac)) >>
       qpat_assum `!p. not_fresh_at checks p ==> _`
         (qspec_then `owner_var` (drule_then strip_assume_tac)) >>
       qexistsl_tac [`owner_var`,`owner_addr`,`owner_id`] >> asm_rewrite_tac[] >>
       fs[ptr_covers_def]) >>
     disch_then ACCEPT_TAC) >>
  drule_all compile_entry_point_kwargs_layout >> strip_tac >>
  qpat_x_assum `selected_registration_resources ctx fn site lo init at_init`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  `calldata_decode_args at_init.vs_call_ctx.cc_calldata kw off = NONE` by asm_rewrite_tac[] >>
  drule_all grouped_supplied_keywords_reject >>
  disch_then (qspec_then `PG` (qx_choosel_then [`z`,`Hz`,`uz`] strip_assume_tac)) >>
  qexistsl_tac [`z`,`Hz`,`uz`] >> asm_rewrite_tac[] >> rpt gen_tac >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspecl_then [`D`,`explicit`] assume_tac) >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (before,Gb,tb) _ _`
    (qspecl_then [`D`,`explicit`] assume_tac) >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (hit,Gh,th) _ _`
    (qspecl_then [`D`,`explicit`] assume_tac) >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (at_init,Gi,ti) _ _`
    (qspecl_then [`D`,`explicit`] assume_tac) >>
  qpat_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`before`,`Gb`,`tb`,`[]`,`Abort Revert_abort z`,`Hz`,`uz`] mp_tac) >>
  simp[listTheory.APPEND_NIL] >> disch_then irule >>
  qpat_assum `gas_origin_ptr_path _ (before,Gb,tb) _ _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`hit`,`Gh`,`th`,`[]`,`Abort Revert_abort z`,`Hz`,`uz`] mp_tac) >>
  simp[listTheory.APPEND_NIL] >> disch_then irule >>
  qpat_assum `gas_origin_ptr_path _ (hit,Gh,th) _ _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`at_init`,`Gi`,`ti`,`[]`,`Abort Revert_abort z`,`Hz`,`uz`] mp_tac) >>
  simp[listTheory.APPEND_NIL]
QED
