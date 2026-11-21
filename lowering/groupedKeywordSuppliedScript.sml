(* Execute the supplied branch of a defaulted parameter's initializer. *)
Theory groupedKeywordSupplied
Ancestors
  groupedInternalLabels groupedKeywordAddress registrationGuardPtr
  entryPtrSeamRegister selectedAcceptedDecoder selectedAcceptedInterfaces
  abiDecoderCoherence abiDecoderCounters abiDecoderCode abiDecoderReentry abiDecoderFrame
  calldataDynOwned calldataRegistrationExec decoderOriginAllocationFrame
  moduleLoweringProps fragGasOriginPtr appendStorageGhostPtr fragExec
  ptrDiscipline ptrSafeRun bodyPtrDefs loweringStateRelDefs valueEncoding vyperCalldata
  venomState emitHelperProps exprLoweringProps loweringShapeDefs compileEnv
  finite_map words arithmetic pair robustCopyTransportPtr venomMemDefs venomInstIdsProps

Theorem grouped_keyword_decode_supplied:
  0 < k /\
  compile_init_kwargs ce ((name,Var dst,ty,e)::vars) (4+off) k hi sa = ((),sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  is_abi_dynamic ce.ce_struct_fields ty = tv_abi_dynamic tv /\
  4+off < dimword (:256) /\
  calldata_decode_args s.vs_call_ctx.cc_calldata (tv::tvs) off = SOME (x::xs) /\
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
  ?src mid first last t G' tn' sc.
    compile_getelemptr_abi (Lit 4w) (is_abi_dynamic ce.ce_struct_fields ty)
      (4+off-4) CALLDATALOAD (Lit 0w) (Lit 0w) sa = (src,mid) /\
    (if is_abi_dynamic ce.ce_struct_fields ty then
       compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) mid = ((),first)
     else first = mid) /\
    compile_abi_decode_to_buf (Var dst) src CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) first = ((),last) /\
    compile_init_kwargs ce vars
      (4+off+abi_embedded_static_size ce.ce_struct_fields ty)
      (k - 1) hi last = ((),sb) /\
    fn_has_code last sb fn /\
    calldata_decode_args s.vs_call_ctx.cc_calldata tvs (off+tv_abi_size tv) = SOME xs /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    fresh_vars_wrt last t /\ ~t.vs_halted /\
    t.vs_current_bb = last.cs_current_bb /\ t.vs_inst_idx = LENGTH last.cs_current_insts /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < last.cs_next_id) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> FLOOKUP t.vs_allocas id = SOME entry) /\
    ((!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit w] /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) ==>
       n = w2n w) ==>
     !inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit w] /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,n) ==>
       n = w2n w) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    value_has_type tv x /\ val_wf tv x /\ ptr_covers G' tn' dst t (type_memory_size tv) /\
    val_in_memory tv x d t.vs_memory /\
    (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==> val_in_memory tv x d mem) /\
    abi_decode_footprint_frame ((d,type_memory_size tv)::sc) s t /\
    (!b n. MEM (b,n) sc ==> ?id. first.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (b,n)) /\
    sa.cs_next_id <= first.cs_next_id /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
    tn'.t_mem SUBSET tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_code = s.vs_code /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_logs = s.vs_logs /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_fmp = s.vs_fmp /\
    t.vs_gas_readings = s.vs_gas_readings /\ t.vs_initial_fmp = s.vs_initial_fmp
Proof
  strip_tac >>
  drule_all compile_init_kwargs_supplied_intervals >> strip_tac >>
  qabbrev_tac `dyn = is_abi_dynamic ce.ce_struct_fields ty` >>
  qabbrev_tac `delta = w2n (cd_word s.vs_call_ctx.cc_calldata (4+off))` >>
  qabbrev_tac `srcpos = if dyn then (4+delta) MOD dimword (:256) else 4+off` >>
  mp_tac (Q.INST [`cd` |-> `s.vs_call_ctx.cc_calldata`, `s` |-> `s`,
    `dyn` |-> `dyn`, `delta` |-> `delta`, `ofs` |-> `off`, `srcpos` |-> `srcpos`,
    `tv` |-> `tv`, `tvs` |-> `tvs`, `x` |-> `x`, `xs` |-> `xs`]
    selected_slot_source_input) >>
  impl_tac >- simp[Abbr `srcpos`, Abbr `delta`, Abbr `dyn`] >>
  strip_tac >>
  `4 + off - 4 = off` by decide_tac >>
  fs[] >>
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
    (qpat_assum `srcpos = _ + 4` (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
     qpat_assum `eval_operand src addr = SOME _` mp_tac >>
     simp_tac bool_ss [ADD_COMM]) >>
  `dyn ==> ~(n2w srcpos : bytes32 <+ 4w)` by
    (strip_tac >>
     `4 <= srcpos` by
       (qpat_assum `srcpos = _ + 4` (fn th => PURE_ONCE_REWRITE_TAC[th]) >> decide_tac) >>
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
  `cd_decode F ready.vs_call_ctx.cc_calldata tv (w2n (n2w srcpos : bytes32)) = SOME x` by
    (qpat_assum `w2n (n2w srcpos : bytes32) = srcpos` (pure_once_rewrite_tac o single) >>
     qpat_assum `ready.vs_call_ctx = s.vs_call_ctx` (pure_once_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  drule selected_argument_decoder_accepts >>
  simp_tac bool_ss [selected_decoder_accepts_def] >>
  disch_then (qspecl_then [`first`,`last`,`last`,`ctx`,`fn`,`site`,`src`,
    `dst`,`ready`,`n2w srcpos`,`d`,`oid`,`d`,`type_memory_size tv`,
    `Gr`,`tr`,`lo`,`PG`,`x`] mp_tac) >>
  impl_tac >-
    (asm_simp_tac (srw_ss()) [eval_operand_def] >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> _`
       (qspecl_then [`id`,`(q,k')`] (drule_then assume_tac)) >>
     fs[NOT_LESS_EQUAL]) >>
  disch_then (qx_choosel_then [`t`,`sc`,`G'`,`tn'`] strip_assume_tac) >>
  suspend "finish"
QED

Resume grouped_keyword_decode_supplied[finish]:
  qpat_assum `vars_pc_only addr ready`
    (strip_assume_tac o SIMP_RULE (srw_ss())
       [vars_pc_only_def, venom_state_component_equality]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK t,G',tn')` by
    (rpt gen_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _`
       (qspecl_then [`D`,`explicit`] (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`addr`,`Ga`,`ta`,`[]`,`OK ready`,`Gr`,`tr`] mp_tac) >>
     asm_rewrite_tac[listTheory.APPEND] >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`ready`,`Gr`,`tr`,`[]`,`OK t`,`G'`,`tn'`] mp_tac) >>
     asm_rewrite_tac[listTheory.APPEND]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t /\
    t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp` by
    (mp_tac (Q.INST [`s` |-> `s`,`t` |-> `t`,`fn` |-> `fn`,`H` |-> `G'`,
       `u` |-> `tn'`,`marks` |-> `[]`] (SPEC_ALL decoder_origin_path_room)) >>
     asm_simp_tac (srw_ss()) []) >>
  `first.cs_next_id <= last.cs_next_id` by
    (`abi_decode_source_opcode CALLDATALOAD` by
       simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
     drule_all abi_decoder_to_buf_code >>
     disch_then (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [abi_decoder_code_def])) >>
  `tn'.t_mem SUBSET tn.t_mem` by
    (qpat_assum `tn'.t_mem SUBSET tr.t_mem` mp_tac >>
     qpat_assum `tr.t_mem = ta.t_mem` (pure_rewrite_tac o single) >>
     qpat_assum `ta.t_mem = tn.t_mem` (pure_rewrite_tac o single) >>
     simp_tac bool_ss []) >>
  `!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
    FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)` by
    (gen_tac >> strip_tac >>
     `not_fresh_at mid p` by
       (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     `not_fresh_at first p` by
       (irule not_fresh_at_mono >> qexists_tac `mid` >> simp[]) >>
     qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `p` drule) >>
     qpat_assum `!p. not_fresh_at mid p ==> _` (qspec_then `p` drule) >>
     qpat_assum `!p. not_fresh_at first p ==> _` (qspec_then `p` drule) >>
     qpat_assum `!op. abi_decoder_operand_live first.cs_next_var op ==> _`
       (qspec_then `Var p` mp_tac) >>
     simp_tac (srw_ss()) [calldata_operand_live_not_fresh, eval_operand_def] >>
     asm_rewrite_tac[] >>
     rpt strip_tac >>
     TRY (MAP_EVERY (fn pat => qpat_assum pat (pure_rewrite_tac o single))
           [`lookup_var p t = lookup_var p ready`,
            `lookup_var p ready = lookup_var p addr`,
            `lookup_var p addr = lookup_var p s`] >> REFL_TAC) >>
     TRY (MAP_EVERY (fn pat => qpat_assum pat (pure_rewrite_tac o single))
           [`FLOOKUP G' p = FLOOKUP Gr p`,`FLOOKUP Gr p = FLOOKUP Ga p`,
            `FLOOKUP Ga p = FLOOKUP G p`] >> REFL_TAC) >>
     `op_taint tn' (Var p) = op_taint tr (Var p)` by
       (simp_tac (srw_ss()) [op_taint_def] >>
        qpat_assum `FLOOKUP tn'.t_var p = FLOOKUP tr.t_var p`
          (pure_rewrite_tac o single) >> REFL_TAC) >>
     MAP_EVERY (fn pat => qpat_assum pat (pure_rewrite_tac o single))
       [`op_taint tn' (Var p) = op_taint tr (Var p)`,
        `op_taint tr (Var p) = op_taint ta (Var p)`,
        `op_taint ta (Var p) = op_taint tn (Var p)`] >> REFL_TAC) >>
  `abi_decode_footprint_frame ((d,type_memory_size tv)::sc) s t` by
    (irule abi_decode_footprint_frame_trans >> qexists_tac `ready` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     pure_rewrite_tac[abi_decode_footprint_frame_def] >>
     MAP_EVERY (fn pat => qpat_assum pat (pure_rewrite_tac o single))
       [`ready.vs_memory = addr.vs_memory`,`addr.vs_memory = s.vs_memory`,
        `ready.vs_call_ctx = s.vs_call_ctx`,
        `ready.vs_data_section = addr.vs_data_section`,
        `addr.vs_data_section = s.vs_data_section`] >> simp_tac bool_ss []) >>
  `!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
    FLOOKUP t.vs_allocas id = SOME entry` by
    (gen_tac >> Cases >> strip_tac >>
     qpat_assum `!id q k. FLOOKUP ready.vs_allocas id = SOME (q,k) ==> _`
       (qspecl_then [`id`,`q`,`r`] mp_tac) >> simp[]) >>
  `!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < last.cs_next_id` by
    (rpt gen_tac >> strip_tac >> CCONTR_TAC >>
     qpat_assum `!id. id < first.cs_next_id \/ _ ==> _` (qspec_then `id` mp_tac) >>
     simp[NOT_LESS] >> strip_tac >>
     qpat_assum `!id entry. FLOOKUP ready.vs_allocas id = SOME entry ==> _`
       (qspecl_then [`id`,`entry`] mp_tac) >> simp[] >> decide_tac) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_assum `ready.vs_alloca_next = s.vs_alloca_next`
       (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' t) ==>
    !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s` by
    (gen_tac >> strip_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] (OK t,G',tn')`
       (qspecl_then [`D`,`K F`] (assume_tac)) >>
     irule selected_zero_path_ptr_pullback >> conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!label bb. lookup_block label _ = _ ==> _`
           (qspecl_then [`lbl`,`bb`] (drule_then ACCEPT_TAC))) >>
     qexistsl_tac [`G'`,`K F`,`t`,`tn'`] >> asm_rewrite_tac[]) >>
  `(!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit w] /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) ==>
       n = w2n w) ==>
     !inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit w] /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,n) ==>
       n = w2n w` by
    (strip_tac >> rpt gen_tac >> strip_tac >>
     Cases_on `inst.inst_id < first.cs_next_id \/ last.cs_next_id <= inst.inst_id`
     >- (qpat_assum `!id. id < first.cs_next_id \/ _ ==> _`
           (qspec_then `inst.inst_id` (drule_then assume_tac)) >>
         `FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n)` by
           metis_tac[] >>
         MAP_EVERY (fn pat => qpat_assum pat mp_tac)
           [`!i w b n. MEM i (fn_insts fn) /\ _ /\ _ /\
               FLOOKUP s.vs_allocas i.inst_id = _ ==> _`,
            `MEM inst (fn_insts fn)`,`inst.inst_opcode = ALLOCA`,
            `inst.inst_operands = [Lit w]`,`FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n)`] >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     `first.cs_next_id <= inst.inst_id /\ inst.inst_id < last.cs_next_id` by decide_tac >>
     qpat_assum `!id q k. first.cs_next_id <= id /\ id < last.cs_next_id /\
         FLOOKUP t.vs_allocas id = SOME (q,k) ==> _`
       (qspecl_then [`inst.inst_id`,`b`,`n`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     strip_tac >>
     rename1 `witness.inst_id = inst.inst_id` >>
     `witness = inst` by metis_tac[venomInstIdsPropsTheory.fn_inst_ids_distinct_inj] >>
     MAP_EVERY (fn pat => qpat_assum pat mp_tac)
       [`n = 32`,`inst.inst_operands = [Lit w]`,`witness.inst_operands = [Lit 32w]`,
        `witness = inst`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]) >>
  qexistsl_tac [`src`,`mid`,`first`,`last`,`t`,`G'`,`tn'`,`sc`] >>
  asm_rewrite_tac[] >>
  qpat_assum `dyn = tv_abi_dynamic tv` (pure_once_rewrite_tac o single o GSYM) >>
  asm_rewrite_tac[]
QED

(* The decoder's scratch allocations are newer than every completed owner. *)
Finalise grouped_keyword_decode_supplied

Theorem grouped_keyword_decode_owner_frame:
  alloca_inv t /\
  FLOOKUP t.vs_allocas oid = SOME (b,n) /\
  FLOOKUP t.vs_allocas did = SOME (d,sz) /\ oid <> did /\
  (!q k. MEM (q,k) scratch ==> ?id. oid < id /\
    FLOOKUP t.vs_allocas id = SOME (q,k)) /\
  abi_decode_footprint_frame ((d,sz)::scratch) s t /\
  tn'.t_mem SUBSET tn.t_mem /\ val_wf tv v /\ val_footprint tv v <= n /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v b mem) ==>
  !mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==> val_in_memory tv v b mem
Proof
  strip_tac >>
  qpat_assum `alloca_inv t`
    (strip_assume_tac o REWRITE_RULE [alloca_inv_def, allocas_non_overlapping_def]) >>
  `!id q k. oid <> id /\ FLOOKUP t.vs_allocas id = SOME (q,k) ==>
    b + val_footprint tv v <= q \/ q + k <= b` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!a1 a2 b1 sz1 b2 sz2. _`
       (qspecl_then [`oid`,`id`,`b`,`n`,`q`,`k`]
         (fn th => mp_tac (MATCH_MP th
           (LIST_CONJ [ASSUME ``oid <> (id:num)``,
             ASSUME ``FLOOKUP t.vs_allocas oid = SOME (b,n)``,
             ASSUME ``FLOOKUP t.vs_allocas id = SOME (q,k)``])))) >>
     qpat_assum `val_footprint tv v <= n` mp_tac >> decide_tac) >>
  `abi_footprint_disjoint b (val_footprint tv v) ((d,sz)::scratch)` by
    (simp_tac bool_ss [abi_footprint_disjoint_def, listTheory.MEM, pairTheory.PAIR_EQ] >>
     rpt gen_tac >> disch_then (DISJ_CASES_THEN strip_assume_tac)
     >- (gvs[] >> metis_tac[ADD_COMM]) >>
     qpat_assum `!q k. MEM (q,k) scratch ==> _`
       (qspecl_then [`d'`,`sz'`] (drule_then strip_assume_tac)) >>
     `oid <> id` by decide_tac >> metis_tac[ADD_COMM]) >>
  `mem_bytes_at b (val_footprint tv v) t.vs_memory =
    mem_bytes_at b (val_footprint tv v) s.vs_memory` by
    (qpat_assum `abi_decode_footprint_frame _ s t`
       (strip_assume_tac o REWRITE_RULE [abi_decode_footprint_frame_def]) >>
     first_x_assum irule >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`p` |-> `b`,`oldmem` |-> `s.vs_memory`,
    `newmem` |-> `t.vs_memory`,`oldtaint` |-> `tn.t_mem`,
    `newtaint` |-> `tn'.t_mem`] (SPEC_ALL calldata_member_robust_window_frame)) >>
  asm_rewrite_tac[]
QED
