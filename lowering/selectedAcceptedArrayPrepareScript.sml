(* The nonbulk parent reaches an installed header on its actual calldata. *)
Theory selectedAcceptedArrayPrepare
Ancestors
  selectedAcceptedArrayInit calldataRecursiveProducers calldataSourceDecisions
  calldataSourceCorrespondence calldataSourceSize abiDecoderRecursiveArray
  abiDecoderRecursiveLoopLayout abiDecoderArraySetupInputs abiDecoderCounters abiDecoderArrayInit
  abiDecoderExecution abiDecoderReentry abiDecoderCoherence abiDecoderContract
  entryDecoderStateFrame calldataDynOwned exprLowering emitHelperProps
  fragGasOriginPtr fragExec venomExecSemantics venomState venomInst
  vyperCalldata valueEncoding words finite_map arithmetic list pred_set

Theorem selected_nonbulk_static_layout[local]:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray ei asz msz dyn maxn ==>
  ei = type_to_abi_dec_info sf ce ty /\ asz = tv_abi_size tv /\
  msz = type_memory_size tv /\ dyn = tv_abi_dynamic tv /\
  dec_info_needs_clamp ei = tv_needs_clamp tv /\
  dec_info_needs_offset ei = tv_abi_dynamic tv
Proof
  simp[type_to_abi_dec_info_def] >> strip_tac >>
  drule calldata_coherent_dynamic >> drule calldata_coherent_clamp >>
  drule calldata_coherent_offset >> drule calldata_coherent_embedded_size >>
  drule abi_decoder_coherent_header >>
  gvs[abi_decoder_header_def]
QED

Theorem selected_nonbulk_source_count[local]:
  ~(~tv_abi_dynamic tv /\ ~tv_needs_clamp tv) /\
  cd_decode F cd (ArrayTV tv (Dynamic maxn)) a = SOME x ==>
  ?n vs. n = w2n (cd_word cd a) /\ n <= maxn /\ x = ArrayV (DynArrayV vs) /\
    cd_decode_elems F cd tv (cd_at F a 32) 0 n = SOME vs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `cd_decode F _ _ _ = _` mp_tac >>
  simp[cd_decode_def] >>
  Cases_on `maxn < w2n (cd_word cd a)` >> simp[] >>
  Cases_on `cd_decode_elems F cd tv (cd_at F a 32) 0 (w2n (cd_word cd a))` >> simp[]
QED

Theorem selected_nonbulk_counter_bounds[local]:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn asz st =
    ((ip,cnt),loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = (labels,st0) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    ei asz msz st0 = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
    ei middle = ((),st1) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) st1 = ((),last) /\
  FST ops = Var iv /\ last.cs_next_var <= limit.cs_next_var ==>
  st.cs_next_var <= loop_st.cs_next_var /\
  st0.cs_next_var = loop_st.cs_next_var + 4 /\
  loop_st.cs_next_var + 4 <= middle.cs_next_var /\
  middle.cs_next_var <= st1.cs_next_var /\
  st1.cs_next_var < last.cs_next_var /\
  loop_st.cs_next_var + 3 < limit.cs_next_var /\ st1.cs_next_var < limit.cs_next_var
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> simp[abi_decode_position_header_delta_def] >> strip_tac >>
  drule abi_decode_array_element_setup_operands >> strip_tac >>
  drule abi_decoder_variable_counter >> strip_tac >>
  qpat_assum `FST ops = Var iv` (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >> decide_tac
QED

Theorem selected_header_distinct[local]:
  abi_decoder_operand_live live (Var q) ==>
  ALL_DISTINCT [q; STRING #"%" (toString live); STRING #"%" (toString (live+1));
    STRING #"%" (toString (live+2)); STRING #"%" (toString (live+3))]
Proof
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    ASCIInumbersTheory.toString_11] >>
  strip_tac >> rpt conj_tac >> first_x_assum irule >> decide_tac
QED

Theorem selected_header_generated_names[local]:
  !live back bound. live+3 < bound /\ live+4 <= back /\ back < bound ==>
  !y. MEM y [STRING #"%" (toString back); STRING #"%" (toString live);
    STRING #"%" (toString (live+1)); STRING #"%" (toString (live+2));
    STRING #"%" (toString (live+3))] ==>
    ~abi_decoder_operand_live live (Var y) /\
    ?k. y = STRING #"%" (toString k) /\ k < bound
Proof
  rpt gen_tac >> strip_tac >> simp[] >> rpt strip_tac >>
  gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    ASCIInumbersTheory.toString_11] >> decide_tac
QED

Theorem selected_nonbulk_parent_to_header:
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_header ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) = DecDynArray ei asz msz dyn maxn /\
  (dyn \/ dec_info_needs_clamp ei) /\
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei asz msz dyn maxn) st = ((),last) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  last.cs_next_var <= limit.cs_next_var /\ unit_alloca_budget ctx < dimword (:256) /\
  (last.cs_current_insts = [] ==> !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  eval_operand src s = SOME p /\ eval_operand (Var root) s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  (!id b k. st.cs_next_id <= id /\ id < last.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (b,k) ==>
    k = 32 /\ b < dimword (:256) /\ b+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d /\ d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= base_addr+cap /\
  d+type_memory_size (ArrayTV tv (Dynamic maxn)) < dimword (:256) /\
  ptr_covers G tn root s (type_memory_size (ArrayTV tv (Dynamic maxn))) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  fresh_vars_wrt limit s /\ allocas_from lower s /\ lower <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  cd_decode F s.vs_call_ctx.cc_calldata (ArrayTV tv (Dynamic maxn)) (w2n p) = SOME x ==>
  ?ip cnt guard_st header_st loop_st labels st0 ops middle st1 body_bb exit_bb n vs t h H u q b.
    ei = type_to_abi_dec_info sf ce ty /\ asz = tv_abi_size tv /\
    msz = type_memory_size tv /\ dyn = tv_abi_dynamic tv /\
    dec_info_needs_offset ei = tv_abi_dynamic tv /\
    n = w2n (cd_word s.vs_call_ctx.cc_calldata (w2n p)) /\ n <= maxn /\
    maxn < dimword (:256) /\
    type_memory_size (ArrayTV tv (Dynamic maxn)) = 32+maxn*msz /\
    32+n*msz <= type_memory_size (ArrayTV tv (Dynamic maxn)) /\
    x = ArrayV (DynArrayV vs) /\
    cd_decode_elems F h.vs_call_ctx.cc_calldata tv (cd_at F (w2n p) 32) 0 n = SOME vs /\
    abi_decode_array_loop_init (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w) maxn asz st =
      ((ip,cnt),loop_st) /\
    abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn asz st = ((),guard_st) /\
    abi_decode_array_header (Var root) src CALLDATALOAD guard_st = (cnt,header_st) /\
    abi_decode_index_init header_st = (ip,loop_st) /\
    abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = (labels,st0) /\
    abi_decode_array_element_setup ip src (Var root) CALLDATALOAD (Lit 0w) (Lit 0w) ei asz msz st0 =
      (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
      ei middle = ((),st1) /\
    abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) st1 = ((),last) /\
    st.cs_next_id <= header_st.cs_next_id /\ header_st.cs_next_id < middle.cs_next_id /\
    middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= last.cs_next_id /\
    header_st.cs_next_id < last.cs_next_id /\ header_st.cs_next_id <> oid /\
    fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
    fn_has_code st0 middle fn /\ fn_has_code middle st1 fn /\ fn_has_code st1 last fn /\
    lookup_block (FST labels) fn.fn_blocks = SOME
      <|bb_label := FST labels; bb_instructions :=
        abi_decode_header_insts (loop_st.cs_next_id+1) ip src CALLDATALOAD
          (STRING #"%" (toString loop_st.cs_next_var))
          (STRING #"%" (toString (loop_st.cs_next_var+1)))
          (STRING #"%" (toString (loop_st.cs_next_var+2)))
          (STRING #"%" (toString (loop_st.cs_next_var+3)))
          (FST (SND labels)) (SND (SND labels))|> /\
    (!bb. lookup_block (FST labels) fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    lookup_block (FST (SND labels)) fn.fn_blocks = SOME body_bb /\
    phi_prefix_length body_bb.bb_instructions = 0 /\
    st0.cs_current_bb = FST (SND labels) /\ st0.cs_current_insts = [] /\
    lookup_block st1.cs_current_bb fn.fn_blocks = SOME
      <|bb_label := st1.cs_current_bb; bb_instructions := st1.cs_current_insts ++
        abi_decode_backedge_insts st1.cs_next_id (STRING #"%" (toString st0.cs_next_var))
          (STRING #"%" (toString st1.cs_next_var)) ip (FST labels)|> /\
    (st1.cs_current_insts = [] ==> !bb. lookup_block st1.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    FST ops = Var (STRING #"%" (toString st0.cs_next_var)) /\
    lookup_block (SND (SND labels)) fn.fn_blocks = SOME exit_bb /\
    phi_prefix_length exit_bb.bb_instructions = 0 /\
    last.cs_current_bb = SND (SND labels) /\ last.cs_current_insts = [] /\
    st.cs_next_var <= loop_st.cs_next_var /\ st0.cs_next_var = loop_st.cs_next_var+4 /\
    st0.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var <= st1.cs_next_var /\
    st1.cs_next_var < last.cs_next_var /\
    abi_decoder_operand_live loop_st.cs_next_var src /\
    abi_decoder_operand_live loop_st.cs_next_var (Var root) /\
    abi_decoder_operand_live loop_st.cs_next_var ip /\
    ALL_DISTINCT [q; STRING #"%" (toString loop_st.cs_next_var);
      STRING #"%" (toString (loop_st.cs_next_var+1));
      STRING #"%" (toString (loop_st.cs_next_var+2));
      STRING #"%" (toString (loop_st.cs_next_var+3))] /\
    (!y. MEM y [STRING #"%" (toString st1.cs_next_var);
      STRING #"%" (toString loop_st.cs_next_var);
      STRING #"%" (toString (loop_st.cs_next_var+1));
      STRING #"%" (toString (loop_st.cs_next_var+2));
      STRING #"%" (toString (loop_st.cs_next_var+3))] ==>
      ~abi_decoder_operand_live loop_st.cs_next_var (Var y) /\
      ?k. y = STRING #"%" (toString k) /\ k < limit.cs_next_var) /\
    (!op. abi_decoder_operand_live loop_st.cs_next_var op ==>
      abi_decoder_operand_live st0.cs_next_var op) /\
    abi_decoder_operand_live middle.cs_next_var (FST ops) /\
    abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
    (!op. abi_decoder_operand_live st0.cs_next_var op ==>
      abi_decoder_operand_live middle.cs_next_var op) /\
    (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)) /\
    run_inst_seq (emitted_insts st loop_st) s = OK t /\
    h = jump_to (FST labels) (t with vs_inst_idx := LENGTH loop_st.cs_current_insts) /\
    ~h.vs_halted /\ h.vs_current_bb = FST labels /\ h.vs_inst_idx = 0 /\
    ip = Var q /\ lookup_var q h = SOME (n2w b) /\ eval_operand cnt h = SOME (n2w n) /\
    FLOOKUP h.vs_allocas header_st.cs_next_id = SOME (b,32) /\
    b+32 < dimword (:256) /\ b+32 <= h.vs_alloca_next /\
    (b+32 <= base_addr \/ base_addr+cap <= b) /\
    mload b h = 0w /\ ptr_covers H u q h 32 /\
    ptr_covers H u root h (type_memory_size (ArrayTV tv (Dynamic maxn))) /\
    mem_word_at d h.vs_memory = n2w n /\
    (!mem. mem_agree_outside u.t_mem h.vs_memory mem ==> mem_word_at d mem = n2w n) /\
    eval_operand src h = SOME p /\ abi_decode_load CALLDATALOAD p h = n2w n /\
    (!i. b <= i /\ i < b+32 ==> i NOTIN u.t_mem) /\
    op_taint u src = {} /\ op_prov H src = NONE /\
    op_taint u cnt = {} /\ op_prov H cnt = NONE /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op h = eval_operand op s) /\
    (!y. not_fresh_at st y ==> FLOOKUP H y = FLOOKUP G y /\ FLOOKUP u.t_var y = FLOOKUP tn.t_var y) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    abi_decode_footprint_frame [(d,32);(b,32)] s h /\ entry_decoder_obs s h /\
    alloca_inv h /\ alloca_frontier_inv ctx fn site h /\ allocas_from lower h /\
    s.vs_alloca_next <= h.vs_alloca_next /\ lower <= h.vs_alloca_next /\
    FLOOKUP h.vs_allocas oid = SOME (base_addr,cap) /\
    (!id b k. FLOOKUP s.vs_allocas id = SOME (b,k) ==> FLOOKUP h.vs_allocas id = SOME (b,k)) /\
    (!id. id <> header_st.cs_next_id ==> FLOOKUP h.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!id b k. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP h.vs_allocas id = SOME (b,k) ==>
      k = 32 /\ b < dimword (:256) /\ b+32 <= h.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    fresh_vars_wrt limit h /\
    (!fuel r. run_from fuel ctx fn h = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn h ==> mem_safe_run fuel' ctx fn s)) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG) (s,G,tn) [] (OK h,H,u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `span = type_memory_size (ArrayTV tv (Dynamic maxn))` >>
  drule_all selected_nonbulk_static_layout >> strip_tac >>
  `~(~tv_abi_dynamic tv /\ ~tv_needs_clamp tv)` by
    (qpat_assum `dyn \/ dec_info_needs_clamp ei` mp_tac >>
     qpat_assum `dyn = tv_abi_dynamic tv` mp_tac >>
     qpat_assum `dec_info_needs_clamp ei = tv_needs_clamp tv` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  drule_all selected_nonbulk_source_count >>
  disch_then (qx_choose_then `n` (qx_choose_then `vs` (map_every assume_tac o CONJUNCTS))) >>
  `abi_decode_load CALLDATALOAD p s = n2w n` by
    asm_rewrite_tac[calldata_decode_load_word,n2w_w2n] >>
  `maxn < dimword (:256)` by metis_tac[abi_decoder_coherent_array_capacity,abiDecoderCoherenceTheory.array] >>
  `span = 32+maxn*msz /\ 32 <= span /\ 32+n*msz <= span` by
    (qpat_assum `n <= maxn` mp_tac >> qpat_assum `msz = _` mp_tac >>
     qpat_assum `Abbrev (span = _)` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[markerTheory.Abbrev_def, type_memory_size_def, LE_MULT_RCANCEL]) >>
  drule_all calldata_nonbulk_parent_shell_conditional >>
  disch_then (qx_choose_then `ip` (qx_choose_then `cnt` (qx_choose_then `guard_st`
    (qx_choose_then `header_st` (qx_choose_then `loop_st` (qx_choose_then `labels`
    (qx_choose_then `st0` (qx_choose_then `ops` (qx_choose_then `middle`
    (qx_choose_then `st1` (qx_choose_then `body_bb` (qx_choose_then `exit_bb`
      (map_every assume_tac o CONJUNCTS))))))))))))) >>
  drule_all selected_nonbulk_counter_bounds >> strip_tac >>
  `loop_st.cs_next_var <= limit.cs_next_var /\ header_st.cs_next_id < last.cs_next_id /\
   st0.cs_next_var <= middle.cs_next_var /\ loop_st.cs_next_var+4 <= st1.cs_next_var`
    by decide_tac >>
  drule calldata_index_init_result_live >> disch_tac >>
  PairCases_on `labels` >>
  rule_assum_tac (REWRITE_RULE [pairTheory.FST,pairTheory.SND]) >>
  drule_all selected_array_init_to_header >>
  disch_then (qspec_then `PG` (qx_choose_then `t` (qx_choose_then `h`
    (qx_choose_then `H` (qx_choose_then `u` (qx_choose_then `q` (qx_choose_then `b`
      (map_every assume_tac o CONJUNCTS)))))))) >>
  qexistsl_tac [`ip`,`cnt`,`guard_st`,`header_st`,`loop_st`,`(labels0,labels1,labels2)`,
    `st0`,`ops`,`middle`,`st1`,`body_bb`,`exit_bb`,`n`,`vs`,`t`,`h`,`H`,`u`,`q`,`b`] >>
  simp_tac bool_ss [pairTheory.FST,pairTheory.SND] >>
  qpat_assum `Abbrev (span = _)`
    (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `entry_decoder_obs _ _`
        (SUBST1_TAC o cj 4 o REWRITE_RULE [entry_decoder_obs_def]) >>
      first_assum ACCEPT_TAC)
  >- decide_tac
  >- (qpat_assum `lookup_block labels0 fn.fn_blocks = SOME _`
        (fn th => simp[NoAsms, th, abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def]))
  >- (qpat_assum `lookup_block st1.cs_current_bb fn.fn_blocks = SOME _`
        (fn th => simp[NoAsms, th, abi_decode_backedge_insts_def, phi_prefix_length_def, mk_inst_def]))
  >- (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (irule selected_header_distinct >>
      qpat_assum `ip = Var q` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC)
  >- (qspecl_then [`loop_st.cs_next_var`,`st1.cs_next_var`,`limit.cs_next_var`]
        mp_tac selected_header_generated_names >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC)
  >- (rpt strip_tac >> irule abi_decoder_operand_live_mono >>
      qexists_tac `loop_st.cs_next_var` >> conj_tac >> (first_assum ACCEPT_TAC ORELSE decide_tac))
  >- (qpat_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op h = _`
        (qspec_then `src` mp_tac) >>
      qpat_assum `eval_operand src s = SOME p` (fn th => simp[NoAsms,th]) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC)
  >> qpat_assum `!fuel r. run_from fuel ctx fn h = r /\ _ ==> _`
       (ACCEPT_TAC o SIMP_RULE bool_ss [])
QED
