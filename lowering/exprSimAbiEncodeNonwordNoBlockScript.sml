Theory exprSimAbiEncodeNonwordNoBlock
Ancestors
  loweringStateRelDefs valueEncodingDefs
  exprSimAbiEncodeConcreteBuiltinWrappers exprSimAbiEncodeConcreteBody
  exprSimAbiEncodeConcreteCompose exprSimAbiEncodeConcreteWrappers
  exprSimAbiEncodeNoBlockBoundary exprSimAbiEncodeNoBlockSafety exprSimAbiEncodeExecution
  exprSimAbiEncodeProducerExecution exprSimAbiEncodeRelabelResources
  abiEncodeWindowBuiltin abiEncoderWindowContract abiDecoderContract abiDecoderLoop
  exprSimAbiEncodeOpenSetup exprSimAbiEncodeConcreteResources
  abiBuiltinEncodeCode abiBuiltinEncodeSetup abiBuiltinEncodeContext
  abiEncoderCounters abiDecoderReentry abiEncoderAdmissible abiEncoderSourceInvoke
  emitHelperProps exprLoweringProps compileEnv venomState list words
  exprSimAbiEncodeEmptySource abiEncoderLeaves abiEncoderWindowLeaves
  abiEncoderPrimitiveEffect abiEncoderExtendSim abiEncoderRegisteredEffect
  abiEncoderWindowLookup abiEncoderWindow valueEncodingProofs venomExecSemantics
  exprSimAbiEncodeNoBlockFrame exprSimAbiEncodeFramedBuiltin exprSimAbiEncodeExecFrame
  emitHelper venomInst rich_list context exprSimAbiEncodeStateTransport exprSimAbiEncodeObserverEntry

(* Raw sequence composition deliberately retains the index-normalized endpoint. *)
Theorem abi_encode_concrete_three_sequences:
  inst_extends st ready /\ inst_extends ready body_end /\
  inst_extends body_end final /\
  run_inst_seq (emitted_insts st ready) initial = OK setup_raw /\
  run_inst_seq (emitted_insts ready body_end)
    (setup_raw with vs_inst_idx := LENGTH ready.cs_current_insts) = OK body_raw /\
  run_inst_seq (emitted_insts body_end final)
    (body_raw with vs_inst_idx := LENGTH body_end.cs_current_insts) = OK finish_raw /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts ready body_end) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts body_end final) ==>
  ?raw. run_inst_seq (emitted_insts st final) initial = OK raw /\
    (raw with vs_inst_idx := LENGTH final.cs_current_insts) =
    (finish_raw with vs_inst_idx := LENGTH final.cs_current_insts)
Proof
  strip_tac >>
  `inst_extends st body_end` by metis_tac[inst_extends_trans] >>
  `emitted_insts st body_end = emitted_insts st ready ++ emitted_insts ready body_end /\
   emitted_insts st final = emitted_insts st body_end ++ emitted_insts body_end final` by
    (conj_tac >> irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?r. run_inst_seq (emitted_insts st body_end) initial = OK r /\
    (r with vs_inst_idx := LENGTH body_end.cs_current_insts) =
    (body_raw with vs_inst_idx := LENGTH body_end.cs_current_insts)` by
    (asm_rewrite_tac[] >> irule abi_encode_run_append_normalized >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`LENGTH ready.cs_current_insts`, `setup_raw`] >>
     asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >> irule abi_encode_run_append_normalized >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`LENGTH body_end.cs_current_insts`, `r`] >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem abi_encode_high_vars_fresh[local]:
  (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s) /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  simp_tac (srw_ss()) [fresh_vars_wrt_def, not_fresh_at_def,
    lookup_var_def, finite_mapTheory.FLOOKUP_DEF] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `STRING #"%" (toString n)` mp_tac) >>
  simp[] >> metis_tac[]
QED

(* The zero-length source word need not lie below the allocation frontier. *)
Theorem abi_encode_empty_copy_concrete:
  compile_abi_encode_to_buf dst src (AbiCopy 0) st = (out,st') /\
  abi_encode_empty_window_pre ctx func st st' dst src at av a d s ==>
  ?raw. abi_encode_concrete_result ctx func st st' out at av d s raw
Proof
  simp_tac bool_ss [abi_encode_empty_window_pre_def] >> strip_tac >>
  `!i b n. i IN window_alloca_sites func (frag_ids st st') /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    (simp[window_alloca_sites_def] >> metis_tac[]) >>
  pop_assum (mk_asm "sizes") >>
  drule abi_encode_copy_code >> strip_tac >>
  fs[abi_encoder_window_copy_iff] >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  `LENGTH (enc at av) = 0` by metis_tac[LENGTH_mem_bytes_at_proof] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `d < dimword (:256)` by decide_tac >>
  `eval_operand (Lit (n2w 0)) s = SOME (n2w 0)` by simp[eval_operand_def] >>
  `eval_operand src s = SOME (n2w (w2n a))` by simp[] >>
  `w2n a < dimword (:256) /\ 0 < dimword (:256)` by simp[wordsTheory.w2n_lt, wordsTheory.dimword_def] >>
  drule_all window_emit_copy_run >> strip_tac >>
  `abi_encoder_extend_sim ctx func s
    ((mcopy d (w2n a) 0 s) with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_run_sequence_extend_sim >>
     (conj_tac >- first_assum ACCEPT_TAC) >> qexists_tac `st` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_encoder_registered_effect (window_alloca_sites func (frag_ids st st'))
    [(d,0)] s ((mcopy d (w2n a) 0 s) with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `mcopy d (w2n a) 0 s` >>
     simp[abi_encoder_registered_output_copy, abi_encoder_registered_inst_idx]) >>
  `abi_encoder_registered_effect (frag_ids st st') [(d,0)] s
    ((mcopy d (w2n a) 0 s) with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`window_alloca_sites func (frag_ids st st')`, `[(d,0)]`] >>
     simp[window_alloca_sites_subset]) >>
  qexists_tac `mcopy d (w2n a) 0 s` >>
  simp_tac bool_ss [abi_encode_concrete_result_def] >>
  asm_rewrite_tac[] >>
  conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
  reverse conj_tac
  >- simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def] >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  simp[eval_operand_def, mcopy_mem_bytes_at_same, abi_encoder_extend_sim_sim] >>
  mp_tac (Q.INST [`d` |-> `d`, `sb` |-> `w2n (a:256 word)`, `n` |-> `0`,
    `ix` |-> `LENGTH st'.cs_current_insts`] window_copy_state_resources) >>
  simp[] >> strip_tac >> conj_tac >- asm "sizes" ACCEPT_TAC >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem abi_encode_setup_empty_pre[local]:
  let allocated = abi_builtin_allocate_state site outsz initial in
  abi_builtin_encode_setup_frame next site outsz p write_size initial actual /\
  abi_encoder_admissible (AbiCopy 0) /\
  abi_encoder_window_input (AbiCopy 0) at av (w2n a) 0 initial.vs_memory /\
  eval_operand src initial = SOME a /\ abi_decoder_operand_live next src /\
  eval_operand dst actual = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at body_st x) /\
  fn_has_code body_st body_end func /\ fn_inst_ids_distinct func /\
  alloca_inv allocated /\ alloca_room ctx func allocated /\
  d+LENGTH (enc at av) <= allocated.vs_alloca_next /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids body_st body_end /\
    FLOOKUP allocated.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
  ~actual.vs_halted /\ actual.vs_current_bb = body_st.cs_current_bb /\
  actual.vs_inst_idx = LENGTH body_st.cs_current_insts ==>
  abi_encode_empty_window_pre ctx func body_st body_end dst src at av a d actual
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `actual.vs_allocas = (abi_builtin_allocate_state site outsz initial).vs_allocas /\
   actual.vs_alloca_next = (abi_builtin_allocate_state site outsz initial).vs_alloca_next` by
    metis_tac[abi_window_setup_allocas, abi_window_setup_frontier] >>
  `alloca_inv actual /\ alloca_room ctx func actual` by
    metis_tac[abi_window_setup_alloca_inv, abi_window_setup_room] >>
  `eval_operand src actual = SOME a` by
    (qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_builtin_encode_setup_frame_def]) >>
     metis_tac[]) >>
  `abi_encoder_window_input (AbiCopy 0) at av (w2n a) 0 actual.vs_memory` by
    (fs[abi_encoder_window_copy_iff, valueEncodingTheory.mem_bytes_at_def] >>
     simp[abi_encoder_window_copy_iff, valueEncodingTheory.mem_bytes_at_def]) >>
  pure_rewrite_tac[abi_encode_empty_window_pre_def] >>
  pure_asm_rewrite_tac[] >> metis_tac[]
QED

Theorem abi_encode_setup_raw_opcodes[local]:
  abi_builtin_encode_setup mid maxlen st = (ops,ready) ==>
  EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;MSTORE]) (emitted_insts st ready)
Proof
  Cases_on `mid` >>
  simp[abi_builtin_encode_setup_def, abi_builtin_encode_method_id_def,
    compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encode_window_concrete_phases:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len m body_end = ((),final) /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  d = p+32+m /\ outsz = 32+32*word_size (maxlen+m) /\
  fn_has_code st ready func /\ fn_has_code ready body_end func /\
  fn_has_code body_end final func /\ fn_inst_ids_distinct func /\
  st.cs_blocks = final.cs_blocks /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p < dimword (:256) /\
  (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  (cap = 0 ==> ei = AbiCopy 0) /\
  (0 < cap ==>
    sb+cap <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (enc at av)) /\
    (sb+cap <= p+32 \/ p+32+w <= sb)) /\
  d+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  venomMemDefs$regions_disjoint (p+32,m) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)) ==>
  ?raw. run_inst_seq (emitted_insts st final) initial = OK raw /\
    let actual = raw with vs_inst_idx := LENGTH final.cs_current_insts in
    eval_operand (FST ops) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (enc at av)+m) /\
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_encode_exec_frame func initial actual /\
    ?prepared body_state.
      abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
      window_strong_result ctx func ready body_end len at av d prepared body_state /\
      abi_encoder_registered_effect {} [(p,32)] body_state actual /\
      actual.vs_allocas = body_state.vs_allocas /\
      actual.vs_alloca_next = body_state.vs_alloca_next /\
      (!op v. abi_decoder_operand_live body_end.cs_next_var op /\
        eval_operand op body_state = SOME v ==> eval_operand op actual = SOME v) /\
      prepared.vs_accounts = initial.vs_accounts /\
      prepared.vs_transient = initial.vs_transient /\
      prepared.vs_logs = initial.vs_logs /\
      prepared.vs_requests = initial.vs_requests /\
      prepared.vs_pending_deletions = initial.vs_pending_deletions /\
      actual.vs_labels = initial.vs_labels
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_window_input ei at av (if cap = 0 then 0 else sb) cap initial.vs_memory` by
    (Cases_on `cap = 0`
     >- (`ei = AbiCopy 0` by metis_tac[] >>
         qpat_assum `cap = 0` (fn th => pure_rewrite_tac[th]) >>
         qpat_assum `ei = AbiCopy 0` (fn th => pure_rewrite_tac[th]) >>
         qpat_x_assum `abi_encoder_window_input _ _ _ sb _ _` mp_tac >>
         qpat_assum `cap = 0` (fn th => pure_rewrite_tac[th]) >>
         qpat_assum `ei = AbiCopy 0` (fn th => pure_rewrite_tac[th]) >>
         simp_tac std_ss [abi_encoder_window_copy_iff, valueEncodingTheory.mem_bytes_at_def, listTheory.TAKE_0]) >>
     `0 < cap` by decide_tac >>
     qpat_x_assum `0 < cap ==> _` mp_tac >> asm_rewrite_tac[] >> metis_tac[]) >>
  qpat_assum `abi_encoder_window_input _ _ _ (if _ then _ else _) _ _`
    (mp_then (Pat `abi_encoder_window_input _ _ _ _ _ _`) mp_tac abi_encode_window_setup_concrete) >>
  disch_then (drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`w`, `p`, `outsz`, `m`, `ctx`] mp_tac) >>
  impl_tac >-
    (asm_rewrite_tac[] >> Cases_on `cap = 0`
     >- (qpat_assum `cap = 0` (fn th => rewrite_tac[th]) >> simp_tac arith_ss []) >>
     `0 < cap` by decide_tac >>
     qpat_x_assum `0 < cap ==> _` mp_tac >> asm_rewrite_tac[] >> metis_tac[]) >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `setup_raw` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qmatch_asmsub_abbrev_tac `abi_builtin_encode_setup_frame _ _ _ _ _ initial prepared` >>
  `abi_encode_exec_frame func initial prepared` by
    (drule abi_encode_setup_raw_opcodes >> strip_tac >>
     drule_all abi_encode_setup_sequence_frame >>
     simp_tac bool_ss [Abbr `prepared`, abi_encode_exec_frame_inst_idx]) >>
  `ready.cs_blocks = body_end.cs_blocks` by
    (drule abi_builtin_encode_setup_shape >> strip_tac >>
     drule abi_builtin_encode_finish_shape >> strip_tac >> metis_tac[]) >>
  `?body_raw. abi_encode_concrete_result ctx func ready body_end len at av d prepared body_raw` by
    (Cases_on `cap = 0` >- suspend "empty_body" >> suspend "positive_body") >>
  qpat_x_assum `abi_encode_concrete_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encode_concrete_result_def]) >>
  rename1 `run_inst_seq (emitted_insts ready body_end) prepared = OK body_raw` >>
  qmatch_asmsub_abbrev_tac `window_strong_result ctx func ready body_end len at av d prepared body_state` >>
  `abi_encode_exec_frame func prepared body_state` by
    (simp_tac bool_ss [Abbr `body_state`, abi_encode_exec_frame_inst_idx] >>
     drule_all abi_encode_no_block_body_frame >> simp[]) >>
  `eval_operand (FST ops) body_state = SOME (n2w p)` by
    (irule abi_encode_setup_buffer_eval >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE
      [window_strong_result_def, abi_encoder_window_result_def]) >>
  suspend "finish"
QED

Resume abi_encode_window_concrete_phases[positive_body]:
  `0 < cap` by decide_tac >>
  qpat_x_assum `0 < cap ==> _` (mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_window_input ei at av sb cap prepared.vs_memory` by
    (qpat_x_assum `abi_encoder_window_input _ _ _ (if _ then _ else _) _ prepared.vs_memory` mp_tac >>
     asm_rewrite_tac[]) >>
  `abi_encoder_window_pre ctx func ready body_end (SND ops) src ei at av sb cap d prepared` by
    (qpat_x_assum `d = _` SUBST_ALL_TAC >>
     qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
     qpat_x_assum `m = _` SUBST_ALL_TAC >>
     irule (SIMP_RULE bool_ss [LET_THM] abi_encode_setup_window_pre) >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     qexistsl_tac [`initial`, `st.cs_next_var`, `32+32*word_size (maxlen+(case method_id of NONE => 0 | SOME mid => 4))`, `p`, `st.cs_next_id`, `w`] >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     rpt strip_tac >>
     qpat_x_assum `!inst b sz. _` (qspecl_then [`inst`, `b`, `sz`] mp_tac) >>
     asm_rewrite_tac[] >> simp_tac bool_ss []) >>
  mp_tac (SPEC_ALL abi_encode_concrete_contract_all) >>
  rewrite_tac[abi_encode_concrete_contract_def] >>
  disch_then drule_all >> simp_tac bool_ss []
QED

Resume abi_encode_window_concrete_phases[empty_body]:
  `ei = AbiCopy 0` by metis_tac[] >>
  qpat_x_assum `ei = AbiCopy 0` SUBST_ALL_TAC >>
  `abi_encoder_window_input (AbiCopy 0) at av (w2n (n2w sb :256 word)) 0 initial.vs_memory` by
    (qpat_x_assum `abi_encoder_window_input _ _ _ sb _ _` mp_tac >>
     qpat_assum `cap = 0` (fn th => pure_rewrite_tac[th]) >>
     simp_tac std_ss [abi_encoder_window_copy_iff, valueEncodingTheory.mem_bytes_at_def, listTheory.TAKE_0]) >>
  `abi_encode_empty_window_pre ctx func ready body_end (SND ops) src at av (n2w sb) d prepared` by
    (qpat_x_assum `d = _` SUBST_ALL_TAC >>
     qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
     qpat_x_assum `m = _` SUBST_ALL_TAC >>
     irule (SIMP_RULE bool_ss [LET_THM] abi_encode_setup_empty_pre) >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     qexistsl_tac [`initial`, `st.cs_next_var`, `32+32*word_size (maxlen+(case method_id of NONE => 0 | SOME mid => 4))`, `p`, `st.cs_next_id`, `w`] >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     rpt strip_tac >>
     qpat_x_assum `!inst b sz. _` (qspecl_then [`inst`, `b`, `sz`] mp_tac) >>
     asm_rewrite_tac[] >> simp_tac bool_ss []) >>
  drule_all abi_encode_empty_copy_concrete >> simp_tac bool_ss []
QED

Resume abi_encode_window_concrete_phases[finish]:
  drule abi_encode_window_finish_concrete >>
  disch_then (drule_at (Pat `window_strong_result _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`p`, `LENGTH (enc at av)`,
    `mem_bytes_at (p+32) (m+LENGTH (enc at av)) body_state.vs_memory`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts body_end final) body_state = OK finish_raw` >>
  qmatch_asmsub_abbrev_tac `abi_decode_frame p 32 body_state actual` >>
  `abi_encode_exec_frame func body_state actual` by
    (`finish_raw.vs_allocas = body_state.vs_allocas /\
      finish_raw.vs_alloca_next = body_state.vs_alloca_next` by
       (qpat_x_assum `actual.vs_allocas = _` mp_tac >>
        qpat_x_assum `actual.vs_alloca_next = _` mp_tac >>
        simp_tac (srw_ss()) [Abbr `actual`]) >>
     drule_all abi_encode_framed_finish_sequence >>
     simp_tac bool_ss [Abbr `actual`, abi_encode_exec_frame_inst_idx]) >>
  `abi_encode_exec_frame func initial actual` by
    metis_tac[abi_encode_exec_frame_trans] >>
  suspend "result"
QED

Resume abi_encode_window_concrete_phases[result]:
  `mem_bytes_at (p+32) m body_state.vs_memory = mem_bytes_at (p+32) m prepared.vs_memory` by
    (irule window_alloca_growth_frame >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_builtin_encode_setup_frame_def]) >>
     conj_tac >- (qpat_x_assum `d + LENGTH _ <= _` mp_tac >>
       pure_asm_rewrite_tac[] >> decide_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`window_alloca_sites func (frag_ids ready body_end)`, `[(d,LENGTH (enc at av))]`] >>
     reverse conj_tac >-
       (conj_tac >- (simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
        first_assum ACCEPT_TAC) >>
     qpat_x_assum `d = _` SUBST_ALL_TAC >>
     qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
     qpat_x_assum `m = _` SUBST_ALL_TAC >>
     rpt strip_tac >>
     qpat_x_assum `_ IN window_alloca_sites _ _` mp_tac >>
     simp_tac (srw_ss()) [window_alloca_sites_def] >> strip_tac >>
     qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _`
       (qspecl_then [`inst`, `b`, `sz`] mp_tac) >>
     qpat_x_assum `FLOOKUP prepared.vs_allocas i = SOME (b,sz)` mp_tac >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss []) >>
  `mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av` by
    (qpat_assum `abi_decode_frame p 32 body_state actual`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
     qpat_x_assum `!p' k. _` (qspecl_then [`d`, `LENGTH (enc at av)`] mp_tac) >>
     (impl_tac >- (qpat_x_assum `d = _` mp_tac >> decide_tac)) >>
     disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `(case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid)` by
    (qpat_assum `abi_decode_frame p 32 body_state actual`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
     `mem_bytes_at (p+32) m actual.vs_memory = mem_bytes_at (p+32) m body_state.vs_memory` by
       (qpat_x_assum `!p' k. _` (qspecl_then [`p+32`, `m`] mp_tac) >>
        simp_tac bool_ss [arithmeticTheory.LE_REFL]) >>
     qpat_x_assum `mem_bytes_at (p+32) m body_state.vs_memory = _` mp_tac >>
     qpat_x_assum `mem_bytes_at (p+32) m actual.vs_memory = _` mp_tac >>
     qpat_x_assum `case method_id of NONE => T | SOME mid => _` mp_tac >>
     qpat_x_assum `m = _` mp_tac >>
     Cases_on `method_id` >> simp_tac (srw_ss()) [] >> metis_tac[]) >>
  suspend "compose"
QED

Resume abi_encode_window_concrete_phases[compose]:
  `?raw. run_inst_seq (emitted_insts st final) initial = OK raw /\
    (raw with vs_inst_idx := LENGTH final.cs_current_insts) = actual` by
    (qpat_x_assum `Abbrev (actual = _)`
       (SUBST_ALL_TAC o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
     irule abi_encode_concrete_three_sequences >>
     qexistsl_tac [`body_end`, `body_raw`, `ready`, `setup_raw`] >>
     simp_tac (srw_ss()) [Abbr `body_state`, Abbr `prepared`] >>
     asm_rewrite_tac[]) >>
  qexists_tac `raw` >> simp_tac bool_ss [LET_THM] >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`prepared`, `body_state`] >> asm_rewrite_tac[] >> metis_tac[]
QED
Finalise abi_encode_window_concrete_phases


Theorem abi_encode_phase_operand_liveness[local]:
  abi_builtin_encode_setup mid maxlen sa = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) op ei ready = (len,body_end) /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  abi_decoder_operand_live sa.cs_next_var op /\
  (!x. op = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops)
Proof
  strip_tac >>
  drule abi_builtin_encode_setup_live >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `abi_decoder_operand_live sa.cs_next_var op` by
    (qpat_assum `!x. op = Var x ==> _` mp_tac >> Cases_on `op` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `abi_decoder_operand_live ready.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists `sa.cs_next_var` >>
     conj_tac
     >- (qpat_assum `ready.cs_next_var = _` (fn th => rewrite_tac[th]) >>
         Cases_on `mid` >> simp_tac (srw_ss()) []) >>
     first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac
      >- (qpat_assum `abi_decoder_operand_live ready.cs_next_var op` mp_tac >>
          qpat_assum `op = Var x` (fn th => rewrite_tac[th]) >>
          simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
      qpat_assum `abi_decoder_operand_live ready.cs_next_var (SND ops)` mp_tac >>
      qpat_assum `SND ops = Var x` (fn th => rewrite_tac[th]) >>
      simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `abi_decoder_operand_live ready.cs_next_var (FST ops)` mp_tac >>
      qpat_assum `FST ops = Var x` (fn th => rewrite_tac[th]) >>
      simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  irule abi_decoder_operand_live_mono >> qexists `ready.cs_next_var` >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_nonword_no_block_phases:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  ~is_word_type (expr_type e) /\
  abi_enc_plan (get_tenv cx) (lowered_value_type ce e) ei /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av /\
  abi_builtin_encode_setup mid (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e))
    sa = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) op ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len
    (case mid of NONE => 0 | SOME _ => 4) body_end = ((),final) /\
  fn_has_code sa ready func /\ fn_has_code ready body_end func /\
  fn_has_code body_end final func /\ fn_inst_ids_distinct func /\
  sa.cs_blocks = final.cs_blocks /\
  local_ptrs_reserved ce sa /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  ?p.
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?raw. run_inst_seq (emitted_insts sa final) s = OK raw /\
      let actual = raw with vs_inst_idx := LENGTH final.cs_current_insts in
      let bytes = enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av in
      let m = case mid of NONE => 0 | SOME _ => 4 in
      eval_operand (FST ops) actual = SOME (n2w p) /\
      mload p actual = n2w (LENGTH bytes+m) /\
      mem_bytes_at (p+32+m) (LENGTH bytes) actual.vs_memory = bytes /\
      (case mid of NONE => T | SOME selector =>
        mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector) /\
      ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
      actual.vs_inst_idx = LENGTH final.cs_current_insts /\
      abi_encode_exec_frame func s actual /\
      stmt_state_rel ctx func ce cx es' actual /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
      lookup_var x actual = SOME w) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
      FLOOKUP actual.vs_allocas aid = SOME row) /\
    (!aid off sz. FLOOKUP s.vs_allocas aid = SOME(off,sz) /\ aid < sa.cs_next_id ==>
      mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz s.vs_memory) /\
    (!name b n. local_region ce es'.scopes s name b n ==>
      mem_bytes_at b n actual.vs_memory = mem_bytes_at b n s.vs_memory) /\
    FLOOKUP actual.vs_allocas sa.cs_next_id =
      SOME(p,32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) /\
    p+(32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) <= actual.vs_alloca_next /\
    actual.vs_alloca_next < dimword (:256)
Proof
  strip_tac >>
  `!j. MEM j (fn_insts func) /\ j.inst_opcode <> STOP /\
    j.inst_opcode <> NOP ==> MEM j (fn_insts func)` by simp[] >>
  drule_all abi_encode_nonword_phase_resources >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `source_word` (qx_choose_then `ct` (qx_choose_then `rv`
    (qx_choose_then `p` (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  qexists `p` >> rpt strip_tac >> simp_tac bool_ss [LET_THM] >>
  `abi_encoder_admissible ei` by metis_tac[abi_enc_plan_admissible] >>
  drule_all abi_encode_phase_operand_liveness >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  suspend "apply"
QED

Resume abi_encode_nonword_no_block_phases[apply]:
  drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`)
    (abi_encode_window_concrete_phases |> SPEC_ALL
     |> Q.INST [`d` |-> `p+32+m`, `outsz` |-> `32+32*word_size(maxlen+m)`]
     |> Q.INST [`m` |-> `(case method_id of NONE => 0 | SOME mid => 4)`,
                `w` |-> `(case method_id of NONE => 0 | SOME mid => 32)`]
     |> PURE_REWRITE_RULE [REFL_CLAUSE, IMP_CLAUSES, AND_CLAUSES]) >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_encoder_window_input _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_room _ _ _`)) >>
  disch_then (drule_at (Pat `abi_builtin_encode_finish _ _ _ _ = _`)) >>
  disch_then (qspec_then `p` mp_tac) >>
  qpat_assum `enc ct rv = _` (fn th => rewrite_tac[th]) >>
  impl_tac >-
    (rewrite_tac[wordsTheory.n2w_w2n] >>
     asm_rewrite_tac[] >> metis_tac[arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_EQ_0]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `abi_encode_exec_frame func s actual` >>
  suspend "caller"
QED

Resume abi_encode_nonword_no_block_phases[caller]:
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits] >>
  `?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by
    metis_tac[optionTheory.IS_SOME_EXISTS,
      exprSimHypsTheory.expr_body_pre_type_evaluates] >>
  `vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av` by
    metis_tac[exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_conversion] >>
  `vyper_to_abi_type (get_tenv cx) (expr_type e) =
    vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)` by
    metis_tac[exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_abi_type] >>
  `32 + (case mid of NONE => 0 | SOME _ => 32) <=
     32+32*word_size (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+
       (case mid of NONE => 0 | SOME _ => 4)) /\
   p <= p+32+(case mid of NONE => 0 | SOME _ => 4) /\
   p+32+(case mid of NONE => 0 | SOME _ => 4)+
     LENGTH (enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av) <=
     p+(32+32*word_size (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+
       (case mid of NONE => 0 | SOME _ => 4)))` by
    (drule_all abi_encode_nonword_observer_geometry >>
     simp_tac bool_ss [LET_THM] >> metis_tac[]) >>
  `stmt_state_rel ctx func ce cx es' s` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  qpat_x_assum `enc ct rv = _` (SUBST_ALL_TAC o SYM) >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `sa.cs_next_var <= ready.cs_next_var /\ sa.cs_next_var <= body_end.cs_next_var` by decide_tac >>
  `stmt_state_rel ctx func ce cx es' actual /\
    (!name b n. local_region ce es'.scopes s name b n ==>
      mem_bytes_at b n actual.vs_memory = mem_bytes_at b n s.vs_memory) /\
    FLOOKUP actual.vs_allocas sa.cs_next_id =
      SOME(p,32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) /\
    p+(32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) <= actual.vs_alloca_next /\
    actual.vs_alloca_next < dimword (:256)` by
    (drule_all (SIMP_RULE bool_ss [] (Q.INST
       [`outsz` |-> `32+32*word_size (maxlen+(case mid of NONE => 0 | SOME x => 4))`]
       (SPEC_ALL abi_encode_phases_caller_state))) >> asm_rewrite_tac[]) >>
  `(!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
      lookup_var x actual = SOME w)` by
    (drule abi_encode_caller_phase_registers >>
     disch_then drule >>
     disch_then (qspec_then `actual` mp_tac) >>
     asm_rewrite_tac[] >>
     simp_tac (srw_ss()) [not_fresh_at_def, abi_decoder_operand_live_def, abi_decoder_older_vars_def]) >>
  `(!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
      FLOOKUP actual.vs_allocas aid = SOME row)` by
    (drule_all abi_encode_caller_phase_allocations >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `alloca_inv actual` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ actual` mp_tac >>
     simp_tac bool_ss [stmt_state_rel_def] >> metis_tac[]) >>
  `sa.cs_next_id <= ready.cs_next_id` by
    (qpat_assum `ready.cs_next_id = _` mp_tac >>
     Cases_on `mid` >> simp_tac (srw_ss()) []) >>
  `(!aid off sz. FLOOKUP s.vs_allocas aid = SOME(off,sz) /\ aid < sa.cs_next_id ==>
      mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz s.vs_memory)` by
    (drule abi_encode_caller_phase_old_rows >> disch_then drule >>
     disch_then (qspec_then `actual` mp_tac) >>
     asm_rewrite_tac[]) >>
  qexists `raw` >>
  qpat_x_assum `Abbrev (actual = _)`
    (fn th => rewrite_tac[GSYM (PURE_REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  asm_rewrite_tac[]
QED
Finalise abi_encode_nonword_no_block_phases

Theorem abi_encode_nonword_no_block_run:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  ~is_word_type (expr_type e) /\
  abi_enc_plan (get_tenv cx) (lowered_value_type ce e) ei /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av /\
  lower_abi_encode F mid op ei (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e))
    sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  sa.cs_blocks = sb.cs_blocks /\ local_ptrs_reserved ce sa /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p raw. run_inst_seq (emitted_insts sa sb) s = OK raw /\
    let actual = raw with vs_inst_idx := LENGTH sb.cs_current_insts in
    let bytes = enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av in
    let m = case mid of NONE => 0 | SOME _ => 4 in
    eval_operand out actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH bytes+m) /\
    mem_bytes_at (p+32+m) (LENGTH bytes) actual.vs_memory = bytes /\
    (case mid of NONE => T | SOME selector =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector) /\
    ~actual.vs_halted /\ actual.vs_current_bb = sb.cs_current_bb /\
    actual.vs_inst_idx = LENGTH sb.cs_current_insts /\
    abi_encode_exec_frame func s actual /\
    stmt_state_rel ctx func ce cx es' actual /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
      lookup_var x actual = SOME w) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
      FLOOKUP actual.vs_allocas aid = SOME row) /\
    (!aid off sz. FLOOKUP s.vs_allocas aid = SOME(off,sz) /\ aid < sa.cs_next_id ==>
      mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz s.vs_memory) /\
    (!name b n. local_region ce es'.scopes s name b n ==>
      mem_bytes_at b n actual.vs_memory = mem_bytes_at b n s.vs_memory) /\
    FLOOKUP actual.vs_allocas sa.cs_next_id =
      SOME(p,32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) /\
    p+(32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) <= actual.vs_alloca_next /\
    actual.vs_alloca_next < dimword (:256)
Proof
  strip_tac >> drule lower_abi_encode_trace >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  `cs_extends sa ready` by
    (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `cs_extends ready body_end` by metis_tac[abiEncoderAppendTheory.cs_extends_abi_encode] >>
  `cs_extends body_end sb` by
    (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `fn_has_code sa ready func /\ fn_has_code ready body_end func /\
   fn_has_code body_end sb func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `body_end.cs_next_var <= sb.cs_next_var` by
    (qpat_assum `sb.cs_next_var = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `ready.cs_next_var <= sb.cs_next_var` by metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  drule_all abi_encode_nonword_no_block_phases >>
  disch_then (qx_choose_then `p` mp_tac) >>
  impl_tac >- (asm_rewrite_tac[] >> simp_tac bool_ss [arithmeticTheory.LESS_EQ_REFL]) >>
  strip_tac >> qexistsl_tac [`p`, `raw`] >> gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_nonword_no_block_observer:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  ~is_word_type (expr_type e) /\
  abi_enc_plan (get_tenv cx) (lowered_value_type ce e) ei /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av /\
  lower_abi_encode F mid op ei (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e))
    sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  sa.cs_blocks = sb.cs_blocks /\ local_ptrs_reserved ce sa /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ fn_has_code sa sb observer ==>
  ?p actual. abi_decode_sim ctx observer s actual /\
    let bytes = enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av in
    let m = case mid of NONE => 0 | SOME _ => 4 in
    eval_operand out actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH bytes+m) /\
    mem_bytes_at (p+32+m) (LENGTH bytes) actual.vs_memory = bytes /\
    (case mid of NONE => T | SOME selector =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector) /\
    ~actual.vs_halted /\ actual.vs_current_bb = sb.cs_current_bb /\
    actual.vs_inst_idx = LENGTH sb.cs_current_insts /\
    abi_encode_exec_frame func s actual /\
    stmt_state_rel ctx func ce cx es' actual /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
      lookup_var x actual = SOME w) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
      FLOOKUP actual.vs_allocas aid = SOME row) /\
    (!aid off sz. FLOOKUP s.vs_allocas aid = SOME(off,sz) /\ aid < sa.cs_next_id ==>
      mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz s.vs_memory) /\
    (!name b n. local_region ce es'.scopes s name b n ==>
      mem_bytes_at b n actual.vs_memory = mem_bytes_at b n s.vs_memory) /\
    FLOOKUP actual.vs_allocas sa.cs_next_id =
      SOME(p,32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) /\
    p+(32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) <= actual.vs_alloca_next /\
    actual.vs_alloca_next < dimword (:256)
Proof
  strip_tac >> drule_all abi_encode_nonword_no_block_run >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all lower_abi_encode_no_blocks_safe >> strip_tac >>
  drule_all lower_abi_encode_no_block_run_reach >> strip_tac >>
  qexistsl_tac [`p`, `raw with vs_inst_idx := LENGTH sb.cs_current_insts`] >> gvs[LET_THM] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
