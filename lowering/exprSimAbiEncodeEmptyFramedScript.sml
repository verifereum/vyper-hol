Theory exprSimAbiEncodeEmptyFramed
Ancestors
  valueEncodingDefs
  exprSimAbiEncodeEmptySource exprSimAbiEncodeExecFrame
  exprSimAbiEncodeFramedSuffix exprSimAbiEncodeSetupOpen abiBuiltinEncodeSetup abiBuiltinAllocation
  abiEncodeWindowBuiltin abiDecoderContract abiDecoderLoop
  exprSimAbiEncodeExecution exprSimAbiEncodeStateTransport exprSimAbiEncodeWindowRoom
  abiEncoderWindowLeaves abiEncoderWindowContract abiEncoderRegisteredEffect
  abiEncoderExtendSim abiEncoderPrimitiveEffect abiEncoderWindowLookup
  abiEncoderLeaves abiEncoderWindow abiEncoderProps valueEncodingProofs
  exprLoweringProps valueEncoding abiEncoderSourceFootprint
  venomState venomExecSemantics compileEnv list words

Theorem abi_encode_empty_copy_framed:
  compile_abi_encode_to_buf dst src (AbiCopy 0) st = (out,st') /\
  abi_encode_empty_window_pre ctx func st st' dst src at av a d s ==>
  ?t. window_strong_result ctx func st st' out at av d s t /\
      (!x. ~not_fresh_at st' x ==> lookup_var x t = lookup_var x s) /\
      abi_encode_exec_frame func s t /\ t.vs_labels = s.vs_labels
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
  qexists_tac `(mcopy d (w2n a) 0 s) with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  reverse conj_tac
  >- simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def] >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  simp[eval_operand_def, mcopy_mem_bytes_at_same, abi_encoder_extend_sim_sim] >>
  mp_tac (Q.INST [`d` |-> `d`, `sb` |-> `w2n (a:256 word)`, `n` |-> `0`,
    `ix` |-> `LENGTH st'.cs_current_insts`] window_copy_state_resources) >>
  simp[] >> strip_tac >> conj_tac >- asm "sizes" ACCEPT_TAC >>
  simp[venomExecSemanticsTheory.mcopy_def,
    venomStateTheory.write_memory_with_expansion_def]
QED

Theorem abi_encode_framed_setup_empty_pre[local]:
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
    (fs[abi_builtin_encode_setup_frame_def] >> metis_tac[]) >>
  `abi_encoder_window_input (AbiCopy 0) at av (w2n a) 0 actual.vs_memory` by
    (fs[abi_encoder_window_copy_iff, valueEncodingTheory.mem_bytes_at_def] >>
     simp[abi_encoder_window_copy_iff, valueEncodingTheory.mem_bytes_at_def]) >>
  pure_rewrite_tac[abi_encode_empty_window_pre_def] >>
  pure_asm_rewrite_tac[] >> metis_tac[]
QED

Theorem abi_encode_empty_framed_phases_open:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src (AbiCopy 0) ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len m body_end = ((),final) /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  d = p+32+m /\ outsz = 32+32*word_size (maxlen+m) /\
  fn_has_code st ready func /\ fn_has_code ready body_end func /\
  fn_has_code body_end final func /\ fn_inst_ids_distinct func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p < dimword (:256) /\
  (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_admissible (AbiCopy 0) /\
  abi_encoder_window_input (AbiCopy 0) at av (w2n a) 0 initial.vs_memory /\
  eval_operand src initial = SOME a /\ abi_decoder_operand_live st.cs_next_var src /\
  (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  d+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  venomMemDefs$regions_disjoint (p+32,m) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)) ==>
  ?prepared body actual.
    eval_operand (FST ops) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (enc at av)+m) /\
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
    window_strong_result ctx func ready body_end len at av d prepared body /\
    abi_decode_frame p 32 body actual /\
    actual.vs_allocas = body.vs_allocas /\ actual.vs_alloca_next = body.vs_alloca_next /\
    abi_encoder_registered_effect {} [(p,32)] body actual /\
    (!op v. abi_decoder_operand_live body_end.cs_next_var op /\ eval_operand op body = SOME v ==>
      eval_operand op actual = SOME v) /\
    abi_encode_exec_frame func initial actual /\
    LENGTH initial.vs_memory <= LENGTH actual.vs_memory /\
    prepared.vs_accounts = initial.vs_accounts /\ prepared.vs_transient = initial.vs_transient /\
    prepared.vs_logs = initial.vs_logs /\ prepared.vs_requests = initial.vs_requests /\
    prepared.vs_pending_deletions = initial.vs_pending_deletions /\
    prepared.vs_labels = initial.vs_labels /\ actual.vs_labels = initial.vs_labels
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_window_input (AbiCopy 0) at av 0 0 initial.vs_memory` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp_tac std_ss [abi_encoder_window_copy_iff, valueEncodingTheory.mem_bytes_at_def,
       listTheory.TAKE_0]) >>
  drule_all (SIMP_RULE std_ss [] (Q.INST [`sb` |-> `0:num`, `cap` |-> `0:num`]
    (SPEC_ALL abi_encode_framed_setup_window_open))) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_builtin_encode_setup_frame _ _ _ _ _ initial prepared` >>
  `abi_encode_empty_window_pre ctx func ready body_end (SND ops) src at av a d prepared` by
    (qpat_x_assum `d = _` SUBST_ALL_TAC >>
     qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
     qpat_x_assum `m = _` SUBST_ALL_TAC >>
     irule (SIMP_RULE bool_ss [LET_THM] abi_encode_framed_setup_empty_pre) >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     qexistsl [`initial`, `st.cs_next_var`, `32+32*word_size (maxlen+(case method_id of NONE => 0 | SOME mid => 4))`, `p`, `st.cs_next_id`, `w`] >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     rpt strip_tac >>
     qpat_x_assum `!inst b sz. _` (qspecl_then [`inst`, `b`, `sz`] mp_tac) >>
     asm_rewrite_tac[] >> simp_tac bool_ss []) >>
  drule_all abi_encode_empty_copy_framed >> strip_tac >>
  rename1 `window_strong_result ctx func ready body_end len at av d prepared body_state` >>
  `eval_operand (FST ops) body_state = SOME (n2w p)` by
    (irule abi_encode_setup_buffer_eval >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE
      [window_strong_result_def, abi_encoder_window_result_def]) >>
  drule_all abi_encode_framed_finish_open >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "endpoint"
QED

Resume abi_encode_empty_framed_phases_open[endpoint]:
  `mem_bytes_at (p+32) m body_state.vs_memory = mem_bytes_at (p+32) m prepared.vs_memory` by
    (irule window_alloca_growth_frame >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_builtin_encode_setup_frame_def]) >>
     conj_tac >- (qpat_x_assum `d + LENGTH _ <= _` mp_tac >>
       pure_asm_rewrite_tac[] >> decide_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`window_alloca_sites func (frag_ids ready body_end)`, `[(d,LENGTH (enc at av))]`] >>
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
  suspend "observations"
QED

Resume abi_encode_empty_framed_phases_open[observations]:
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
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> qexists `prepared` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule abi_decode_sim_trans >> qexists `body_state` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_encode_exec_frame func initial actual` by
    (irule abi_encode_exec_frame_trans >> qexists `prepared` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule abi_encode_exec_frame_trans >> qexists `body_state` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `LENGTH initial.vs_memory <= LENGTH actual.vs_memory` by
    (drule abi_encode_exec_frame_memory_length >> simp[]) >>
  `actual.vs_labels = initial.vs_labels` by metis_tac[] >>
  qexistsl [`prepared`, `body_state`, `actual`] >>
  qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
  qpat_x_assum `w = _` SUBST_ALL_TAC >>
  qpat_x_assum `m = _` SUBST_ALL_TAC >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise abi_encode_empty_framed_phases_open

Theorem abi_encode_empty_framed_caller_suffix:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src (AbiCopy 0) ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len m body_end = ((),final) /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  d = p+32+m /\ outsz = 32+32*word_size (maxlen+m) /\
  fn_has_code st ready obs /\ fn_has_code ready body_end obs /\
  fn_has_code body_end final obs /\ fn_inst_ids_distinct obs /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p < dimword (:256) /\
  (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_admissible (AbiCopy 0) /\
  abi_encoder_window_input (AbiCopy 0) at av (w2n a) 0 initial.vs_memory /\
  eval_operand src initial = SOME a /\ abi_decoder_operand_live st.cs_next_var src /\
  (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room (ctx with ctx_functions := [obs]) obs
    (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  d+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  venomMemDefs$regions_disjoint (p+32,m) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts obs) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)) /\
  stmt_state_rel ctx func ce cx vs initial /\ local_ptrs_reserved ce st /\
  fn_inst_ids_distinct func /\
  (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\ j.inst_opcode <> NOP ==>
    MEM j (fn_insts func)) /\
  (!j. MEM j (fn_insts obs) ==> j.inst_opcode <> INVOKE) /\
  st.cs_next_var <= ready.cs_next_var /\ st.cs_next_var <= body_end.cs_next_var /\
  32+w <= outsz /\ p <= d /\ d+LENGTH (enc at av) <= p+outsz ==>
  ?prepared body actual.
    eval_operand (FST ops) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (enc at av)+m) /\
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_decode_sim ctx obs initial actual /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
    window_strong_result (ctx with ctx_functions := [obs]) obs ready body_end len at av d prepared body /\
    abi_decode_frame p 32 body actual /\
    actual.vs_allocas = body.vs_allocas /\ actual.vs_alloca_next = body.vs_alloca_next /\
    abi_encoder_registered_effect {} [(p,32)] body actual /\
    (!op v. abi_decoder_operand_live body_end.cs_next_var op /\ eval_operand op body = SOME v ==>
      eval_operand op actual = SOME v) /\
    abi_encode_exec_frame obs initial actual /\
    LENGTH initial.vs_memory <= LENGTH actual.vs_memory /\
    prepared.vs_accounts = initial.vs_accounts /\ prepared.vs_transient = initial.vs_transient /\
    prepared.vs_logs = initial.vs_logs /\ prepared.vs_requests = initial.vs_requests /\
    prepared.vs_pending_deletions = initial.vs_pending_deletions /\
    prepared.vs_labels = initial.vs_labels /\ actual.vs_labels = initial.vs_labels /\
    stmt_state_rel ctx func ce cx vs actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_empty_framed_phases_open >> strip_tac >>
  rename1 `window_strong_result _ obs ready body_end len at av d prepared body_state` >>
  `outsz = 32+32*word_size (maxlen+(case method_id of NONE => 0 | SOME x => 4))` by
    (qpat_assum `outsz = _` (fn th => rewrite_tac [th]) >>
     qpat_assum `m = _` (fn th => rewrite_tac [th])) >>
  `stmt_state_rel ctx func ce cx vs actual` by
    (drule_all (cj 1 abi_encode_phases_caller_state) >> strip_tac) >>
  `abi_decode_sim ctx obs initial actual` by
    (drule_all abi_decode_sim_ctx_no_invoke >> disch_then (qspec_then `ctx` ACCEPT_TAC)) >>
  qexistsl [`prepared`, `body_state`, `actual`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
