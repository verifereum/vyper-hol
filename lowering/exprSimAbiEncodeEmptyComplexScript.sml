Theory exprSimAbiEncodeEmptyComplex
Ancestors
  valueEncodingDefs
  exprSimAbiEncodeEmptyFramed exprSimAbiEncodeTranslatedZero
  exprSimAbiEncodeEmptySource abiDecoderLoop abiEncoderProps
  abiEncoderWindowContract abiEncoderRegisteredEffect abiEncoderExtendSim
  abiDecoderContract exprSimAbiEncodeExecFrame
  exprLoweringProps valueEncoding venomState words
  exprSimAbiEncodeSetupOpen exprSimAbiEncodeExecution abiEncodeWindowBuiltin
  abiBuiltinEncodeSetup abiBuiltinAllocation abiEncoderWindowLeaves
  abiEncoderProps abiDecoderFrame abiEncoderLeaves abiEncoderAdmissible
  abiEncoderWindow exprSimAbiEncodeFramedSuffix fragExec
  exprSimAbiEncodeWindowRoom exprSimAbiEncodeStateTransport

Theorem abi_encode_empty_complex_framed:
  compile_abi_encode_to_buf dst src (AbiComplex []) st = (out,st') /\
  enc at av = [] /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  window_strong_result ctx func st st' out at av d s s /\
  (!x. ~not_fresh_at st' x ==> lookup_var x s = lookup_var x s) /\
  abi_encode_exec_frame func s s /\ s.vs_labels = s.vs_labels
Proof
  simp[abi_encode_empty_complex_body_probe] >> strip_tac >>
  gvs[window_strong_result_def, abi_encoder_window_result_def,
      abi_encoder_registered_effect_refl, window_alloca_growth_refl,
      abi_encoder_extend_sim_refl, abi_decode_sim_refl,
      eval_operand_def, valueEncodingTheory.mem_bytes_at_def,
      frag_ids_def, window_alloca_sites_def]
QED

(* Shared endpoint, retaining all three concrete phase witnesses. *)
Definition abi_encode_empty_phases_result_def:
  abi_encode_empty_phases_result ctx func st ready body_end final ops len
    method_id outsz p w d m at av initial <=>
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
End

Theorem abi_encode_empty_phases_open:
  (ei = AbiCopy 0 \/ ei = AbiComplex []) /\ enc at av = [] /\
  abi_encoder_window_input ei at av (w2n a) 0 initial.vs_memory /\
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
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
  abi_encode_empty_phases_result ctx func st ready body_end final ops len
    method_id outsz p w d m at av initial
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `ei = AbiCopy 0`
  >- (`abi_encoder_admissible (AbiCopy 0)` by simp[abi_encoder_admissible_def] >>
      qpat_x_assum `ei = AbiCopy 0` SUBST_ALL_TAC >>
      pure_rewrite_tac[abi_encode_empty_phases_result_def] >>
      drule_all abi_encode_empty_framed_phases_open >>
      qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
      qpat_x_assum `m = _` SUBST_ALL_TAC >>
      qpat_x_assum `w = _` SUBST_ALL_TAC >> simp_tac bool_ss []) >>
  `ei = AbiComplex []` by metis_tac[] >>
  `abi_encoder_window_input (AbiComplex []) at av 0 0 initial.vs_memory` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     qpat_assum `ei = AbiComplex []` SUBST1_TAC >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[Once abi_encoder_window_input_cases] >> strip_tac >>
     simp[Once abi_encoder_window_input_cases] >> metis_tac[]) >>
  qpat_x_assum `ei = AbiComplex []` SUBST_ALL_TAC >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_empty_complex_body_probe, pairTheory.PAIR_EQ]) >>
  qpat_x_assum `Lit 0w = len` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `ready = body_end` (SUBST_ALL_TAC o SYM) >>
  drule_all (SIMP_RULE std_ss [] (Q.INST [`sb` |-> `0:num`, `cap` |-> `0:num`]
    (SPEC_ALL abi_encode_framed_setup_window_open))) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_builtin_encode_setup_frame _ _ _ _ _ initial prepared` >>
  `alloca_inv prepared /\ alloca_room ctx func prepared` by
    metis_tac[abi_window_setup_alloca_inv, abi_window_setup_room] >>
  `window_strong_result ctx func ready ready (Lit 0w) at av d prepared prepared` by
    (irule (SRULE [abi_encode_empty_complex_body_probe]
       (cj 1 abi_encode_empty_complex_framed)) >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss []) >>
  `eval_operand (Lit 0w) prepared = SOME (n2w (LENGTH (enc at av)))` by
    (qpat_assum `enc at av = []` (fn th => rewrite_tac [th]) >>
     simp_tac (srw_ss()) [eval_operand_def]) >>
  drule_all abi_encode_framed_finish_open >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "endpoint"
QED

Resume abi_encode_empty_phases_open[endpoint]:
  `mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av` by
    (qpat_assum `enc at av = []` (fn th => rewrite_tac [th]) >>
     simp_tac (srw_ss()) [valueEncodingTheory.mem_bytes_at_def]) >>
  `(case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid)` by
    (qpat_assum `abi_decode_frame p 32 prepared actual`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
     `mem_bytes_at (p+32) m actual.vs_memory = mem_bytes_at (p+32) m prepared.vs_memory` by
       (qpat_x_assum `!p' k. _` (qspecl_then [`p+32`, `m`] mp_tac) >>
        simp_tac bool_ss [arithmeticTheory.LE_REFL]) >>
     qpat_x_assum `mem_bytes_at (p+32) m actual.vs_memory = _` mp_tac >>
     qpat_x_assum `case method_id of NONE => T | SOME mid => _` mp_tac >>
     qpat_x_assum `m = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `method_id` >> simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> qexists `prepared` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_encode_exec_frame func initial actual` by
    (irule abi_encode_exec_frame_trans >> qexists `prepared` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `LENGTH initial.vs_memory <= LENGTH actual.vs_memory` by
    metis_tac[abi_encode_exec_frame_memory_length] >>
  `actual.vs_labels = initial.vs_labels` by metis_tac[] >>
  pure_rewrite_tac[abi_encode_empty_phases_result_def] >>
  qexistsl [`prepared`, `prepared`, `actual`] >>
  qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
  qpat_x_assum `w = _` SUBST_ALL_TAC >>
  qpat_x_assum `m = _` SUBST_ALL_TAC >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise abi_encode_empty_phases_open

Theorem abi_encode_empty_complex_raw:
  compile_abi_encode_to_buf dst src (AbiComplex []) st = (out,st') ==>
  out = Lit 0w /\ frag_exec ctx st st' (\t. t = s) (\t. t = s) (\r. F)
Proof
  simp[abi_encode_empty_complex_body_probe] >> strip_tac >>
  gvs[] >> irule frag_exec_refl >> simp[]
QED

(* Context transport and the real-function frame use the very same phase
   witnesses, rather than independently obtained execution endpoints. *)
Theorem abi_encode_empty_phases_caller:
  abi_encode_empty_phases_result (ctx with ctx_functions := [obs]) obs
    st ready body_end final ops len method_id outsz p w d m at av initial /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  abi_builtin_encode_finish (FST ops) len m body_end = ((),final) /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  outsz = 32+32*word_size (maxlen+m) /\
  fn_has_code st ready obs /\ fn_has_code ready body_end obs /\
  fn_has_code body_end final obs /\ fn_inst_ids_distinct obs /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
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
  qpat_x_assum `abi_encode_empty_phases_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encode_empty_phases_result_def]) >>
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
