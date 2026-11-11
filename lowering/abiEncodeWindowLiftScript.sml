(* Composition of the live-window ABI builtin phases. *)
Theory abiEncodeWindowLift
Ancestors
  abiEncodeWindowBytes abiEncodeWindowTransport abiBuiltinEncodeCode abiBuiltinEncodeContext
  abiEncoderWindowRunMem abiEncoderWindowContract abiEncoderWindowPhase
  abiEncoderRegisteredEffect abiBuiltinAllocation abiBuiltinEncodeMethod
  compileEnv emitHelper venomState venomExecSemantics words list arithmetic
  pred_set finite_map memContinuation fragExec freshWrites abiDecoderReentry

Theorem abi_encode_endpoint_chain[local]:
  window_phase ctx func st ready {st.cs_next_id}
    (case mid of NONE => [] | SOME _ => [(p+32,32)]) s u /\
  window_phase ctx func ready body_end scratch
    [(p+32+(case mid of NONE => 0 | SOME _ => 4),LENGTH payload)] u t /\
  window_phase ctx func body_end final {} [(p,32)] t t' /\
  mem_cont_sim ctx func s u /\ mem_cont_sim ctx func u t /\ mem_cont_sim ctx func t t' /\
  st.cs_next_var <= ready.cs_next_var /\ ready.cs_next_var <= body_end.cs_next_var /\
  st.cs_next_id IN ids /\ scratch SUBSET ids /\ 32 <= n /\
  (IS_SOME mid ==> 64 <= n) /\
  (case mid of NONE => 0 | SOME _ => 4) + LENGTH payload <= n-32 /\
  p+n <= t.vs_alloca_next ==>
  window_phase ctx func st final ids [(p,n)] s t' /\
  mem_cont_sim ctx func s t' /\ p+n <= t'.vs_alloca_next /\
  (!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP t'.vs_allocas i = SOME r)
Proof
  strip_tac >>
  `window_phase ctx func st body_end ids [(p,n)] s t` by
    (irule window_phase_chain >>
     qpat_assum `window_phase _ _ st ready _ _ s u` (fn th => irule_at Any th) >>
     qpat_assum `window_phase _ _ ready body_end _ _ u t` (fn th => irule_at Any th) >>
     asm_rewrite_tac[] >> simp_tac (srw_ss()) [SUBSET_DEF] >>
     Cases_on `mid` >> gvs[] >> intLib.COOPER_TAC) >>
  `window_phase ctx func st final ids [(p,n)] s t'` by
    (irule window_phase_chain >>
     qpat_assum `window_phase _ _ st body_end _ _ s t` (fn th => irule_at Any th) >>
     qpat_assum `window_phase _ _ body_end final _ _ t t'` (fn th => irule_at Any th) >>
     asm_rewrite_tac[] >> simp_tac (srw_ss()) [] >>
     simp[LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  `mem_cont_sim ctx func s t'` by metis_tac[mem_cont_sim_trans] >>
  `p+n <= t'.vs_alloca_next` by
    metis_tac[window_phase_resources, window_alloca_growth_def, LESS_EQ_TRANS] >>
  metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated]
QED

Theorem abi_encode_after_setup_window_mem[local]:
  abi_builtin_encode_setup mid maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len k body_end = ((),final) /\
  k = (case mid of NONE => 0 | SOME _ => 4) /\ n = 32+32*word_size (maxlen+k) /\
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap s.vs_memory /\
  LENGTH (enc at av) <= maxlen /\ eval_operand src s = SOME (n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\ sb+cap <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (p,n) /\
  (!i b sz. i IN window_alloca_sites func (frag_ids st final) /\ i <> st.cs_next_id /\
    FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
  window_phase ctx func st ready {st.cs_next_id}
    (case mid of NONE => [] | SOME _ => [(p+32,32)]) s u /\
  eval_operand (SND ops) u = SOME (n2w (p+32+k)) /\
  FLOOKUP u.vs_allocas st.cs_next_id = SOME (p,n) /\
  p+n <= u.vs_alloca_next /\ p+n < dimword (:256) /\
  mem_cont_sim ctx func s u /\ eval_operand (FST ops) u = SOME (n2w p) /\
  (case mid of NONE => T | SOME m => mem_bytes_at (p+32) 4 u.vs_memory = abi_builtin_encode_method_bytes m) ==>
  ?v. window_phase ctx func st final (window_alloca_sites func (frag_ids st final)) [(p,n)] s v /\
    mem_cont_sim ctx func s v /\ eval_operand (FST ops) v = SOME (n2w p) /\
    FLOOKUP v.vs_allocas st.cs_next_id = SOME (p,n) /\ p+n <= v.vs_alloca_next /\ p+n < dimword (:256) /\
    mem_bytes_at (p+32) (LENGTH (case mid of NONE => enc at av | SOME m => abi_builtin_encode_method_bytes m ++ enc at av)) v.vs_memory =
      (case mid of NONE => enc at av | SOME m => abi_builtin_encode_method_bytes m ++ enc at av) /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+k))))
      (vyperValue$BytesV (case mid of NONE => enc at av | SOME m => abi_builtin_encode_method_bytes m ++ enc at av)) p v.vs_memory /\
    (!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP v.vs_allocas i = SOME r)
Proof
  strip_tac >> drule_all abi_builtin_encode_code >> strip_tac >>
  drule_all abi_encode_window_pre_transport >> disch_tac >>
  drule_all compile_abi_encode_to_buf_window_strong_mem >> strip_tac >>
  `abi_builtin_encode_finish (FST ops) len (case mid of NONE => 0 | SOME _ => 4) body_end = ((),final)` by
    (qpat_x_assum `k = _` SUBST_ALL_TAC >> asm_rewrite_tac[]) >>
  drule_all abi_encode_window_sites >> strip_tac >>
  `k + LENGTH (enc at av) <= n-32 /\ 32 <= n` by
    (qpat_x_assum `n = _` SUBST_ALL_TAC >>
     qpat_x_assum `LENGTH (enc at av) <= maxlen` mp_tac >>
     mp_tac (Q.SPEC `maxlen+k` abi_builtin_word_size_capacity) >>
     qabbrev_tac `ww = word_size (maxlen+k)` >> intLib.COOPER_TAC) >>
  `case mid of NONE => T | SOME m => mem_bytes_at (p+32) 4 t.vs_memory = abi_builtin_encode_method_bytes m` by
    (qpat_x_assum `k = _` SUBST_ALL_TAC >> drule_all abi_encode_selector_window_frame >> simp_tac bool_ss []) >>
  drule window_phase_strong_result >> disch_tac >>
  drule window_strong_result_public >> disch_tac >>
  drule abi_encoder_window_result_output >> strip_tac >>
  `alloca_inv t /\ alloca_room ctx func t` by metis_tac[window_phase_resources] >>
  `~t.vs_halted /\ t.vs_current_bb = body_end.cs_current_bb /\
    t.vs_inst_idx = LENGTH body_end.cs_current_insts` by metis_tac[window_phase_control] >>
  `FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n)` by
    metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `p+n <= t.vs_alloca_next` by
    metis_tac[window_phase_resources, window_alloca_growth_def, LESS_EQ_TRANS] >>
  `p < dimword (:256) /\ p+32 <= t.vs_alloca_next` by intLib.COOPER_TAC >>
  `!x. FST ops = Var x ==> not_fresh_at ready x` by
    (drule abi_builtin_encode_setup_live >> strip_tac >> rpt strip_tac >>
     qpat_x_assum `abi_decoder_operand_live ready.cs_next_var (FST ops)` mp_tac >>
     qpat_x_assum `FST ops = Var x` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `eval_operand (FST ops) t = SOME (n2w p)` by metis_tac[window_phase_operand] >>
  `!x. FST ops = Var x ==> not_fresh_at body_end x` by metis_tac[not_fresh_at_mono] >>
  qpat_x_assum `k = _` SUBST_ALL_TAC >>
  drule_all abi_encode_finish_window_bytes >> strip_tac >>
  `IS_SOME mid ==> 64 <= n` by
    (qpat_x_assum `n = _` SUBST_ALL_TAC >> Cases_on `mid` >> simp_tac (srw_ss()) [] >>
     mp_tac (Q.SPEC `maxlen+4` abi_builtin_word_size_capacity) >>
     POP_ASSUM_LIST (K all_tac) >> intLib.COOPER_TAC) >>
  drule_all abi_encode_endpoint_chain >> strip_tac >> qexists_tac `t'` >> asm_rewrite_tac[]
QED

Theorem lower_abi_encode_window_mem:
  let k = (case mid of NONE => 0 | SOME _ => 4) in
  let n = 32+32*word_size (maxlen+k) in
  let ids = window_alloca_sites func (frag_ids st final) in
  let bytes = (case mid of NONE => enc at av | SOME m => abi_builtin_encode_method_bytes m ++ enc at av) in
  lower_abi_encode ensure mid src ei maxlen st = (out,final) /\
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap s.vs_memory /\
  LENGTH (enc at av) <= maxlen /\ eval_operand src s = SOME (n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\ n < dimword (:256) /\
  ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,n)) /\
  sb+cap <= s.vs_alloca_next /\ venomMemDefs$regions_disjoint (sb,cap) (p,n) /\
  (!i b sz. i IN ids /\ i <> st.cs_next_id /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st final ids [(p,n)] s t /\ mem_cont_sim ctx func s t /\
    eval_operand out t = SOME (n2w p) /\ FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n) /\
    p+n <= t.vs_alloca_next /\ p+n < dimword (:256) /\
    mem_bytes_at (p+32) (LENGTH bytes) t.vs_memory = bytes /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+k)))) (vyperValue$BytesV bytes) p t.vs_memory /\
    (!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r)
Proof
  pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  qabbrev_tac `k = (case mid of NONE => 0 | SOME _ => 4)` >>
  qabbrev_tac `n = 32+32*word_size (maxlen+k)` >>
  qabbrev_tac `ids = window_alloca_sites func (frag_ids st final)` >>
  qabbrev_tac `bytes = (case mid of NONE => enc at av | SOME m => abi_builtin_encode_method_bytes m ++ enc at av)` >>
  strip_tac >>
  drule lower_abi_encode_trace >> strip_tac >>
  drule_all abi_builtin_encode_code >> strip_tac >>
  `!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = n` by
    metis_tac[optionTheory.SOME_11, optionTheory.NOT_SOME_NONE, pairTheory.PAIR_EQ] >>
  `?u q. window_phase ctx func st ready {st.cs_next_id}
      (case mid of NONE => [] | SOME _ => [(q+32,32)]) s u /\
    mem_cont_sim ctx func s u /\ eval_operand (FST ops) u = SOME (n2w q) /\
    eval_operand (SND ops) u = SOME (n2w (q+32+k)) /\
    FLOOKUP u.vs_allocas st.cs_next_id = SOME (q,n) /\
    q+n <= u.vs_alloca_next /\ q+n < dimword (:256) /\
    ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ q = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas st.cs_next_id = SOME (q,n)) /\
    (case mid of NONE => T | SOME m =>
      mem_bytes_at (q+32) 4 u.vs_memory = abi_builtin_encode_method_bytes m)` by
    (qpat_x_assum `Abbrev (n = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_x_assum `Abbrev (k = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_x_assum `n = _` SUBST_ALL_TAC >>
     qpat_x_assum `k = _` SUBST_ALL_TAC >>
     drule_all abi_encode_setup_window_bytes >> simp_tac bool_ss [ADD_ASSOC]) >>
  `q = p` by metis_tac[optionTheory.SOME_11, optionTheory.NOT_SOME_NONE, pairTheory.PAIR_EQ] >>
  qpat_x_assum `q = p` SUBST_ALL_TAC >>
  qpat_assum `Abbrev (k = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (n = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (bytes = _)` (fn th => rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
  qpat_x_assum `Abbrev (ids = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `k = _` SUBST_ALL_TAC >>
  qpat_x_assum `out = _` SUBST_ALL_TAC >>
  irule abi_encode_after_setup_window_mem >>
  qpat_assum `abi_builtin_encode_setup _ _ _ = _` (fn th => irule_at Any th) >>
  qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` (fn th => irule_at Any th) >>
  qpat_assum `window_phase _ _ st ready _ _ s u` (fn th => irule_at Any th) >>
  qpat_assum `abi_encoder_window_input _ _ _ _ _ _` (fn th => irule_at Any th) >>
  asm_rewrite_tac[]
QED

