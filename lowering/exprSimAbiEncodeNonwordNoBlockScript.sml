Theory exprSimAbiEncodeNonwordNoBlock
Ancestors
  exprSimAbiEncodeConcreteBuiltinWrappers exprSimAbiEncodeConcreteBody
  exprSimAbiEncodeConcreteCompose exprSimAbiEncodeConcreteWrappers
  exprSimAbiEncodeNoBlockBoundary exprSimAbiEncodeExecution
  exprSimAbiEncodeProducerExecution exprSimAbiEncodeRelabelResources
  abiEncoderWindowContract abiDecoderContract abiDecoderLoop
  exprSimAbiEncodeOpenSetup exprSimAbiEncodeConcreteResources
  abiBuiltinEncodeCode abiBuiltinEncodeSetup
  emitHelperProps exprLoweringProps compileEnv venomState list words
  exprSimAbiEncodeEmptySource abiEncoderLeaves abiEncoderWindowLeaves
  abiEncoderPrimitiveEffect abiEncoderExtendSim abiEncoderRegisteredEffect
  abiEncoderWindowLookup abiEncoderWindow valueEncodingProofs venomExecSemantics

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
  ready.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  sb+cap <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  d+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (enc at av)) /\
  (sb+cap <= p+32 \/ p+32+w <= sb) /\
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
    actual.vs_inst_idx = LENGTH final.cs_current_insts
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_window_setup_concrete >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK setup_raw` >>
  qmatch_asmsub_abbrev_tac `abi_builtin_encode_setup_frame _ _ _ _ _ initial prepared` >>
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
  suspend "body"
QED

Resume abi_encode_window_concrete_phases[body]:
  `ready.cs_blocks = body_end.cs_blocks` by
    (drule abi_builtin_encode_setup_shape >> strip_tac >>
     drule abi_builtin_encode_finish_shape >> strip_tac >> metis_tac[]) >>
  mp_tac (SPEC_ALL abi_encode_concrete_contract_all) >>
  rewrite_tac[abi_encode_concrete_contract_def] >>
  disch_then drule_all >>
  simp_tac bool_ss [abi_encode_concrete_result_def] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts ready body_end) prepared = OK body_raw` >>
  qmatch_asmsub_abbrev_tac `window_strong_result ctx func ready body_end len at av d prepared body_state` >>
  `eval_operand (FST ops) body_state = SOME (n2w p)` by
    (irule abi_encode_setup_buffer_eval >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE
      [window_strong_result_def, abi_encoder_window_result_def]) >>
  suspend "finish"
QED

Resume abi_encode_window_concrete_phases[finish]:
  `fresh_vars_wrt limit_st body_state` by
    (irule abi_encode_high_vars_fresh >>
     qexistsl_tac [`body_end`, `prepared`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule abi_encode_window_finish_concrete >>
  disch_then (drule_at (Pat `window_strong_result _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (qspecl_then [`p`, `LENGTH (enc at av)`,
    `mem_bytes_at (p+32) (m+LENGTH (enc at av)) body_state.vs_memory`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts body_end final) body_state = OK finish_raw` >>
  qmatch_asmsub_abbrev_tac `abi_decode_frame p 32 body_state actual` >>
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
  metis_tac[]
QED
Finalise abi_encode_window_concrete_phases

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
