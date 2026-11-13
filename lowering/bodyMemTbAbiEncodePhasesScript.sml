(* Memory-checked execution of lower_abi_encode's three phases (buffer setup,
   window encoder body, length store) for any body shape, loops included:
   the counted twin of exprSimAbiEncodeTranslatedPhases. *)
Theory bodyMemTbAbiEncodePhases
Ancestors
  exprSimAbiEncodeTranslatedPhases abiEncoderWindowRunMem
  exprSimAbiEncodeConcreteBuiltinWrappers exprSimAbiEncodeConcreteResources
  exprSimAbiEncodeExecution exprSimAbiEncodeFramedBuiltin exprSimAbiEncodeExecFrame
  exprSimAbiEncodeEmptySource abiEncoderWindowContract abiEncoderWindow abiEncoderLeaves
  abiBuiltinEncodeCode abiBuiltinEncodeSetup abiBuiltinAllocation abiDecoderReentry
  abiDecoderContract valueEncodingDefs
  allocaFootprint instMemFrontier fragExecMem fragGasSeqMem fragGasPathMem memSafeRun
  entryDecoderHistoryFrame emitHelperProps exprLoweringProps emitHelper compileEnv
  context venomExecSemantics venomState venomInst venomMemDefs vfmConstants
  finite_map list rich_list words arithmetic
Libs
  stepInstBaseLib

(* ===== Exact phase code ===== *)

Theorem abi_builtin_encode_setup_insts:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) ==>
  emitted_insts st ready =
    [mk_inst st.cs_next_id ALLOCA
       [Lit (n2w (32+32*word_size (maxlen+(case method_id of NONE => 0 | SOME _ => 4))))]
       [STRING #"%" (toString st.cs_next_var)];
     mk_inst (st.cs_next_id+1) ADD
       [Var (STRING #"%" (toString st.cs_next_var));
        Lit (n2w (32+(case method_id of NONE => 0 | SOME _ => 4)))]
       [STRING #"%" (toString (st.cs_next_var+1))]] ++
    (case method_id of
       NONE => []
     | SOME mid =>
       [mk_inst (st.cs_next_id+2) ADD
          [Var (STRING #"%" (toString st.cs_next_var)); Lit 32w]
          [STRING #"%" (toString (st.cs_next_var+2))];
        mk_inst (st.cs_next_id+3) MSTORE
          [Var (STRING #"%" (toString (st.cs_next_var+2))); Lit (mid << 224)] []])
Proof
  Cases_on `method_id` >>
  simp[abi_builtin_encode_setup_def, abi_builtin_encode_method_id_def,
    compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND]
QED

Theorem abi_builtin_encode_finish_insts:
  abi_builtin_encode_finish buf len m st = ((),final) ==>
  emitted_insts st final =
    if m > 0 then
      [mk_inst st.cs_next_id ADD [len; Lit (n2w m)] [STRING #"%" (toString st.cs_next_var)];
       mk_inst (st.cs_next_id+1) MSTORE [buf; Var (STRING #"%" (toString st.cs_next_var))] []]
    else [mk_inst st.cs_next_id MSTORE [buf; len] []]
Proof
  Cases_on `m > 0` >>
  simp[abi_builtin_encode_finish_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND]
QED

(* ===== Memory checks of the straight-line phases ===== *)

Theorem abi_encode_straight_path_mem:
  fn_has_code sa sb func /\ inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n. gas_path_mem ctx func s n (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    (fs[inst_extends_def] >> metis_tac[IS_PREFIX_APPEND]) >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (fs[inst_extends_def] >> qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >> simp[]) >>
  metis_tac[]
QED

Theorem abi_encode_method_store_mem_ok[local]:
  FLOOKUP (abi_builtin_allocate_state id outsz s).vs_allocas id = SOME (p,outsz) /\
  alloca_next_valid (abi_builtin_allocate_state id outsz s) /\
  outsz < dimword (:256) /\ p+32 < dimword (:256) /\ 64 <= outsz /\
  b <> d /\ b <> m ==>
  run_inst_seq_mem_ok
    [mk_inst id ALLOCA [Lit (n2w outsz)] [b];
     mk_inst id1 ADD [Var b; Lit c] [d];
     mk_inst id2 ADD [Var b; Lit 32w] [m];
     mk_inst id3 MSTORE [Var m; Lit x] []] s
Proof
  strip_tac >>
  drule_all step_alloca_site >> disch_then (qspec_then `b` assume_tac) >>
  `p + outsz <= (abi_builtin_allocate_state id outsz s).vs_alloca_next` by
    (fs[alloca_next_valid_def] >> res_tac >> decide_tac) >>
  qabbrev_tac `a = abi_builtin_allocate_state id outsz s` >>
  `step_inst_base (mk_inst id1 ADD [Var b; Lit c] [d]) (update_var b (n2w p) a) =
     OK (update_var d (n2w p + c) (update_var b (n2w p) a))` by
    (irule step_ADD >> simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst id2 ADD [Var b; Lit 32w] [m])
     (update_var d (n2w p + c) (update_var b (n2w p) a)) =
   OK (update_var m (n2w p + 32w) (update_var d (n2w p + c) (update_var b (n2w p) a)))` by
    (irule step_ADD >> simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  asm_simp_tac (srw_ss()) [run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
    below_frontier_MSTORE] >>
  simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, word_add_n2w,
    below_frontier_no_ranges, inst_dload_in_section_def, mk_inst_def]
QED

Theorem abi_encode_setup_mem_ok[local]:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  outsz = 32+32*word_size (maxlen+m) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  outsz < dimword (:256) /\ (method_id <> NONE ==> p+32 < dimword (:256)) ==>
  run_inst_seq_mem_ok (emitted_insts st ready) initial
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas
     st.cs_next_id = SOME (p,outsz)` by
    (rewrite_tac[alloca_site_cases] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `_ \/ _` kall_tac >>
  drule abi_builtin_encode_setup_insts >>
  disch_then SUBST1_TAC >> Cases_on `method_id` >> gvs[]
  >- (irule run_inst_seq_mem_ok_every >>
      simp[below_frontier_no_ranges, inst_dload_in_section_def, mk_inst_def]) >>
  `1 <= word_size (maxlen + 4)` by simp[word_size_def, X_LE_DIV] >>
  irule abi_encode_method_store_mem_ok >>
  fs[alloca_inv_def, ASCIInumbersTheory.toString_inj] >> metis_tac[]
QED

Theorem abi_encode_finish_mem_ok[local]:
  abi_builtin_encode_finish buf len m st = ((),final) /\
  eval_operand buf s = SOME (n2w p) /\ eval_operand len s = SOME lw /\
  p + 32 <= s.vs_alloca_next /\ p < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var buf ==>
  run_inst_seq_mem_ok (emitted_insts st final) s
Proof
  strip_tac >> drule abi_builtin_encode_finish_insts >>
  disch_then SUBST1_TAC >> IF_CASES_TAC
  >- (`step_inst_base (mk_inst st.cs_next_id ADD [len; Lit (n2w m)]
         [STRING #"%" (toString st.cs_next_var)]) s =
       OK (update_var (STRING #"%" (toString st.cs_next_var)) (lw + n2w m) s)` by
        (irule step_ADD >> simp[eval_operand_def]) >>
      `eval_operand buf
         (update_var (STRING #"%" (toString st.cs_next_var)) (lw + n2w m) s) =
       SOME (n2w p)` by
        (irule eval_operand_update_other_local >> simp[] >>
         Cases_on `buf` >>
         fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def]) >>
      asm_simp_tac (srw_ss()) [run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
        below_frontier_MSTORE] >>
      simp[below_frontier_no_ranges, inst_dload_in_section_def, mk_inst_def]) >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
  simp[inst_dload_in_section_def, mk_inst_def]
QED

(* ===== Empty encoder bodies ===== *)

Theorem abi_encode_zero_window_input[local]:
  (ei = AbiCopy 0 \/ ei = AbiComplex []) /\
  abi_encoder_window_input ei at av sb 0 mem ==>
  abi_encoder_window_input ei at av 0 0 mem
Proof
  strip_tac >> gvs[]
  >- (pop_assum mp_tac >>
      simp_tac std_ss [abi_encoder_window_copy_iff, valueEncodingDefsTheory.mem_bytes_at_def,
        listTheory.TAKE_0]) >>
  pop_assum mp_tac >> simp[Once abi_encoder_window_input_cases] >>
  strip_tac >> simp[Once abi_encoder_window_input_cases] >> metis_tac[]
QED

Theorem abi_encode_zero_body[local]:
  (ei = AbiCopy 0 \/ ei = AbiComplex []) /\
  compile_abi_encode_to_buf dst src ei st = (len,en) ==>
  len = Lit 0w /\ inst_extends st en /\ same_blocks st en /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st en) /\
  (!s. run_inst_seq_mem_ok (emitted_insts st en) s) /\
  (!s u. run_inst_seq (emitted_insts st en) s = OK u ==>
    u.vs_vars = s.vs_vars /\ u.vs_labels = s.vs_labels /\
    u.vs_alloca_next = s.vs_alloca_next)
Proof
  strip_tac >> gvs[]
  >- (drule abi_encode_copy_code >> strip_tac >>
      drule emit_void_extends >> strip_tac >>
      drule emitted_insts_emit_void >> strip_tac >>
      `!s. run_inst_seq_mem_ok (emitted_insts st en) s` by
        (simp[run_inst_seq_mem_ok_last, below_frontier_MCOPY, eval_operand_def] >>
         simp[inst_dload_in_section_def, mk_inst_def]) >>
      `!s u. run_inst_seq (emitted_insts st en) s = OK u ==>
         u.vs_vars = s.vs_vars /\ u.vs_labels = s.vs_labels /\
         u.vs_alloca_next = s.vs_alloca_next` by
        (simp[run_inst_seq_def, AllCaseEqs(), PULL_EXISTS] >>
         rpt gen_tac >> simp[simp_opcode_clause ``MCOPY``] >>
         simp[eval_operand_def, mcopy_def, write_memory_with_expansion_def,
           AllCaseEqs(), PULL_EXISTS] >>
         rw[] >> simp[]) >>
      gvs[inst_extends_def, mk_inst_def, is_terminator_def]) >>
  gvs[abi_encode_empty_complex_body_probe, inst_extends_def, same_blocks_def,
    emitted_insts_def, run_inst_seq_mem_ok_def, run_inst_seq_def]
QED

(* ===== Three phases ===== *)

Theorem abi_encode_phases_mem:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len m body_end = ((),final) /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  d = p+32+m /\ outsz = 32+32*word_size (maxlen+m) /\
  fn_has_code st final func /\
  fn_has_code st ready func /\ fn_has_code ready body_end func /\
  fn_has_code body_end final func /\ fn_inst_ids_distinct func /\
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
  (cap = 0 ==> (ei = AbiCopy 0 \/ ei = AbiComplex []) /\ enc at av = []) /\
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
  ?n actual. gas_path_mem ctx func initial n (OK actual) /\
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
  `p + outsz <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next` by
    (qpat_assum `alloca_inv (abi_builtin_allocate_state _ _ _)`
       (strip_assume_tac o REWRITE_RULE [alloca_inv_def, alloca_next_valid_def]) >>
     first_x_assum irule >> qexists_tac `st.cs_next_id` >>
     metis_tac[alloca_site_cases]) >>
  Cases_on `cap = 0` >- suspend "zero" >> suspend "positive"
QED

Resume abi_encode_phases_mem[positive]:
  qpat_x_assum `0 < cap ==> _` mp_tac >>
  (impl_tac >- decide_tac) >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_window_input _ _ _ _ _ _`
    (mp_then (Pat `abi_encoder_window_input _ _ _ _ _ _`) mp_tac abi_encode_window_setup_concrete) >>
  disch_then (drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`w`, `p`, `outsz`, `m`, `ctx`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `setup_raw` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qmatch_asmsub_abbrev_tac `abi_builtin_encode_setup_frame _ _ _ _ _ initial prepared` >>
  `abi_encode_exec_frame func initial prepared` by
    (`EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;MSTORE]) (emitted_insts st ready)` by
       (drule abi_builtin_encode_setup_insts >> disch_then SUBST1_TAC >>
        Cases_on `method_id` >>
        simp_tac bool_ss [optionTheory.option_case_def, APPEND, EVERY_DEF, mk_inst_opcode, MEM]) >>
     drule_all abi_encode_setup_sequence_frame >>
     simp_tac bool_ss [Abbr `prepared`, abi_encode_exec_frame_inst_idx]) >>
  `?n1. gas_path_mem ctx func initial n1 (OK prepared)` by
    (simp_tac bool_ss [Abbr `prepared`] >>
     irule abi_encode_straight_path_mem >> simp_tac bool_ss [PULL_EXISTS] >> qexists_tac `st` >>
     drule_all abi_encode_setup_mem_ok >> strip_tac >>
     drule abi_builtin_encode_setup_shape >> strip_tac >>
     asm_rewrite_tac[]) >>
  suspend "body"
QED

Resume abi_encode_phases_mem[body]:
  `abi_encoder_window_pre ctx func ready body_end (SND ops) src ei at av sb cap d prepared` by
    (qpat_x_assum `d = _` SUBST_ALL_TAC >>
     qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
     qpat_x_assum `m = _` SUBST_ALL_TAC >>
     irule (SIMP_RULE bool_ss [LET_THM] abi_encode_setup_window_pre) >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     qexistsl_tac [`initial`, `st.cs_next_var`,
       `32+32*word_size (maxlen+(case method_id of NONE => 0 | SOME mid => 4))`,
       `p`, `st.cs_next_id`, `w`] >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     rpt strip_tac >>
     qpat_x_assum `!inst b sz. _` (qspecl_then [`inst`, `b`, `sz`] mp_tac) >>
     asm_rewrite_tac[] >> simp_tac bool_ss []) >>
  drule_all compile_abi_encode_to_buf_window_strong_counted_mem >>
  disch_then (qx_choosel_then [`body_state`, `n2`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `eval_operand (FST ops) body_state = SOME (n2w p)` by
    (irule abi_encode_setup_buffer_eval >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  `p + 32 <= body_state.vs_alloca_next` by
    (qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [abi_builtin_encode_setup_frame_def]) >>
     qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [window_strong_result_def, window_alloca_growth_def]) >>
     decide_tac) >>
  qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE
      [window_strong_result_def, abi_encoder_window_result_def]) >>
  suspend "finish"
QED

Resume abi_encode_phases_mem[finish]:
  drule abi_encode_window_finish_concrete >>
  disch_then (drule_at (Pat `window_strong_result _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`p`, `LENGTH (enc at av)`,
    `mem_bytes_at (p+32) (m+LENGTH (enc at av)) body_state.vs_memory`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts body_end final) body_state = OK finish_raw` >>
  qmatch_asmsub_abbrev_tac `abi_decode_frame p 32 body_state actual` >>
  `?n3. gas_path_mem ctx func body_state n3 (OK actual)` by
    (simp_tac bool_ss [Abbr `actual`] >>
     irule abi_encode_straight_path_mem >> simp_tac bool_ss [PULL_EXISTS] >> qexists_tac `body_end` >>
     `run_inst_seq_mem_ok (emitted_insts body_end final) body_state` by
       (irule abi_encode_finish_mem_ok >> asm_rewrite_tac[] >> metis_tac[]) >>
     drule abi_builtin_encode_finish_shape >> strip_tac >>
     asm_rewrite_tac[]) >>
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

Resume abi_encode_phases_mem[result]:
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
  qexistsl_tac [`n1 + n2 + n3`, `actual`] >>
  conj_tac >- metis_tac[gas_path_mem_then] >>
  asm_rewrite_tac[] >>
  qexistsl [`prepared`, `body_state`] >> asm_rewrite_tac[] >> metis_tac[]
QED

Resume abi_encode_phases_mem[zero]:
  `enc at av = []` by metis_tac[] >>
  qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _`
    (mp_then (Pos last) mp_tac abi_encode_zero_body) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  `st.cs_blocks = final.cs_blocks /\ final.cs_current_bb = st.cs_current_bb` by
    (qpat_assum `same_blocks ready body_end`
       (strip_assume_tac o REWRITE_RULE [same_blocks_def]) >>
     metis_tac[]) >>
  drule_all abi_encode_translated_concrete_phases >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  suspend "path"
QED

Resume abi_encode_phases_mem[path]:
  `abi_encoder_window_input ei at av 0 0 initial.vs_memory` by
    metis_tac[abi_encode_zero_window_input] >>
  qpat_assum `abi_encoder_window_input _ _ _ 0 0 _`
    (mp_then (Pat `abi_encoder_window_input _ _ _ _ _ _`) mp_tac abi_encode_window_setup_concrete) >>
  disch_then (drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`w`, `p`, `outsz`, `m`, `ctx`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp_tac arith_ss [])) >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `setup_raw` strip_assume_tac) >>
  `inst_extends st body_end /\ inst_extends st final` by
    metis_tac[inst_extends_trans] >>
  `emitted_insts st final =
     emitted_insts st ready ++ (emitted_insts ready body_end ++ emitted_insts body_end final)` by
    (`emitted_insts st body_end = emitted_insts st ready ++ emitted_insts ready body_end` by
       (irule emitted_insts_append >> REWRITE_TAC [GSYM inst_extends_def] >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     `emitted_insts st final = emitted_insts st body_end ++ emitted_insts body_end final` by
       (irule emitted_insts_append >> REWRITE_TAC [GSYM inst_extends_def] >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     asm_rewrite_tac[APPEND_ASSOC]) >>
  `run_inst_seq_mem_ok (emitted_insts st ready) initial` by
    (drule_all abi_encode_setup_mem_ok >> disch_then ACCEPT_TAC) >>
  `!s1. run_inst_seq (emitted_insts st ready) initial = OK s1 ==>
     run_inst_seq_mem_ok (emitted_insts ready body_end ++ emitted_insts body_end final) s1` by
    (qx_gen_tac `s1` >> strip_tac >>
     `s1 = setup_raw` by
       (qpat_x_assum `run_inst_seq (emitted_insts st ready) initial = OK s1` mp_tac >>
        qpat_assum `run_inst_seq (emitted_insts st ready) initial = OK setup_raw`
          (fn th => rewrite_tac [th]) >>
        simp_tac (srw_ss()) []) >>
     pop_assum SUBST_ALL_TAC >>
     match_mp_tac run_inst_seq_mem_ok_append >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     qx_gen_tac `s2` >> strip_tac >>
     qpat_assum `!s u. run_inst_seq (emitted_insts ready body_end) s = OK u ==> _`
       (drule_then strip_assume_tac) >>
     `eval_operand (FST ops) s2 = SOME (n2w p)` by
       (qpat_assum `eval_operand (FST ops) (setup_raw with vs_inst_idx := _) = _`
          (mp_tac o REWRITE_RULE [eval_operand_inst_idx]) >>
        metis_tac[eval_operand_same_vars]) >>
     `p + 32 <= s2.vs_alloca_next` by
       (qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _`
          (strip_assume_tac o SIMP_RULE (srw_ss()) [abi_builtin_encode_setup_frame_def]) >>
        decide_tac) >>
     `eval_operand len s2 = SOME 0w` by
       (qpat_assum `len = Lit 0w` SUBST1_TAC >> simp_tac (srw_ss()) [eval_operand_def]) >>
     drule_all abi_encode_finish_mem_ok >> disch_then ACCEPT_TAC) >>
  `run_inst_seq_mem_ok (emitted_insts st final) initial` by
    (qpat_x_assum `emitted_insts st final = _` SUBST1_TAC >>
     match_mp_tac run_inst_seq_mem_ok_append >> conj_tac >> first_assum ACCEPT_TAC) >>
  `?n. gas_path_mem ctx func initial n
     (OK (raw with vs_inst_idx := LENGTH final.cs_current_insts))` by
    (irule abi_encode_straight_path_mem >> simp_tac bool_ss [PULL_EXISTS] >> qexists_tac `st` >>
     asm_rewrite_tac[EVERY_APPEND]) >>
  qexistsl_tac [`n`, `raw with vs_inst_idx := LENGTH final.cs_current_insts`] >>
  qpat_x_assum `outsz = _` SUBST_ALL_TAC >> qpat_x_assum `d = _` SUBST_ALL_TAC >>
  qpat_x_assum `w = _` SUBST_ALL_TAC >> qpat_x_assum `m = _` SUBST_ALL_TAC >>
  qpat_x_assum `len = _` SUBST_ALL_TAC >>
  asm_rewrite_tac[] >> qexistsl [`prepared`, `body_state`] >> asm_rewrite_tac[]
QED

Finalise abi_encode_phases_mem
