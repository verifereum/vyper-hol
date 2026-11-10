(* Source mapping extension boundary for write-side subscripts. *)
Theory targetSubscriptMapping
Ancestors
  targetPlaceSimCasesBase loweringPosts vyperState exprSimHash exprSimHashBoundary exprSimMapKey fragGasMode
  supportedTypes vyperTypeSystem vyperTyping vyperValue valueEncoding valueEncodingDefs vyperStorage
  emitHelperProps venomInst exprSimAlloc exprSimPrecompiles exprSimProps compileEnv loweringStateRelDefs
  exprLowering exprLoweringProps emitHelper fragExec venomState words finite_map list arithmetic valueEncodingProps

Theorem target_mapping_extend_place:
  extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript kv) es =
    (INL pv, es') ==>
  es' = es /\
  place_ptr_rel cenv cx s pv (hashmap_slot slot (encode_hashmap_key kt kv))
    (SOME (slot_loc tr)) vt /\
  place_readable cx es' pv
Proof
  Cases_on `vt`
  >- (rename1 `Type typ` >>
      Cases_on `evaluate_type (get_tenv cx) typ` >>
      simp[extend_place_def, lift_option_type_def, bind_def,
           return_def, raise_def, place_ptr_rel_def, place_readable_def] >>
      rpt strip_tac >> gvs[place_ptr_rel_def, place_readable_def]) >>
  simp[extend_place_nested_mapping] >> rpt strip_tac >>
  gvs[place_ptr_rel_def, place_readable_def]
QED

Theorem target_SHA3_bytes_path:
  emit_op SHA3 [ptr_op; len] sa = (op,sb) /\ fn_has_code sa sb func /\
  eval_operand ptr_op s = SOME p /\ eval_operand len s = SOME n /\
  mem_bytes_at (w2n p) (w2n n) s.vs_memory = bs /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_marked_path F ctx func s 0
    (OK ((update_var (STRING #"%" (toString sa.cs_next_var))
       (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) s)
       with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> pure_rewrite_tac[gas_marked_path_def, COND_CLAUSES] >>
  irule emit_op_zero_path >> simp[] >>
  qexistsl_tac [`[ptr_op; len]`, `op`, `SHA3`, `sb`] >>
  simp[is_terminator_def] >> rpt strip_tac >>
  irule step_SHA3_bytes >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem target_scratch_store_frame:
  stmt_state_rel ctx func cenv cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= a /\ a + 32 <= b + sz /\
  (!aid off len. aid < sa.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
     regions_disjoint b sz off len) /\
  (!name off len. local_region cenv es.scopes s name off len ==>
     regions_disjoint b sz off len) ==>
  stmt_state_rel ctx func cenv cx es (mstore a w s) /\
  wb_frame cenv es sa s (mstore a w s)
Proof
  strip_tac >> conj_tac
  >- (irule literal_mstore_state_rel >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`b`, `inst`, `sz`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >>
      simp[regions_disjoint_def]) >>
  irule scratch_mstore_frame >> conj_tac >> rpt strip_tac >>
  first_x_assum drule >> simp[regions_disjoint_def] >> decide_tac
QED

Theorem target_mapping_scratch_bytes[local]:
  mem_bytes_at a 64 (mstore (a+32) kw (mstore a slot s)).vs_memory =
    word_to_bytes (slot:bytes32) T ++ word_to_bytes (kw:bytes32) T
Proof
  `a + 64 <= LENGTH (mstore (a+32) kw (mstore a slot s)).vs_memory` by
    (qmatch_goalsub_abbrev_tac `mstore (a+32) kw z` >>
     simp[Once mstore_def, byteTheory.LENGTH_word_to_bytes, LENGTH_TAKE, LENGTH_DROP] >>
     CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >>
     rw[] >> decide_tac) >>
  mp_tac (Q.SPECL [`a`, `32`, `32`,
    `(mstore (a+32) kw (mstore a slot s)).vs_memory`] mem_bytes_at_split) >>
  simp[mem_bytes_at_mstore_same, mstore_mem_bytes_at_disjoint]
QED

Theorem target_mapping_hash_suffix[local]:
  emit_void MSTORE [ptr_op; bop] sm = ((),sc) /\
  emit_op ADD [ptr_op; Lit 32w] sc = (kp,sd) /\
  emit_void MSTORE [kp; key] sd = ((),se) /\
  emit_op SHA3 [ptr_op; Lit 64w] se = (op,sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sm x) /\
  (!x. bop = Var x ==> not_fresh_at sm x) /\
  (!x. key = Var x ==> not_fresh_at sm x) /\
  eval_operand ptr_op s = SOME w /\ eval_operand bop s = SOME slot /\
  eval_operand key s = SOME kw /\ w2n w + 64 < dimword(:256) ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
      eval_operand op t = SOME (hashmap_slot slot kw) /\
      (t with vs_vars := s.vs_vars) =
        mstore (w2n w+32) kw (mstore (w2n w) slot s) /\
      (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  qpat_x_assum `emit_void MSTORE _ sm = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
  qpat_x_assum `emit_op ADD _ sc = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qpat_x_assum `emit_void MSTORE _ sd = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
  qpat_x_assum `emit_op SHA3 _ se = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qabbrev_tac `v0 = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `v1 = STRING #"%" (toString (sm.cs_next_var+1))` >>
  `v0 <> v1` by simp[Abbr `v0`, Abbr `v1`] >>
  `!x. not_fresh_at sm x ==> x <> v0 /\ x <> v1` by
    (simp[not_fresh_at_def, Abbr `v0`, Abbr `v1`] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qabbrev_tac `s1 = mstore (w2n w) slot s` >>
  qabbrev_tac `s2 = update_var v0 (n2w (w2n w+32)) s1` >>
  qabbrev_tac `s3 = mstore (w2n w+32) kw s2` >>
  `eval_operand ptr_op s1 = SOME w /\ eval_operand key s1 = SOME kw` by
    (Cases_on `ptr_op` >> Cases_on `key` >>
     gvs[Abbr `s1`, mstore_def, eval_operand_def, lookup_var_def]) >>
  `eval_operand ptr_op s2 = SOME w /\ eval_operand key s2 = SOME kw` by
    (Cases_on `ptr_op` >> Cases_on `key` >>
     gvs[Abbr `s2`, eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst sm.cs_next_id MSTORE [ptr_op;bop] []) s = OK s1` by
    (simp[Abbr `s1`] >> irule step_MSTORE >> simp[]) >>
  `step_inst_base (mk_inst (sm.cs_next_id+1) ADD [ptr_op;Lit 32w] [v0]) s1 = OK s2` by
    (simp[Abbr `s2`, GSYM word_add_n2w, n2w_w2n] >>
     irule step_ADD >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst (sm.cs_next_id+2) MSTORE [Var v0;key] []) s2 = OK s3` by
    (simp[Abbr `s3`] >> irule EQ_TRANS >> irule_at Any step_MSTORE >>
     `w2n w + 32 < dimword(:256)` by decide_tac >>
     fs[eval_operand_def, Abbr `s2`, lookup_var_update_var, w2n_n2w, LESS_MOD]) >>
  `eval_operand ptr_op s3 = SOME w` by
    (Cases_on `ptr_op` >> gvs[Abbr `s3`, mstore_def, eval_operand_def, lookup_var_def]) >>
  `mem_bytes_at (w2n w) 64 s3.vs_memory =
     word_to_bytes slot T ++ word_to_bytes kw T` by
    (`s3.vs_memory = (mstore (w2n w+32) kw s1).vs_memory` by
       simp[Abbr `s3`, Abbr `s2`, update_var_def, mstore_def] >>
     simp[Abbr `s1`, target_mapping_scratch_bytes]) >>
  `step_inst_base (mk_inst (sm.cs_next_id+3) SHA3 [ptr_op;Lit 64w] [v1]) s3 =
     OK (update_var v1 (hashmap_slot slot kw) s3)` by
    (simp[vyperStorageTheory.hashmap_slot_def, byteTheory.word_of_bytes_be_def,
          byteTheory.word_to_bytes_be_def] >>
     irule step_SHA3_bytes >> simp[eval_operand_def]) >>
  `emitted_insts sm sb = emitted_insts sm sc ++ emitted_insts sc sd ++
     emitted_insts sd se ++ emitted_insts se sb` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, APPEND_ASSOC] >>
  qexists_tac `update_var v1 (hashmap_slot slot kw) s3` >>
  conj_tac >- simp[Abbr `v0`, Abbr `v1`, run_inst_seq_def, ADD_ASSOC] >>
  conj_tac >- simp[eval_operand_def, lookup_var_update_var, Abbr `v1`] >>
  conj_tac
  >- (`s.vs_vars = s1.vs_vars` by simp[Abbr `s1`, mstore_def] >>
      pop_assum SUBST1_TAC >>
      simp[Abbr `s3`, Abbr `s2`, update_var_def, mstore_def]) >>
  rpt strip_tac >>
  simp[Abbr `s3`, Abbr `s2`, Abbr `s1`, lookup_var_update_var,
       mstore_def, lookup_var_def]
QED

Theorem target_mapping_scratch_preserve[local]:
  stmt_state_rel ctx func cenv cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (a,64) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint a 64 b sz) ==>
  stmt_state_rel ctx func cenv cx es (mstore (a+32) kw (mstore a slot s)) /\
  (!b sz. regions_disjoint a 64 b sz ==>
    mem_bytes_at b sz (mstore (a+32) kw (mstore a slot s)).vs_memory =
      mem_bytes_at b sz s.vs_memory)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es (mstore a slot s)` by
    (irule literal_mstore_state_rel >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`a`, `inst`, `64`] >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[regions_disjoint_def]) >>
  conj_tac
  >- (irule literal_mstore_state_rel >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`a`, `inst`, `64`] >> simp[mstore_def] >>
      gvs[local_region_def, regions_disjoint_def, lookup_var_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `mem_bytes_at b sz (mstore (a+32) kw (mstore a slot s)).vs_memory =
     mem_bytes_at b sz (mstore a slot s).vs_memory` by
    (irule mstore_region_frame >> qexistsl_tac [`a`, `64`] >> simp[]) >>
  simp[] >> irule mstore_region_frame >>
  qexistsl_tac [`a`, `64`] >> simp[]
QED

Theorem target_mapping_run:
  compile_mapping_subscript bop key sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ eval_operand key s = SOME kw ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (hashmap_slot slot kw) /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
         mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
      (!n b sz. local_region cenv es.scopes s n b sz ==>
         mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory)
Proof
  simp[compile_mapping_subscript_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_alloc_buffer 64 sa = (buf,sm)` >>
  rename1 `emit_void MSTORE [buf.buf_operand; bop] sm = (u1,sc)` >>
  rename1 `emit_op ADD _ sc = (kp,sd)` >>
  rename1 `emit_void MSTORE [kp; key] sd = (u2,se)` >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (`MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
       [STRING #"%" (toString sa.cs_next_var)]) sb.cs_current_insts` by
       gvs[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def,
           fresh_id_def, fresh_var_def, emit_def] >>
     gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
     irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
     gvs[MEM_APPEND]) >>
  `64 < dimword(:256)` by (simp[dimword_def] >> CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> decide_tac) >>
  drule literal_alloc_buffer_run >>
  disch_then drule >> simp[] >> strip_tac >>
  `t.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `eval_operand bop t = SOME slot /\ eval_operand key t = SOME kw` by
    (conj_tac >> Cases_on `bop` >> Cases_on `key` >>
     gvs[eval_operand_def]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspec_then `64` (qspec_then `sa` mp_tac) ci_mono_compile_alloc_buffer >>
     simp[ci_mono_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `w2n w + 64 < dimword(:256)` by
    (simp[dimword_def] >> CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> simp[]) >>
  Cases_on `u2` >>
  qpat_assum `emit_void MSTORE _ sm = _`
    (mp_then Any mp_tac target_mapping_hash_suffix) >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`w`, `slot`, `t`, `kw`] mp_tac) >>
  simp[] >> strip_tac >>
  `inst_extends sa sm` by
    (qpat_x_assum `compile_alloc_buffer _ sa = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >>
     drule inst_extends_emit_op >> simp[]) >>
  `inst_extends sm sc /\ inst_extends sc sd /\ inst_extends sd se /\ inst_extends se sb` by
    metis_tac[inst_extends_emit_void, inst_extends_emit_op] >>
  `inst_extends sm sb` by metis_tac[inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  qexists_tac `t'` >> conj_tac
  >- (asm_rewrite_tac[] >>
      qpat_assum `run_inst_seq (emitted_insts sa sm) _ = _`
        (mp_tac o MATCH_MP run_inst_seq_append) >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `emit_void MSTORE _ sm = _` kall_tac >>
  qpat_x_assum `emit_op ADD _ sc = _` kall_tac >>
  qpat_x_assum `emit_void MSTORE _ sd = _` kall_tac >>
  qpat_x_assum `emit_op SHA3 _ se = _` kall_tac >>
  `stmt_state_rel ctx func cenv cx es (t' with vs_vars := t.vs_vars)` by
    (asm_rewrite_tac[] >> irule (cj 1 target_mapping_scratch_preserve) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit 64w]
       [STRING #"%" (toString sa.cs_next_var)]` >> simp[mk_inst_def]) >>
  conj_tac
  >- (`t' = (t' with vs_vars := t.vs_vars) with vs_vars := t'.vs_vars` by simp[] >>
      pop_assum SUBST1_TAC >> irule stmt_state_rel_vars_frame >>
      simp[] >> gvs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  `t'.vs_allocas = t.vs_allocas` by
    (qpat_assum `t' with vs_vars := _ = _`
       (mp_tac o AP_TERM ``\z:venom_state. z.vs_allocas``) >>
     simp[mstore_def]) >>
  conj_tac >- metis_tac[] >>
  `t'.vs_memory = (mstore (w2n w+32) kw (mstore (w2n w) slot t)).vs_memory` by
    (qpat_assum `t' with vs_vars := _ = _`
       (mp_tac o AP_TERM ``\z:venom_state. z.vs_memory``) >> simp[]) >>
  `!b sz. regions_disjoint (w2n w) 64 b sz ==>
     mem_bytes_at b sz t'.vs_memory = mem_bytes_at b sz t.vs_memory` by
    (rpt strip_tac >>
     `mem_bytes_at b sz (mstore (w2n w+32) kw (mstore (w2n w) slot t)).vs_memory =
        mem_bytes_at b sz (mstore (w2n w) slot t).vs_memory` by
       (irule mstore_region_frame >> qexistsl_tac [`w2n w`, `64`] >> simp[]) >>
     `mem_bytes_at b sz (mstore (w2n w) slot t).vs_memory =
        mem_bytes_at b sz t.vs_memory` by
       (irule mstore_region_frame >> qexistsl_tac [`w2n w`, `64`] >> simp[]) >>
     metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `local_region cenv es.scopes t n b sz` by
    (irule local_region_frame_fwd >>
     qexistsl_tac [`s`, `sa`, `es.scopes`] >> simp[]) >>
  metis_tac[]
QED

Theorem target_mapping_scalar_encoding:
  hashmap_key_type kt /\ ~is_bytestring_type kt /\
  evaluate_type tenv kt = SOME tv /\ value_has_type tv key ==>
  typed_val_to_w256 tv key = encode_hashmap_key kt key
Proof
  Cases_on `kt` >> simp[hashmap_key_type_def] >>
  rpt strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `key` >>
  gvs[hashmap_key_type_def, is_bytestring_type_def,
      value_has_type_def, typed_val_to_w256_def, val_to_w256_def,
      encode_hashmap_key_def]
QED

Theorem target_mapping_scalar_operand:
  hashmap_key_type kt /\ ~is_bytestring_type kt /\ is_word_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv key /\
  expr_val_rel cx kt key op s ==>
  eval_operand op s = SOME (encode_hashmap_key kt key)
Proof
  strip_tac >> drule_all target_mapping_scalar_encoding >>
  gvs[expr_val_rel_def]
QED

(* Dynamic keys expose precisely the payload that the key hashing code reads.
   The conversion theory has local bytes/string projections; this shared
   mapping boundary additionally identifies the source hash encoding. *)
Theorem target_mapping_dynamic_operand:
  hashmap_key_type kt /\ is_bytestring_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv key /\
  expr_val_rel cx kt key op s ==>
  ?w bs. eval_operand op s = SOME w /\
    mem_word_at (w2n w) s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (w2n w + 32) (LENGTH bs) s.vs_memory = bs /\
    encode_hashmap_key kt key = word_of_bytes_be (Keccak_256_w64 bs)
Proof
  Cases_on `kt` >> simp[hashmap_key_type_def, is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[hashmap_key_type_def, is_bytestring_type_def] >>
  rpt strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `key` >>
  gvs[is_bytestring_type_def, value_has_type_def, expr_val_rel_def,
      is_word_type_def, val_in_memory_def, encode_hashmap_key_def,
      evaluate_type_def] >>
  qmatch_asmsub_abbrev_tac `mem_bytes_at _ _ _ = payload` >>
  qexists_tac `payload` >>
  simp[Abbr `payload`, vyperMiscTheory.n2w_o_ORD_eq]
QED

Theorem target_mapping_scalar_post:
  hashmap_key_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv key /\
  expr_post ctx func cenv cx e es sa sb s0 es' key op s ==>
  eval_operand op s = SOME (encode_hashmap_key (expr_type e) key)
Proof
  strip_tac >> irule target_mapping_scalar_operand >>
  gvs[expr_post_def] >> metis_tac[]
QED

Theorem target_mapping_dynamic_post:
  hashmap_key_type (expr_type e) /\ is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv key /\
  expr_post ctx func cenv cx e es sa sb s0 es' key op s ==>
  ?w bs. eval_operand op s = SOME w /\
    mem_word_at (w2n w) s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (w2n w + 32) (LENGTH bs) s.vs_memory = bs /\
    encode_hashmap_key (expr_type e) key = word_of_bytes_be (Keccak_256_w64 bs)
Proof
  strip_tac >> irule target_mapping_dynamic_operand >>
  gvs[expr_post_def] >> metis_tac[]
QED

Theorem target_mapping_suffix_shape:
  compile_mapping_subscript bop key sa = (op,sb) ==>
  (!x. op = Var x ==> not_fresh_at sb x) /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
    (emitted_insts sa sb)
Proof
  simp[compile_mapping_subscript_def, contextTheory.compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  pure_rewrite_tac[emitted_insts_def, APPEND_ASSOC] >>
  pure_rewrite_tac[rich_listTheory.DROP_LENGTH_APPEND] >>
  `!k. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + k) = 0` by decide_tac >>
  simp[listTheory.DROP_APPEND, mk_inst_def, is_terminator_def,
       not_fresh_at_def]
QED

Theorem target_mapping_run_path:
  compile_mapping_subscript bop key sa = (op,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> drule target_mapping_suffix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  drule_all hash_run_path >> simp[]
QED

Theorem target_keccak_key_suffix_shape:
  compile_keccak256_key key F sa = (op,sb) ==>
  (!x. op = Var x ==> not_fresh_at sb x) /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
    (emitted_insts sa sb)
Proof
  simp[compile_keccak256_key_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  pure_rewrite_tac[emitted_insts_def, APPEND_ASSOC] >>
  pure_rewrite_tac[rich_listTheory.DROP_LENGTH_APPEND] >>
  `!k. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + k) = 0` by decide_tac >>
  simp[listTheory.DROP_APPEND, mk_inst_def, is_terminator_def,
       not_fresh_at_def]
QED

Theorem target_keccak_key_run_path:
  compile_keccak256_key key F sa = (op,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> drule target_keccak_key_suffix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  drule_all hash_run_path >> simp[]
QED

Theorem target_mapping_post:
  extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript key) es' =
    (INL pv, es'') /\
  stmt_state_rel ctx func cenv cx es'' t /\
  eval_operand op t = SOME (hashmap_slot slot (encode_hashmap_key kt key)) /\
  (!x. op = Var x ==> not_fresh_at sb x) /\
  wb_frame cenv es sa s0 t ==>
  target_post ctx func cenv cx es sa sb s0 es'' pv vt
    (op,SOME (slot_loc tr),SOME (value_type_place vt)) t
Proof
  strip_tac >> simp[target_post_def] >>
  gvs[wb_frame_def] >>
  metis_tac[target_mapping_extend_place]
QED

(* Counted scratch suffix, retaining the frame of the whole target. *)
Theorem target_mapping_counted_suffix:
  compile_mapping_subscript bop keyop sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es' s /\
  local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  wb_frame cenv es sa s0 s /\
  (!x. bop = Var x ==> not_fresh_at sm x) /\
  (!x. keyop = Var x ==> not_fresh_at sm x) /\
  eval_operand bop s = SOME slot /\
  eval_operand keyop s = SOME (encode_hashmap_key kt key) /\
  extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript key) es' =
    (INL pv, es'') /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    target_post ctx func cenv cx es sa sb s0 es'' pv vt
      (op,SOME (slot_loc tr),SOME (value_type_place vt)) t
Proof
  strip_tac >> drule_all target_mapping_run >> strip_tac >>
  drule_all target_mapping_run_path >> strip_tac >>
  `es'' = es'` by metis_tac[target_mapping_extend_place] >> gvs[] >>
  `wb_frame cenv es sa s0 t` by
    (irule wb_frame_allocating_tail >> conj_tac >- simp[] >>
     qexistsl_tac [`s`, `es'.scopes`, `sm`] >> simp[] >>
     metis_tac[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[] >> irule target_mapping_post >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[target_mapping_suffix_shape]
QED

Theorem target_keccak_key_counted_prefix:
  compile_keccak256_key key F sa = (op,sb) /\ fn_has_code sa sb func /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  eval_operand key s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  b+32 < dimword(:256) /\ LENGTH bs < dimword(:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand op t = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    stmt_state_rel ctx func cenv cx es t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s
Proof
  strip_tac >> drule_all compile_keccak256_key_run >> strip_tac >>
  drule_all target_keccak_key_run_path >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (`t = (t with vs_vars := s.vs_vars) with vs_vars := t.vs_vars` by simp[] >>
     pop_assum SUBST1_TAC >> irule stmt_state_rel_vars_frame >>
     simp[] >> gvs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, eval_operand_def] >>
  conj_tac >- (gvs[lookup_var_def] >> metis_tac[]) >>
  qpat_assum `t with vs_vars := _ = s`
    (mp_tac o AP_TERM ``\z:venom_state. z with vs_inst_idx := s.vs_inst_idx``) >>
  simp[]
QED

Theorem target_mapping_dynamic_counted_suffix:
  compile_keccak256_key keyop F sc = (hashop,sm) /\
  compile_mapping_subscript bop hashop sm = (op,sb) /\
  fn_has_code sc sm func /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es' s /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\ wb_frame cenv es sa s0 s /\
  (!x. bop = Var x ==> not_fresh_at sc x) /\
  (!x. keyop = Var x ==> not_fresh_at sc x) /\
  eval_operand bop s = SOME slot /\ eval_operand keyop s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  b+32 < dimword(:256) /\ LENGTH bs < dimword(:256) /\
  encode_hashmap_key kt key = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs) /\
  extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript key) es' =
    (INL pv, es'') /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    target_post ctx func cenv cx es sa sb s0 es'' pv vt
      (op,SOME (slot_loc tr),SOME (value_type_place vt)) t
Proof
  strip_tac >> drule_all target_keccak_key_counted_prefix >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  drule target_keccak_key_suffix_shape >> strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_labels = s.vs_labels` by
    (qpat_assum `u with <|vs_vars := _; vs_inst_idx := _|> = s`
      (fn th => map_every (mp_tac o C AP_TERM th)
        [``\z:venom_state. z.vs_memory``, ``\z:venom_state. z.vs_allocas``,
         ``\z:venom_state. z.vs_labels``]) >> simp[]) >>
  `eval_operand bop u = SOME slot` by
    (Cases_on `bop` >> gvs[eval_operand_def]) >>
  `wb_frame cenv es sa s0 u` by
    (irule wb_frame_allocating_tail >> conj_tac >- simp[] >>
     qexistsl_tac [`s`, `es'.scopes`, `sc`] >> simp[] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. bop = Var x ==> not_fresh_at sm x` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by decide_tac >>
  `eval_operand hashop u = SOME (encode_hashmap_key kt key)` by simp[] >>
  qpat_x_assum `EVERY _ (emitted_insts sc sm)` kall_tac >>
  qpat_x_assum `sm.cs_current_insts = _` kall_tac >>
  drule_all target_mapping_counted_suffix >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  `gas_marked_path F ctx func s (0+0) (OK t)` by
    (irule gas_marked_path_then >> qexists_tac `u` >> simp[]) >> gvs[]
QED
