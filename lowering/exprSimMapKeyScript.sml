(* Mapping-key representation and pure hashing boundaries. *)
Theory exprSimMapKey
Ancestors
  exprSimHash exprSimLeaves valueEncodingProofs exprLoweringProps
  vyperTypeSystem vyperValue vyperTyping vyperStorage valueEncoding
  vyperInterpreter vyperState list rich_list compileEnv loweringPosts context venomState
  emitHelper emitHelperProps venomExecSemantics venomInst fragExec ASCIInumbers
  exprSimAlloc exprSimLiteralBuffer exprSimOps exprBopSimProps exprSimProps
  exprLowering exprCallbackContracts exprCallBounds exprSafeOperandBuiltins
  vyperTypeSystem vyperAST exprOperandVar freshWrites

Theorem encode_hashmap_key_scalar:
  !kt kv tenv tv.
    hashmap_key_type kt /\ ~is_bytestring_type kt /\
    evaluate_type tenv kt = SOME tv /\ value_has_type tv kv ==>
    encode_hashmap_key kt kv = typed_val_to_w256 tv kv
Proof
  Cases_on `kt` >> simp[hashmap_key_type_def] >>
  rpt gen_tac >> strip_tac
  >- (rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[hashmap_key_type_def, is_bytestring_type_def,
          evaluate_type_def, AllCaseEqs()] >>
      Cases_on `kv` >>
      gvs[value_has_type_def, encode_hashmap_key_def,
          typed_val_to_w256_def, val_to_w256_def, AllCaseEqs()]) >>
  gvs[evaluate_type_def, AllCaseEqs()] >> Cases_on `kv` >>
  gvs[value_has_type_def, encode_hashmap_key_def,
      typed_val_to_w256_def, val_to_w256_def]
QED

Theorem expr_val_rel_hashmap_scalar:
  hashmap_key_type kt /\ ~is_bytestring_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv /\
  expr_val_rel cx kt kv op s ==>
  eval_operand op s = SOME (encode_hashmap_key kt kv)
Proof
  strip_tac >>
  `is_word_type kt` by
    (Cases_on `kt` >> gvs[hashmap_key_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[hashmap_key_type_def, is_word_type_def, is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def, evaluate_type_def,
         AllCaseEqs()]) >>
  drule_all encode_hashmap_key_scalar >> strip_tac >>
  gvs[loweringPostsTheory.expr_val_rel_def] >>
  first_x_assum drule >> simp[]
QED

Theorem expr_post_hashmap_bytestring:
  expr_post ctx func cenv cx e es sa sm s0 es' kv op s /\
  expr_type e = kt /\ is_bytestring_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv ==>
  ?b bs. eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
    b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    encode_hashmap_key kt kv = word_of_bytes_be (Keccak_256_w64 bs)
Proof
  strip_tac >> Cases_on `kt` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[is_bytestring_type_def, evaluate_type_def]
  >- (Cases_on `kv` >> gvs[value_has_type_def] >>
      rename1 `StringV str` >>
      `evaluate_type (get_tenv cx) (expr_type e) =
         SOME (BaseTV (StringT n))` by simp[evaluate_type_def] >>
      drule_all hash_string_post_view >> strip_tac >>
      qexistsl_tac [`b`, `MAP (n2w o ORD) str`] >>
      gvs[encode_hashmap_key_def, vyperMiscTheory.n2w_o_ORD_eq,
          wordsTheory.dimword_def]) >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  gvs[is_bytestring_type_def, evaluate_type_def] >>
  Cases_on `kv` >> gvs[value_has_type_def] >>
  rename1 `BytesV bs` >> rename1 `Dynamic cap` >>
  `evaluate_type (get_tenv cx) (expr_type e) =
     SOME (BaseTV (BytesT (Dynamic cap)))` by simp[evaluate_type_def] >>
  drule_all hash_dynamic_post_view >> strip_tac >>
  qexistsl_tac [`b`, `bs`] >> gvs[encode_hashmap_key_def, wordsTheory.dimword_def]
QED

Theorem hashmap_fixed_key_alignment_probe[local]:
  encode_hashmap_key (BaseT (BytesT (Fixed 1))) (BytesV [1w]) =
    (n2w (2 ** 248):bytes32) /\
  encode_hashmap_key (BaseT (BytesT (Fixed 32)))
    (BytesV (1w :: REPLICATE 31 0w)) = (n2w (2 ** 248):bytes32)
Proof
  EVAL_TAC >> wordsLib.WORD_DECIDE_TAC
QED

Theorem hashmap_empty_dynamic_key_probe[local]:
  encode_hashmap_key (BaseT (BytesT (Dynamic 0))) (BytesV []) =
    word_of_bytes_be (Keccak_256_w64 []) /\
  encode_hashmap_key (BaseT (StringT 0)) (StringV "") =
    word_of_bytes_be (Keccak_256_w64 [])
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``Keccak_256_w64``])
QED

Theorem emit_ADD_frame:
  emit_op ADD [a;b] sa = (op,sb) /\
  eval_operand a s = SOME u /\ eval_operand b s = SOME v ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (u + v) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString sa.cs_next_var)) (u + v) s` >>
  simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_pure2_def,
       bind_outputs_def, eval_operand_def, lookup_var_update_var,
       update_var_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def, lookup_var_def,
                       finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem emit_MLOAD_frame:
  emit_op MLOAD [p] sa = (op,sb) /\ eval_operand p s = SOME a ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (mload (w2n a) s) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n a) s) s` >>
  simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_read1_def,
       eval_operand_def, lookup_var_update_var, update_var_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def, lookup_var_def,
                       finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

(* Capacity-general staging: the allocation may also own later words. *)
Theorem hash_alloc_capacity_mstore_frame:
  32 <= cap /\ cap < dimword (:256) /\
  compile_alloc_buffer cap sa = (buf, sm) /\
  emit_void MSTORE [buf.buf_operand; val_op] sm = ((), sh) /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\
  eval_operand val_op s = SOME w /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t addr. run_inst_seq (emitted_insts sa sh) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand buf.buf_operand t = SOME addr /\
    t.vs_memory = (mstore (w2n addr) w s).vs_memory /\
    t.vs_labels = s.vs_labels /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n addr,cap) /\
    w2n addr + cap < dimword (:256) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n addr) cap b len) /\
    (!name b len. local_region cenv es.scopes t name b len ==>
       regions_disjoint (w2n addr) cap b len) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    sh.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sh /\
    sh.cs_next_var = sa.cs_next_var + 1 /\
    sh.cs_next_id = sa.cs_next_id + 2 /\
    local_ptrs_reserved cenv sh /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sh x) /\
    (!n b sz. local_region cenv es.scopes s n b sz ==>
      mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory)
Proof
  strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `eval_operand buf.buf_operand allocated = SOME addr` >>
  `allocated.vs_labels = s.vs_labels` by
    (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand val_op allocated = SOME w` by
    (Cases_on `val_op` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sm sh) allocated =
     OK (mstore (w2n addr) w allocated)` by
    (irule literal_emit_mstore_run >>
     qexistsl_tac [`buf.buf_operand`, `val_op`] >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (mstore (w2n addr) w allocated)` by
    (irule literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`w2n addr`,
       `mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
          [STRING #"%" (toString sa.cs_next_var)]`, `cap`] >>
     simp[mk_inst_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[regions_disjoint_def]) >>
  suspend "compose"
QED

Resume hash_alloc_capacity_mstore_frame[compose]:
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh /\
   sh.cs_next_var = sa.cs_next_var + 1 /\
   sh.cs_next_id = sa.cs_next_id + 2 /\
   (!x. buf.buf_operand = Var x ==> not_fresh_at sh x)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >>
     gvs[emitted_insts_def, not_fresh_at_def, toString_inj,
       rich_listTheory.DROP_LENGTH_APPEND, rich_listTheory.DROP_APPEND1,
       rich_listTheory.DROP_APPEND2]) >>
  `local_ptrs_reserved cenv sh` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `run_inst_seq (emitted_insts sa sh) s =
     run_inst_seq (emitted_insts sm sh) allocated` by
    (irule (cj 1 run_inst_seq_chain) >> simp[]) >>
  `sh.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sh` by
    (irule (cj 2 run_inst_seq_chain) >> goal_assum drule >> simp[]) >>
  `eval_operand buf.buf_operand (mstore (w2n addr) w allocated) = SOME addr` by
    gvs[mstore_def, eval_operand_def, lookup_var_def] >>
  `!aid b len. aid < sa.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
     mem_bytes_at b len (mstore (w2n addr) w allocated).vs_memory =
     mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     `mem_bytes_at b len (mstore (w2n addr) w allocated).vs_memory =
      mem_bytes_at b len allocated.vs_memory` by
       (irule mstore_region_frame >> qexistsl_tac [`w2n addr`, `cap`] >>
        simp[] >> qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _` irule >>
        qexists_tac `aid` >> simp[]) >> simp[]) >>
  `!n b sz. local_region cenv es.scopes s n b sz ==>
    mem_bytes_at b sz (mstore (w2n addr) w allocated).vs_memory =
    mem_bytes_at b sz s.vs_memory` by
    (match_mp_tac local_regions_memory_tail >>
     qexistsl_tac [`sa`, `es.scopes`, `allocated`] >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `allocated.vs_memory = s.vs_memory`
       (fn th => pure_rewrite_tac[GSYM th]) >>
     irule mstore_region_frame >>
     qexistsl_tac [`w2n addr`, `cap`] >> simp[] >>
     qpat_x_assum `!name b len. local_region _ _ allocated _ _ _ ==> _` drule >> simp[]) >>
  `!name b len.
     local_region cenv es.scopes (mstore (w2n addr) w allocated) name b len ==>
     regions_disjoint (w2n addr) cap b len` by
    (simp[local_region_def, mstore_def] >>
     rpt strip_tac >> first_x_assum irule >>
     simp[local_region_def] >> qexists_tac `name` >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`mstore (w2n addr) w allocated`, `addr`] >>
  simp[] >> conj_tac >- simp[mstore_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise hash_alloc_capacity_mstore_frame

Theorem hash_alloc_two_words_frame:
  compile_alloc_buffer 64 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; op0] sm = ((),sh) /\
  emit_op ADD [buf.buf_operand; Lit 32w] sh = (wordptr,sp) /\
  emit_void MSTORE [wordptr; op1] sp = ((),sb) /\
  (!x. op0 = Var x ==> not_fresh_at sa x) /\
  (!x. op1 = Var x ==> not_fresh_at sa x) /\
  eval_operand op0 s = SOME w0 /\ eval_operand op1 s = SOME w1 /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t addr. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand buf.buf_operand t = SOME addr /\
    mem_bytes_at (w2n addr) 64 t.vs_memory =
      word_to_bytes_be w0 ++ word_to_bytes_be w1 /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n addr,64) /\
    w2n addr + 64 < dimword (:256) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n addr) 64 b len) /\
    (!name b len. local_region cenv es.scopes t name b len ==>
       regions_disjoint (w2n addr) 64 b len) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!n b sz. local_region cenv es.scopes s n b sz ==>
       mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory)
Proof
  strip_tac >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) hash_alloc_capacity_mstore_frame >>
  simp[wordsTheory.dimword_def] >> disch_then drule_all >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sh) s = OK s1` >>
  suspend "second_store"
QED

Resume hash_alloc_two_words_frame[second_store]:
  drule_at (Pat `emit_op ADD _ _ = _`) emit_ADD_frame >>
  disch_then (qspecl_then [`32w`, `addr`, `s1`] mp_tac) >>
  simp[eval_operand_def] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sh sp) s1 = OK s2` >>
  `s2.vs_labels = s.vs_labels /\ s2.vs_memory = s1.vs_memory /\
   s2.vs_allocas = s1.vs_allocas` by
    (qpat_assum `s2 with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. (z.vs_labels,z.vs_memory,z.vs_allocas)`) >> simp[]) >>
  `eval_operand op1 s2 = SOME w1` by
    (Cases_on `op1` >> gvs[eval_operand_def] >>
     rename1 `lookup_var v s = SOME w1` >>
     `not_fresh_at sh v` by
       (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     simp[]) >>
  `w2n (addr + 32w) = w2n addr + 32` by
    simp[wordsTheory.word_add_def, wordsTheory.dimword_def] >>
  `run_inst_seq (emitted_insts sp sb) s2 =
     OK (mstore (w2n addr + 32) w1 s2)` by
    (drule_all literal_emit_mstore_run >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es s2` by
    (irule hash_readonly_state_rel >> goal_assum (drule_at Any) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (mstore (w2n addr + 32) w1 s2)` by
    (irule literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`w2n addr`,
       `mk_inst sa.cs_next_id ALLOCA [Lit 64w]
          [STRING #"%" (toString sa.cs_next_var)]`, `64`] >>
     simp[mk_inst_def] >> rpt strip_tac >>
     `local_region cenv es.scopes s1 name lb lsz` by
       (drule_at (Pat `local_region _ _ _ _ _ _`) local_region_frame >>
        disch_then irule >> simp[] >> conj_tac
        >- (qexists_tac `sh` >> simp[]) >>
        qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     qpat_x_assum `!name b len. local_region _ _ s1 _ _ _ ==> _` drule >>
     simp[regions_disjoint_def]) >>
  suspend "compose_two"
QED

Resume hash_alloc_two_words_frame[compose_two]:
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >>
  strip_tac >>
  qpat_assum `emit_void MSTORE [wordptr; op1] _ = _`
    (mp_then Any mp_tac emitted_insts_emit_void) >> strip_tac >>
  `run_inst_seq (emitted_insts sa sp) s = OK s2 /\
   sp.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sp` by
    (qpat_assum `run_inst_seq (emitted_insts sa sh) s = OK s1`
       (mp_then (Pat `run_inst_seq _ _ = OK _`) mp_tac run_inst_seq_chain) >>
     disch_then (qspec_then `sp` mp_tac) >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK (mstore (w2n addr+32) w1 s2)` by
    (qpat_assum `run_inst_seq (emitted_insts sa sp) s = OK s2`
       (mp_then (Pat `run_inst_seq _ _ = OK _`) mp_tac run_inst_seq_chain) >>
     disch_then (qspec_then `sb` mp_tac) >> simp[]) >>
  `eval_operand buf.buf_operand s2 = SOME addr` by
    (`s2.vs_labels = s1.vs_labels` by simp[] >>
     Cases_on `buf.buf_operand` >> gvs[eval_operand_def] >> res_tac >> gvs[]) >>
  `(mstore (w2n addr+32) w1 s2).vs_allocas = s1.vs_allocas` by simp[mstore_def] >>
  qexistsl_tac [`mstore (w2n addr+32) w1 s2`, `addr`] >>
  simp[eval_operand_mstore] >>
  rpt conj_tac
  >- suspend "two_word_view"
  >- suspend "old_separation"
  >- suspend "local_separation"
  >- suspend "old_variables"
  >- suspend "allocation_memory"
  >> suspend "local_memory"
QED

Resume hash_alloc_two_words_frame[two_word_view]:
  `mem_bytes_at (w2n addr) 32 (mstore (w2n addr+32) w1 s2).vs_memory =
   mem_bytes_at (w2n addr) 32 s2.vs_memory` by
    (irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> simp[]) >>
  `64 = 32 + 32` by simp[] >>
  asm_rewrite_tac[valueEncodingProofsTheory.mem_bytes_at_split_padded] >>
  simp[valueEncodingPropsTheory.mem_bytes_at_mstore_same,
       byteTheory.word_to_bytes_be_def]
QED

Resume hash_alloc_two_words_frame[old_separation]:
  qpat_assum `!aid b len. _ ==> regions_disjoint _ _ _ _` ACCEPT_TAC
QED

Resume hash_alloc_two_words_frame[local_separation]:
  rpt strip_tac >>
  `local_region cenv es.scopes s1 name b len` by
    (drule_at (Pat `local_region _ _ _ _ _ _`) local_region_frame >>
     disch_then irule >> simp[mstore_def, GSYM lookup_var_def] >> conj_tac
     >- (qexists_tac `sh` >> simp[]) >>
     qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
  qpat_x_assum `!name b len. local_region _ _ s1 _ _ _ ==> _` drule >> simp[]
QED

Resume hash_alloc_two_words_frame[old_variables]:
  rpt strip_tac >>
  `not_fresh_at sh x` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  simp[]
QED

Resume hash_alloc_two_words_frame[allocation_memory]:
  rpt strip_tac >>
  `regions_disjoint (w2n addr) 64 b len` by
    (qpat_x_assum `!aid b len. _ ==> regions_disjoint _ _ _ _` drule_all >> simp[]) >>
  `mem_bytes_at b len (mstore (w2n addr+32) w1 s2).vs_memory =
   mem_bytes_at b len s2.vs_memory` by
    (irule mstore_region_frame >> qexistsl_tac [`w2n addr`, `64`] >> simp[]) >>
  simp[] >> irule mstore_region_frame >> qexistsl_tac [`w2n addr`, `64`] >> simp[]
QED

Resume hash_alloc_two_words_frame[local_memory]:
  rpt strip_tac >>
  `local_region cenv es.scopes s1 n b sz` by
    (drule_at (Pat `local_region _ _ s _ _ _`) local_region_frame_fwd >>
     disch_then irule >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `regions_disjoint (w2n addr) 64 b sz` by
    (qpat_x_assum `!name b len. local_region _ _ s1 _ _ _ ==> _` drule >> simp[]) >>
  `mem_bytes_at b sz (mstore (w2n addr+32) w1 s2).vs_memory =
   mem_bytes_at b sz s2.vs_memory` by
    (irule mstore_region_frame >> qexistsl_tac [`w2n addr`, `64`] >> simp[]) >>
  simp[] >> irule mstore_region_frame >> qexistsl_tac [`w2n addr`, `64`] >> simp[]
QED

Finalise hash_alloc_two_words_frame

(* Both instruction orders read precisely the payload, excluding its length. *)
Theorem emit_length_prefixed_hash_run:
  ((emit_op MLOAD [ptr_op] sa = (len,sm) /\
    emit_op ADD [ptr_op; Lit 32w] sm = (data,sn)) \/
   (emit_op ADD [ptr_op; Lit 32w] sa = (data,sm) /\
    emit_op MLOAD [ptr_op] sm = (len,sn))) /\
  emit_op SHA3 [data; len] sn = (op,sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  disch_tac >>
  `?s2. run_inst_seq (emitted_insts sa sn) s = OK s2 /\
    sn.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sn /\
    sa.cs_next_var <= sn.cs_next_var /\
    eval_operand data s2 = SOME (n2w (b+32)) /\
    eval_operand len s2 = SOME (n2w (LENGTH bs)) /\
    s2.vs_memory = s.vs_memory /\
    (s2 with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x s2 = lookup_var x s)` by
    (qpat_x_assum `_ /\ _` strip_assume_tac
     >- suspend "load_first"
     >> suspend "add_first") >>
  qpat_x_assum `_ /\ _` (mp_tac o CONJUNCT2) >> strip_tac >>
  drule_at (Pat `emit_op SHA3 _ _ = _`) emit_SHA3_bytes_frame >>
  disch_then (qspecl_then [`s2`, `n2w (b+32)`, `n2w (LENGTH bs)`, `bs`] mp_tac) >>
  simp[GSYM mem_bytes_at_def] >> strip_tac >>
  qpat_assum `emit_op SHA3 _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >>
  strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s = OK t` by
    (qpat_assum `run_inst_seq (emitted_insts sa sn) s = OK s2`
       (mp_then (Pat `run_inst_seq _ _ = OK _`) mp_tac run_inst_seq_chain) >>
     disch_then (qspec_then `sb` mp_tac) >> simp[]) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (qpat_x_assum `t with vs_vars := _ = _`
        (mp_tac o Q.AP_TERM `\z. z with vs_vars := s.vs_vars`) >> simp[]) >>
  rpt strip_tac >> `not_fresh_at sn x` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >> simp[]
QED

Resume emit_length_prefixed_hash_run[load_first]:
  drule_at (Pat `emit_op MLOAD _ _ = _`) emit_MLOAD_frame >>
  disch_then drule >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK s1` >>
  `eval_operand ptr_op s1 = SOME (n2w b)` by
    (`s1.vs_labels = s.vs_labels` by
       (qpat_x_assum `s1 with vs_vars := _ = _`
          (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[]) >>
     Cases_on `ptr_op` >> gvs[eval_operand_def] >> res_tac >> gvs[]) >>
  drule_at (Pat `emit_op ADD _ _ = _`) emit_ADD_frame >>
  disch_then (qspecl_then [`32w`, `n2w b`, `s1`] mp_tac) >>
  simp[eval_operand_def] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sn) s1 = OK s2` >>
  `b < dimword (:256)` by decide_tac >>
  `s2.vs_memory = s.vs_memory` by
    (qpat_x_assum `s2 with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_memory`) >>
     qpat_x_assum `s1 with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_memory`) >> simp[]) >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> strip_tac >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> strip_tac >>
  `eval_operand len s2 = SOME (n2w (LENGTH bs))` by
    gvs[eval_operand_def, not_fresh_at_def, mload_def, mem_word_at_def] >>
  `run_inst_seq (emitted_insts sa sn) s = OK s2 /\
   sn.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sn` by
    (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK s1`
       (mp_then (Pat `run_inst_seq _ _ = OK _`) mp_tac run_inst_seq_chain) >>
     disch_then (qspec_then `sn` mp_tac) >> simp[]) >>
  qexists_tac `s2` >> simp[wordsTheory.word_add_n2w] >> conj_tac
  >- (qpat_x_assum `s2 with vs_vars := _ = _`
        (mp_tac o Q.AP_TERM `\z. z with vs_vars := s.vs_vars`) >> simp[]) >>
  rpt strip_tac >> `not_fresh_at sm x` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >> simp[]
QED

Resume emit_length_prefixed_hash_run[add_first]:
  drule_at (Pat `emit_op ADD _ _ = _`) emit_ADD_frame >>
  disch_then (qspecl_then [`32w`, `n2w b`, `s`] mp_tac) >>
  simp[eval_operand_def] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK s1` >>
  `eval_operand ptr_op s1 = SOME (n2w b)` by
    (`s1.vs_labels = s.vs_labels` by
       (qpat_x_assum `s1 with vs_vars := _ = _`
          (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[]) >>
     Cases_on `ptr_op` >> gvs[eval_operand_def] >> res_tac >> gvs[]) >>
  drule_at (Pat `emit_op MLOAD _ _ = _`) emit_MLOAD_frame >>
  disch_then drule >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sn) s1 = OK s2` >>
  `b < dimword (:256)` by decide_tac >>
  `s1.vs_memory = s.vs_memory /\ s2.vs_memory = s.vs_memory` by
    (qpat_x_assum `s2 with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_memory`) >>
     qpat_x_assum `s1 with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_memory`) >> simp[]) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> strip_tac >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> strip_tac >>
  `eval_operand data s2 = SOME (n2w (b+32))` by
    gvs[eval_operand_def, not_fresh_at_def, wordsTheory.word_add_n2w] >>
  `run_inst_seq (emitted_insts sa sn) s = OK s2 /\
   sn.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sn` by
    (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK s1`
       (mp_then (Pat `run_inst_seq _ _ = OK _`) mp_tac run_inst_seq_chain) >>
     disch_then (qspec_then `sn` mp_tac) >> simp[]) >>
  `eval_operand len s2 = SOME (n2w (LENGTH bs))` by
    gvs[mload_def, mem_word_at_def] >>
  qexists_tac `s2` >> simp[wordsTheory.word_add_n2w] >> conj_tac
  >- (qpat_x_assum `s2 with vs_vars := _ = _`
        (mp_tac o Q.AP_TERM `\z. z with vs_vars := s.vs_vars`) >> simp[]) >>
  rpt strip_tac >> `not_fresh_at sm x` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >> simp[]
QED

Finalise emit_length_prefixed_hash_run

(* Compiler shape boundaries keep emission internals out of consumers. *)
Theorem compile_keccak256_key_parts:
  compile_keccak256_key key F sa = (op,sb) ==>
  ?data sm len sn.
    emit_op ADD [key; Lit 32w] sa = (data,sm) /\
    emit_op MLOAD [key] sm = (len,sn) /\
    emit_op SHA3 [data; len] sn = (op,sb)
Proof
  Cases_on `emit_op ADD [key; Lit 32w] sa` >>
  rename1 `_ = (data,sm)` >>
  Cases_on `emit_op MLOAD [key] sm` >>
  gvs[compile_keccak256_key_def, comp_bind_def]
QED

Theorem compile_mapping_subscript_parts:
  compile_mapping_subscript base_op key sa = (op,sb) ==>
  ?buf sm sn ptr sp sq.
    compile_alloc_buffer 64 sa = (buf,sm) /\
    emit_void MSTORE [buf.buf_operand; base_op] sm = ((),sn) /\
    emit_op ADD [buf.buf_operand; Lit 32w] sn = (ptr,sp) /\
    emit_void MSTORE [ptr; key] sp = ((),sq) /\
    emit_op SHA3 [buf.buf_operand; Lit 64w] sq = (op,sb)
Proof
  Cases_on `compile_alloc_buffer 64 sa` >> rename1 `_ = (buf,sm)` >>
  Cases_on `emit_void MSTORE [buf.buf_operand; base_op] sm` >>
  rename1 `_ = (u,sn)` >> Cases_on `u` >>
  Cases_on `emit_op ADD [buf.buf_operand; Lit 32w] sn` >>
  rename1 `emit_op ADD _ _ = (keyptr,sp)` >>
  Cases_on `emit_void MSTORE [keyptr; key] sp` >>
  rename1 `_ = (u,sq)` >> Cases_on `u` >>
  gvs[compile_mapping_subscript_def, comp_bind_def, comp_ignore_bind_def]
QED

Theorem compile_expr_mapping_subscript_parts:
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sb) /\
  place_type cenv obj = MapPT kt vt ==>
  ?bvv sm key sn hashed sp slot.
    compile_expr cenv ty obj sa = (bvv,sm) /\
    lower_value compile_expr cenv (expr_type idx) idx sm = (key,sn) /\
    (if is_bytestring_type kt then compile_keccak256_key key F sn
     else (key,sn)) = (hashed,sp) /\
    compile_mapping_subscript (vv_operand bvv) hashed sp = (slot,sb) /\
    vv = LocatedValue ann (mk_ptr slot
      (case vv_location bvv of SOME loc => loc | NONE => LocMemory))
Proof
  strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       compile_subscript_def, comp_bind_def, comp_return_def,
       vyperASTTheory.expr_size_def, vyperASTTheory.expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qpat_x_assum `lower_value cb cenv ity idx sm = _` mp_tac >>
  `lower_value
     (expr_child_callback (expr_size idx + (expr_size obj + (type_size ann + 1)))
        compile_expr) cenv (expr_type idx) idx =
   lower_value compile_expr cenv (expr_type idx) idx` by
    (irule exprCallbackContractsTheory.lower_value_callback_contract >>
     simp[exprCallbackContractsTheory.expr_callbacks_agree_def,
          FUN_EQ_THM, exprCallBoundsTheory.expr_child_callback_def]) >>
  simp[SF ETA_ss] >> strip_tac >>
  Cases_on `is_bytestring_type kt` >> gvs[comp_return_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem compile_mapping_operand_not_label:
  type_place_expr env obj = SOME (HashMapT kt vt) /\
  compile_expr cenv ty obj sa = (vv,sm) ==>
  !l. vv_operand vv <> Label l
Proof
  Cases_on `obj` >> simp[well_typed_expr_def] >>
  rpt strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def]
  >~ [`FLOOKUP cenv.ce_module_vars id`]
  >- (Cases_on `FLOOKUP cenv.ce_module_vars id` >>
      gvs[AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >>
      rpt strip_tac >>
      gvs[contextTheory.vv_operand_def, contextTheory.mk_ptr_def])
  >> strip_tac >>
  drule exprSafeOperandBuiltinsTheory.compile_subscript_not_label >>
  simp[]
QED
