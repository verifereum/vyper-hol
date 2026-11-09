(* Mapping-key representation and pure hashing boundaries. *)
Theory exprSimMapKey
Ancestors
  exprSimHash exprSimLeaves valueEncodingProofs exprLoweringProps
  vyperTypeSystem vyperValue vyperTyping vyperStorage valueEncoding valueEncodingDefs
  vyperInterpreter vyperState list rich_list compileEnv loweringStateRelDefs loweringPosts context venomState
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

Theorem mapping_suffix_shape:
  (compile_keccak256_key key F sa = (op,sb) \/
   compile_mapping_subscript base_op key sa = (op,sb)) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS)
    (emitted_insts sa sb) /\
  sb.cs_next_var = sa.cs_next_var + 3 /\
  (?v. op = Var v /\ not_fresh_at sb v)
Proof
  strip_tac >>
  gvs[compile_keccak256_key_def, compile_mapping_subscript_def,
      contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
      fresh_var_def, emit_def, same_blocks_def, emitted_insts_def,
      not_fresh_at_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[is_terminator_def, mk_inst_def] >>
  qexists_tac `sa.cs_next_var + 2` >> simp[]
QED

Theorem mapping_suffix_next_id:
  (compile_keccak256_key key F sa = (op,sb) ==>
   sb.cs_next_id = sa.cs_next_id + 3) /\
  (compile_mapping_subscript base_op key sa = (op,sb) ==>
   sb.cs_next_id = sa.cs_next_id + 5)
Proof
  conj_tac >> strip_tac >>
  gvs[compile_keccak256_key_def, compile_mapping_subscript_def,
      contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
      fresh_var_def, emit_def]
QED

Theorem mapping_alloca_code:
  compile_mapping_subscript base_op key sa = (op,sb) /\
  fn_has_code sa sb func ==>
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >> qpat_x_assum `compile_mapping_subscript _ _ _ = _` mp_tac >>
  simp[compile_mapping_subscript_def,
    contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  irule hash_emitted_inst_mem >> goal_assum (drule_at Any) >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem compile_keccak256_key_run:
  compile_keccak256_key key F sa = (op,sb) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  eval_operand key s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule compile_keccak256_key_parts >> strip_tac >>
  drule_at (Pat `emit_op SHA3 _ _ = _`) emit_length_prefixed_hash_run >>
  disch_then irule >> simp[] >>
  qexistsl_tac [`b`, `key`, `sm`] >> gvs[wordsTheory.dimword_def]
QED

Theorem compile_hashmap_dynamic_key_frame:
  expr_post ctx func cenv cx e es sa sm s0 es' kv key s /\
  expr_type e = kt /\ is_bytestring_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv /\
  compile_keccak256_key key F sm = (op,sb) /\
  (!x. key = Var x ==> not_fresh_at sm x) /\
  local_ptrs_reserved cenv sm ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    eval_operand op t = SOME (encode_hashmap_key kt kv) /\
    stmt_state_rel ctx func cenv cx es' t /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all expr_post_hashmap_bytestring >> strip_tac >>
  drule_all compile_keccak256_key_run >> strip_tac >>
  qexists_tac `t` >> simp[byteTheory.word_of_bytes_be_def] >>
  irule hash_readonly_state_rel >> goal_assum (drule_at Any) >>
  gvs[loweringPostsTheory.expr_post_def]
QED

Theorem compile_mapping_subscript_run:
  compile_mapping_subscript base_op key sa = (op,sb) /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  eval_operand base_op s = SOME w0 /\ eval_operand key s = SOME w1 /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (hashmap_slot w0 w1) /\
    stmt_state_rel ctx func cenv cx es t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!n b sz. local_region cenv es.scopes s n b sz ==>
       mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory)
Proof
  strip_tac >> drule compile_mapping_subscript_parts >> strip_tac >>
  drule_all hash_alloc_two_words_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sq) s = OK staged` >>
  `eval_operand (Lit 64w) staged = SOME 64w` by simp[eval_operand_def] >>
  drule_at (Pat `emit_op SHA3 _ _ = _`) emit_SHA3_bytes_frame >>
  simp[eval_operand_def] >> disch_then drule_all >> strip_tac >>
  `t.vs_memory = staged.vs_memory /\ t.vs_allocas = staged.vs_allocas` by
    (qpat_assum `t with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas)`) >> simp[]) >>
  `sb.cs_current_insts = sq.cs_current_insts ++ emitted_insts sq sb` by
    (qpat_assum `emit_op SHA3 _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> simp[]) >>
  `sq.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sq /\
   sa.cs_next_var <= sq.cs_next_var` by
    (qpat_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_assum `emit_void MSTORE [buf.buf_operand; base_op] _ = _` mp_tac >>
     qpat_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_assum `emit_void MSTORE [ptr'; key] _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def] >> rpt strip_tac >> gvs[] >>
     rewrite_tac[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[rich_listTheory.DROP_LENGTH_APPEND]) >>
  `local_ptrs_reserved cenv sq` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> qexistsl_tac [`staged`, `sq`] >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK t` by
    (qpat_assum `run_inst_seq (emitted_insts sa sq) s = OK staged`
       (mp_then (Pat `run_inst_seq _ _ = OK _`) mp_tac run_inst_seq_chain) >>
     disch_then (qspec_then `sb` mp_tac) >> simp[]) >>
  qexists_tac `t` >> simp[vyperStorageTheory.hashmap_slot_def, byteTheory.word_of_bytes_be_def] >> rpt conj_tac
  >- (rpt strip_tac >> `not_fresh_at sq x` by
        (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >> simp[])
  >- (rpt strip_tac >> qpat_x_assum `!aid b len. _ ==> mem_bytes_at _ _ _ = _` drule_all >> simp[])
  >> rpt strip_tac >> qpat_x_assum `!n b sz. local_region _ _ _ _ _ _ ==> _` drule >> simp[]
QED

Theorem compile_mapping_subscript_frame:
  compile_mapping_subscript base_op key sa = (op,sb) /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  eval_operand base_op s = SOME w0 /\ eval_operand key s = SOME w1 /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (hashmap_slot w0 w1) /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t
Proof
  strip_tac >> drule_all mapping_alloca_code >> strip_tac >>
  drule_all compile_mapping_subscript_run >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  simp[loweringPostsTheory.wb_frame_def] >>
  conj_tac >- metis_tac[] >>
  irule locals_kept_regions >> first_assum ACCEPT_TAC
QED

Theorem compile_hashmap_tail_run:
  expr_post ctx func cenv cx e es sa sn s0 en kv key s /\
  expr_type e = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv /\
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript base_op hashed sp = (slot,sb) /\
  (!x. key = Var x ==> not_fresh_at sn x) /\
  (!x. base_op = Var x ==> not_fresh_at sn x) /\
  eval_operand base_op s = SOME base_slot /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sn /\
  fn_has_code sp sb func ==>
  ?u. run_inst_seq (emitted_insts sn sb) s = OK u /\
    eval_operand slot u = SOME (hashmap_slot base_slot (encode_hashmap_key kt kv)) /\
    stmt_state_rel ctx func cenv cx en u /\ wb_frame cenv en sn s u
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx en s` by
    (drule exprSimWordArgsTheory.expr_post_state >> simp[]) >>
  `?t. run_inst_seq (emitted_insts sn sp) s = OK t /\
    eval_operand hashed t = SOME (encode_hashmap_key kt kv) /\
    stmt_state_rel ctx func cenv cx en t /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x s)` by
    (Cases_on `is_bytestring_type kt`
     >- (gvs[] >> drule compile_hashmap_dynamic_key_frame >>
         disch_then (qspecl_then [`tv`, `sp`, `hashed`, `expr_type e`] mp_tac) >>
         simp[]) >>
     gvs[] >> qexists_tac `s` >>
     simp[emitted_insts_def, run_inst_seq_def] >>
     irule expr_val_rel_hashmap_scalar >> simp[] >>
     qexistsl_tac [`cx`, `tv`] >> gvs[loweringPostsTheory.expr_post_def]) >>
  `sn.cs_next_var <= sp.cs_next_var /\ sn.cs_next_id <= sp.cs_next_id /\
   sp.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sp /\
   (!x. hashed = Var x ==> not_fresh_at sp x)` by
    (Cases_on `is_bytestring_type kt` >> gvs[]
     >- (drule (cj 1 mapping_suffix_next_id) >> strip_tac >>
         drule (cj 1 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >>
         strip_tac >> gvs[]) >>
     simp[emitted_insts_def]) >>
  `local_ptrs_reserved cenv sp` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `(!x. base_op = Var x ==> not_fresh_at sp x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand base_op t = SOME base_slot` by
    (Cases_on `base_op` >> gvs[eval_operand_def] >>
     qpat_assum `t with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[] >> metis_tac[]) >>
  drule_all compile_mapping_subscript_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sp sb) t = OK u` >>
  `sb.cs_current_insts = sp.cs_current_insts ++ emitted_insts sp sb` by
    (drule (cj 2 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >> simp[]) >>
  `run_inst_seq (emitted_insts sn sb) s = OK u` by
    (qpat_assum `run_inst_seq (emitted_insts sn sp) s = OK t`
       (mp_then (Pat `run_inst_seq _ _ = OK _`) mp_tac run_inst_seq_chain) >>
     disch_then (qspec_then `sb` mp_tac) >> simp[]) >>
  `wb_frame cenv en sn s t` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     qexistsl_tac [`sn`, `s`] >>
     gvs[exprSimWordArgsTheory.wb_frame_refl] >>
     qpat_assum `t with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas)`) >> simp[] >>
     metis_tac[]) >>
  qexists_tac `u` >> simp[] >>
  irule exprSimWordArgsTheory.wb_frame_trans >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (qexistsl_tac [`en`, `sp`, `t`] >> simp[]) >>
  goal_assum (drule_at Any)
QED

Theorem compile_hashmap_tail_shape:
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript base_op hashed sp = (slot,sb) ==>
  same_blocks sn sb /\
  sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS)
    (emitted_insts sn sb)
Proof
  strip_tac >>
  drule (cj 2 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >> strip_tac >>
  Cases_on `is_bytestring_type kt` >> gvs[]
  >- (drule (cj 1 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >>
      strip_tac >>
      `same_blocks sn sb` by metis_tac[exprLoweringPropsTheory.same_blocks_trans] >>
      `emitted_insts sn sb = emitted_insts sn sp ++ emitted_insts sp sb` by
        (irule emitted_insts_append >> simp[]) >>
      simp[APPEND_ASSOC]) >>
  simp[]
QED

(* This is solely a target fragment; counted source lifting is separate. *)
Theorem compile_hashmap_tail_frag:
  expr_type e = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv /\
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript base_op hashed sp = (slot,sb) /\
  (!x. key = Var x ==> not_fresh_at sn x) /\
  (!x. base_op = Var x ==> not_fresh_at sn x) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sn /\
  fn_has_code sp sb func /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM en.scopes /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id ==>
  frag_exec ctx sn sb
    (\s. expr_post ctx func cenv cx e es sa sn s0 en kv key s /\
         eval_operand base_op s = SOME base_slot)
    (\u. eval_operand slot u = SOME (hashmap_slot base_slot (encode_hashmap_key kt kv)) /\
         stmt_state_rel ctx func cenv cx en u /\ wb_frame cenv es sa s0 u) R
Proof
  strip_tac >> drule_all compile_hashmap_tail_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sn sb)` by fs[EVERY_MEM] >>
  irule hash_run_frag >> simp[] >> rpt strip_tac >>
  drule_all compile_hashmap_tail_run >> strip_tac >>
  qexists_tac `u` >> simp[stmt_state_rel_inst_idx] >>
  `wb_frame cenv es sa s0 s` by
    (drule exprSimWordArgsTheory.expr_post_frame >> simp[]) >>
  `wb_frame cenv es sa s0 u` by
    (irule exprSimWordArgsTheory.wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl_tac [`en`, `sn`, `s`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  qpat_x_assum `wb_frame cenv es sa s0 u` mp_tac >>
  simp[loweringPostsTheory.wb_frame_def, lookup_var_def] >>
  strip_tac >> first_assum ACCEPT_TAC
QED


(* The mapping hash suffix has no GAS instruction: lift its concrete run
   to the counted execution interface without changing its final data. *)
Theorem compile_hashmap_tail_zero_path:
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript base_op hashed sp = (slot,sb) /\
  fn_has_code sn sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  run_inst_seq (emitted_insts sn sb) s = OK t ==>
  gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule_all compile_hashmap_tail_shape >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sn sb) = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sn sb)` by fs[EVERY_MEM] >>
  gvs[fragExecTheory.fn_has_code_def, exprLoweringPropsTheory.same_blocks_def,
      rich_listTheory.IS_PREFIX_APPEND] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX (emitted_insts sn sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[rich_listTheory.DROP_APPEND1] >>
  simp[fragGasModeTheory.gas_marked_path_def] >>
  drule_all fragGasSeqTheory.tuple_run_inst_seq_gas_path >> simp[]
QED

Theorem compile_mapping_index_success_tail:
  expr_post ctx func cenv cx idx em sm sn s1 en kv key t /\
  expr_type idx = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv /\
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript base_op hashed sp = (slot,sb) /\
  (!x. key = Var x ==> not_fresh_at sn x) /\
  (!x. base_op = Var x ==> not_fresh_at sm x) /\ (!l. base_op <> Label l) /\
  eval_operand base_op s1 = SOME base_slot /\
  fn_inst_ids_distinct func /\ fn_has_code sp sb func /\ fn_has_code sn sb func /\
  stmt_state_rel ctx func cenv cx em s1 /\ local_ptrs_reserved cenv sm /\
  MAP FDOM em.scopes = MAP FDOM en.scopes /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?u. gas_marked_path F ctx func t 0 (OK u) /\
      eval_operand slot u = SOME (hashmap_slot base_slot (encode_hashmap_key kt kv)) /\
      stmt_state_rel ctx func cenv cx en u /\ wb_frame cenv em sm s1 u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `eval_operand base_op t = SOME base_slot` by
    (irule eval_operand_frame >>
     simp[] >> qexistsl_tac [`sm`, `s1`] >>
     gvs[loweringPostsTheory.expr_post_def]) >>
  `!x. base_op = Var x ==> not_fresh_at sn x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `local_ptrs_reserved cenv sn` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all compile_hashmap_tail_run >> strip_tac >>
  `gas_marked_path F ctx func t 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_all compile_hashmap_tail_zero_path >> simp[]) >>
  `wb_frame cenv em sm s1 t` by
    (drule exprSimWordArgsTheory.expr_post_frame >> simp[]) >>
  `wb_frame cenv em sm s1 u` by
    (irule exprSimWordArgsTheory.wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl_tac [`en`, `sn`, `t`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx] >>
  conj_tac
  >- (qpat_x_assum `wb_frame cenv em sm s1 u` mp_tac >>
      simp[loweringPostsTheory.wb_frame_def, lookup_var_def] >>
      strip_tac >> first_assum ACCEPT_TAC) >>
  drule_all compile_hashmap_tail_shape >> strip_tac >>
  `u.vs_current_bb = t.vs_current_bb` suffices_by
    gvs[exprLoweringPropsTheory.same_blocks_def] >>
  drule_at (Pos hd)
    (Q.ISPEC `\s:venom_state. s.vs_current_bb`
      exprLoweringPropsTheory.run_inst_seq_preserves_field) >>
  simp[] >> disch_then irule >> rpt strip_tac >>
  fs[EVERY_MEM] >>
  metis_tac[venomInstProofsTheory.step_preserves_control_flow,
            venomExecSemanticsTheory.step_inst_non_invoke]
QED
