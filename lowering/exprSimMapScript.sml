(* Mapping read-side simulation: key representation and hash steps. *)
Theory exprSimMap
Ancestors
  emitHelper list rich_list venomInst
  exprSimHyps exprSimHash exprSimLeaves valueEncodingProofs
  vyperTypeEnv vyperStoragePlaceProvenance exprLowering exprLoweringProps
  fragExec compileEnv venomState context vyperInterpreter vyperState
  vyperTypeSystem compileEnv vyperValue vyperTyping vyperStorage valueEncoding

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
  gvs[exprSimTheory.expr_val_rel_def] >> res_tac >> gvs[]
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

(* Computation probes distinguish left-aligned fixed bytes from data hashing. *)
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

Theorem compile_toplevel_map_sim:
  expr_map_pre cenv cx env (TopLevelName ann (src,id)) es ==>
  expr_map_sim ctx func cenv cx ty (TopLevelName ann (src,id)) es
Proof
  strip_tac >>
  `env_consistent env cx es /\
   ?kt vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt vt)` by
    gvs[expr_map_pre_def, expr_sim_inv_def, well_typed_expr_def,
        AllCaseEqs()] >>
  drule_all env_consistent_toplevel_hashmap_static >> strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `lookup_var_slot_from_layout cx tr src id_str = SOME slot` >>
  drule_all lookup_global_mapping >> strip_tac >>
  `storage_mapping_region cx tr (n2w slot) (HashMapT kt vt)` by
    (irule lookup_global_mapping_region >> qexistsl_tac [`src`, `es`, `es`, `id`] >>
     simp[]) >>
  rw[expr_map_sim_def] >>
  `res = INL (HashMapRef tr (n2w slot) kt vt) /\ es' = es` by
    gvs[Once evaluate_def] >> gvs[] >>
  reverse (Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`)
  >- (irule frag_exec_conseq >>
      qexistsl_tac [`\s. F`, `\s. F`, `expr_exit (INL (HashMapRef tr (n2w slot) kt vt))`] >>
      simp[frag_exec_false_pre] >>
      gvs[stmt_state_rel_def, state_rel_def]) >>
  fs[] >>
  drule_at (Pat `find_var_decl_by_name _ _ = _`) toplevel_storage_ce_vars >>
  simp[var_decl_transient_def] >> disch_then drule_all >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_def, vyperASTTheory.expr_type_def] >>
  Cases_on `tr` >> simp[] >> strip_tac >> gvs[] >>
  irule frag_exec_refl >> rpt strip_tac >> gvs[] >>
  simp[slot_loc_def, contextTheory.mk_ptr_def, eval_operand_def,
       exprSimTheory.locals_kept_def]
QED

(* Pure compiler boundaries; runtime consumers need not unfold emissions. *)
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

Theorem mapping_suffix_shape:
  (compile_keccak256_key key F sa = (op,sb) \/
   compile_mapping_subscript base_op key sa = (op,sb)) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
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
  qexists `sa.cs_next_var + 2` >> simp[]
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
  qexistsl [`b`, `key`, `sm`] >> gvs[wordsTheory.dimword_def]
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
  qexists `t` >> simp[byteTheory.word_of_bytes_be_def] >>
  irule hash_readonly_state_rel >> goal_assum (drule_at Any) >>
  gvs[exprSimTheory.expr_post_def]
QED

(* The slot hash uses exactly the two staged words; SHA3 itself is readonly. *)
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
    (qpat_assum `emit_op SHA3 _ _ = _` (mp_then Any mp_tac emitHelperPropsTheory.emitted_insts_emit_op) >> simp[]) >>
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
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> qexistsl [`staged`, `sq`] >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK t` by
    (qpat_assum `run_inst_seq (emitted_insts sa sq) s = OK staged`
       (mp_then (Pat `run_inst_seq _ _ = OK _`) mp_tac run_inst_seq_chain) >>
     disch_then (qspec_then `sb` mp_tac) >> simp[]) >>
  qexists `t` >> simp[vyperStorageTheory.hashmap_slot_def, byteTheory.word_of_bytes_be_def] >> rpt conj_tac
  >- (rpt strip_tac >> `not_fresh_at sq x` by
        (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >> simp[])
  >- (rpt strip_tac >> qpat_x_assum `!aid b len. _ ==> mem_bytes_at _ _ _ = _` drule_all >> simp[])
  >> rpt strip_tac >> qpat_x_assum `!n b sz. local_region _ _ _ _ _ _ ==> _` drule >> simp[]
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
  qpat_x_assum `lower_value cb cenv ity idx sm = _`
    (fn th => mp_tac th) >>
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

Theorem mapping_leaf_storage_valid:
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  contract_storage_well_formed cx es ==>
  slots_in_range (get_storage cx es tr) (w2n slot) tv /\
  storage_read_live cx tr (get_storage cx es tr) slot tv
Proof
  strip_tac >>
  qpat_x_assum `storage_mapping_region _ _ _ _` mp_tac >>
  rewrite_tac[storage_mapping_region_def] >> strip_tac >>
  qpat_x_assum `!subs leaf_slot leaf_tv. _`
    (qspecl_then [`[]`, `slot`, `tv`] mp_tac) >>
  simp[vyperStorageLayoutSafetyTheory.resolve_hashmap_leaf_def] >> strip_tac >>
  conj_tac
  >- (irule vyperStorageLayoutSafetyTheory.contract_storage_well_formed_region >>
      simp[vyperStorageBackendTheory.get_storage_backend_eq] >>
      goal_assum (drule_at Any) >> qexists `es` >> simp[]) >>
  irule accountsRelPropsTheory.declared_storage_region_read_live >>
  goal_assum (drule_at Any)
QED

Theorem mapping_leaf_storage_holds:
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  contract_storage_well_formed cx es ==>
  storage_holds cx tr typ (PlaceR (StoragePlace tr slot tv)) slot es
Proof
  strip_tac >> drule_all mapping_leaf_storage_valid >> strip_tac >>
  drule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >> strip_tac >>
  drule_all vyperLookupStorageTheory.decode_value_from_slots_in_range >> strip_tac >>
  simp[exprSimTheory.storage_holds_def, read_result_def, read_place_def,
       read_storage_slot_def, bind_def, lift_option_def, return_def,
       vyperStorageBackendTheory.get_storage_backend_eq]
QED

Theorem mapping_leaf_vv_holds:
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  contract_storage_well_formed cx es /\
  p.ptr_location = slot_loc tr /\
  eval_operand p.ptr_operand s = SOME slot ==>
  vv_holds cenv cx typ (PlaceR (StoragePlace tr slot tv))
    (LocatedValue typ p) es s
Proof
  strip_tac >> drule_all mapping_leaf_storage_holds >> strip_tac >>
  Cases_on `tr` >>
  gvs[exprSimTheory.vv_holds_def, slot_loc_def]
QED
