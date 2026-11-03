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

Theorem mapping_subscript_index_pre:
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  place_type cenv obj = MapPT kt vt /\
  eval_expr cx obj es = (INL bres, em) ==>
  expr_map_pre cenv cx env obj es /\
  expr_sim_inv cenv cx env em /\
  expr_body_pre cenv cx env idx em
Proof
  strip_tac >>
  `expr_map_pre cenv cx env obj es` by
    metis_tac[expr_body_pre_map_subscript_base, expr_map_pre_subscript_base] >>
  drule_all expr_map_pre_eval_result >> strip_tac >>
  simp[] >> irule expr_subscript_pre_index >>
  simp[] >> qexistsl [`ann`, `es`, `obj`] >> simp[]
QED

Theorem mapping_subscript_key_typed:
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  place_type cenv obj = MapPT kt vt /\
  eval_expr cx obj es = (INL bres,em) /\
  (do ir <- eval_expr cx idx; read_result cx ir od) em = (INL kv,en) ==>
  expr_sim_inv cenv cx env en /\ expr_type idx = kt /\
  hashmap_key_type kt /\
  ?tv. evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv
Proof
  strip_tac >>
  `expr_body_pre cenv cx env idx em` by
    metis_tac[mapping_subscript_index_pre] >>
  `expr_type idx = kt /\ hashmap_key_type kt` by
    metis_tac[mapping_subscript_key_type] >>
  drule_all expr_body_pre_eval >> strip_tac >>
  gvs[vyperTypeExprResultTheory.expr_result_typed_def,
      vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
      vyperTypeExprSoundnessTheory.value_runtime_typed_def,
      vyperTypeInvariantsTheory.value_result_typed_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  metis_tac[]
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
  qexists `t` >> simp[] >>
  simp[exprSimWordArgsTheory.wb_frame_def] >>
  conj_tac >- metis_tac[] >>
  irule exprSimTheory.locals_kept_regions >> first_assum ACCEPT_TAC
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
     gvs[] >> qexists `s` >>
     simp[emitted_insts_def, run_inst_seq_def] >>
     irule expr_val_rel_hashmap_scalar >> simp[] >>
     qexistsl [`cx`, `tv`] >> gvs[exprSimTheory.expr_post_def]) >>
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
     qexistsl [`sn`, `s`] >>
     gvs[exprSimWordArgsTheory.wb_frame_refl] >>
     qpat_assum `t with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas)`) >> simp[] >>
     metis_tac[]) >>
  qexists `u` >> simp[] >>
  irule exprSimWordArgsTheory.wb_frame_trans >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (qexistsl [`en`, `sp`, `t`] >> simp[]) >>
  goal_assum (drule_at Any)
QED

Theorem compile_hashmap_tail_shape:
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript base_op hashed sp = (slot,sb) ==>
  same_blocks sn sb /\
  sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sn sb)
Proof
  strip_tac >>
  drule (cj 2 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >> strip_tac >>
  Cases_on `is_bytestring_type kt` >> gvs[]
  >- (drule (cj 1 (REWRITE_RULE [DISJ_IMP_THM] mapping_suffix_shape)) >>
      strip_tac >>
      `same_blocks sn sb` by metis_tac[emitHelperPropsTheory.same_blocks_trans] >>
      `emitted_insts sn sb = emitted_insts sn sp ++ emitted_insts sp sb` by
        (irule emitted_insts_append >> simp[]) >>
      simp[APPEND_ASSOC]) >>
  simp[]
QED

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
  irule hash_run_frag >> simp[] >> rpt strip_tac >>
  drule_all compile_hashmap_tail_run >> strip_tac >>
  qexists `u` >> simp[stmt_state_rel_inst_idx] >>
  `wb_frame cenv es sa s0 s` by
    (drule exprSimWordArgsTheory.expr_post_frame >> simp[]) >>
  `wb_frame cenv es sa s0 u` by
    (irule exprSimWordArgsTheory.wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl [`en`, `sn`, `s`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  qpat_x_assum `wb_frame cenv es sa s0 u` mp_tac >>
  simp[exprSimWordArgsTheory.wb_frame_def, lookup_var_def] >>
  strip_tac >> first_assum ACCEPT_TAC
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
  fn_inst_ids_distinct func /\ fn_has_code sp sb func /\
  stmt_state_rel ctx func cenv cx em s1 /\ local_ptrs_reserved cenv sm /\
  MAP FDOM em.scopes = MAP FDOM en.scopes /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id ==>
  frag_exec ctx sn sb (\s. s = t)
    (\u. eval_operand slot u = SOME (hashmap_slot base_slot (encode_hashmap_key kt kv)) /\
         stmt_state_rel ctx func cenv cx en u /\ wb_frame cenv em sm s1 u) R
Proof
  strip_tac >>
  `eval_operand base_op t = SOME base_slot` by
    (irule exprSimOpsTheory.eval_operand_frame >>
     simp[] >> qexistsl [`sm`, `s1`] >>
     gvs[exprSimTheory.expr_post_def]) >>
  `!x. base_op = Var x ==> not_fresh_at sn x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `local_ptrs_reserved cenv sn` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all compile_hashmap_tail_frag >>
  disch_then (qspecl_then [`base_slot`, `R`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[]
QED

Theorem compile_mapping_index_continuation:
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  (nocalls ==> int_calls_expr (Subscript ann obj idx) = []) /\
  expr_sim_case nocalls ctx func cenv cx idx /\
  place_type cenv obj = MapPT kt vt /\
  eval_expr cx obj es = (INL (HashMapRef tr base_slot kt vt),em) /\
  eval_expr cx (Subscript ann obj idx) es = (res,es') /\
  storage_mapping_region cx tr base_slot (HashMapT kt vt) /\
  p.ptr_location = slot_loc tr /\
  eval_operand p.ptr_operand s1 = SOME base_slot /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!l. p.ptr_operand <> Label l) /\
  stmt_state_rel ctx func cenv cx em s1 /\ wb_frame cenv es sa s0 s1 /\
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  lower_value compile_expr cenv (expr_type idx) idx sm = (key,sn) /\
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript p.ptr_operand hashed sp = (slot,sb) /\
  fn_has_code sm sn func /\ fn_has_code sp sb func /\
  fn_inst_ids_distinct func /\ cs_extends sm sn /\ cs_extends sn sb ==>
  frag_exec ctx sm sb (\s. s = s1)
    (\s. ?tr base_slot kv tv.
      res = INL tv /\ storage_mapping_region cx tr base_slot (HashMapT kt vt) /\
      select_result cx (expr_type obj) (HashMapRef tr base_slot kt vt)
        (ValueSubscript kv) es' = (INL tv,es') /\
      p.ptr_location = slot_loc tr /\
      eval_operand slot s = SOME (hashmap_slot base_slot (encode_hashmap_key kt kv)) /\
      stmt_state_rel ctx func cenv cx es' s /\ wb_frame cenv es sa s0 s)
    (expr_exit res)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env idx em` by
    metis_tac[mapping_subscript_index_pre] >>
  `expr_sim ctx func cenv cx (expr_type idx) idx em` by
    (gvs[expr_sim_case_def] >> first_x_assum irule >>
     conj_tac >- metis_tac[int_calls_subscript_operands] >>
     qexists `env` >> simp[]) >>
  Cases_on `(do ir <- eval_expr cx idx; read_result cx ir od) em` >>
  rename1 `_ = (kr,en)` >>
  `expr_res_ok kr` by metis_tac[expr_body_pre_res_ok] >>
  drule_all eval_expr_subscript_forced_index >> strip_tac >>
  qmatch_goalsub_abbrev_tac `frag_exec ctx sm sb _ Q _` >>
  irule frag_exec_conseq >>
  qexistsl [`\s. s = s1 /\ stmt_state_rel ctx func cenv cx em s`,
            `Q`, `expr_exit res`] >> simp[] >>
  irule expr_sim_suffix >>
  goal_assum (drule_at Any) >> simp[] >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  goal_assum (drule_at Any) >> simp[] >>
  (conj_tac
  >- (Cases_on `kr` >> gvs[] >> gen_tac >> Cases_on `r` >>
      gvs[exprSimTheory.expr_res_ok_def, exprSimTheory.expr_exit_def]) >>
  rpt strip_tac >>
  `no_type_error_result res` by
    metis_tac[expr_body_pre_eval_result, expr_map_pre_eval_result] >>
  `select_result cx (expr_type obj) (HashMapRef tr base_slot kt vt)
     (ValueSubscript v) en = (res,es')` by
    (qpat_x_assum `!ann. eval_expr _ _ _ = _`
       (qspec_then `ann` mp_tac) >> simp[]) >>
  drule_all vyperTypeExprSoundnessTheory.select_result_hashmap_no_type_error >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env en /\ expr_type idx = kt /\
   hashmap_key_type kt /\
   ?tv. evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv v` by
    metis_tac[mapping_subscript_key_typed] >>
  `!x. key = Var x ==> not_fresh_at sn x` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `MAP FDOM em.scopes = MAP FDOM en.scopes` by
    metis_tac[exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom] >>
  `MAP FDOM es.scopes = MAP FDOM em.scopes` by
    metis_tac[vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom] >>
  drule_all compile_mapping_index_success_tail >>
  disch_then (qspec_then `expr_exit (INL tv)` mp_tac) >>
  disch_then (mp_then Any irule frag_exec_conseq) >> simp[] >>
  rpt strip_tac >> simp[Abbr `Q`] >>
  qexistsl [`tr`, `base_slot`, `v`] >> simp[] >>
  irule exprSimWordArgsTheory.wb_frame_trans >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (qexistsl [`em`, `sm`, `s1`] >> simp[]) >>
  goal_assum (drule_at Any))
QED
