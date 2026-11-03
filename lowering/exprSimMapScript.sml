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
