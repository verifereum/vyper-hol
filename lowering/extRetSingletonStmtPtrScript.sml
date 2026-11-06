(* Compiler cuts for the actual nonraw bytestring return statement. *)
Theory extRetSingletonStmtPtr
Ancestors
  extRetRawStmtPtr extRetSingletonWordCapacityPtr extRetAbiSingletonReturnPtr
  extRetBufferCursorStatePtr exprOperandVar loweringHalt exprLoweringProps
  emitHelperProps fragExec stmtLowering compileEnv stmtSimReturn loweringPosts rich_list
  vyperTypeArgFits vyperTyping vyperTypeSystem

Theorem external_return_singleton_stmt_parts[local]:
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv',sb) /\
  fn_has_code sa sb func /\ ~block_is_terminated sa /\
  cenv.ce_return_pc = NONE /\ ~is_word_type ty /\ ~cenv.ce_raw_return /\
  cenv.ce_nonreentrant = (F,nkey,ut,iv) /\
  is_bytestring_type ty /\ is_bytestring_type (lowered_value_type cenv e) ==>
  ?op sm buf sn len so.
    lower_value compile_expr cenv ty e sa = (op,sm) /\
    compile_alloc_buffer cenv.ce_max_return_size sm = (buf,sn) /\
    compile_abi_encode_to_buf buf.buf_operand op cenv.ce_ret_enc_info sn = (len,so) /\
    emit_inst RETURN [buf.buf_operand;len] [] so = ((),sb) /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\
    fn_has_code sn so func /\ fn_has_code so sb func
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule compile_external_return_abi_parts >> simp[] >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule compile_abi_encode_to_buf_extends >> strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  `cs_extends sb cs'` by
    (irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends sa' cs'` by
    (irule cs_extends_trans >> qexists `sb` >> simp[]) >>
  `cs_extends cs'' cs'` by
    (irule cs_extends_trans >> qexists `sa'` >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `fn_has_code cs'' sa' func /\ fn_has_code sa' cs' func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sa' sb func /\ fn_has_code sb cs' func` by
    (irule fn_has_code_split >> simp[]) >>
  metis_tac[]
QED

(* Assignment compatibility, not equality of source and declared types. *)
Theorem external_return_declared_value_typed[local]:
  type_stmt env ty (Return (SOME e)) = SOME env' /\
  env.type_defs = get_tenv cx /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v ==>
  ?tu. evaluate_type (get_tenv cx) ty = SOME tu /\ value_has_type tu v
Proof
  simp[Once type_stmt_def] >> strip_tac >> gvs[] >>
  drule_all type_widens_to_value_has_type >> simp[]
QED
