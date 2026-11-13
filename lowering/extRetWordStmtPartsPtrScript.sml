Theory extRetWordStmtPartsPtr
Ancestors
  stmtLowering compileEnv fragExec exprWordOperand exprLoweringProps
  loweringHalt loweringPosts vyperTypeSystem finite_map emitHelper context rich_list

Theorem external_return_word_stmt_parts:
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv',sb) /\
  fn_has_code sa sb func /\ ~block_is_terminated sa /\
  cenv.ce_return_pc = NONE /\ is_word_type ty /\
  is_word_type (expr_type e) /\ ~cenv.ce_raw_return /\
  cenv.ce_nonreentrant = (F,nkey,ut,iv) /\ well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t) ==>
  ?op sm.
    lower_value compile_expr cenv ty e sa = (op,sm) /\
    compile_external_return (SOME op) T F cenv.ce_ret_enc_info
      cenv.ce_max_return_size F nkey ut iv sm = ((),sb) /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    (!y. op = Var y ==> not_fresh_at sm y)
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule lower_value_word_shape >>
  disch_then (qspec_then `env` mp_tac) >>
  disch_then drule_all >> strip_tac >>
  `cs_extends cs'' cs'` by
    (qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_external_return_def, compile_alloc_buffer_def,
          emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_id_def,
          fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
     irule cs_extends_same_block >> simp[IS_PREFIX_APPEND, GSYM APPEND_ASSOC]) >>
  drule_all fn_has_code_split >> simp[]
QED
