(* Paired ordinary and shadow compiler decompositions for linked mapping subscripts. *)
Theory bodyMapSubscriptCodeMods
Ancestors
  bodyFullPredsMods exprSimMapKey gasShadowCompile gasShadowState gasShadow
  exprLoweringProps exprSimHypsDefs vyperAST compileEnv context

Theorem mapping_subscript_paired_parts_mods:
  !mods exps DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty es
     ann obj idx sa sb shadow_sa shadow_sb vv kt vt.
    expr_map_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
    place_type cenv obj = MapPT kt vt /\
    ~copies_subscript_base cenv obj idx /\
    place_type (gas_shadow_env T cenv) (gas_shadow_expr obj) = MapPT kt vt /\
    ~copies_subscript_base (gas_shadow_env T cenv)
      (gas_shadow_expr obj) (gas_shadow_expr idx) /\
    compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sb) /\
    compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr (Subscript ann obj idx)) shadow_sa = (vv,shadow_sb) /\
    gas_shadow_state sa shadow_sa /\
    gas_shadow_state sb shadow_sb ==>
    ?bvv sm key sn hashed sp slot.
      compile_expr cenv ty obj sa = (bvv,sm) /\
      lower_value compile_expr cenv (expr_type idx) idx sm = (key,sn) /\
      (if is_bytestring_type kt then compile_keccak256_key key F sn
       else (key,sn)) = (hashed,sp) /\
      compile_mapping_subscript (vv_operand bvv) hashed sp = (slot,sb) /\
      vv = LocatedValue ann (mk_ptr slot
        (case vv_location bvv of SOME loc => loc | NONE => LocMemory)) /\
      ?shadow_bvv shadow_sm shadow_key shadow_sn shadow_hashed shadow_sp.
        compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa =
          (shadow_bvv,shadow_sm) /\
        lower_value compile_expr (gas_shadow_env T cenv) (expr_type idx)
          (gas_shadow_expr idx) shadow_sm = (shadow_key,shadow_sn) /\
        (if is_bytestring_type kt then compile_keccak256_key shadow_key F shadow_sn
         else (shadow_key,shadow_sn)) = (shadow_hashed,shadow_sp) /\
        compile_mapping_subscript (vv_operand shadow_bvv) shadow_hashed shadow_sp =
          (vv_operand vv,shadow_sb) /\
        gas_shadow_state sm shadow_sm
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_expr_mapping_subscript_parts >> strip_tac >>
  qexistsl_tac [`bvv`,`sm`,`key`,`sn`,`hashed`,`sp`,`slot`] >>
  simp[] >>
  qpat_x_assum `compile_expr (gas_shadow_env _ _) _
      (gas_shadow_expr (Subscript _ _ _)) _ = _`
      (assume_tac o REWRITE_RULE [gas_shadow_expr_def]) >>
  drule_all compile_expr_mapping_subscript_parts >> strip_tac >>
  `gas_shadow_state sm sm'` by
    (`gas_shadow_compiles (compile_expr cenv ty obj)
        (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj))` by
       irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_compile_expr_env >>
     pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `compile_expr (gas_shadow_env T cenv) ty
       (gas_shadow_expr obj) shadow_sa` >> simp[] >>
     qpat_assum `(q,r) = (bvv',sm')` mp_tac >> simp[]) >>
  qexistsl_tac [`bvv'`,`sm'`,`key'`,`sn'`,`hashed'`,`sp'`] >>
  simp[gas_shadow_expr_type] >>
  gvs[contextTheory.vv_operand_def, contextTheory.mk_ptr_def]
QED
