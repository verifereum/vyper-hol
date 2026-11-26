(* Compiler-only split of the linked word-local declaration. *)
Theory bodyAnnWordIntervalsMods
Ancestors
  loweringPosts loweringSlice stmtSimProps stmtSimAssign exprLoweringProps
  entryDecodeStaticProps loweringHalt gasShadowCompileStmtHelpers
  gasShadowCompileStmtBase gasShadowState bodyFullShared
  compileEnv stmtLowering gasShadow vyperAST finite_map

Theorem annassign_stmt_env_parts[local]:
  stmt_env cenv lctx ret_ty (AnnAssign id typ e) sa = (ce,sf) ==>
  ?r. declare_local cenv id typ sa = (ce,r) /\
      compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sf)
Proof
  Cases_on `declare_local cenv id typ sa` >>
  rename1 `declare_local _ _ _ _ = (decl,r)` >>
  Cases_on `compile_stmt decl lctx ret_ty (AnnAssign id typ e) r` >>
  simp[stmt_env_def, declare_stmt_local_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[]
QED

Theorem annassign_word_interval[local]:
  declare_local cenv id typ sa = (ce,r) /\
  compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sf) /\
  cenv.ce_alloca_locals /\ is_word_type typ /\ expr_type e = typ /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sf func ==>
  ?p a b op.
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) 32) /\
    (!n. n <> id ==> FLOOKUP ce.ce_vars n = FLOOKUP cenv.ce_vars n) /\
    ce with <|ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
              ce_dynarray_capacity := cenv.ce_dynarray_capacity|> = cenv /\
    type_memory_bytes cenv typ = 32 /\
    compile_alloc_buffer 32 sa = (<|buf_operand := Var p; buf_size := 32|>,a) /\
    emit_inst ALLOCA [Lit 32w] [p] r = ((),a) /\
    lower_value compile_expr ce typ e a = (op,b) /\
    emit_void MSTORE [Var p;op] b = ((),sf) /\
    cs_extends sa a /\ cs_extends a b /\ cs_extends b sf /\
    fn_has_code sa a func /\ fn_has_code a b func /\ fn_has_code b sf func /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]) (fn_insts func) /\
    local_ptrs_reserved ce a /\ not_fresh_at a p /\
    sa.cs_next_var <= a.cs_next_var /\ a.cs_next_var <= b.cs_next_var /\
    sa.cs_next_id <= a.cs_next_id
Proof
  strip_tac >>
  drule_all_then strip_assume_tac declare_local_ptr >>
  `local_ptrs_reserved ce r` by metis_tac[declare_local_reserved] >>
  `fn_has_code r sf func` by
    fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  `~has_length_word typ` by simp[is_word_type_no_length_word] >>
  `!a b op. lower_value compile_expr ce (expr_type e) e a = (op,b) ==>
      cs_extends a b` by metis_tac[compile_expr_grows] >>
  drule_all_then strip_assume_tac compile_annassign_word_parts >>
  rename1 `emit_inst ALLOCA _ _ r = ((),a)` >>
  rename1 `lower_value _ _ _ _ a = (op,b)` >>
  `type_memory_bytes cenv typ = 32` by metis_tac[word_type_dec_sizes] >>
  `compile_alloc_buffer 32 sa =
     (<|buf_operand := Var (STRING #"%" (toString sa.cs_next_var)); buf_size := 32|>,a)` by
    (qpat_x_assum `emit_inst ALLOCA _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
          emitHelperTheory.emit_inst_def, fresh_id_def, fresh_var_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def, pairTheory.pair_case_thm,
          emit_def] >> strip_tac >> gvs[]) >>
  drule_then strip_assume_tac compile_alloc_buffer_parts >>
  `cs_extends sa a` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends a sf` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa a func /\ fn_has_code a sf func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code b sf func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `a.cs_next_var <= b.cs_next_var` by metis_tac[compile_expr_grows] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`, `a`, `b`, `op`] >>
  gvs[]
QED

Theorem annassign_word_intervals_mods:
  stmt_env cenv lctx ret_ty (AnnAssign id typ e) sa = (ce,sf) /\
  stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (AnnAssign id typ e)) shadow_sa = (gas_shadow_env T ce,shadow_sf) /\
  gas_shadow_state sa shadow_sa /\ cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars id = NONE /\ is_word_type typ /\ expr_type e = typ /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sf func /\
  fn_has_code shadow_sa shadow_sf shadow_func ==>
  ?r shadow_r p a b op shadow_a shadow_b.
    declare_local cenv id typ sa = (ce,r) /\
    declare_local (gas_shadow_env T cenv) id typ shadow_sa = (gas_shadow_env T ce,shadow_r) /\
    compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sf) /\
    compile_stmt (gas_shadow_env T ce) lctx ret_ty
      (AnnAssign id typ (gas_shadow_expr e)) shadow_r = ((),shadow_sf) /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) 32) /\
    (!n. n <> id ==> FLOOKUP ce.ce_vars n = FLOOKUP cenv.ce_vars n) /\
    ce with <|ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
              ce_dynarray_capacity := cenv.ce_dynarray_capacity|> = cenv /\
    type_memory_bytes cenv typ = 32 /\
    compile_alloc_buffer 32 sa = (<|buf_operand := Var p; buf_size := 32|>,a) /\
    emit_inst ALLOCA [Lit 32w] [p] r = ((),a) /\
    lower_value compile_expr ce typ e a = (op,b) /\
    emit_void MSTORE [Var p;op] b = ((),sf) /\
    cs_extends sa a /\ cs_extends a b /\ cs_extends b sf /\
    fn_has_code sa a func /\ fn_has_code a b func /\ fn_has_code b sf func /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]) (fn_insts func) /\
    local_ptrs_reserved ce a /\ not_fresh_at a p /\
    sa.cs_next_var <= a.cs_next_var /\ a.cs_next_var <= b.cs_next_var /\
    sa.cs_next_id <= a.cs_next_id /\
    compile_alloc_buffer 32 shadow_sa =
      (<|buf_operand := Var p; buf_size := 32|>,shadow_a) /\
    emit_inst ALLOCA [Lit 32w] [p] shadow_r = ((),shadow_a) /\
    lower_value compile_expr (gas_shadow_env T ce) typ (gas_shadow_expr e) shadow_a =
      (op,shadow_b) /\
    emit_void MSTORE [Var p;op] shadow_b = ((),shadow_sf) /\
    gas_shadow_state r shadow_r /\
    gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
    fn_has_code shadow_sa shadow_a shadow_func /\
    fn_has_code shadow_a shadow_b shadow_func /\
    fn_has_code shadow_b shadow_sf shadow_func
Proof
  strip_tac >>
  qpat_assum `stmt_env _ _ _ (AnnAssign _ _ e) sa = _`
    (qx_choose_then `r` strip_assume_tac o MATCH_MP annassign_stmt_env_parts) >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (qx_choose_then `shadow_r` strip_assume_tac o MATCH_MP annassign_stmt_env_parts o
     REWRITE_RULE [gas_shadow_stmt_def]) >>
  drule_all_then (qx_choosel_then [`p`,`a`,`b`,`op`] strip_assume_tac)
    annassign_word_interval >>
  `gas_shadow_state r shadow_r` by
    (mp_tac (REWRITE_RULE [gas_shadow_compiles_env_def]
       (Q.INST [`cenv` |-> `cenv`, `id` |-> `id`, `ty` |-> `typ`, `sd` |-> `T`]
         gas_shadow_compiles_env_declare_local)) >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  `local_ptrs_reserved (gas_shadow_env T cenv) shadow_sa` by
    metis_tac[local_ptrs_reserved_gas_shadow] >>
  `expr_type (gas_shadow_expr e) = typ` by simp[gas_shadow_expr_type] >>
  `(gas_shadow_env T cenv).ce_alloca_locals` by simp[] >>
  drule_all_then (qx_choosel_then [`shadow_p`,`shadow_a`,`shadow_b`,`shadow_op`]
    strip_assume_tac) (Q.INST [`e` |-> `gas_shadow_expr e`] annassign_word_interval) >>
  `shadow_p = p` by fs[] >>
  qpat_x_assum `shadow_p = p` SUBST_ALL_TAC >>
  `gas_shadow_state a shadow_a` by
    (mp_tac (REWRITE_RULE [gas_shadow_compiles_def]
       (Q.INST [`opc` |-> `ALLOCA`, `ops` |-> `[Lit 32w]`, `outs` |-> `[p]`]
         gas_shadow_compiles_emit_inst)) >>
     disch_then (qspecl_then [`r`,`shadow_r`] mp_tac) >> simp[]) >>
  `shadow_op = op /\ gas_shadow_state b shadow_b` by
    (mp_tac (REWRITE_RULE [gas_shadow_compiles_def]
       (Q.INST [`cenv` |-> `ce`, `e` |-> `e`, `ty` |-> `typ`, `sd` |-> `T`]
         gas_shadow_stmt_lower_value_env)) >>
     disch_then (qspecl_then [`a`,`shadow_a`] mp_tac) >> simp[]) >>
  qpat_x_assum `shadow_op = op` SUBST_ALL_TAC >>
  qexistsl_tac [`r`,`shadow_r`,`p`,`a`,`b`,`op`,`shadow_a`,`shadow_b`] >> simp[]
QED
