(* Static compiler boundaries for the direct joint word declaration proof. *)
Theory bodyFullAnnAssignWordEntry
Ancestors
  exprSimSource stmtSimProps loweringSlice exprLoweringProps gasShadow
  gasShadowCompileStmtHelpers gasShadowCompileStmtBase
  stmtSimAssign entryDecodeStaticProps loweringHalt fragExec
  compileEnv exprLowering stmtLowering loweringPosts
  vyperTypeSystem vyperAST list finite_map

Theorem annassign_word_full_shadow_parts:
  is_word_type typ /\ ~has_length_word typ /\ expr_type e = typ /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  gas_shadow_state r shadow_r /\
  compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sf) /\
  compile_stmt ce lctx ret_ty (AnnAssign id typ (gas_shadow_expr e)) shadow_r =
    ((),shadow_sf) /\
  emit_inst ALLOCA [Lit (n2w sz)] [p] r = ((),a) /\
  lower_value compile_expr ce typ e a = (op,b) /\
  fn_has_code shadow_r shadow_sf shadow_func ==>
  ?shadow_a shadow_b.
    emit_inst ALLOCA [Lit (n2w sz)] [p] shadow_r = ((),shadow_a) /\
    lower_value compile_expr ce typ (gas_shadow_expr e) shadow_a = (op,shadow_b) /\
    gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
    emit_void MSTORE [Var p;op] shadow_b = ((),shadow_sf) /\
    fn_has_code shadow_a shadow_b shadow_func
Proof
  strip_tac >>
  Cases_on `emit_inst ALLOCA [Lit (n2w sz)] [p] shadow_r` >>
  rename1 `emit_inst ALLOCA _ _ shadow_r = (u,shadow_a)` >>
  `u = () /\ gas_shadow_state a shadow_a` by
    (mp_tac (Q.INST [`opc` |-> `ALLOCA`, `ops` |-> `[Lit (n2w sz)]`,
       `outs` |-> `[p]`] gasShadowStateTheory.gas_shadow_compiles_emit_inst) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`r`, `shadow_r`] mp_tac) >> gvs[]) >> gvs[] >>
  Cases_on `lower_value compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_a` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) _ = (shadow_op,shadow_b)` >>
  `shadow_op = op /\ gas_shadow_state b shadow_b` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `ty` |-> `expr_type e`]
       gas_shadow_stmt_lower_value) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`a`, `shadow_a`] mp_tac) >> simp[]) >> gvs[] >>
  `cs_extends shadow_a shadow_b` by
    (qpat_x_assum `lower_value _ _ _ (gas_shadow_expr e) _ = _`
       (mp_tac o MATCH_MP (CONJUNCT2 compile_expr_grows)) >> simp[]) >>
  qpat_x_assum `compile_stmt _ _ _ (AnnAssign _ _ (gas_shadow_expr e)) _ = _` mp_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr e) _ = _` mp_tac >>
  simp[compile_stmt_def, compile_assign_value_def, emit_local_alloca_def,
       lower_value_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       gas_shadow_expr_type] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
  `cs_extends shadow_r shadow_a` by
    metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def] >>
  `cs_extends shadow_b shadow_sf` by
    metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def] >>
  `cs_extends shadow_a shadow_sf` by metis_tac[cs_extends_trans] >>
  metis_tac[fragExecTheory.fn_has_code_split]
QED

Theorem annassign_word_full_declared_layout:
  declare_local old id (expr_type e) sa = (ce,r) /\
  compile_stmt ce lctx ret_ty (AnnAssign id (expr_type e) e) r = ((),sf) /\
  old.ce_alloca_locals /\ FLOOKUP old.ce_vars id = NONE /\
  is_word_type (expr_type e) /\ expr_body_pre ce cx env e es /\
  local_ptrs_reserved old sa /\ fn_has_code sa sf func ==>
  ?p a b op.
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) 32) /\
    (!n. n <> id ==> FLOOKUP ce.ce_vars n = FLOOKUP old.ce_vars n) /\
    ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
              ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
    emit_inst ALLOCA [Lit 32w] [p] r = ((),a) /\
    lower_value compile_expr ce (expr_type e) e a = (op,b) /\
    emit_void MSTORE [Var p;op] b = ((),sf) /\
    cs_extends r a /\ cs_extends a b /\ cs_extends b sf /\
    fn_has_code a b func /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]) (fn_insts func) /\
    local_ptrs_reserved ce a /\ not_fresh_at a p /\
    compile_alloc_buffer 32 sa = (<|buf_operand := Var p; buf_size := 32|>,a) /\
    cs_extends sa a /\ fn_has_code sa a func /\
    type_memory_bytes old (expr_type e) = 32 /\ ~has_length_word (expr_type e)
Proof
  strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `local_ptrs_reserved ce r` by metis_tac[declare_local_reserved] >>
  `fn_has_code r sf func` by
    fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  `~has_length_word (expr_type e)` by
    metis_tac[stmtSimAssignTheory.is_word_type_no_length_word] >>
  `!sa sb op. lower_value compile_expr ce (expr_type e) e sa = (op,sb) ==>
      cs_extends sa sb` by metis_tac[expr_body_pre_lower_value_word_shape] >>
  drule_all compile_annassign_word_parts >> strip_tac >>
  `compile_alloc_buffer (type_memory_bytes old (expr_type e)) sa =
      (<|buf_operand := Var (STRING #"%" (toString sa.cs_next_var));
         buf_size := type_memory_bytes old (expr_type e)|>,sa')` by
    (qpat_x_assum `emit_inst ALLOCA _ _ _ = _` mp_tac >>
     qpat_x_assum `r = _` SUBST1_TAC >>
     simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
          emitHelperTheory.emit_inst_def, fresh_id_def, fresh_var_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          pairTheory.pair_case_thm] >> strip_tac >> gvs[]) >>
  `cs_extends sa sa'` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `fn_has_code sa sa' func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `type_memory_bytes old (expr_type e) = 32` by
    metis_tac[entryDecodeStaticPropsTheory.word_type_dec_sizes] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`, `sa'`, `sb`, `vop`] >>
  gvs[]
QED
