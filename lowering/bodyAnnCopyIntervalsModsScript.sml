Theory bodyAnnCopyIntervalsMods
Ancestors
  bodyFullAnnAssignMemoryPost exprLoweringProps compileEnv fragExec

(* The same VV is returned by the two RHS compilations. In the empty
   branch both unwrap intervals are identities, not lowering operations. *)
Theorem ann_copy_intervals_mods:
  stmt_env old lctx ret_ty (AnnAssign id typ e) sa = (ce,sf) /\
  stmt_env (gas_shadow_env T old) lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)) shadow_sa =
    (gas_shadow_env T ce,shadow_sf) /\
  old.ce_alloca_locals /\ ~is_word_type typ /\
  local_ptrs_reserved old sa /\ gas_shadow_state sa shadow_sa /\
  fn_has_code sa sf func /\ fn_has_code shadow_sa shadow_sf shadow_func ==>
  ?r shadow_r p sz a shadow_a vv sv shadow_sv op b shadow_b.
    declare_local old id typ sa = (ce,r) /\
    declare_local (gas_shadow_env T old) id typ shadow_sa = (gas_shadow_env T ce,shadow_r) /\
    compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sf) /\
    compile_stmt (gas_shadow_env T ce) lctx ret_ty
      (AnnAssign id typ (gas_shadow_expr e)) shadow_r = ((),shadow_sf) /\
    sz = type_memory_bytes old typ /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
    ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
      ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
    emit_inst ALLOCA [Lit (n2w sz)] [p] r = ((),a) /\
    emit_inst ALLOCA [Lit (n2w sz)] [p] shadow_r = ((),shadow_a) /\
    compile_alloc_buffer sz sa = (<|buf_operand := Var p; buf_size := sz|>,a) /\
    compile_alloc_buffer sz shadow_sa =
      (<|buf_operand := Var p; buf_size := sz|>,shadow_a) /\
    compile_expr ce (expr_type e) e a = (vv,sv) /\
    compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_a = (vv,shadow_sv) /\
    (if has_length_word typ /\ is_empty_value_expr e then
       b = sv /\ shadow_b = shadow_sv /\ op = Lit 0w /\
       emit_void MSTORE [Var p; Lit 0w] b = ((),sf) /\
       emit_void MSTORE [Var p; Lit 0w] shadow_b = ((),shadow_sf)
     else
       unwrap_value ce vv sv = (op,b) /\
       unwrap_value (gas_shadow_env T ce) vv shadow_sv = (op,shadow_b) /\
       lower_value compile_expr ce (expr_type e) e a = (op,b) /\
       lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_a =
         (op,shadow_b) /\
       compile_assign_value ce (Var p) LocMemory op F (vv_location vv)
         typ (lowered_value_type ce e) (type_memory_bytes ce typ) b = ((),sf) /\
       compile_assign_value (gas_shadow_env T ce) (Var p) LocMemory op F (vv_location vv)
         typ (lowered_value_type (gas_shadow_env T ce) (gas_shadow_expr e))
         (type_memory_bytes (gas_shadow_env T ce) typ) shadow_b = ((),shadow_sf)) /\
    gas_shadow_state r shadow_r /\ gas_shadow_state a shadow_a /\
    gas_shadow_state sv shadow_sv /\ gas_shadow_state b shadow_b /\
    cs_extends sa a /\ cs_extends a sv /\ cs_extends sv b /\ cs_extends b sf /\
    cs_extends a b /\ cs_extends shadow_sa shadow_a /\
    cs_extends shadow_a shadow_b /\ cs_extends shadow_b shadow_sf /\
    cs_extends shadow_a shadow_sv /\ cs_extends shadow_sv shadow_b /\
    fn_has_code sa a func /\ fn_has_code a sv func /\
    fn_has_code a b func /\ fn_has_code sv b func /\ fn_has_code b sf func /\
    fn_has_code shadow_sa shadow_a shadow_func /\
    fn_has_code shadow_a shadow_b shadow_func /\
    fn_has_code shadow_a shadow_sv shadow_func /\ fn_has_code shadow_sv shadow_b shadow_func /\
    fn_has_code shadow_b shadow_sf shadow_func /\
    local_ptrs_reserved ce a /\ local_ptrs_reserved ce b /\
    not_fresh_at a p /\ not_fresh_at b p /\
    (!x. not_fresh_at sa x ==> not_fresh_at a x /\ not_fresh_at b x) /\
    sa.cs_next_id < a.cs_next_id /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func)
Proof
  strip_tac >> drule_all annassign_full_prefix_parts >>
  disch_then (qx_choosel_then
    [`r`,`shadow_r`,`p`,`sz`,`a`,`shadow_a`,`vv`,`sv`,`shadow_sv`,`op`,`b`,`shadow_b`]
    strip_assume_tac) >>
  `cs_extends shadow_a shadow_sv` by
    (qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
       (mp_then Any mp_tac (CONJUNCT1 compile_expr_grows)) >> simp[]) >>
  `cs_extends shadow_sv shadow_b` by
    (qpat_x_assum `if _ then _ else _` mp_tac >> IF_CASES_TAC >> strip_tac
     >- fs[cs_extends_refl] >>
     qspecl_then [`gas_shadow_env T ce`,`vv`,`shadow_sv`] mp_tac ci_mono_unwrap_value >>
     PURE_ASM_REWRITE_TAC[ci_mono_def,pairTheory.SND] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  qspecl_then [`a`,`sv`,`b`,`func`] mp_tac fn_has_code_split >>
  (impl_tac >- simp[]) >> strip_tac >>
  qspecl_then [`shadow_a`,`shadow_sv`,`shadow_b`,`shadow_func`] mp_tac fn_has_code_split >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`r`,`shadow_r`,`p`,`sz`,`a`,`shadow_a`,`vv`,`sv`,`shadow_sv`,`op`,`b`,`shadow_b`] >>
  asm_rewrite_tac[]
QED
