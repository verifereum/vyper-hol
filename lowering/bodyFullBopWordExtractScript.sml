Theory bodyFullBopWordExtract
Ancestors
  bodyPtrBopTypedSource bodyPtrBopScalarRun exprBopSimProps exprSimOperators
  bodyPtrBopInFlagInterface bodyPtrBopInFlagRobust bodyPtrBopInFlagCertificate
  bodyPtrBopScalarDispatch pred_set
  bodySimFull loweringPosts exprSimSource exprSimWordArgs exprSimDefs
  bodyPtrDefs vyperStorageFootprint gasStorage gasShadowState gasShadow
  exprLoweringProps valueEncoding vyperTypeSystem vyperState compileEnv freshWrites

Theorem bop_word_suffix_extract:
  word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  lower_value compile_expr cenv ty (gas_shadow_expr (Builtin ann (Bop bop) [e1;e2]))
    shadow_sa = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  gas_admissible (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx))
    expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  lower_value compile_expr cenv (expr_type e1) e2 s1 = (y,s2) /\
  lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e1) shadow_sa =
    (x,shadow_s1) /\
  lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e2) shadow_s1 =
    (y,shadow_s2) /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) s2 = (op,sb) /\
  gas_shadow_state s1 shadow_s1 /\ gas_shadow_state s2 shadow_s2 /\
  cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sb /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  s2.cs_next_var <= sb.cs_next_var /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\ (!l. y <> Label l) /\
  cs_extends shadow_sa shadow_s1 /\ cs_extends shadow_s1 shadow_s2 /\
  cs_extends shadow_s2 shadow_sb /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func /\
  fn_has_code shadow_sa shadow_s1 shadow_func /\
  fn_has_code shadow_s1 shadow_s2 shadow_func /\
  fn_has_code shadow_s2 shadow_sb shadow_func /\
  (!tail. bind (eval_expr cx e1) (read_result cx)
    (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
    (INL v1, mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    (expr_post H ctx func cenv cx e1 es sa s1 s0 mid v1 x t /\
      expr_store_bound cx (expr_type e1) v1 x t /\
      t.vs_current_bb = s1.cs_current_bb /\
      t.vs_inst_idx = LENGTH s1.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
      ptr_val_ok cx (post_value_type cenv e1) v1 x G1 tn1 t /\
      (~is_word_type (post_value_type cenv e1) ==> ptr_buf_ok cenv e1 x G1 t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
      ~t.vs_halted /\ mid.gas_obs = [])) /\
  (!tail. bind (eval_expr cx e2) (read_result cx)
    (mid with gas_obs := gas_explicit right t.vs_gas_readings ++ tail) =
    (INL v2, fin with gas_obs := tail)) /\
  storage_trace_domain cx st0 fin.storage_trace /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    (expr_post H ctx func cenv cx e2 mid s1 s2 t fin v2 y u /\
      expr_store_bound cx (expr_type e2) v2 y u /\
      u.vs_current_bb = s2.cs_current_bb /\
      u.vs_inst_idx = LENGTH s2.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx fin G2 tn2 u /\
      ptr_val_ok cx (post_value_type cenv e2) v2 y G2 tn2 u /\
      (~is_word_type (post_value_type cenv e2) ==> ptr_buf_ok cenv e2 y G2 u) /\
      ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\
      ~u.vs_halted /\ fin.gas_obs = [])) ==>
  well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  type_bits (expr_type e1) MOD 8 = 0 /\
  (bop = Exp ==> IS_SOME (expr_int_literal e1) \/
    ?n. expr_int_literal e2 = SOME n /\ 0 <= n) /\
  (!n. expr_int_literal e1 = SOME n ==> v1 = IntV n) /\
  (!n. expr_int_literal e2 = SOME n ==> v2 = IntV n) /\
  (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) /\
  (?tv1. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
    value_has_type tv1 v1) /\
  (?tv2. evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2 /\
    value_has_type tv2 v2) /\
  expr_res_ok (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  MAP FDOM mid.scopes = MAP FDOM fin.scopes /\
  (?B. bop_scalar_seq {z | not_fresh_at s2 z}
     ({x;y} UNION IMAGE Lit UNIV) (emitted_insts s2 sb) B /\ op IN B) /\
  ((?v r. bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin = INL v /\
      word_value v /\ run_inst_seq (emitted_insts s2 sb) u = OK r /\
      eval_operand op r = SOME (val_to_w256 v)) \/
   (?m r. bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin =
      INR (Error (RuntimeError m)) /\
      run_inst_seq (emitted_insts s2 sb) u = Abort Revert_abort r))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace /\
   valid_horizon cx st0 (storage_trace_horizon fin.storage_trace)
     fin.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SRULE []) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (qspec_then `storage_trace_horizon fin.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SRULE []) >>
  `mid with gas_obs := [] = mid /\ fin with gas_obs := [] = fin` by
    simp[evaluation_state_component_equality] >>
  `(?gs. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := gs) =
      (INL v1,mid)) /\
   (?gs. bind (eval_expr cx e2) (read_result cx) (mid with gas_obs := gs) =
      (INL v2,fin))` by
    (conj_tac >- (qexists_tac `gas_explicit left s0.vs_gas_readings` >>
       qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
         (qspec_then `[]` (assume_tac o SRULE [listTheory.APPEND_NIL])) >>
       metis_tac[]) >>
     qexists_tac `gas_explicit right t.vs_gas_readings` >>
     qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
       (qspec_then `[]` (assume_tac o SRULE [listTheory.APPEND_NIL])) >>
       metis_tac[]) >>
  `is_word_type (expr_type e1) /\ is_word_type (expr_type e2)` by
    metis_tac[word_value_type_word] >>
  drule bop_pair_source_facts >>
  disch_then (qspecl_then [`v2`, `v1`, `fin`, `mid`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `( ?B. bop_scalar_seq {z | not_fresh_at s2 z}
       ({x;y} UNION IMAGE Lit UNIV) (emitted_insts s2 sb) B /\ op IN B) /\
    ((?v r. bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin = INL v /\
       word_value v /\ run_inst_seq (emitted_insts s2 sb) u = OK r /\
       eval_operand op r = SOME (val_to_w256 v)) \/
     (?m r. bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin =
       INR (Error (RuntimeError m)) /\
       run_inst_seq (emitted_insts s2 sb) u = Abort Revert_abort r))`
    suffices_by metis_tac[] >>
  `word_value v1 /\ word_value v2` by metis_tac[word_value_type_typed] >>
  `eval_operand x t = SOME (val_to_w256 v1) /\
   eval_operand y u = SOME (val_to_w256 v2)` by
    (gvs[expr_post_def, post_value_type_word] >>
     metis_tac[expr_val_rel_word, optionTheory.IS_SOME_EXISTS]) >>
  `eval_operand x u = SOME (val_to_w256 v1)` by
    (irule eval_operand_frame >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`s1`, `t`] >>
     qpat_assum `expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, expr_post_def] >> metis_tac[]) >>
  `!z. x = Var z ==> not_fresh_at s2 z` by metis_tac[not_fresh_at_mono] >>
  Cases_on `bop = In \/ bop = NotIn`
  >- (`?fid. expr_type e2 = FlagT fid` by
        (Cases_on `bop = In` >>
         `bop = In \/ bop = NotIn` by metis_tac[] >>
         gvs[] >>
         qpat_x_assum `well_typed_binop _ _ _ _`
           (strip_assume_tac o PURE_REWRITE_RULE [well_typed_binop_def]) >>
         gvs[is_word_type_def]) >>
      `?m. value_has_type (FlagTV m) v1 /\
           value_has_type (FlagTV m) v2 /\ m <= 256` by
        (irule membership_flag_typed_inputs >> metis_tac[]) >>
      conj_tac
      >- (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)
            membership_flag_scalar_certificate >>
          disch_then (qspecl_then
            [`{z | not_fresh_at s2 z}`, `{x;y} UNION IMAGE Lit UNIV`] mp_tac) >>
          simp[] >> metis_tac[]) >>
      disj1_tac >> irule membership_flag_source_run_robust >>
      simp[] >> metis_tac[]) >>
  conj_tac
  >- (irule bop_scalar_binop_certificate >> simp[] >> metis_tac[]) >>
  drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`) bop_scalar_typed_run >>
  disch_then match_mp_tac >> simp[] >> metis_tac[]
QED
