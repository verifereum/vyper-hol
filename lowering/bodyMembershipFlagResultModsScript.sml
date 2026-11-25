(* Linked successful scalar suffix for flag membership. *)
Theory bodyMembershipFlagResultMods
Ancestors bodyBopScalarNormalOutcomeMods bodyPtrBopInFlagInterface
  bodyPtrBopInFlagRobust bodyPtrBopInFlagCertificate exprBopSimProps
  exprSimSource exprBopFlag vyperStorageFootprint gasContext list vyperState
  exprSimHypsDefs vyperTypeSystem compileEnv bodyFullPostsMods loweringPosts
  exprSimProps freshWrites vyperValue
Libs monadsyntax

Theorem flag_admissible_at_landing[local]:
  gas_admissible (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2]))
    (read_result cx)) expr_res_ok es /\
  (!tail. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := l ++ tail) =
    (INL v1,mid with gas_obs := tail)) /\
  (!tail. bind (eval_expr cx e2) (read_result cx) (mid with gas_obs := r ++ tail) =
    (INL v2,fin with gas_obs := tail)) /\ fin.gas_obs = [] ==>
  expr_res_ok (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 fin)
Proof
  strip_tac >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  PURE_REWRITE_TAC [REWRITE_RULE [ETA_AX] eval_expr_bop_bind, gas_admissible_def] >>
  disch_then (irule o SPEC_ALL) >>
  qexistsl_tac [`fin`,`l ++ r`] >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _` (qspec_then `r` assume_tac) >>
  qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
    (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
  PURE_ONCE_REWRITE_TAC [bind_def] >> asm_rewrite_tac[] >> simp[] >>
  PURE_ONCE_REWRITE_TAC [bind_def] >> asm_rewrite_tac[] >> simp[]
QED

Theorem flag_operand_word[local]:
  expr_post_mods H ctx func ce cx e es sa sb s0 fin v op u /\
  expr_type e = FlagT fid /\ evaluate_type (get_tenv cx) (FlagT fid) = SOME tv /\
  value_has_type tv v ==> eval_operand op u = SOME (val_to_w256 v)
Proof
  strip_tac >>
  `word_value_type (FlagT fid)` by simp[word_value_type_def, is_flag_type_def] >>
  `word_value v` by (drule_all word_value_type_typed >> simp[]) >>
  `is_word_type (FlagT fid)` by simp[is_word_type_def, is_flag_type_def] >>
  fs[expr_post_mods_def, expr_post_def, post_value_type_word] >>
  drule_all expr_val_rel_typed >> simp[typed_val_to_w256_word_value]
QED

Theorem membership_flag_result_mods:
  (bop = In \/ bop = NotIn) /\
  expr_type e1 = FlagT fid /\ expr_type e2 = FlagT fid /\
  ann = BaseT BoolT /\
  well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) s2 = (op,sb) /\
  fn_has_code s2 sb func /\
  sa.cs_next_var <= s1.cs_next_var /\
  s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\
  local_ptrs_reserved cenv sa /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  (!l. x <> Label l) /\
  (!tail. bind (eval_expr cx e1) (read_result cx)
    (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
    (INL v1,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e1 es sa s1 s0 mid v1 x t /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e1) v1 x G1 tn1 t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) /\
  (!tail. bind (eval_expr cx e2) (read_result cx)
    (mid with gas_obs := gas_explicit right t.vs_gas_readings ++ tail) =
    (INL v2,fin with gas_obs := tail)) /\
  storage_trace_domain cx st0 fin.storage_trace /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    expr_post_mods H ctx func cenv cx e2 mid s1 s2 t fin v2 y u /\
    u.vs_current_bb = s2.cs_current_bb /\
    u.vs_inst_idx = LENGTH s2.cs_current_insts /\
    alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    t.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx fin G2 tn2 u /\
    ptr_val_ok cx (post_value_type cenv e2) v2 y G2 tn2 u /\
    ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\
    ~u.vs_halted /\
    fin.gas_obs = []) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  MAP FDOM mid.scopes = MAP FDOM fin.scopes /\
  evaluate_type (get_tenv cx) (FlagT fid) = SOME tv /\
  value_has_type tv v1 /\ value_has_type tv v2 /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\
  gas_admissible (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2]))
    (read_result cx)) expr_res_ok es ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0
    (\ee. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 ee,ee))
    (fin,u,G2,tn2)
    (\H res ee G tn t'. ?v. res = INL v /\
      expr_post_mods H ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
        es sa sb s0 ee v op t' /\
      expr_store_bound cx
        (post_value_type cenv (Builtin ann (Bop bop) [e1;e2])) v op t' /\
      t'.vs_current_bb = sb.cs_current_bb /\
      t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t' /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t') /\
      s0.vs_alloca_next <= t'.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t' /\
      ptr_val_ok cx
        (post_value_type cenv (Builtin ann (Bop bop) [e1;e2])) v op G tn t' /\
      (~is_word_type
        (post_value_type cenv (Builtin ann (Bop bop) [e1;e2])) ==>
        ptr_buf_ok cenv (Builtin ann (Bop bop) [e1;e2]) op G t') /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace /\
   valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (qspec_then `storage_trace_horizon fin.storage_trace` (drule_then strip_assume_tac)) >>
  `expr_res_ok (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin)` by
    (irule flag_admissible_at_landing >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`es`,`gas_explicit left s0.vs_gas_readings`,`mid`,
       `gas_explicit right t.vs_gas_readings`] >> simp[]) >>
  `?m. value_has_type (FlagTV m) v1 /\ value_has_type (FlagTV m) v2 /\ m <= 256` by
    (`well_typed_binop ann bop (FlagT fid) (FlagT fid)` by
       (qpat_assum `well_typed_binop _ _ _ _` (fn th =>
         qpat_assum `expr_type e1 = _` (fn h1 =>
           qpat_assum `expr_type e2 = _` (fn h2 =>
             ACCEPT_TAC (PURE_REWRITE_RULE [h1,h2] th))))) >>
     drule_at (Pat `well_typed_binop _ _ _ (FlagT _)`) membership_flag_typed_inputs >>
     disch_then irule >> rpt (first_assum (irule_at Any))) >>
  `eval_operand x t = SOME (val_to_w256 v1) /\ eval_operand y u = SOME (val_to_w256 v2)` by
    (conj_tac
     >- (qpat_assum `expr_post_mods _ _ _ _ _ e1 _ _ _ _ _ _ _ _`
           (mp_then (Pat `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac
             flag_operand_word) >>
         disch_then irule >> qexistsl_tac [`fid`,`tv`] >> simp[]) >>
     qpat_assum `expr_post_mods _ _ _ _ _ e2 _ _ _ _ _ _ _ _`
       (mp_then (Pat `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac
         flag_operand_word) >>
     disch_then irule >> qexistsl_tac [`fid`,`tv`] >> simp[]) >>
  `eval_operand x u = SOME (val_to_w256 v1)` by
    (irule eval_operand_frame >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`s1`,`t`] >> fs[expr_post_mods_def, expr_post_def]) >>
  `!z. x = Var z ==> not_fresh_at s2 z` by metis_tac[not_fresh_at_mono] >>
  `?v r. bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin = INL v /\
      word_value v /\ run_inst_seq (emitted_insts s2 sb) u = OK r /\
      eval_operand op r = SOME (val_to_w256 v)` by
    (irule membership_flag_source_run_robust >>
     qpat_assum `compile_binop _ _ _ _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `value_has_type (FlagTV m) v1` (irule_at Any) >> simp[]) >>
  `expr_val_rel cx ann v op r` by
    simp[expr_val_rel_def, is_word_type_def, evaluate_type_def,
         typed_val_to_w256_word_value] >>
  `?B. (bop_scalar_seq {z | not_fresh_at s2 z}
      ({x;y} UNION IMAGE Lit UNIV) (emitted_insts s2 sb) B /\
      ({x;y} UNION IMAGE Lit UNIV) SUBSET B /\
      sb.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 sb /\
      same_blocks s2 sb /\ s2.cs_next_var <= sb.cs_next_var) /\ op IN B` by
    (irule membership_flag_scalar_certificate >> simp[] >>
     first_assum (irule_at Any) >> simp[]) >>
  mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] bop_scalar_normal_outcome_mods)) >>
  impl_tac
  >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
                       simp[is_word_type_def, is_flag_type_def])) >>
  disch_then ACCEPT_TAC
QED
