(* Lift the successful scalar suffix after two reached linked reads. *)
Theory bodyBopScalarNormalOutcomeMods
Ancestors
  bodyBopWordNormalPostMods bodyFullBopWordSuccess bodyPtrBopScalarDispatch
  bodyFullPostsMods bodyFullShadowBodyInv bodyPtrDefs gasOutcomeFullPostMods
  exprBopSimProps exprBopSimDefs exprLoweringProps exprSimMemDefs
  vyperStorageTrace vyperStorageFootprint vyperTypeSystem vyperAST
  vyperState gasContext gasStorage fragExec fragGasOriginPtr loweringPosts
  augAssignPtrCompiler freshWrites ptrDiscipline rich_list list pred_set
Libs monadsyntax

Theorem scalar_read_horizon[local]:
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs) =
    (INL v, ee with gas_obs := ys) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  valid_horizon cx st0 H es.storage_trace
Proof
  strip_tac >> drule_at (Pat `_ = _`) valid_horizon_frame >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result] >> disch_then irule >> simp[]
QED

Theorem scalar_suffix_prefix[local]:
  well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) s2 = (op,sb) /\
  fn_has_code s2 sb func /\
  u.vs_current_bb = s2.cs_current_bb /\ u.vs_inst_idx = LENGTH s2.cs_current_insts ==>
  ?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts s2 sb) (DROP u.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >>
  `MEM bop [Add;Sub;Mul;Div;Mod;UnsafeAdd;UnsafeSub;UnsafeMul;UnsafeDiv;
           And;Or;XOr;ShL;ShR;Eq;NotEq;Lt;LtE;Gt;GtE;Exp;Min;Max;In;NotIn]` by
    (qpat_assum `well_typed_binop _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `bop` >> simp[well_typed_binop_def]) >>
  drule compile_binop_straight_fresh_ptr >>
  simp[straight_fresh_def] >> disch_then drule >> strip_tac >>
  qpat_x_assum `fn_has_code s2 sb func` (mp_tac o REWRITE_RULE [fn_has_code_def]) >>
  simp[IS_PREFIX_APPEND] >> strip_tac >> qexists_tac `bb` >> simp[DROP_APPEND]
QED

Theorem scalar_suffix_operands_clean[local]:
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  ptr_val_ok cx (post_value_type cenv e1) v1 x G1 tn1 t /\
  ptr_val_ok cx (post_value_type cenv e2) v2 y G2 tn2 u /\
  ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) ==>
  !a. a IN ({x;y} UNION IMAGE Lit UNIV) ==>
      op_prov G2 a = NONE /\ op_taint tn2 a = {}
Proof
  strip_tac >>
  `op_prov G2 x = op_prov G1 x /\ op_taint tn2 x = op_taint tn1 x` by
    (Cases_on `x` >> gvs[op_prov_def, op_taint_def, ghost_kept_at_def]) >>
  mp_tac (Q.INST [`x` |-> `x`, `y` |-> `y`, `G` |-> `G2`, `tn` |-> `tn2`]
    bop_scalar_binop_input_clean) >> fs[post_value_type_word, ptr_val_ok_def]
QED

Theorem bop_scalar_normal_outcome_mods:
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\ is_word_type ann /\
  well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) s2 = (op,sb) /\
  fn_has_code s2 sb func /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ local_ptrs_reserved cenv sa /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
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
    u.vs_current_bb = s2.cs_current_bb /\ u.vs_inst_idx = LENGTH s2.cs_current_insts /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    t.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx fin G2 tn2 u /\
    ptr_val_ok cx (post_value_type cenv e2) v2 y G2 tn2 u /\
    ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\ ~u.vs_halted /\ fin.gas_obs = []) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ MAP FDOM mid.scopes = MAP FDOM fin.scopes /\
  bop_scalar_seq {z | not_fresh_at s2 z} ({x;y} UNION IMAGE Lit UNIV)
    (emitted_insts s2 sb) B /\ op IN B /\
  bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin = INL v /\
  run_inst_seq (emitted_insts s2 sb) u = OK r /\ expr_val_rel cx ann v op r ==>
  let e = Builtin ann (Bop bop) [e1;e2] in
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0
    (\ee. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 ee,ee))
    (fin,u,G2,tn2)
    (\H res ee G tn t'. ?v. res = INL v /\
      expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t' /\
      expr_store_bound cx (post_value_type cenv e) v op t' /\
      t'.vs_current_bb = sb.cs_current_bb /\ t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t' /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t') /\
      s0.vs_alloca_next <= t'.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t' /\
      ptr_val_ok cx (post_value_type cenv e) v op G tn t' /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t') /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) R
Proof
  simp[LET_THM] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace /\
   valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (qspec_then `storage_trace_horizon fin.storage_trace` (drule_then strip_assume_tac)) >>
  `!a. a IN ({x;y} UNION IMAGE Lit UNIV) ==>
       op_prov G2 a = NONE /\ op_taint tn2 a = {}` by
    (mp_tac (SPEC_ALL scalar_suffix_operands_clean) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `allocas_from lo u` by fs[ghost_inv_at_mods_def] >>
  drule_all_then strip_assume_tac scalar_suffix_prefix >>
  drule_all bop_word_scalar_success_joint >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G'`,`fin`,`INL v`,
    `r with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb)`,`tn'`] >>
  simp[] >> gen_tac >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (irule scalar_read_horizon >>
     qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
       (qspec_then `[]` (irule_at Any)) >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (irule scalar_read_horizon >>
     qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
       (qspec_then `[]` (irule_at Any)) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!h. valid_horizon _ _ h es.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. valid_horizon _ _ h fin.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!a. a IN B ==> _` (qspec_then `op` (drule_then strip_assume_tac)) >>
  `!z. not_fresh_at s2 z ==> FLOOKUP G' z = FLOOKUP G2 z /\
       FLOOKUP tn'.t_var z = FLOOKUP tn2.t_var z` by
    (qpat_assum `!z. z IN {z | not_fresh_at s2 z} ==> _` mp_tac >> simp[]) >>
  mp_tac (Q.INST_TYPE [`:'a` |-> `:256`] (SRULE [LET_THM] bop_word_normal_post_mods)) >>
  (impl_tac >- simp[]) >> simp[expr_type_def, post_value_type_word]
QED
