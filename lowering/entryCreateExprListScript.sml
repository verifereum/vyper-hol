(* Ordinary word arguments: the compiler cursors correspond to successful
   reads, not just to syntactic membership in the source list. *)
Theory entryCreateExprList
Ancestors
  entryCreateScopedBind entryCreateCompositeFocus entryCreatePendingScope
  entryCreateFocusSpec entryCreateCompletedCut entryCreateBodyCut
  bodyFullWordArgs createSizeOperandCode createSizeCutCode exprSimFullBundleProps wordArgsPtr
  bodyFullPreds exprSimSource exprSimPrecompiles gasShadowCompileStmtHelpers
  exprLoweringProps gasShadowState s1PrefixDefs exprBodyPreProps
  vyperStorageTrace vyperStorageFootprint gasExemptCert gasStorage gasSummary
  fragGasOriginPtr fragGasOrigin fragGasMode fragGasPath exprSimWordArgs exprSimHyps
  bodyFullIfExpReach
  loweringPosts bodyPtrDefs vyperState vyperInterpreter fragExec
  list finite_map pred_set pair

Definition create_word_args_post_def:
  create_word_args_post (DF,lo,d,ctx,func) cenv cx
      (es,sa,sb,s,G,tn) todo xs H res ee G' tn' u <=>
    (?vs. res = INL vs /\
       typed_args_post H ctx func cenv cx es sa s ee todo xs vs u) /\
    expr_sim_full_endpoint func sb s u /\
    ghost_inv_at (DF H) lo d cenv cx ee G' tn' u /\
    ghost_kept_at lo cenv es sa G tn s G' tn' /\
    EVERY (\x. op_taint tn' x = {}) xs
End

Definition create_word_args_exit_def:
  create_word_args_exit ctx cx H res ee gt r <=>
    wb_args_exit res r /\ halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)
End

Theorem create_word_args_cut_code:
  !todo sa sb xs.
    lower_word_args ce tyf todo sa = (xs,sb) ==> create_cut_code {} sa sb
Proof
  Induct >> simp[lower_word_args_nil] >> rpt gen_tac >>
  simp[lower_word_args_cons] >> strip_tac >>
  irule create_cut_code_join >>
  qexists_tac `s1` >> conj_tac
  >- metis_tac[create_operand_cut_code, SND] >>
  metis_tac[]
QED

Theorem create_word_args_read_frame[local]:
  storage_trace_frame (bind (eval_expr cx e) (read_result cx))
Proof
  irule storage_trace_frame_bind_all >>
  simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]
QED

Theorem create_word_args_cons_frame[local]:
  storage_trace_frame (bind (eval_exprs cx todo) (\vs. return (v::vs)))
Proof
  irule storage_trace_frame_bind_all >>
  simp[evaluate_storage_trace_frame, storage_trace_frame_return]
QED

Theorem create_word_args_cons_ignore[local]:
  ignore_bind (bind (eval_exprs cx todo) (\vs. return (v::vs))) (return ()) =
  ignore_bind (eval_exprs cx todo) (return ())
Proof
  simp[FUN_EQ_THM, bind_def, ignore_bind_def, return_def] >> gen_tac >>
  Cases_on `eval_exprs cx todo x` >> Cases_on `q` >> simp[]
QED

Theorem create_word_args_cut_cons_result[local]:
  create_operand_cut sa sb E C f tops cx st0 (eval_exprs cx todo) (es,s) ==>
  create_operand_cut sa sb E C f tops cx st0
    (bind (eval_exprs cx todo) (\vs. return (v::vs))) (es,s)
Proof
  simp[create_operand_cut_def] >> rpt strip_tac >>
  irule create_cut_bind_left >> simp[storage_trace_frame_return] >> res_tac
QED

(* A pure result map does not extend the compiled interval or consume a
   reading. Keep all three scoped branches at the original witness. *)
Theorem create_word_args_scoped_cons_result[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
    (eval_exprs cx todo) (es,s,G0,tn0) Q R /\
  (!H vs ee G tn t. valid_horizon cx st0 H es.storage_trace /\
    Q H (INL vs) ee G tn t ==> Q' H (INL (v::vs)) ee G tn t) /\
  (!H ee G tn t exc. ~Q H (INR exc) ee G tn t) /\
  (!H res ee gt r. R H res ee gt r ==> ?exc. res = INR exc /\ R' H (INR exc) ee gt r) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
    (bind (eval_exprs cx todo) (\vs. return (v::vs))) (es,s,G0,tn0) Q' R'
Proof
  strip_tac >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [scoped_operand_outcome_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks`
  >~ [`gas_bad_storage_at _ _ _ _ _ _`]
  >- (disj1_tac >> simp[] >> conj_tac
      >- (irule gas_bad_storage_at_bind_left >> simp[storage_trace_frame_return]) >>
      metis_tac[])
  >- (disj2_tac >> disj1_tac >> Cases_on `res`
      >- (rename1 `eval_exprs _ _ _ = (INL vs,_)` >>
          qexistsl_tac [`INL (v::vs)`,`ee`,`r`,`G'`,`tn'`] >>
          simp[bind_def, return_def] >> rpt strip_tac >> res_tac >> gvs[] >>
          `valid_horizon cx st0 H es.storage_trace` by
            (qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]` assume_tac) >>
             imp_res_tac valid_horizon_frame >> fs[evaluate_storage_trace_frame] >>
             metis_tac[]) >>
          metis_tac[sumTheory.sum_distinct]) >>
      rename1 `eval_exprs _ _ _ = (INR exc,_)` >>
      qexistsl_tac [`INR exc`,`ee`,`r`,`G'`,`tn'`] >>
      simp[bind_def] >> rpt strip_tac >> res_tac >> gvs[] >> metis_tac[sumTheory.INR_11]) >>
  disj2_tac >> disj2_tac >> simp[create_word_args_cons_ignore] >> metis_tac[]
QED

Theorem create_word_args_nil[local]:
  create_operand_at sa s /\ ~s.vs_halted /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H C f ce cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G tn s) /\ alloca_history f s ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 sa sa
    (eval_exprs cx []) (es,s,G,tn)
    (create_word_args_post (DF,lo,d,C,f) ce cx (es,sa,sa,s,G,tn) [] []) R /\
  create_operand_cut sa sa E C f tops cx st0 (eval_exprs cx []) (es,s)
Proof
  strip_tac >> reverse conj_tac
  >- (simp[create_operand_cut_def] >> metis_tac[create_operand_empty_scope]) >>
  irule scoped_operand_pure >> simp[eval_exprs_nil, return_def] >>
  qexistsl_tac [`es`, `INL []`] >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[create_word_args_post_def, typed_args_post_def, create_operand_at_def,
       expr_sim_full_endpoint_def, wb_frame_refl, ghost_kept_at_def] >>
  conj_tac
  >- (qsuff_tac `storage_well_formed_on cx (es with gas_obs := []) (FST H) =
                 storage_well_formed_on cx es (FST H)` >- simp[] >>
      irule storage_well_formed_on_backends >> simp[]) >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  fs[ghost_inv_at_def, create_operand_at_def] >> strip_tac >> first_assum ACCEPT_TAC
QED

(* The same local precondition is used when following the semantic witness
   or when replaying to the split of a supplied native visit. *)
Definition create_word_args_pre_def:
  create_word_args_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) tops cenv env cx tyf
      todo (es,st0,sa,sb,sha,shb,xs,s,G,tn) <=>
    (!e. tyf (gas_shadow_expr e) = tyf e) /\
    (!e ee. MEM e todo /\ expr_sim_inv cenv cx env ee ==>
      expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)) /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\ expr_sim_inv cenv cx env es /\
    lower_word_args cenv tyf todo sa = (xs,sb) /\
    lower_word_args (gas_shadow_env T cenv) tyf (MAP gas_shadow_expr todo) sha = (xs,shb) /\
    expr_sim_full_code (ctx,shctx,func,shfunc) (sa,sb,sha,shb) /\
    local_ptrs_reserved cenv sa /\
    (!fn inst t. frag_reachable ctx func s fn inst t ==> dalloca_fmp_headroom inst t) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    return_buf_frame d cenv sa s /\ alloca_history func s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
    ~s.vs_halted /\ create_operand_at sa s
End

Theorem create_word_args_shadow_split[local]:
  (!e. tyf (gas_shadow_expr e) = tyf e) /\
  gas_shadow_state a ha /\
  lower_value compile_expr ce (tyf e) e a = (op,m) /\
  lower_value compile_expr (gas_shadow_env T ce) (tyf e) (gas_shadow_expr e) ha = (op,hm) /\
  lower_word_args ce tyf todo m = (xs,b) /\
  lower_word_args (gas_shadow_env T ce) tyf (MAP gas_shadow_expr todo) hm = (xs,hb) ==>
  gas_shadow_state m hm /\ cs_extends ha hm /\ cs_extends hm hb
Proof
  strip_tac >> conj_asm1_tac
  >- (`gas_shadow_compiles (lower_value compile_expr ce (tyf e) e)
          (lower_value compile_expr (gas_shadow_env T ce) (tyf e) (gas_shadow_expr e))`
        by simp[gas_shadow_stmt_lower_value_env] >>
      fs[gas_shadow_compiles_def] >> metis_tac[pairTheory.SND]) >>
  metis_tac[ci_mono_lower_word_args, ci_mono_lower_value_compile_expr,
            ci_mono_def, pairTheory.SND]
QED

Theorem create_word_args_pre_cons[local]:
  create_word_args_pre (DF,lo,d,C,shC,PG,f,shf) tops ce env cx tyf
    (e::todo) (es,st0,a,b,ha,hb,ops,s,G,tn) ==>
  ?m hm op xs.
    ops = op::xs /\
    expr_body_pre ce cx env e es /\ is_word_type (expr_type e) /\
    expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (tyf e) e es
      (st0,a,m,ha,hm,op,s,G,tn) /\
    lower_word_args ce tyf todo m = (xs,b) /\
    lower_word_args (gas_shadow_env T ce) tyf (MAP gas_shadow_expr todo) hm = (xs,hb) /\
    fn_has_code m b f /\ fn_has_code hm hb shf
Proof
  simp[create_word_args_pre_def, create_operand_at_def, expr_sim_full_code_def] >>
  strip_tac >>
  `expr_body_pre ce cx env e es /\ is_word_type (expr_type e)` by metis_tac[] >>
  gvs[lower_word_args_cons, MAP] >>
  drule_all create_word_args_shadow_split >> strip_tac >>
  `cs_extends a s1 /\ cs_extends s1 b` by
    metis_tac[ci_mono_lower_word_args, ci_mono_lower_value_compile_expr,
              ci_mono_def, pairTheory.SND] >>
  `fn_has_code a s1 f /\ fn_has_code s1 b f` by metis_tac[fn_has_code_split] >>
  `fn_has_code ha s1' shf /\ fn_has_code s1' hb shf` by metis_tac[fn_has_code_split] >>
  qexistsl_tac [`s1`,`s1'`] >> simp[expr_sim_full_pre_def] >>
  metis_tac[expr_body_pre_gas_admissible]
QED

Theorem create_word_args_read_state[local]:
  expr_body_pre ce cx env e es /\ body_const_cells_agree [(NONE,tops)] cx env es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
    (INL v,mid) ==>
  expr_sim_inv ce cx env mid /\ body_const_cells_agree [(NONE,tops)] cx env mid /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >>
  `well_typed_expr env e` by (drule expr_body_pre_static_facts >> simp[]) >>
  `expr_body_pre ce cx env e (es with gas_obs := obs)` by simp[] >>
  `body_const_cells_agree [(NONE,tops)] cx env (es with gas_obs := obs)` by simp[] >>
  conj_tac
  >- (drule_all (SRULE [SF ETA_ss] expr_body_pre_eval) >> simp[]) >>
  conj_tac
  >- (irule body_const_cells_agree_expr_read >>
      goal_assum (drule_at (Pat `bind (eval_expr _ _) _ _ = _`)) >> simp[]) >>
  drule (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom) >> simp[]
QED

Theorem create_word_args_return_frame[local]:
  return_buf_frame d ce a s /\ a.cs_next_var <= m.cs_next_var /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  expr_post H C f ce cx e es a m s mid v op t ==>
  return_buf_frame d ce m t
Proof
  Cases_on `d` >> simp[return_buf_frame_def] >>
  PairCases_on `x` >> simp[return_buf_frame_def] >> strip_tac >>
  rename1 `ce.ce_return_buf = SOME (PtrVar (Var z) sz)` >>
  qexistsl_tac [`z`,`sz`] >> fs[expr_post_def] >>
  metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]
QED

(* The tail readiness is re-established at the actual read-result state.
   It is not an eager evaluation of the tail at the original state. *)
Theorem create_word_args_tail_pre[local]:
  create_word_args_pre (DF,lo,d,C,shC,PG,f,shf) tops ce env cx tyf
    (e::todo) (es,st0,a,b,ha,hb,op::xs,s,G,tn) /\
  expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (tyf e) e es
    (st0,a,m,ha,hm,op,s,G,tn) /\
  lower_word_args ce tyf todo m = (xs,b) /\
  lower_word_args (gas_shadow_env T ce) tyf (MAP gas_shadow_expr todo) hm = (xs,hb) /\
  fn_has_code m b f /\ fn_has_code hm hb shf /\
  expr_body_pre ce cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) = (INL v,mid) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       expr_sim_full_post (DF,lo,d,C,f) ce cx e (es,a,m,s,op,G,tn)
         H (INL v) (mid with gas_obs := []) G1 tn1 t /\
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites C shC,C,f,PG)
         (s,G,tn) marks (OK t,G1,tn1)) ==>
  create_word_args_pre (DF,lo,d,C,shC,PG,f,shf) tops ce env cx tyf
    todo (mid with gas_obs := [],st0,m,b,hm,hb,xs,t,G1,tn1)
Proof
  simp[create_word_args_pre_def, expr_sim_full_code_def] >> strip_tac >>
  drule_all create_word_args_read_state >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by simp[GSYM storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0`
    by metis_tac[body_inv_no_phi] >>
  `!fn inst u. frag_reachable C f t fn inst u ==> dalloca_fmp_headroom inst u` by
    (drule gas_origin_ptr_path_dalloca_fmp_headroom >> metis_tac[]) >>
  `~t.vs_halted` by metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase,
                             gas_marked_path_exec, gas_path_normal] >>
  `a.cs_next_var <= m.cs_next_var` by
    (fs[expr_sim_full_pre_def] >>
     metis_tac[ci_mono_lower_value_compile_expr, ci_mono_def, pairTheory.SND]) >>
  `return_buf_frame d ce m t` by
    (fs[expr_sim_full_post_def, expr_sim_full_endpoint_def] >>
     metis_tac[create_word_args_return_frame]) >>
  fs[expr_sim_full_post_def, expr_sim_full_endpoint_def,
     create_operand_at_def, expr_sim_full_pre_def] >>
  rpt conj_tac
  >- metis_tac[]
  >- metis_tac[local_ptrs_reserved_next_var]
  >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]
  >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  rpt strip_tac >> res_tac >> fs[expr_post_def] >>
  metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]
QED

Theorem create_word_args_cons_post[local]:
  expr_sim_full_post (DF,lo,d,C,f) ce cx e (es,a,m,s,op,G,tn)
    H (INL v) mid G1 tn1 t /\
  create_word_args_post (DF,lo,d,C,f) ce cx (mid,m,b,t,G1,tn1)
    todo xs H (INL vs) ee G2 tn2 u /\
  stmt_state_rel H C f ce cx es s /\ local_ptrs_reserved ce a /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  a.cs_next_var <= m.cs_next_var /\ a.cs_next_id <= m.cs_next_id /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (!z. op = Var z ==> not_fresh_at m z) /\ (!l. op <> Label l) ==>
  create_word_args_post (DF,lo,d,C,f) ce cx (es,a,b,s,G,tn)
    (e::todo) (op::xs) H (INL (v::vs)) ee G2 tn2 u
Proof
  simp[create_word_args_post_def, expr_sim_full_post_def] >> strip_tac >>
  `typed_args_post H C f ce cx es a s ee (e::todo) (op::xs) (v::vs) u` by
    metis_tac[typed_args_post_cons] >>
  `s.vs_alloca_next <= u.vs_alloca_next` by
    fs[expr_sim_full_endpoint_def, arithmeticTheory.LESS_EQ_TRANS] >>
  `op_taint tn2 op = {}` by
    (`ghost_kept ce mid m G1 tn1 t G2 tn2` by
       (qpat_assum `ghost_kept_at lo ce mid m _ _ _ _ _`
         (mp_tac o REWRITE_RULE [ghost_kept_at_def]) >>
        simp[NoAsms, ghost_kept_def] >> strip_tac >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     `op_taint tn1 op = {}` by fs[ptr_val_ok_def] >>
     metis_tac[ghost_kept_operand]) >>
  fs[expr_sim_full_endpoint_def] >>
  `wb_frame ce es mid a s t` by metis_tac[expr_post_frame] >>
  drule_all ghost_kept_at_wb_trans >> simp[]
QED

Theorem create_word_args_tail_scoped[local]:
  create_word_args_pre (DF,lo,d,C,shC,PG,f,shf) tops ce env cx tyf
    (e::todo) (es,st0,a,b,ha,hb,op::xs,s,G,tn) /\
  expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (tyf e) e es
    (st0,a,m,ha,hm,op,s,G,tn) /\
  lower_word_args ce tyf todo m = (xs,b) /\
  lower_word_args (gas_shadow_env T ce) tyf (MAP gas_shadow_expr todo) hm = (xs,hb) /\
  fn_has_code m b f /\ fn_has_code hm hb shf /\
  expr_body_pre ce cx env e es /\ is_word_type (expr_type e) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) = (INL v,mid) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       expr_sim_full_post (DF,lo,d,C,f) ce cx e (es,a,m,s,op,G,tn)
         H (INL v) (mid with gas_obs := []) G1 tn1 t /\
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites C shC,C,f,PG)
         (s,G,tn) marks (OK t,G1,tn1)) /\
  (create_word_args_pre (DF,lo,d,C,shC,PG,f,shf) tops ce env cx tyf
      todo (mid with gas_obs := [],st0,m,b,hm,hb,xs,t,G1,tn1) ==>
   scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) tops cx st0 m b
     (eval_exprs cx todo) (mid with gas_obs := [],t,G1,tn1)
     (create_word_args_post (DF,lo,d,C,f) ce cx (mid with gas_obs := [],m,b,t,G1,tn1) todo xs)
     (create_word_args_exit C cx)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) tops cx st0 m b
    (bind (eval_exprs cx todo) (\vs. return (v::vs))) (mid with gas_obs := [],t,G1,tn1)
    (create_word_args_post (DF,lo,d,C,f) ce cx (es,a,b,s,G,tn) (e::todo) (op::xs))
    (create_word_args_exit C cx)
Proof
  strip_tac >> drule_all create_word_args_tail_pre >> strip_tac >> res_tac >>
  `body_const_cells_agree [(NONE,tops)] cx env es` by fs[create_word_args_pre_def] >>
  drule_all create_word_args_read_state >> strip_tac >>
  `lower_value compile_expr ce (tyf e) e a = (op,m)` by fs[expr_sim_full_pre_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  drule expr_body_pre_type_evaluates >> simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  irule create_word_args_scoped_cons_result >> first_assum (irule_at Any) >>
  conj_tac >- simp[create_word_args_post_def] >>
  reverse conj_tac
  >- (simp[create_word_args_exit_def, wb_args_exit_def] >> rpt gen_tac >>
      Cases_on `res` >> simp[]) >>
  rpt strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (imp_res_tac valid_horizon_frame >> fs[create_word_args_read_frame] >> metis_tac[]) >>
  `stmt_state_rel H C f ce cx es s /\ local_ptrs_reserved ce a` by
    (fs[create_word_args_pre_def] >> res_tac) >>
  `valid_horizon cx st0 H mid.storage_trace` by fs[] >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by simp[] >>
  qpat_assum `!K. valid_horizon _ _ K mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  irule create_word_args_cons_post >>
  simp[] >> qexistsl_tac [`G1`,`m`,`mid with gas_obs := []`,`t`,`tn1`] >>
  gvs[expr_sim_full_post_def, create_word_args_post_def, post_value_type_word]
QED

Theorem create_word_args_pre_nil[local]:
  create_word_args_pre (DF,lo,d,C,shC,PG,f,shf) tops ce env cx tyf
    [] (es,st0,a,b,ha,hb,ops,s,G,tn) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG)
    tops cx st0 a b (eval_exprs cx []) (es,s,G,tn)
    (create_word_args_post (DF,lo,d,C,f) ce cx (es,a,b,s,G,tn) [] ops)
    (create_word_args_exit C cx) /\
  create_operand_cut a b (gas_explicit_sites C shC) C f tops cx st0
    (eval_exprs cx []) (es,s)
Proof
  simp[create_word_args_pre_def, lower_word_args_nil] >> strip_tac >>
  drule_all create_word_args_nil >> simp[]
QED

Theorem create_word_args_eval_cons[local]:
  eval_exprs cx (e::todo) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (eval_exprs cx todo) (\vs. return (v::vs)))
Proof
  simp[Once evaluate_def, FUN_EQ_THM, bind_def] >>
  gen_tac >> BasicProvers.TOP_CASE_TAC >> BasicProvers.TOP_CASE_TAC >> simp[]
QED

Theorem create_word_args_cert_cons[local]:
  ignore_bind (bind source
    (\v. bind (eval_exprs cx todo) (\vs. return (v::vs)))) (return ()) =
  bind source (\v. ignore_bind (eval_exprs cx todo) (return ()))
Proof
  simp[FUN_EQ_THM, bind_def, ignore_bind_def, return_def] >> gen_tac >>
  Cases_on `source x` >> Cases_on `q` >> simp[] >>
  Cases_on `eval_exprs cx todo r` >> Cases_on `q` >> simp[]
QED

Theorem create_word_args_head_scoped[local]:
  expr_sim_scoped (DF,lo,d,C,shC,PG,f,shf) ce cx ty e es /\
  expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx ty e es
    (st0,a,m,ha,hm,op,s,G,tn) /\ body_inv tops C ce cx ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG)
    tops cx st0 a m (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (expr_sim_full_post (DF,lo,d,C,f) ce cx e (es,a,m,s,op,G,tn))
    (\H res ee gt r. (?exc. res = INR exc) /\
       create_word_args_exit C cx H (case res of INL v => INL [v] | INR exc => INR exc) ee gt r)
Proof
  simp[expr_sim_scoped_def] >> strip_tac >> res_tac >>
  `cx_tops cx = tops` by metis_tac[bodyInvCodePropsTheory.body_inv_main_code] >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [scoped_operand_outcome_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >> simp[] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >> simp[] >>
      Cases_on `res` >>
      gvs[create_operand_exit_post_def, create_word_args_exit_def, wb_args_exit_def,
          exprSimDefsTheory.halt_exit_def]) >>
  disj2_tac >> disj2_tac >> simp[] >> metis_tac[]
QED
