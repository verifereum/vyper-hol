(* The constructor interface discharges all arm implementation premises. *)
Theory bodyIntCallPostProvenanceConditionalJoin
Ancestors
  bodyIntCallPostProvenanceConditionalRoot bodyIntCallPostProvenanceConditionalArm
  bodyIntCallPostProvenanceCallbacks exprSimIfExp exprSimOperators
  exprSimHypsDefs exprSimHyps exprLoweringProps bodyExprPreFacts bodyIntCallArgType exprSimSource
  exprCallbackContracts loweringPosts vyperAST vyperState compileEnv
  exprLowering exprSimDefs loweringStateRelDefs

Theorem intcall_ifexp_outcome:
  !ctx func cenv cx env ty t c a b es sa sb vv s0.
    expr_body_pre cenv cx env (IfExp t c a b) es /\
    ~expr_has_effect (IfExp t c a b) /\
    expr_sim_case T ctx func cenv cx c /\
    (!e env es1 sa sm vv u. (e = a \/ e = b) /\
      expr_body_pre cenv cx env e es1 /\
      compile_expr cenv ty e sa = (vv,sm) /\ fn_has_code sa sm func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      gas_admissible (eval_expr cx e) expr_vv_res_ok es1 /\
      stmt_state_rel ctx func cenv cx es1 u /\ ~u.vs_halted /\
      u.vs_current_bb = sa.cs_current_bb /\ u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es1,u)
        (\res ee t. ?tv. res = INL tv /\
          vv_post ctx func cenv cx e es1 sa sm u ee tv vv t /\
          t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
          intcall_vv_provenance cenv cx (expr_type e) sa sm ee tv vv t)
        (\res ee r. expr_exit res r)) /\
    compile_expr cenv ty (IfExp t c a b) sa = (vv,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx (IfExp t c a b)) (es,s0)
      (\res ee u. ?tv. res = INL tv /\
        vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 ee tv vv u /\
        u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        intcall_vv_provenance cenv cx t sa sb ee tv vv u)
      (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_ifexp >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env a es /\ expr_body_pre cenv cx env b es` by metis_tac[] >>
  `~expr_has_effect c /\ ~expr_has_effect a /\ ~expr_has_effect b`
    by fs[expr_has_effect_thm] >>
  irule intcall_ifexp_outcome_from_arm >> simp[] >>
  conj_tac >- metis_tac[cj 2 compile_expr_grows] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `expr_body_pre _ _ _ (IfExp _ _ _ _) _`
        (mp_then Any mp_tac expr_body_pre_copy_ok) >>
      simp[expr_type_def] >> metis_tac[]) >>
  reverse conj_tac
  >- (conj_tac
      >- (rpt strip_tac >>
          `expr_body_pre cenv cx env e es /\ ~expr_has_effect e` by metis_tac[] >>
          drule ifexp_body_pre_lowered_type_compatible >>
          simp[effect_free_int_calls] >> metis_tac[]) >>
      irule expr_sim_case_apply >> metis_tac[effect_free_int_calls]) >>
  qexistsl_tac [`env`,`ty`] >> simp[] >>
  conj_tac >- metis_tac[cj 2 compile_expr_grows] >>
  conj_tac >- (rpt gen_tac >> strip_tac >> irule intcall_ifexp_arm_outcome >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[expr_body_pre_def] >>
      metis_tac[effect_free_post_value_type]) >>
  suspend "children"
QED
Resume intcall_ifexp_outcome[children]:
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env c (es with gas_obs := gs)` by simp[] >>
  drule_all expr_body_pre_eval >> strip_tac >>
  drule eval_expr_read_INL >> strip_tac >>
  `expr_body_pre cenv cx env a es1 /\ expr_body_pre cenv cx env b es1` by metis_tac[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!e env es1 sa sm vv u. _`
        (qspecl_then [`e`, `env`, `es1`] mp_tac) >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  metis_tac[ifexp_body_pre_read_typed, expr_body_pre_gas_obs]
QED
Finalise intcall_ifexp_outcome
