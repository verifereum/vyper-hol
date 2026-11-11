(* Memory case of the body induction (bodyMemory's body_mem_mutual): a
   ternary, as bodySimExprCases' body_ifexp_case splits it.  An arm that is
   a widened internal call is bodyMemIfExpWidened's; otherwise the value
   judgment is bodyIfExpMemory's compile_ifexp_vv_sim_mem, and the forced
   one its compile_ifexp_word_sim_mem for word types and
   exprSimMemUnwrap's expr_sim_mem_of_vv_sim_mem for the rest. *)
Theory bodyMemIfExp
Ancestors
  bodyMemIfExpWidened bodyIfExpMemory exprSimMemUnwrap
  bodyMemoryPreds exprSimOperators exprSimIfExp exprSimSource exprSimHyps
  exprSimHypsDefs

Theorem body_ifexp_mem_ok:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_mem_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_mem_ok cx e3) /\
    body_expr_mem_ok cx e1 ==>
    body_expr_mem_ok cx (IfExp v5 e1 e2 e3)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `?e. (e = e2 \/ e = e3) /\ int_calls_expr e <> [] /\
             ~same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)`
  >- (qspecl_then [`cx`, `v5`, `e1`, `e2`, `e3`] mp_tac
        body_ifexp_widened_call_arm_mem >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then irule >> metis_tac[]) >>
  drule expr_body_pre_ifexp >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `expr_sim_mem ctx func cenv cx (BaseT BoolT) e1 es` by
    metis_tac[body_expr_mem_ok_def] >>
  `!gs tv es1.
     (do result <- eval_expr cx e1; read_result cx result od)
       (es with gas_obs := gs) = (INL tv, es1) ==>
     expr_body_pre cenv cx env e2 es1 /\ expr_body_pre cenv cx env e3 es1 /\
     body_expr_mem_ok cx e2 /\ body_expr_mem_ok cx e3` by
    (rpt gen_tac >> strip_tac >>
     `expr_body_pre cenv cx env e1 (es with gas_obs := gs)` by simp[] >>
     drule_all expr_body_pre_eval >> strip_tac >>
     drule eval_expr_read_INL >> strip_tac >> metis_tac[]) >>
  `!gs tv es1.
     (do result <- eval_expr cx e1; read_result cx result od)
       (es with gas_obs := gs) = (INL tv, es1) ==>
     expr_sim_mem ctx func cenv cx ty e2 es1 /\
     expr_sim_mem ctx func cenv cx ty e3 es1 /\
     expr_vv_sim_mem ctx func cenv cx ty e2 es1 /\
     expr_vv_sim_mem ctx func cenv cx ty e3 es1` by
    (rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
     metis_tac[body_expr_mem_ok_def]) >>
  `!sa sb op. lower_value compile_expr cenv (BaseT BoolT) e1 sa = (op, sb) ==>
     cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
     sa.cs_next_id <= sb.cs_next_id` by
    metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
  `!e sa sb op. (e = e2 \/ e = e3) /\
     lower_value compile_expr cenv ty e sa = (op, sb) ==>
     cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
     sa.cs_next_id <= sb.cs_next_id` by
    metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
  `!tvt. evaluate_type (get_tenv cx) v5 = SOME tvt /\ ~is_word_type v5 ==>
     type_memory_bytes cenv v5 = type_memory_size tvt /\
     type_memory_size tvt < 2 ** 64` by
    (rpt gen_tac >> strip_tac >>
     qspecl_then [`cenv`, `cx`, `env`, `IfExp v5 e1 e2 e3`]
       mp_tac expr_body_pre_copy_ok >>
     simp[vyperASTTheory.expr_type_def] >>
     disch_then (qspec_then `es` mp_tac) >> simp[]) >>
  `~is_word_type v5 ==>
   !e. (e = e2 \/ e = e3) ==>
       lowered_value_type cenv e = expr_type e \/
       is_bytestring_type (expr_type e) /\
       is_bytestring_type (lowered_value_type cenv e) /\
       arg_type_fits (lowered_value_type cenv e) (expr_type e) \/
       same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)` by
    (rpt strip_tac >> metis_tac[ifexp_body_pre_lowered_type_compatible]) >>
  `!gs tv es1.
     (do result <- eval_expr cx e1; read_result cx result od)
       (es with gas_obs := gs) = (INL tv, es1) ==>
     expr_sim_mem ctx func cenv cx ty e2 es1 /\
     expr_sim_mem ctx func cenv cx ty e3 es1 /\
     expr_vv_sim_mem ctx func cenv cx ty e2 es1 /\
     expr_vv_sim_mem ctx func cenv cx ty e3 es1 /\
     !e gs' v es2. ~is_word_type v5 /\ (e = e2 \/ e = e3) /\
       (do r <- eval_expr cx e; read_result cx r od)
         (es1 with gas_obs := gs') = (INL v, es2) ==>
       ?tvt. evaluate_type (get_tenv cx) v5 = SOME tvt /\ value_has_type tvt v` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!gs tv es1. _ ==> expr_body_pre _ _ _ _ _ /\ _` drule >>
     strip_tac >> rpt conj_tac
     >- metis_tac[body_expr_mem_ok_def]
     >- metis_tac[body_expr_mem_ok_def]
     >- metis_tac[body_expr_mem_ok_def]
     >- metis_tac[body_expr_mem_ok_def] >>
     rpt gen_tac >> strip_tac >>
     `expr_body_pre cenv cx env e (es1 with gas_obs := gs')` by gvs[] >>
     `v5 = expr_type e` by gvs[] >> pop_assum SUBST1_TAC >>
     irule ifexp_body_pre_read_typed >> metis_tac[]) >>
  `expr_vv_sim_mem ctx func cenv cx ty (IfExp v5 e1 e2 e3) es` by
    (`is_word_type v5 ==> ?tvt. evaluate_type (get_tenv cx) v5 = SOME tvt` by
       (qpat_assum `expr_body_pre _ _ _ (IfExp _ _ _ _) _`
          (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
        simp[optionTheory.IS_SOME_EXISTS, vyperASTTheory.expr_type_def]) >>
     irule compile_ifexp_vv_sim_mem >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[] >> Cases_on `is_word_type v5`
  >- (irule compile_ifexp_word_sim_mem >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule expr_sim_mem_of_vv_sim_mem >> simp[vyperASTTheory.expr_type_def] >>
  rpt strip_tac >> drule compile_expr_ifexp >> strip_tac >> gvs[]
QED
