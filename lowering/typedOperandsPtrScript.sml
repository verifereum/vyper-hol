Theory typedOperandsPtr
Ancestors
  wordOperandsPtr bodyPtrPreds exprSimPrecompiles gasSummaryComposePtr vyperState list

(* A recursive readiness interface is needed because facts about later
   operands are available only when the preceding operand can evaluate.
   This mirrors typed_args_ready, without assuming ghost-state existence. *)
Definition typed_args_ready_ptr_def:
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv [] = T /\
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv (e::args) =
    ((!es. Inv es ==>
       expr_sim_ptr d ctx PG func cenv cx (arg_ty e) e es /\
       is_word_type (expr_type e) /\
       IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
       (!res es'. (do r <- eval_expr cx e; read_result cx r od) es = (res, es') ==> expr_res_ok res) /\
       (!v es'. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
         Inv es')) /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv args))
End

Theorem typed_args_ready_ptr_head:
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv (e::args) /\ Inv es ==>
    expr_sim_ptr d ctx PG func cenv cx (arg_ty e) e es /\
    is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
    (!res es'. (do r <- eval_expr cx e; read_result cx r od) es = (res, es') ==> expr_res_ok res) /\
    (!v es'. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==> Inv es')
Proof
  simp[typed_args_ready_ptr_def] >> metis_tac[]
QED

Theorem typed_args_ready_ptr_tail:
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv (e::args) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) ==>
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv args
Proof
  simp[typed_args_ready_ptr_def, bind_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem body_exprs_typed_args_ready_ptr:
  body_exprs_ptr_ok cx args /\
  typed_args_ready ctx func cenv cx arg_ty Inv args /\
  body_inv tops ctx cenv cx /\
  (!e es. MEM e args /\ Inv es ==> expr_body_pre cenv cx env e es) ==>
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv args
Proof
  Induct_on `args`
  >- simp[typed_args_ready_ptr_def] >>
  simp_tac pure_ss [typed_args_ready_ptr_def, typed_args_ready_def,
    body_exprs_ptr_ok_def, MEM] >> gen_tac >> strip_tac >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      fs[body_expr_ptr_ok_def] >> metis_tac[]) >>
  strip_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem typed_args_post_cons_ptr:
  expr_post ctx func cenv cx e es sa s1 s0 es1 v x t /\
  typed_args_post ctx func cenv cx es1 s1 t es' args xs vs u /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 s1 G1 tn1 t G2 tn2 /\
  op_taint tn1 x = {} /\ EVERY (\z. op_taint tn2 z = {}) xs ==>
  typed_args_post ctx func cenv cx es sa s0 es' (e::args) (x::xs) (v::vs) u /\
  EVERY (\z. op_taint tn2 z = {}) (x::xs) /\
  ghost_kept cenv es sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >> conj_tac
  >- (irule typed_args_post_cons >> metis_tac[]) >>
  conj_tac
  >- (Cases_on `x` >> gvs[ptrDisciplineTheory.op_taint_def,
        bodyPtrDefsTheory.ghost_kept_def] >> metis_tac[]) >>
  irule ghost_kept_trans >>
  drule exprSimWordArgsTheory.expr_post_frame >> strip_tac >>
  fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def] >>
  metis_tac[]
QED

Theorem lower_typed_args_nil_sim_ptr:
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  ghost_inv d cenv cx es G0 tn0 s0 /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx, func) PG
    (eval_exprs cx []) (es, s0, G0, tn0)
    (\rr ee G tn t. ?vs. rr = INL vs /\
       typed_args_post ctx func cenv cx es sa s0 ee [] [] vs t /\
       t.vs_current_bb = sa.cs_current_bb /\
       t.vs_inst_idx = LENGTH sa.cs_current_insts /\
       ghost_inv d cenv cx ee G tn t /\
       EVERY (\x. op_taint tn x = {}) [] /\
       ghost_kept cenv es sa G0 tn0 s0 G tn)
    (\rr ee gt r. wb_args_exit rr r)
Proof
  strip_tac >>
  simp[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj1_tac >>
  simp[fragGasPathPtrTheory.gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL []`, `es`, `G0`, `tn0`, `OK s0`] >>
  simp[exprSimWordArgsTheory.eval_exprs_nil, return_def,
       gasSummaryTheory.gas_explicit_def,
       fragGasPathPtrTheory.gas_path_ptr_rules,
       typed_args_post_def, loweringPostsTheory.wb_frame_def,
       bodyPtrDefsTheory.ghost_kept_def, stmtFragPtrTheory.ghost_inv_gas_obs] >>
  fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_gas_obs]
QED

Theorem typed_args_ready_ptr_admissible:
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!ee gs. Inv ee ==> Inv (ee with gas_obs := gs)) ==>
  gas_admissible (do r <- eval_expr cx e; read_result cx r od) expr_res_ok es
Proof
  simp[gasContextTheory.gas_admissible_def, typed_args_ready_ptr_def] >>
  metis_tac[]
QED

Theorem typed_args_ready_ptr_marked_facts:
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!ee gs. Inv ee ==> Inv (ee with gas_obs := gs)) /\
  gas_marked_exec F (ctx,func)
    (do r <- eval_expr cx e; read_result cx r od) (es,s0) marks (INL v) mid r ==>
  Inv (mid with gas_obs := []) /\
  typed_args_ready_ptr d ctx PG func cenv cx arg_ty Inv args /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >>
  `(do r <- eval_expr cx e; read_result cx r od)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, mid with gas_obs := [])` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[combinTheory.o_DEF]) >>
  `Inv (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[] >>
  drule_all typed_args_ready_ptr_head >> strip_tac >>
  drule typed_args_ready_ptr_tail >>
  drule exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom >>
  simp[] >> metis_tac[]
QED
