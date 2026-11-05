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
