(* Pointer-only readiness: typed_args_ready remains the owner of source
   typing and admissibility.  The conditional tail matches the body IH. *)
Theory typedWordArgsReadyPtr
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs vyperInterpreter vyperState list

Definition ptr_args_ready_def:
  (ptr_args_ready d ctx PG func cenv cx arg_ty Inv [] = T) /\
  (ptr_args_ready d ctx PG func cenv cx arg_ty Inv (e::args) =
    ((!es. Inv es ==> expr_sim_ptr d ctx PG func cenv cx (arg_ty e) e es) /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv,t) /\
                        read_result cx tv s1 = (INL v,t1)) ==>
      ptr_args_ready d ctx PG func cenv cx arg_ty Inv args)))
End

Theorem ptr_args_ready_head:
  ptr_args_ready d ctx PG func cenv cx arg_ty Inv (e::args) /\ Inv es ==>
  expr_sim_ptr d ctx PG func cenv cx (arg_ty e) e es
Proof
  simp[ptr_args_ready_def]
QED

Theorem ptr_args_ready_tail:
  ptr_args_ready d ctx PG func cenv cx arg_ty Inv (e::args) /\
  (do tv <- eval_expr cx e; read_result cx tv od) es = (INL v,es1) ==>
  ptr_args_ready d ctx PG func cenv cx arg_ty Inv args
Proof
  simp[ptr_args_ready_def, vyperStateTheory.bind_def] >>
  strip_tac >> first_x_assum irule >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem body_exprs_ptr_ok_ready:
  !args.
  body_exprs_ptr_ok cx args /\ body_inv tops ctx cenv cx /\
  (!e es. MEM e args /\ Inv es ==> expr_body_pre cenv cx env e es) ==>
  ptr_args_ready d ctx PG func cenv cx arg_ty Inv args
Proof
  Induct >> simp[body_exprs_ptr_ok_def, ptr_args_ready_def] >>
  rpt strip_tac
  >- (fs[body_expr_ptr_ok_def] >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED
