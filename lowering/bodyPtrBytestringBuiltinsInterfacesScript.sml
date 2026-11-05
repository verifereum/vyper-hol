(* Initial interface checks for bytestring pointer cases.
   The uint2str allocation is B+n, not B: its interior result must retain
   a whole B-byte capacity. No new semantic definition is needed. *)
Theory bodyPtrBytestringBuiltinsInterfaces
Ancestors
  arithmetic bodyPtrPreds exprSimHypsDefs allocLimits

Theorem enlarged_buffer_offset_bounds:
  !B n k. 0 < B /\ k <= n ==>
    k < B + n /\ k + B <= B + n
Proof
  decide_tac
QED

Theorem uint2str_result_capacity:
  !B n d. 0 < B ==>
    n - d < B + n /\ (n - d) + B <= B + n
Proof
  rpt gen_tac >> disch_tac >> irule enlarged_buffer_offset_bounds >> simp[]
QED

Theorem acc_code_body_pre_impossible:
  !cenv cx env t args es.
    ~expr_body_pre cenv cx env (Builtin t (Acc Code) args) es
Proof
  simp[expr_body_pre_def, alloc_limits_expr_def]
QED

Theorem acc_code_body_ptr_vacuous:
  !cx t args. body_expr_ptr_ok cx (Builtin t (Acc Code) args)
Proof
  simp[body_expr_ptr_ok_def, acc_code_body_pre_impossible]
QED

Theorem body_exprs_ptr_head:
  !cx e es. body_exprs_ptr_ok cx (e::es) ==> body_expr_ptr_ok cx e
Proof
  simp[body_exprs_ptr_ok_def]
QED

Theorem body_exprs_ptr_tail:
  !cx e es.
    body_exprs_ptr_ok cx (e::es) /\
    (?s tv t s1 v t1. eval_expr cx e s = (INL tv,t) /\
                     read_result cx tv s1 = (INL v,t1)) ==>
    body_exprs_ptr_ok cx es
Proof
  simp[body_exprs_ptr_ok_def] >> metis_tac[]
QED
