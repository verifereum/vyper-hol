(* Call branches of the checked selected-prefix evaluator schema. *)
Theory guardSourceCalls
Ancestors
  guardSourceOrdinarySchema guardSourceCallConstructors
  guardSourceCallPrimitives guardSourceIntCall
Libs
  guardSourceSchemaLib

val call_branches = List.filter
  (fn (name,_) => guardSourceSchemaLib.owner name = "calls")
  (guardSourceSchemaLib.manifest finite_prefix_evaluate_ind);

fun discharge_primitive constructor primitive =
  let
    val (variables,body) = strip_forall (#1 (dest_imp (concl constructor)))
    val premise = GENL variables (PART_MATCH I (SPEC_ALL primitive) body)
  in MATCH_MP constructor premise end;

Theorem finite_prefix_call_branches:
  ^(list_mk_conj (map #2 call_branches))
Proof
  conj_tac >-
    MATCH_ACCEPT_TAC (discharge_primitive finite_prefix_Expr_Call_Send eval_send_finite_prefix) >>
  conj_tac >-
    MATCH_ACCEPT_TAC (discharge_primitive finite_prefix_Expr_Call_ExtCall eval_ext_call_finite_prefix) >>
  conj_tac >- MATCH_ACCEPT_TAC finite_prefix_Expr_Call_IntCall >>
  conj_tac >-
    MATCH_ACCEPT_TAC (discharge_primitive finite_prefix_Expr_Call_RawCallTarget eval_raw_call_finite_prefix) >>
  conj_tac >-
    MATCH_ACCEPT_TAC (discharge_primitive finite_prefix_Expr_Call_RawCallCalldataTarget eval_raw_call_finite_prefix) >>
  conj_tac >- MATCH_ACCEPT_TAC finite_prefix_Expr_Call_RawLog >>
  conj_tac >- MATCH_ACCEPT_TAC finite_prefix_Expr_Call_RawRevert >>
  conj_tac >- MATCH_ACCEPT_TAC finite_prefix_Expr_Call_SelfDestructTarget >>
  MATCH_ACCEPT_TAC (discharge_primitive finite_prefix_Expr_Call_CreateTarget eval_create_finite_prefix)
QED
