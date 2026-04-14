open HolKernel boolLib bossLib Parse;
open vyperTypeSoundnessDefsTheory;
open vyperInterpreterTheory vyperStateTheory vyperContextTheory;
open vyperASTTheory vyperValueTheory vyperMiscTheory;
open finite_mapTheory listTheory;

val _ = new_theory "vyperTypeErrorCounterexample";

(* Counterexample: well-typed program produces TypeError *)
(* A HashMap variable accessed via TopLevelName, then materialised in Return(SOME e) *)

Definition ce2_hm_id_def:
  ce2_hm_id = "hm"
End

Definition ce2_module_def:
  ce2_module : toplevel list = [
    HashMapDecl Public F ce2_hm_id (BaseT (UintT 256)) (Type (BaseT (UintT 256))) (SOME 0)
  ]
End

Definition ce2_txn_def:
  ce2_txn = <| sender := 0w; target := 0w; function_name := "";
               args := []; value := 0; time_stamp := 0;
               block_number := 0; block_hashes := []; blob_hashes := [];
               blob_base_fee := 0; gas_price := 0; chain_id := 0;
               is_creation := F; coinbase := 0w; gas_limit := 0;
               base_fee := 0; prev_randao := 0; origin := 0w |>
End

Definition ce2_cx_def:
  ce2_cx = <| stk := []; txn := ce2_txn;
              sources := [(0w, [(NONE, ce2_module)])];
              layouts := [(0w, ([((NONE, ce2_hm_id), 0)], []))];
              in_deploy := F; nonreentrant_slot := NONE |>
End

Definition ce2_acct_def:
  ce2_acct = <| nonce := 0; balance := 0; storage := K 0w; code := [] |>
End

Definition ce2_st_def:
  ce2_st = <| immutables := []; logs := []; scopes := [FEMPTY];
              accounts := K ce2_acct; tStorage := K (K 0w) |>
End

Definition ce2_env_def:
  ce2_env = <| var_types := FEMPTY; global_types := FEMPTY;
               toplevel_types := FUPDATE FEMPTY ((NONE, string_to_num ce2_hm_id), NoneT);
               type_defs := FEMPTY; fn_sigs := FEMPTY;
               flag_members := FEMPTY |>
End

Definition ce2_expr_def:
  ce2_expr = TopLevelName NoneT (NONE, ce2_hm_id)
End

Definition ce2_stmt_def:
  ce2_stmt = Return (SOME ce2_expr)
End

(* The expression is well-typed *)
Theorem ce2_expr_well_typed:
  well_typed_expr ce2_env ce2_expr
Proof
  simp[well_typed_expr_def, well_formed_type_def, evaluate_type_def, ce2_env_def, ce2_expr_def, FLOOKUP_UPDATE]
QED

(* The statement is well-typed with ret_ty = NoneT *)
Theorem ce2_stmt_well_typed:
  well_typed_stmt ce2_env NoneT ce2_stmt
Proof
  simp[well_typed_stmt_def, ce2_stmt_def, expr_type_def, ce2_expr_def, SRULE [ce2_expr_def] ce2_expr_well_typed]
QED

(* env_consistent holds *)
Theorem ce2_env_consistent:
  env_consistent ce2_env ce2_cx ce2_st
Proof
  simp[env_consistent_def, fn_sigs_consistent_def, ce2_env_def, ce2_cx_def, ce2_st_def, FLOOKUP_DEF, FDOM_FEMPTY, get_tenv_def, get_module_code_def, type_env_all_modules_def, type_env_def, find_var_decl_by_num_def, FLOOKUP_UPDATE, FUPDATE_LIST, ce2_module_def, ce2_txn_def]
QED

(* state_well_typed holds *)
Theorem ce2_state_well_typed:
  state_well_typed ce2_st
Proof
  simp[state_well_typed_def, ce2_st_def, scope_well_typed_def, FLOOKUP_EMPTY]
QED

(* functions_well_typed holds (no functions) *)
Theorem ce2_functions_well_typed:
  functions_well_typed ce2_cx
Proof
  simp[functions_well_typed_def] >> rpt strip_tac >> gvs[ce2_cx_def, ce2_module_def, get_module_code_def, lookup_callable_function_def, lookup_function_def, AllCaseEqs()]
QED

(* context_well_typed holds *)
Theorem ce2_context_well_typed:
  context_well_typed ce2_cx
Proof
  simp[context_well_typed_def, ce2_cx_def, ce2_txn_def]
QED

(* eval_stmt produces TypeError *)
Theorem ce2_eval_produces_type_error:
  ?s st'. eval_stmt ce2_cx ce2_stmt ce2_st = (INR (Error (TypeError s)), st')
Proof
  EVAL_TAC >> simp[]
QED

(* Therefore the no-TypeError conjunct of P0 is false *)
Theorem type_error_counterexample:
  ~(!cx s. !env ret_ty st res st'.
    well_typed_stmt env ret_ty s /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    context_well_typed cx /\
    eval_stmt cx s st = (res, st') ==>
    (!s. res <> INR (Error (TypeError s))))
Proof
  simp[] >> map_every qexists [`ce2_cx`, `ce2_stmt`, `ce2_env`, `NoneT`, `ce2_st`] >> rpt strip_tac >> strip_assume_tac ce2_eval_produces_type_error >> gvs[ce2_stmt_well_typed, ce2_env_consistent, ce2_state_well_typed, ce2_functions_well_typed, ce2_context_well_typed] >> metis_tac[]
QED

val _ = export_theory();
