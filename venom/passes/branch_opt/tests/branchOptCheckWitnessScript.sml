(* The branch_opt checker on a function where the pass makes both of its
   rewrites: the soundness theorem applies to the pass's actual output,
   from the initial state, with no premise left over. *)
Theory branchOptCheckWitness
Ancestors
  branchOptDefs branchOptCheck branchOptCheckProofs venomInst venomState

(* entry: jnz on c = iszero x  (rewrite 1: jnz x, labels swapped)
   then:  jnz on y = eq x 5    (rewrite 2: insert t = iszero y, swap) *)
Definition bo_witness_fn_def:
  bo_witness_fn = mk_raw_function "bo_witness"
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 1 CALLDATALOAD [Lit 0w] ["x"];
           mk_inst 2 ISZERO [Var "x"] ["c"];
           mk_inst 3 JNZ [Var "c"; Label "then"; Label "else"] []] |>;
     <| bb_label := "then";
        bb_instructions :=
          [mk_inst 4 EQ [Var "x"; Lit 5w] ["y"];
           mk_inst 5 JNZ [Var "y"; Label "a"; Label "b"] []] |>;
     <| bb_label := "else"; bb_instructions := [mk_inst 6 STOP [] []] |>;
     <| bb_label := "a"; bb_instructions := [mk_inst 7 STOP [] []] |>;
     <| bb_label := "b"; bb_instructions := [mk_inst 8 STOP [] []] |>]
End

Definition bo_witness_supply_def:
  bo_witness_supply = <|
    irs_next_inst := 9; irs_next_var := 0; irs_next_label := 0;
    irs_used_inst_ids := [1; 2; 3; 4; 5; 6; 7; 8];
    irs_used_vars := fn_ir_vars bo_witness_fn;
    irs_used_labels := ["entry"; "then"; "else"; "a"; "b"] |>
End

(* Both rewrites fire: the pass's output is not its input. *)
Theorem bo_witness_rewrites:
  MAP (\bb. bb.bb_instructions) (branch_opt_function (K 0) bo_witness_fn).fn_blocks =
  [[mk_inst 1 CALLDATALOAD [Lit 0w] ["x"];
    mk_inst 2 ISZERO [Var "x"] ["c"];
    mk_inst 3 JNZ [Var "x"; Label "else"; Label "then"] []];
   [mk_inst 4 EQ [Var "x"; Lit 5w] ["y"];
    mk_inst 5 ISZERO [Var "y"] ["bo_tmp_5"];
    mk_inst 5 JNZ [Var "bo_tmp_5"; Label "b"; Label "a"] []];
   [mk_inst 6 STOP [] []];
   [mk_inst 7 STOP [] []];
   [mk_inst 8 STOP [] []]]
Proof
  EVAL_TAC
QED

Theorem bo_witness_check:
  check_branch_opt_fn bo_witness_fn (branch_opt_function (K 0) bo_witness_fn)
Proof
  EVAL_TAC
QED

Theorem bo_witness_supply_check:
  check_branch_opt_fn bo_witness_fn
    (FST (branch_opt_function_supply (K 0) bo_witness_supply bo_witness_fn)) /\
  (FST (branch_opt_function_supply (K 0) bo_witness_supply bo_witness_fn))
    .fn_blocks <> bo_witness_fn.fn_blocks
Proof
  EVAL_TAC
QED

Theorem bo_witness_init_vars:
  (init_venom_state "entry").vs_vars = FEMPTY
Proof
  EVAL_TAC
QED

(* The soundness theorem, discharged for the pass's output and started from
   the initial state with no variables. *)
Theorem bo_witness_sound =
  MATCH_MP check_branch_opt_fn_run_function bo_witness_check
  |> Q.SPEC `init_venom_state "entry"` |> GEN_ALL;
