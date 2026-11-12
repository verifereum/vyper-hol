(* Output variables of a multi-output producer are distinct PHI origins. *)
Theory phiElimNonVacuity
Ancestors
  phiTransform phiOrigins phiDefs dfgDefs venomInst venomWf codegenReadyCompute
  o1PassContract unitShapeDefs finite_map pred_set list

Definition witness_phi_dfg_def:
  witness_phi_dfg = dfg_build_insts
    [mk_inst 0 INVOKE [Label "callee"] ["r"; "s"];
     mk_inst 1 PARAM [Lit 0w] ["x"];
     mk_inst 2 ASSIGN [Var "r"] ["copy"]]
End

Theorem witness_invoke_and_root_keeps_phi:
  phi_single_origin witness_phi_dfg
    (mk_inst 3 PHI [Label "a"; Var "r"; Label "b"; Var "x"] ["p"]) = NONE
Proof
  EVAL_TAC >> simp[]
QED

Theorem witness_distinct_invoke_outputs_keep_phi:
  phi_single_origin witness_phi_dfg
    (mk_inst 3 PHI [Label "a"; Var "r"; Label "b"; Var "s"] ["p"]) = NONE
Proof
  EVAL_TAC >> simp[]
QED

Theorem witness_copy_of_invoke_output_eliminates_phi:
  transform_inst witness_phi_dfg
    (mk_inst 3 PHI [Label "a"; Var "r"; Label "b"; Var "copy"] ["p"]) =
  mk_inst 3 ASSIGN [Var "r"] ["p"]
Proof
  EVAL_TAC >> simp[]
QED

Definition witness_phi_function_def:
  witness_phi_function = mk_raw_function "witness"
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 0 ASSIGN [Lit 7w] ["x"];
           mk_inst 1 JMP [Label "join"] []] |>;
     <| bb_label := "join";
        bb_instructions :=
          [mk_inst 2 PHI [Label "entry"; Var "x"] ["p"];
           mk_inst 3 STOP [] []] |>]
End

Theorem witness_phi_function_satisfies_entry_assumptions:
  wf_function witness_phi_function /\
  fn_inst_wf witness_phi_function /\
  wf_ssa witness_phi_function /\
  fn_pseudos_prefix witness_phi_function /\
  first_block_no_preds witness_phi_function /\
  first_block_no_phi witness_phi_function
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[] >>
  `i = 0 /\ j = 1` by decide_tac >> gvs[is_pseudo_def]
QED

Theorem witness_phi_function_changes:
  transform_function witness_phi_function <> witness_phi_function
Proof
  EVAL_TAC >> simp[is_pseudo_def, is_terminator_def]
QED

(* A multi-origin PHI reached through one sibling must remain visible through
   the next sibling.  Otherwise p would become an unavailable q. *)
Theorem witness_shared_phi_origins_keep_phi:
  phi_single_origin
    (dfg_build_insts
      [mk_inst 0 PARAM [Lit 0w] ["a"];
       mk_inst 1 PARAM [Lit 1w] ["b"];
       mk_inst 2 PARAM [Lit 2w] ["c"];
       mk_inst 3 PHI [Label "r1"; Var "b"; Label "r2"; Var "c"] ["r"];
       mk_inst 4 PHI [Label "q1"; Var "a"; Label "q2"; Var "r"] ["q"]])
    (mk_inst 5 PHI [Label "qjoin"; Var "q"; Label "direct"; Var "r"] ["p"]) = NONE
Proof
  EVAL_TAC >> simp[INSERT_UNION_EQ]
QED

(* Entering a loop through its copy must cut the cycle without a fake root. *)
Theorem witness_copy_cycle_eliminates_phi:
  phi_single_origin
    (dfg_build_insts
      [mk_inst 0 CALLDATALOAD [Lit 0w] ["1"];
       mk_inst 2 PHI [Label "main"; Var "1"; Label "body"; Var "4"] ["3"];
       mk_inst 5 ASSIGN [Var "3"] ["4"]])
    (mk_inst 8 PHI [Label "condition"; Var "3"; Label "body"; Var "4"] ["5"]) = SOME "1"
Proof
  EVAL_TAC >> simp[INSERT_UNION_EQ]
QED
