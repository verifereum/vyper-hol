Theory makeSsaCurrentCutProbe
Ancestors
  makeSsaCurrentWfSsa venomWf venomInst makeSsaCurrentSimDefs

(* A phi-free diamond: both arms define x, and the join demands x. *)
Definition current_cut_probe_diamond_def:
  current_cut_probe_diamond = mk_raw_function "cut_diamond"
    [<| bb_label := "E"; bb_instructions :=
        [current_probe_inst 0 JNZ [Lit 1w; Label "A"; Label "B"] []] |>;
     <| bb_label := "A"; bb_instructions :=
        [current_probe_inst 1 ASSIGN [Lit 2w] ["x"];
         current_probe_inst 2 JMP [Label "J"] []] |>;
     <| bb_label := "B"; bb_instructions :=
        [current_probe_inst 3 ASSIGN [Lit 3w] ["x"];
         current_probe_inst 4 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
        [current_probe_inst 5 ASSIGN [Var "x"] ["z"];
         current_probe_inst 6 STOP [] []] |>]
End

Theorem current_cut_probe_diamond_structural:
  wf_function current_cut_probe_diamond /\ fn_inst_wf current_cut_probe_diamond /\
  first_block_no_preds current_cut_probe_diamond /\
  first_block_no_phi current_cut_probe_diamond /\
  ir_supply_covers_fn (current_wf_probe_supply current_cut_probe_diamond)
    current_cut_probe_diamond /\
  ir_supply_inst_ok (current_wf_probe_supply current_cut_probe_diamond)
Proof
  EVAL_TAC
QED

Theorem current_cut_probe_diamond_shape:
  MAP (\bb. (bb.bb_label, MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs))
      bb.bb_instructions))
    (FST (make_ssa_current_fn (current_wf_probe_supply current_cut_probe_diamond)
      current_cut_probe_diamond)).fn_blocks =
  [("E",[(JNZ,[Lit 1w; Label "A"; Label "B"],[])]);
   ("A",[(ASSIGN,[Lit 2w],["formal_var_1"]); (JMP,[Label "J"],[])]);
   ("B",[(ASSIGN,[Lit 3w],["formal_var_0"]); (JMP,[Label "J"],[])]);
   ("J",[(PHI,[Label "A"; Var "formal_var_1"; Label "B"; Var "formal_var_0"],["x"]);
         (ASSIGN,[Var "x"],["z"]); (STOP,[],[])])]
Proof
  EVAL_TAC
QED

(* Nondegenerate original PHI with a loop-carried self input. *)
Definition current_cut_probe_loop_def:
  current_cut_probe_loop = mk_raw_function "cut_loop"
    [<| bb_label := "E"; bb_instructions :=
        [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
         current_probe_inst 1 JMP [Label "H"] []] |>;
     <| bb_label := "H"; bb_instructions :=
        [current_probe_inst 2 PHI [Label "E"; Var "a"; Label "D"; Var "v"] ["v"];
         current_probe_inst 3 JNZ [Var "v"; Label "D"; Label "X"] []] |>;
     <| bb_label := "D"; bb_instructions :=
        [current_probe_inst 4 JMP [Label "H"] []] |>;
     <| bb_label := "X"; bb_instructions :=
        [current_probe_inst 5 ASSIGN [Var "v"] ["z"];
         current_probe_inst 6 STOP [] []] |>]
End

Theorem current_cut_probe_loop_structural:
  wf_function current_cut_probe_loop /\ fn_inst_wf current_cut_probe_loop /\
  first_block_no_preds current_cut_probe_loop /\ first_block_no_phi current_cut_probe_loop /\
  ir_supply_covers_fn (current_wf_probe_supply current_cut_probe_loop) current_cut_probe_loop /\
  ir_supply_inst_ok (current_wf_probe_supply current_cut_probe_loop)
Proof
  EVAL_TAC
QED

Theorem current_cut_probe_loop_shape:
  MAP (\bb. (bb.bb_label, MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs))
      bb.bb_instructions))
    (FST (make_ssa_current_fn (current_wf_probe_supply current_cut_probe_loop)
      current_cut_probe_loop)).fn_blocks =
  [("E",[(ASSIGN,[Lit 1w],["a"]); (JMP,[Label "H"],[])]);
   ("H",[(ASSIGN,[Var "formal_var_0"],["v"]);
         (ASSIGN,[Var "a"],["formal_var_0"]);
         (JNZ,[Var "formal_var_0"; Label "D"; Label "X"],[])]);
   ("D",[(JMP,[Label "H"],[])]);
   ("X",[(ASSIGN,[Var "formal_var_0"],["z"]); (STOP,[],[])])]
Proof
  EVAL_TAC
QED

(* This negative control is NOT a counterexample to the frozen contract. *)
Theorem current_cut_probe_loop_rejected:
  ~fn_phis_non_degenerate current_cut_probe_loop
Proof
  simp[fn_phis_non_degenerate_def, current_cut_probe_loop_def,
       mk_raw_function_def, fn_insts_def, current_probe_inst_def, phi_pairs_def] >>
  qexistsl_tac [`current_probe_inst 2 PHI
    [Label "E"; Var "a"; Label "D"; Var "v"] ["v"]`, `"v"`] >>
  simp[current_probe_inst_def, phi_pairs_def] >> EVAL_TAC >> metis_tac[]
QED

(* A local warning, not a certified cut counterexample: an original PHI
   overwrites the inserted token, while cleanup redirects the later use. *)
Theorem current_cut_probe_fork_original_token:
  current_original_scan "v" "H" 0
    [current_probe_inst 2 PHI
      [Label "E"; Var "a"; Label "D"; Var "b"; Label "F"; Var "c"] ["v"]]
    (CurrentInserted "v" "H") = CurrentOriginal "H" 0 0 /\
  (EL 2 (EL 1 (FST (make_ssa_current_fn
    (current_wf_probe_supply current_wf_probe_fork) current_wf_probe_fork)).fn_blocks).
      bb_instructions).inst_operands =
    [Var "formal_var_0"; Label "D"; Label "F"]
Proof
  EVAL_TAC
QED
