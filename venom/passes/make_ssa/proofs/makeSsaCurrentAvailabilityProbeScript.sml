Theory makeSsaCurrentAvailabilityProbe
Ancestors
  makeSsaCurrentWfSsa makeSsaCurrentSimDefs makeSsaCurrentDefs
  venomExecSemantics venomState venomInst venomWf
  phiWellFormed list finite_map

(* A dead original PHI still executes a read after cleanup. *)
Definition current_availability_dead_def:
  current_availability_dead = mk_raw_function "dead"
    [<| bb_label := "E"; bb_instructions :=
        [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
         current_probe_inst 1 JMP [Label "H"] []] |>;
     <| bb_label := "H"; bb_instructions :=
        [current_probe_inst 2 PHI
          [Label "E"; Var "a"; Label "H"; Var "v"] ["v"];
         current_probe_inst 3 JNZ [Lit 0w; Label "H"; Label "X"] []] |>;
     <| bb_label := "X"; bb_instructions :=
        [current_probe_inst 4 STOP [] []] |>]
End

Theorem current_availability_dead_shape:
  MAP (\bb. MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs))
      bb.bb_instructions)
    (FST (make_ssa_current_fn (current_wf_probe_supply current_availability_dead)
      current_availability_dead)).fn_blocks =
  [[(ASSIGN,[Lit 1w],["a"]); (JMP,[Label "H"],[])];
   [(ASSIGN,[Var "formal_var_0"],["v"]);
    (ASSIGN,[Var "a"],["formal_var_0"]);
    (JNZ,[Lit 0w;Label "H";Label "X"],[])];
   [(STOP,[],[])]]
Proof
  EVAL_TAC
QED

Theorem current_availability_external_runtime:
  step_inst 0 C (current_probe_inst 0 ASSIGN [Lit 1w] ["a"])
    (init_venom_state "E") = OK (update_var "a" 1w (init_venom_state "E")) /\
  lookup_var "a" (update_var "a" 1w (init_venom_state "E")) = SOME 1w /\
  step_inst 0 C (current_probe_inst 2 ASSIGN [Var "a"] ["v"])
    (update_var "a" 1w (init_venom_state "E")) =
    OK (update_var "v" 1w (update_var "a" 1w (init_venom_state "E"))) /\
  lookup_var "a" (init_venom_state "E") = NONE
Proof
  EVAL_TAC
QED

(* The retained original PHI is evaluated before the inserted copy. *)
Theorem current_availability_local_runtime:
  eval_phis ((update_var "a" 1w (init_venom_state "D")) with vs_prev_bb := SOME "E")
    [current_probe_inst 10 PHI
      [Label "E"; Var "a"; Label "D"; Var "b"] ["p"]] =
    OK (update_var "p" 1w
      ((update_var "a" 1w (init_venom_state "D")) with vs_prev_bb := SOME "E")) /\
  lookup_var "p" (update_var "p" 1w
    ((update_var "a" 1w (init_venom_state "D")) with vs_prev_bb := SOME "E")) = SOME 1w /\
  step_inst 0 C (current_probe_inst 2 ASSIGN [Var "p"] ["v"])
    (update_var "p" 1w
      ((update_var "a" 1w (init_venom_state "D")) with vs_prev_bb := SOME "E")) =
    OK (update_var "v" 1w (update_var "p" 1w
      ((update_var "a" 1w (init_venom_state "D")) with vs_prev_bb := SOME "E")))
Proof
  EVAL_TAC
QED

(* This full-input candidate is a negative control, not a counterexample:
   its only non-self input is a, so the frozen non-degeneracy check rejects it. *)
Theorem current_availability_dead_rejected:
  ~fn_phis_non_degenerate current_availability_dead
Proof
  simp[fn_phis_non_degenerate_def, current_availability_dead_def,
    mk_raw_function_def, fn_insts_def, current_probe_inst_def, phi_pairs_def] >>
  qexistsl [`current_probe_inst 2 PHI
    [Label "E"; Var "a"; Label "H"; Var "v"] ["v"]`, `"v"`] >>
  simp[current_probe_inst_def, phi_pairs_def] >> EVAL_TAC >> metis_tac[]
QED

(* At the precleanup boundary, a constant PHI from a strict dominator
   becomes a copy without deleting the producer's output. *)
Theorem current_availability_external_cleanup:
  simplify_current_phi_prefix
    [current_probe_inst 10 PHI
       [Label "E"; Var "a"; Label "H"; Var "p"] ["p"];
     current_probe_inst 2 STOP [] []] =
    [current_probe_inst 10 ASSIGN [Var "a"] ["p"];
     current_probe_inst 2 STOP [] []] /\
  simplify_current_phi (current_probe_inst 11 PHI
    [Label "E"; Var "a"; Label "D"; Var "a"] ["q"]) =
    current_probe_inst 11 ASSIGN [Var "a"] ["q"]
Proof
  EVAL_TAC
QED
