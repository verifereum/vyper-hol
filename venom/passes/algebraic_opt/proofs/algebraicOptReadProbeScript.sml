Theory algebraicOptReadProbe
Ancestors
  algebraicOptChainProofs algebraicOptFreshnessProofs algebraicOptSimulationProps
  venomState dfgAnalysisProps
Libs
  listTheory finite_mapTheory

(* A counterexample to the proposed original-all-truthy relation's
   read-closure implication, NOT to the pass or its frozen theorem.
   The target snapshot is intentionally not claimed to be reachable. *)
Definition ao_read_probe_fn_def:
  ao_read_probe_fn = ao_chain_probe
    [mk_inst 4 ISZERO [Var "c"] ["d"];
     mk_inst 5 MSTORE [Lit 0w; Var "d"] [];
     mk_inst 6 STOP [] []]
End

Definition ao_read_probe_source_def:
  ao_read_probe_source =
    update_var "d" 1w (update_var "c" 0w (update_var "b" 1w
      (update_var "a" 0w (update_var "x" 6w (init_venom_state "entry")))))
End

Definition ao_read_probe_target_def:
  ao_read_probe_target = update_var "b" 2w ao_read_probe_source
End

Theorem ao_read_probe_truthy_classification:
  ao_all_truthy (dfg_build_function ao_read_probe_fn)
    (mk_inst 2 ISZERO [Var "a"] ["b"]) /\
  ao_resolve_iszero_op (ao_compute_fn_iszero_targets ao_read_probe_fn)
    MSTORE (Var "d") = Var "b" /\
  ao_word_chain [6w;0w;1w;0w;1w]
Proof
  EVAL_TAC >> rpt strip_tac >>
  `j = 0 \/ j = 1 \/ j = 2 \/ j = 3` by decide_tac >>
  gvs[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem ao_read_probe_candidate_observations:
  !v. (lookup_var v ao_read_probe_source = NONE <=>
       lookup_var v ao_read_probe_target = NONE) /\
      (lookup_var v ao_read_probe_source = SOME 0w <=>
       lookup_var v ao_read_probe_target = SOME 0w) /\
      (v <> "b" ==> lookup_var v ao_read_probe_source =
                    lookup_var v ao_read_probe_target)
Proof
  gen_tac >> Cases_on `v = "b"` >>
  simp[ao_read_probe_source_def, ao_read_probe_target_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem ao_read_probe_exposed_exact_read_differs:
  eval_operand
    (ao_resolve_iszero_op (ao_compute_fn_iszero_targets ao_read_probe_fn)
      MSTORE (Var "d")) ao_read_probe_source = SOME 1w /\
  eval_operand
    (ao_resolve_iszero_op (ao_compute_fn_iszero_targets ao_read_probe_fn)
      MSTORE (Var "d")) ao_read_probe_target = SOME 2w
Proof
  EVAL_TAC
QED

Theorem ao_read_probe_same_frame:
  state_frame ao_read_probe_source = state_frame ao_read_probe_target
Proof
  simp[ao_read_probe_target_def, update_var_def]
QED

(* Label roots are not unconditionally successful: source success must
   supply their label-table lookup, both ordinarily and before a PHI batch. *)
Theorem ao_root_eval_cases:
  eval_operand (Lit w) s = SOME w /\
  (eval_operand (Label lbl) s = SOME w <=> FLOOKUP s.vs_labels lbl = SOME w) /\
  (eval_operand (Label lbl) s = NONE <=> FLOOKUP s.vs_labels lbl = NONE)
Proof
  simp[eval_operand_def]
QED

Theorem ao_read_probe_source_chain_evaluates:
  MAP (\op. eval_operand op ao_read_probe_source)
    [Var "x"; Var "a"; Var "b"; Var "c"; Var "d"] =
  MAP SOME [6w;0w;1w;0w;1w] /\
  ao_all_truthy (dfg_build_function ao_read_probe_fn)
    (mk_inst 0 OR [Lit 2w; Lit 4w] ["x"])
Proof
  EVAL_TAC
QED
