(* Checked interface probes for abort-frame preparation. *)
Theory fnFrameTerminalAbort
Ancestors
  fnFrameTerminalPrep generatedPrefixSim planSpillBounds mixedPrefixSim
  stackPlanGen stackPlanOps stackPlanTypes stackModel venomInst

(* A transient spill is covered by the output high-water mark even though
   the live spill map is empty again after restoration. *)
Theorem abort_escape_output_allocator_probe:
  !lv dfg cfg fn ih nt lbl.
  (SND (THE (generate_inst_plan lv dfg cfg fn
    (mk_inst 0 REVERT [Var "size"; Lit 32w] [])
    ["size"] ih nt lbl terminal_escape_ps))).ps_alloc.sa_next_offset = 32 /\
  (apply_prefix_ops 0 FEMPTY
    [SOPush (Lit 32w); SOSpill 0; SODup 16; SORestore 0; SOSwap 1]
    terminal_escape_ps).ps_alloc.sa_next_offset = 32
Proof
  rpt gen_tac >> EVAL_TAC >> simp[]
QED

Theorem abort_assert_prefix_probe:
  !lv dfg cfg fn ih nt lbl.
  OPTION_MAP FST (generate_inst_plan lv dfg cfg fn
    (mk_inst 0 ASSERT [Lit 0w] []) [] ih nt lbl (init_plan_state 0)) =
  SOME [SOPush (Lit 0w); SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"]
Proof
  rpt gen_tac >> EVAL_TAC >> simp[]
QED

Theorem abort_assert_unreachable_prefix_probe:
  !lv dfg cfg fn ih nt lbl.
  ?endlabel.
  OPTION_MAP FST (generate_inst_plan lv dfg cfg fn
    (mk_inst 0 ASSERT_UNREACHABLE [Lit 0w] []) [] ih nt lbl
    (init_plan_state 0)) =
  SOME [SOPush (Lit 0w); SOPushLabel endlabel; SOEmit "JUMPI";
        SOEmit "INVALID"; SOLabel endlabel]
Proof
  rpt gen_tac >> qexists `"reachable_1"` >> EVAL_TAC >> simp[]
QED
