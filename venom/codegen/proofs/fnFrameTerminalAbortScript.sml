(* Checked interface probes for abort-frame preparation. *)
Theory fnFrameTerminalAbort
Ancestors
  fnFrameTerminalPrep generatedPrefixSim planSpillBounds mixedPrefixSim
  stackPlanGen stackPlanOps stackPlanTypes stackModel venomInst
  asmFrame asmSem codegenRel frameRel contextCodegenRel genBlockSim
  preparedPrefixSim

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

(* Consume the actual prefix simulation at its allocator boundary.  The
   memory clause already accounts for transient stores, not just live slots. *)
Theorem prepared_local_run_frame_context:
  st.as_stack = top ++ rest /\
  asm_steps lo o2pc prog n (st with as_stack := top) = AsmOK mid /\
  venom_asm_rel lo arranged
    (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
  context_memory_rel cplan vs.vs_memory st.as_memory /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset ==>
  asm_steps lo o2pc prog n st =
    AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
  context_memory_rel cplan vs.vs_memory mid.as_memory
Proof
  strip_tac >> conj_tac
  >- (drule asm_steps_frame >>
      disch_then (qspec_then `rest` mp_tac) >>
      `st with as_stack := top ++ rest = st` by
        simp[asm_state_component_equality] >> simp[]) >>
  irule context_memory_rel_local_prefix >>
  qexistsl [`arranged.ps_alloc`, `st.as_memory`, `r`] >>
  gvs[venom_asm_rel_def]
QED

Theorem selected_prefix_prepared_frame_sim:
  opc <> INVOKE /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spillbase ps /\ residual_budget_wf spillbase [] ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
    operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := st.as_memory)
    (st with as_stack := top) /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp (iops ++ rops)) /\
  st.as_stack = top ++ rest /\
  context_memory_rel cplan vs.vs_memory st.as_memory /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset ==>
  plan_state_residual_wf spillbase selected (LENGTH selected) arranged /\
  arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected /\
  ?mid.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (iops ++ rops))) st =
      AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
    venom_asm_rel lo arranged
      (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
    context_memory_rel cplan vs.vs_memory mid.as_memory /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops))
Proof
  strip_tac >>
  `asm_block_at prog (st with as_stack := top).as_pc
     (execute_plan initial_fmp (iops ++ rops))` by simp[] >>
  drule_all selected_prefix_prepared_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  simp[] >> qexists `st'` >> simp[] >>
  drule_all prepared_local_run_frame_context >> simp[]
QED
