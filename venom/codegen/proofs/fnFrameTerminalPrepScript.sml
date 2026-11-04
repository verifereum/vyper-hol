(* Shared boundary probes for frame-aware terminal simulation. *)
Theory fnFrameTerminalPrep
Ancestors
  genFrameSim frameRel contextCodegenRelProps contextCodegenRel codegenRel
  instSimHelpers asmFrame stackPlanTypes stackPlanGen venomInst genBlockSim
  mixedPrefixSim stackModel

Theorem fn_frame_inv_local_state:
  !ctx cplan lo fn ra rest mem0 ps vs st.
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st ==>
  ?top. st.as_stack = top ++ rest /\
    venom_asm_rel lo ps
      (frame_view fn ra vs with vs_memory := st.as_memory)
      (st with as_stack := top)
Proof
  rpt gen_tac >>
  `!op. operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
        operand_val (frame_view fn ra vs) lo op` by
    (Cases >> simp[operand_val_def]) >>
  simp[fn_frame_inv_def] >> strip_tac >> qexists `top` >>
  gvs[context_venom_asm_rel_def, venom_asm_rel_def,
      plan_stack_rel_def, plan_spill_rel_def, operand_val_def,
      memory_rel_refl]
QED

(* A local prefix's masked memory agreement composes with the ambient
   relation; no ordering of the source read range relative to spills is used. *)
Theorem context_memory_rel_local_prefix:
  !r cplan alloc vm am am'.
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= alloc.sa_spill_base /\
  alloc.sa_next_offset <= r.sr_spill_end /\
  context_memory_rel cplan vm am /\ memory_rel alloc am am' ==>
  context_memory_rel cplan vm am'
Proof
  simp[context_memory_rel_def, memory_rel_def] >> rpt strip_tac >>
  `~(alloc.sa_spill_base <= i /\ i < alloc.sa_next_offset)` by
    (strip_tac >> qpat_x_assum `~context_spill_byte cplan i` mp_tac >>
     simp[context_spill_byte_def] >> qexists `r` >> simp[]) >>
  metis_tac[]
QED

(* Initial depth 15 becomes 16 after the first literal input. *)
Definition terminal_escape_ps_def:
  terminal_escape_ps = (init_plan_state 0) with
    ps_stack := Var "size" :: MAP (\n. Var (REPLICATE n #"x")) (COUNT_LIST 15)
End

Theorem terminal_escape_input_plan:
  FST (emit_input_plan RETURN [Lit 32w; Var "size"] ["size"] terminal_escape_ps) =
  [SOPush (Lit 32w); SOSpill 0; SODup 16; SORestore 0; SOSwap 1]
Proof
  EVAL_TAC
QED

Definition terminal_escape_inst_def:
  terminal_escape_inst = mk_inst 0 RETURN [Var "size"; Lit 32w] []
End

Theorem terminal_escape_generated_ops:
  !lv dfg cfg fn ih nt lbl.
  OPTION_MAP FST (generate_inst_plan lv dfg cfg fn terminal_escape_inst
    ["size"] ih nt lbl terminal_escape_ps) =
  SOME [SOPush (Lit 32w); SOSpill 0; SODup 16; SORestore 0; SOSwap 1;
        SOEmit "RETURN"]
Proof
  rpt gen_tac >> EVAL_TAC
QED

Theorem terminal_escape_initial_wf:
  generated_plan_state_wf 0 terminal_escape_ps /\
  stack_get_depth (Var "size") terminal_escape_ps.ps_stack = SOME 15 /\
  LENGTH (compute_operands terminal_escape_inst) = 2 /\
  LENGTH (SND (emit_input_plan RETURN (compute_operands terminal_escape_inst)
    ["size"] terminal_escape_ps)).ps_stack = 18
Proof
  EVAL_TAC >> simp[]
QED

Theorem terminal_escape_prefix_spill_wf:
  prefix_spill_wf 0 FEMPTY
    [SOPush (Lit 32w); SOSpill 0; SODup 16; SORestore 0; SOSwap 1]
    terminal_escape_ps
Proof
  EVAL_TAC >> simp[] >> qexists `Lit 32w` >> simp[]
QED
