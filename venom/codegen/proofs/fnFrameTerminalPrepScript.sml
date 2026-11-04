(* Shared boundary probes for frame-aware terminal simulation. *)
Theory fnFrameTerminalPrep
Ancestors
  genFrameSim frameRel contextCodegenRelProps contextCodegenRel codegenRel
  instSimHelpers asmFrame

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
