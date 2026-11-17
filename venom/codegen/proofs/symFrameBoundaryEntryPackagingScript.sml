(* Entry and cleanup frame packaging.  Numerical and concrete suppliers
 * provide pointwise runs at the same count; no boundary algorithm is
 * replayed here.  In particular the label offsets need not be canonical. *)
Theory symFrameBoundaryEntryPackaging
Ancestors
  symFrameBoundaryPairing fnPlanPrefix fnFrameBoundary
  codegenSymRel stackPlanGen stackPlanTypes planExec asmSem asmSymSem
  frameRel contextCodegenRel venomState venomInst list finite_map

Theorem sym_clean_stack_plan_frame_of_runs_own:
  !allow_own own ctx cp lo o2pc prog fn base ps vs as clean_ops ps2
   ra rest mem0 env ret srest labs0 ss as2 ss2.
    code_labels_agree prog lo /\
    o2pc = build_offset_to_pc prog /\ asm_static_wf prog /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps as ss /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp clean_ops)) as = AsmOK as2 /\
    as2.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp clean_ops) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps2 vs as2 /\
    generated_plan_state_wf_marked base ps2 /\
    (!op. MEM op ps2.ps_stack \/ op IN FDOM ps2.ps_spilled ==>
      op = dead_stack_marker \/ MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    sym_steps prog env (LENGTH (execute_plan cp.cp_initial_fmp clean_ops)) ss = SymOK ss2 /\
    sym_kinds_ok cp fn ret srest ps2 ss2 /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
      FLOOKUP ss2.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp clean_ops)) as = AsmOK as2 /\
    as2.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp clean_ops) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps2 vs as2 /\
    generated_plan_state_wf_marked base ps2 /\
    (!op. MEM op ps2.ps_stack \/ op IN FDOM ps2.ps_spilled ==>
      op = dead_stack_marker \/ MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cp.cp_initial_fmp clean_ops)) ss = SymOK ss2 /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps2 as2 ss2
Proof
  rpt gen_tac >> strip_tac >>
  drule_all sym_frame_inv_same_count_own >> strip_tac >>
  simp[sym_steps_mode_ok] >> first_assum ACCEPT_TAC
QED

Theorem sym_entry_prefix_frame_of_runs_own:
  !allow_own own ctx cp lo o2pc prog fn param_ops installed ps1
   a vp ra rest env ret srest ss a' ss'.
    code_labels_agree prog lo /\
    o2pc = build_offset_to_pc prog /\ asm_static_wf prog /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest ss.sym_mem_labels installed a ss /\
    asm_steps lo o2pc prog
      (LENGTH (execute_plan cp.cp_initial_fmp
        (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))) a = AsmOK a' /\
    a'.as_pc = a.as_pc + LENGTH (execute_plan cp.cp_initial_fmp
      (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
    fn_frame_inv ctx cp lo fn ra rest a.as_memory ps1 vp a' /\
    sym_steps prog env
      (LENGTH (execute_plan cp.cp_initial_fmp
        (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))) ss = SymOK ss' /\
    sym_kinds_ok cp fn ret srest ps1 ss' /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
    asm_steps lo o2pc prog
      (LENGTH (execute_plan cp.cp_initial_fmp
        (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))) a = AsmOK a' /\
    a'.as_pc = a.as_pc + LENGTH (execute_plan cp.cp_initial_fmp
      (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
    fn_frame_inv ctx cp lo fn ra rest a.as_memory ps1 vp a' /\
    sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cp.cp_initial_fmp
        (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))) ss = SymOK ss' /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest ss.sym_mem_labels ps1 a' ss'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all sym_frame_inv_same_count_own >> strip_tac >>
  simp[sym_steps_mode_ok]
QED
