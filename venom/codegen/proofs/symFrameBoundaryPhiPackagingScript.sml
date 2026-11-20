(* PHI boundary frame packaging from paired successful legacy runs.
   Numerical execution is supplied by the caller, not repeated here. *)
Theory symFrameBoundaryPhiPackaging
Ancestors
  symFrameBoundaryPairing fnFrameStepsPhi asmFrame

Theorem sym_frame_inv_local_same_count_own:
  !lo o2pc prog env own ctx cp fn ret srest labs0 ps cs ss top rest n endpoint out last.
  code_labels_agree prog lo /\
  o2pc = build_offset_to_pc prog /\ asm_static_wf prog /\
  sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps cs ss /\
  cs.as_stack = top ++ rest /\
  asm_steps lo o2pc prog n (cs with as_stack := top) = AsmOK endpoint /\
  sym_steps prog env n ss = SymOK out /\
  sym_kinds_ok cp fn ret srest last out /\
  (!b. ~closure_spill_byte ctx cp fn.fn_name b ==>
    FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
  asm_steps lo o2pc prog n cs =
    AsmOK (endpoint with as_stack := endpoint.as_stack ++ rest) /\
  sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 last
    (endpoint with as_stack := endpoint.as_stack ++ rest) out
Proof
  rpt gen_tac >> strip_tac >> drule asm_steps_frame >>
  disch_then (qspec_then `rest` mp_tac) >>
  `cs with as_stack := top ++ rest = cs` by
    simp[asmSemTheory.asm_state_component_equality] >>
  simp[] >> strip_tac >> metis_tac[sym_frame_inv_same_count_own]
QED

Theorem sym_phi_run_prefix_frame_of_runs_own:
  !allow_own lo o2pc prog env own ctx cp fn ret srest labs0 ps cs ss top rest
    ops endpoint out last ra base pred entry source m done todo.
  code_labels_agree prog lo /\
  o2pc = build_offset_to_pc prog /\ asm_static_wf prog /\
  sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps cs ss /\
  cs.as_stack = top ++ rest /\
  asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp ops))
    (cs with as_stack := top) = AsmOK endpoint /\
  endpoint.as_pc = cs.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
  phi_run_config fn ra lo base pred entry source m (done ++ todo) [] last endpoint /\
  sym_steps prog env (LENGTH (execute_plan cp.cp_initial_fmp ops)) ss = SymOK out /\
  sym_kinds_ok cp fn ret srest last out /\ out.sym_base.as_pc = endpoint.as_pc /\
  (!b. ~closure_spill_byte ctx cp fn.fn_name b ==>
    FLOOKUP out.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
  ?endpoint out.
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp ops)) cs =
      AsmOK (endpoint with as_stack := endpoint.as_stack ++ rest) /\
    endpoint.as_pc = cs.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
    phi_run_config fn ra lo base pred entry source m (done ++ todo) [] last endpoint /\
    sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cp.cp_initial_fmp ops)) ss = SymOK out /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 last
      (endpoint with as_stack := endpoint.as_stack ++ rest) out
Proof
  rpt gen_tac >> strip_tac >>
  drule_all sym_frame_inv_local_same_count_own >> strip_tac >>
  qexistsl [`endpoint`, `out`] >> simp[] >>
  irule codegenSymRelTheory.sym_steps_mode_ok >> simp[]
QED
