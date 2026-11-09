(*
 * The symbolic fuel induction: the two steps of fnEntryStep and fnBlockStep
 * with the symbolic run added, and their closure over all fuel.  The
 * concrete function-level statements at each fuel come from codegen's own
 * steps (fn_entry_block_step, fn_block_frame_step).
 *
 * TOP-LEVEL:
 *   sym_fn_entry_block_step  - sym_fn_sim_at (SUC fuel) from the four
 *                              function statements at fuel
 *   sym_fn_block_frame_step  - sym_fn_frame_sim_at (SUC fuel), likewise
 *   sym_fn_sims_all          - all four at every fuel
 *)
Theory symFnStep
Ancestors
  symBlockBody symFrameBoundary symFnSimSpec codegenSymRel fnEntryStep
  fnBlockStep fnBlockStepHelpers fnBlockBody fnSimSpec asmSymBridge
  asmSymSem frameRel contextCodegenRel codegenRel venomExecSemantics
  venomState planExec stackOpSim blockSimHelpers

Theorem sym_frame_inv_cleanup_fields:
  !prog env ctx cp fn ret srest labs0 ps h promised as ss.
    sym_frame_inv prog env ctx cp fn ret srest labs0
      (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
      as ss <=>
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss
Proof
  simp[sym_frame_inv_def, sym_kinds_ok_def]
QED

Theorem sym_label_block_steps:
  !lo o2pc prog as fmp lbl ops env ctx cp fn ret srest labs0 ps ss.
    asm_block_at prog as.as_pc (execute_plan fmp (SOLabel lbl :: ops)) /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    asm_steps lo o2pc prog 1 as = AsmOK (as with as_pc := as.as_pc + 1) /\
    sym_steps prog env 1 ss =
      SymOK (ss with sym_base := ss.sym_base with as_pc := as.as_pc + 1) /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps
      (as with as_pc := as.as_pc + 1)
      (ss with sym_base := ss.sym_base with as_pc := as.as_pc + 1) /\
    asm_block_at prog (as.as_pc + 1) (execute_plan fmp ops)
Proof
  rpt gen_tac >> strip_tac >> drule label_block_steps >> strip_tac >> simp[] >>
  gvs[sym_frame_inv_def, asm_sym_rel_def] >>
  gvs[execute_plan_def, exec_stack_op_def, asm_block_at_cons] >>
  conj_tac
  >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [numLib.num_CONV ``1:num``])) >>
      simp[sym_steps_def, sym_step_def, sym_lift_def,
           asmSemTheory.asm_step_def, asmSemTheory.asm_next_def,
           sym_state_component_equality]) >>
  simp[sym_kinds_ok_def] >> gvs[sym_kinds_ok_def] >> metis_tac[]
QED

Theorem sym_body_result_prefix:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss res n as1 ss1.
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    sym_steps prog env n ss = SymOK ss1 /\
    sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
      as1 ss1 res ==>
    sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
      as ss res
Proof
  rpt gen_tac >> simp[sym_body_result_def] >> strip_tac >> rpt conj_tac
  >> rpt gen_tac >> strip_tac
  >> first_x_assum drule >> strip_tac
  >> qexists_tac `n + n'`
  >> simp[stackOpSimTheory.asm_steps_add, sym_steps_add]
  >> metis_tac[]
QED

Theorem sym_fn_entry_block_step:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
         sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel ==>
         sym_fn_sim_at (SUC fuel)
Proof
  cheat
QED

Theorem sym_fn_block_frame_step:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
         sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel ==>
         sym_fn_frame_sim_at (SUC fuel)
Proof
  cheat
QED

Theorem sym_fn_sims_all:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
         sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel
Proof
  Induct
  >- (simp[gen_fn_sim_at_def, gen_fn_frame_sim_at_def, sym_fn_sim_at_def,
           sym_fn_frame_sim_at_def] >>
      rpt strip_tac >> gvs[Once run_blocks_def]) >>
  metis_tac[fn_entry_block_step, fn_block_frame_step,
            sym_fn_entry_block_step, sym_fn_block_frame_step]
QED
