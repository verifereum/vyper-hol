(*
 * MakeSSA, which runs twice (stages 0 and 4), against the O1 pass
 * contract: the admissions o1ContractTheorems re-exports.
 *
 * The per-function facts are MakeSSA's run correspondence and frame
 * simulations (makeSsaCurrentSim, makeSsaCurrentFrameRf), which
 * o1PassLift lifts to the stage simulation and to every memory fact that
 * exempts revert forwarding.  The first run (row 0 to row 1) also keeps
 * the source rows (o1ContractMakeSsa{Ptr,Taint,Src}) and leaves an output
 * that meets MakeSSA's input rows again (makeSsaCurrentInputOk,
 * makeSsaCurrentNonDegenerate), for the second run; the second run (row 4
 * to row 5) leaves SSA (makeSsaCurrentWfSsa).  Both runs take a function
 * with the O1 shape and make_ssa_input_ok, which rows 0 and 4 carry.
 *)
Theory o1ContractMakeSsa
Ancestors
  o1PassContract o1PassLift o1ComposeSupport venomPassSchedule
  venomPassDispatcher venomCompilerTypes venomRetProps unitMemInv
  unitTransformDefs ptrDiscipline ctxLookupAgreeHelpers venomInst venomWf
  makeSsaCurrentDefs makeSsaCurrentSim makeSsaCurrentFrameRf
  makeSsaCurrentWfSsa makeSsaCurrentNonDegenerate makeSsaCurrentInputOk
  o1ContractMakeSsaReplay o1ContractMakeSsaStep o1ContractMakeSsaPtr
  o1ContractMakeSsaTaint o1ContractMakeSsaSrc list

(* ===== The stage's functions ===== *)

Theorem make_ssa_stage_functions:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' ==>
  C'.ctx_entry = C.ctx_entry /\
  C'.ctx_global_reserved = C.ctx_global_reserved /\
  LIST_REL (\fn fn'. ?t t'.
    ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
    make_ssa_current_fn t fn = (fn',t'))
    C.ctx_functions C'.ctx_functions
Proof
  simp[ctx_pass_stage_def] >> strip_tac >> simp[] >>
  irule LIST_REL_mono >> goal_assum (drule_at Any) >>
  rpt strip_tac >> gvs[] >> drule make_ssa_pass_step_replay >> simp[]
QED

(* The n-th output function is MakeSSA's run on the n-th input one, which
   meets the per-function lemmas' premises. *)
Theorem make_ssa_stage_el:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  n < LENGTH C.ctx_functions ==>
  make_ssa_input_ok (EL n C.ctx_functions) /\
  fn_inst_wf (EL n C.ctx_functions) /\ wf_function (EL n C.ctx_functions) /\
  first_block_no_preds (EL n C.ctx_functions) /\
  first_block_no_phi (EL n C.ctx_functions) /\
  ?t t'. ir_supply_covers_fn t (EL n C.ctx_functions) /\
    ir_supply_inst_ok t /\
    make_ssa_current_fn t (EL n C.ctx_functions) = (EL n C'.ctx_functions,t')
Proof
  strip_tac >> drule make_ssa_stage_functions >> strip_tac >>
  `MEM (EL n C.ctx_functions) C.ctx_functions` by metis_tac[MEM_EL] >>
  `o1_fn_shape C (EL n C.ctx_functions) /\
   make_ssa_input_ok (EL n C.ctx_functions)` by
    metis_tac[o1_ctx_shape_def, EVERY_MEM] >>
  gvs[o1_fn_shape_def, LIST_REL_EL_EQN]
QED

Theorem make_ssa_stage_length:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' ==>
  LENGTH C'.ctx_functions = LENGTH C.ctx_functions
Proof
  strip_tac >> drule make_ssa_stage_functions >> strip_tac >>
  imp_res_tac LIST_REL_LENGTH >> simp[]
QED

(* ===== Simulation and memory facts ===== *)

Theorem make_ssa_stage_bisim:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions ==>
  ctx_bisim C C'
Proof
  strip_tac >> irule fn_bisim_ctx_bisim >>
  drule make_ssa_stage_length >> strip_tac >>
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  drule_all make_ssa_stage_el >> strip_tac >>
  irule make_ssa_current_fn_fn_bisim >> gvs[make_ssa_input_ok_def] >>
  metis_tac[]
QED

Theorem make_ssa_stage_sim:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted ==> ctx_sim D C C' vs vs
Proof
  strip_tac >>
  `ctx_bisim C C'` by metis_tac[make_ssa_stage_bisim] >>
  `C'.ctx_entry = C.ctx_entry` by gvs[ctx_pass_stage_def] >>
  irule ctx_bisim_ctx_sim >> simp[] >>
  rpt gen_tac >> irule run_context_not_int_ret >> rpt strip_tac >>
  `MEM fn C.ctx_functions /\ fn.fn_name = name` by
    metis_tac[lookup_function_MEM,
              ctxLookupAgreeHelpersTheory.lookup_function_selected_name] >>
  gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM,
      entry_fn_no_return_def] >> metis_tac[]
QED

(* Every memory fact that exempts revert forwarding carries over. *)
Theorem make_ssa_stage_mem_inv:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_corr_closed_rf M /\ mem_inv M C vs ==>
  mem_inv M C' vs
Proof
  strip_tac >>
  `ctx_bisim C C'` by metis_tac[make_ssa_stage_bisim] >>
  `C'.ctx_entry = C.ctx_entry` by gvs[ctx_pass_stage_def] >>
  drule make_ssa_stage_length >> strip_tac >>
  irule frame_sim_rf_mem_inv >> simp[] >>
  qexists_tac `C` >> simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  drule_all make_ssa_stage_el >> strip_tac >>
  `fn_bisim (EL n C.ctx_functions) (EL n C'.ctx_functions)` by
    (irule make_ssa_current_fn_fn_bisim >> gvs[make_ssa_input_ok_def] >>
     metis_tac[])
  >~ [`frame_sim_rf`]
  >- (irule make_ssa_current_fn_frame_sim_rf >> metis_tac[])
  >~ [`frame_sim`]
  >- (irule make_ssa_current_fn_frame_sim >> gvs[make_ssa_input_ok_def] >>
      metis_tac[]) >>
  gvs[fn_bisim_def]
QED

Theorem make_ssa_stage_max_live_eom:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' ==>
  max_live_eom C' = max_live_eom C
Proof
  strip_tac >> drule ctx_pass_stage_max_live_eom >>
  simp[fn_pass_static_layout_effect_def, fn_pass_tag_def]
QED

(* ===== Function rows ===== *)

(* The first run's output meets the second run's input rows. *)
Theorem make_ssa_stage_input_ok:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions ==>
  EVERY make_ssa_input_ok C'.ctx_functions
Proof
  strip_tac >> drule make_ssa_stage_length >> strip_tac >>
  simp[EVERY_EL] >> rpt strip_tac >>
  `n < LENGTH C.ctx_functions` by gvs[] >>
  drule_all make_ssa_stage_el >> strip_tac >>
  `fn_phis_non_degenerate (EL n C'.ctx_functions)` by
    (irule make_ssa_current_fn_phis_non_degenerate >> metis_tac[]) >>
  drule_all make_ssa_current_fn_input_ok >> strip_tac >>
  rewrite_tac[make_ssa_input_ok_def] >> asm_rewrite_tac[]
QED

(* The second run's output is SSA. *)
Theorem make_ssa_stage_wf_ssa:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions ==>
  EVERY wf_ssa C'.ctx_functions
Proof
  strip_tac >> drule make_ssa_stage_length >> strip_tac >>
  simp[EVERY_EL] >> rpt strip_tac >>
  `n < LENGTH C.ctx_functions` by gvs[] >>
  drule_all make_ssa_stage_el >> strip_tac >>
  irule make_ssa_current_fn_wf_ssa >> gvs[make_ssa_input_ok_def] >>
  metis_tac[]
QED

(* ===== The two runs ===== *)

(* Row 0 (the walk's source invariant) to row 1 (the source invariant,
   with MakeSSA's input rows for its second run). *)
Theorem make_ssa_run_contract_1:
  o1_run_contract rpolicy D 0
Proof
  `EL 0 o1_fn_passes = CFP_Simple VP_MakeSSA` by simp[o1_fn_passes_def] >>
  simp[o1_run_contract_def, o1_stage_contract_def, o1_inv_def] >>
  rpt gen_tac >> strip_tac >>
  `EVERY make_ssa_input_ok C.ctx_functions /\ o1_src_inv D C vs` by
    fs[o1_walk_src_inv_def] >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted` by
    gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  conj_tac >- metis_tac[make_ssa_stage_sim] >>
  `mem_inv raw_mem_ok C' vs` by
    (irule make_ssa_stage_mem_inv >> fs[o1_src_inv_def] >>
     metis_tac[mem_corr_closed_rf_raw_mem_ok]) >>
  `taint_within D C' vs` by metis_tac[make_ssa_stage_taint] >>
  drule_all make_ssa_stage_src_rows >> strip_tac >>
  `EVERY make_ssa_input_ok C'.ctx_functions` by
    metis_tac[make_ssa_stage_input_ok] >>
  `EVERY ssa_form C'.ctx_functions` by
    metis_tac[make_ssa_stage_wf_ssa, wf_ssa_def, EVERY_MEM] >>
  fs[o1_src_inv_def] >>
  `ptr_discipline lo C' vs` by
    (irule make_ssa_stage_ptr >> simp[o1_src_inv_def] >> metis_tac[]) >>
  `C'.ctx_global_reserved = C.ctx_global_reserved` by fs[ctx_pass_stage_def] >>
  fs[fixed_region_reserved_def] >> metis_tac[]
QED

(* Row 4 (the lowered memory fact) to row 5 (it, and SSA). *)
Theorem make_ssa_run_contract_2:
  o1_run_contract rpolicy D 4
Proof
  `EL 4 o1_fn_passes = CFP_Simple VP_MakeSSA` by simp[o1_fn_passes_def] >>
  simp[o1_run_contract_def, o1_stage_contract_def, o1_inv_def] >>
  rpt gen_tac >> strip_tac >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted` by
    gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  conj_tac >- metis_tac[make_ssa_stage_sim] >>
  simp[o1_ssa_inv_def] >> conj_tac
  >- (gvs[o1_lowered_inv_def] >> qexists_tac `eom` >>
      conj_tac >- metis_tac[make_ssa_stage_max_live_eom] >>
      irule make_ssa_stage_mem_inv >>
      metis_tac[mem_corr_closed_rf_lowered_mem_fact]) >>
  metis_tac[make_ssa_stage_wf_ssa]
QED

Theorem o1_contract_make_ssa_1:
  o1_step_contract_at 0 rpolicy (CFP_Simple VP_MakeSSA) /\
  o1_run_contract rpolicy D 0
Proof
  simp[make_ssa_step_contract_at, make_ssa_run_contract_1]
QED

Theorem o1_contract_make_ssa_2:
  o1_step_contract_at 4 rpolicy (CFP_Simple VP_MakeSSA) /\
  o1_run_contract rpolicy D 4
Proof
  simp[make_ssa_step_contract_at, make_ssa_run_contract_2]
QED
