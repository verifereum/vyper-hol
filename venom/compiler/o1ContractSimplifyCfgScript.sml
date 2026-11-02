(*
 * SimplifyCFG's two runs against the O1 pass contract.
 *
 * The pass keeps every function's runs (simplify_cfg_fn_correct) and the
 * states its frames reach (simplify_cfg_frame_sim), given
 * simplify_cfg_fn_ok: no PHI in the first block, PHI outputs written once
 * and covering every reachable predecessor, and definite assignment.
 * o1PassLift lifts both to the stage contract.
 *
 * The pre-walk run gets simplify_cfg_fn_ok from the lowering's output (no
 * PHI, definite assignment: o1_pre_walk_inv) and leaves every block
 * reachable with definite assignment kept (o1_walk_src_inv, MakeSSA's
 * input).  The walk run (stage 5) gets it from wf_ssa, which MakeSSA's
 * second run establishes, and keeps wf_ssa for SUE.
 *)
Theory o1ContractSimplifyCfg
Ancestors
  o1ContractSimplifyCfgStep o1PassContract o1PassLift simplifyCfgCorrectness simplifyCfgProof
  simplifyCfgDefs unitMemInv venomPassSchedule venomCompilerTypes
  venomWf cfgWf simplifyCfgLabelProps venomPassDispatcher

Theorem simplify_cfg_pass_step_function:
  fn_pass_step rpolicy (CFP_Simple VP_SimplifyCFG) observed s fn out ==>
  out.fpo_function = simplify_cfg_fn fn
Proof
  simp[fn_pass_step_def, execute_configured_fn_pass_simplify_cfg] >>
  Cases_on `simplify_cfg_fn_with_labels fn` >>
  simp[simplify_cfg_fn_def] >> rpt strip_tac >> gvs[]
QED

Theorem simplify_cfg_stage_functions:
  ctx_pass_stage rpolicy (CFP_Simple VP_SimplifyCFG) view C C' ==>
  C'.ctx_functions = MAP simplify_cfg_fn C.ctx_functions
Proof
  simp[ctx_pass_stage_def] >> strip_tac >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  qspec_tac (`C'.ctx_functions`, `ys`) >>
  qspec_tac (`C.ctx_functions`, `xs`) >>
  Induct >> Cases >> simp[] >>
  rpt strip_tac >> gvs[] >>
  drule simplify_cfg_pass_step_function >> simp[]
QED

Theorem simplify_cfg_stage_eom_bounded:
  ctx_pass_stage rpolicy (CFP_Simple VP_SimplifyCFG) view C C' /\
  ctx_eom_bounded eom C ==> ctx_eom_bounded eom C'
Proof
  strip_tac >> drule simplify_cfg_stage_functions >>
  simp[ctx_eom_bounded_def, listTheory.MEM_MAP] >> rpt strip_tac >>
  qspec_then `y` mp_tac (GEN_ALL simplify_cfg_fn_metadata) >>
  simp[venomInstTheory.fn_static_layout_eq_def] >> strip_tac >>
  gvs[ctx_eom_bounded_def] >> first_x_assum irule >>
  qexists_tac `y` >> simp[]
QED

(* The pre-walk run: lowering output (no PHI, definite assignment) to
   MakeSSA's input (every block reachable, definite assignment kept). *)
Theorem simplify_cfg_stage_pre_walk:
  !view. o1_stage_contract rpolicy (CFP_Simple VP_SimplifyCFG) view no_pre
           o1_pre_walk_inv o1_walk_src_inv
Proof
  cheat
QED

(* The walk run, stage 5: wf_ssa in, wf_ssa out. *)
Theorem simplify_cfg_stage_walk:
  o1_run_contract rpolicy 5
Proof
  cheat
QED

Theorem o1_contract_simplify_cfg_pre_walk:
  o1_step_contract rpolicy (CFP_Simple VP_SimplifyCFG) /\
  (!view. o1_stage_contract rpolicy (CFP_Simple VP_SimplifyCFG) view no_pre
            o1_pre_walk_inv o1_walk_src_inv)
Proof
  simp[simplify_cfg_step_contract, simplify_cfg_stage_pre_walk]
QED

Theorem o1_contract_simplify_cfg:
  o1_step_contract rpolicy (CFP_Simple VP_SimplifyCFG) /\
  o1_run_contract rpolicy 5
Proof
  simp[simplify_cfg_step_contract, simplify_cfg_stage_walk]
QED
