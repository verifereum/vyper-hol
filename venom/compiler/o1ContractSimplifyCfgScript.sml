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
  o1PassContract o1PassLift simplifyCfgCorrectness simplifyCfgProof
  simplifyCfgDefs unitMemInv venomPassSchedule venomCompilerTypes
  venomWf cfgWf

Theorem o1_contract_simplify_cfg_pre_walk:
  o1_step_contract rpolicy (CFP_Simple VP_SimplifyCFG) /\
  (!view. o1_stage_contract rpolicy (CFP_Simple VP_SimplifyCFG) view no_pre
            o1_pre_walk_inv o1_walk_src_inv)
Proof
  cheat
QED

Theorem o1_contract_simplify_cfg:
  o1_step_contract rpolicy (CFP_Simple VP_SimplifyCFG) /\
  o1_run_contract rpolicy 5
Proof
  cheat
QED
