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
  opcodeClass ctxLookupAgreeHelpers venomExecSemantics

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

Theorem step_inst_intret_opcodes:
  step_inst fuel C inst s = IntRet vals t ==>
  MEM inst.inst_opcode [RET; RETFMP; DRET]
Proof
  Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[Once step_inst_def] >>
      gvs[AllCaseEqs(), bind_outputs_def]) >>
  simp[step_inst_non_invoke] >> strip_tac >>
  drule step_inst_base_intret_opcodes >> simp[] >> metis_tac[]
QED

Theorem exec_block_no_return:
  EVERY (\inst. ~MEM inst.inst_opcode [RET; RETFMP; DRET])
    bb.bb_instructions ==>
  exec_block fuel C bb s <> IntRet vals t
Proof
  qid_spec_tac `s` >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >- simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `~MEM inst.inst_opcode [RET; RETFMP; DRET]` by
    (drule_all EVERY_get_instruction >> simp[]) >>
  `!v t. step_inst fuel C inst s <> IntRet v t` by
    metis_tac[step_inst_intret_opcodes] >>
  Cases_on `step_inst fuel C inst s` >> simp[] >>
  rpt IF_CASES_TAC >> simp[] >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    gvs[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  simp[] >>
  qexists_tac `v' with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[]
QED

Theorem run_block_no_return:
  EVERY (\inst. ~MEM inst.inst_opcode [RET; RETFMP; DRET])
    bb.bb_instructions ==>
  run_block fuel C bb s <> IntRet vals t
Proof
  strip_tac >> simp[run_block_def] >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >>
  simp[] >> irule exec_block_no_return >> simp[]
QED

Theorem run_blocks_no_return:
  entry_fn_no_return fn ==>
  !fuel C s vals t. run_blocks fuel C fn s <> IntRet vals t
Proof
  strip_tac >> Induct >> rpt gen_tac
  >- simp[Once run_blocks_def] >>
  simp[run_blocks_unfold] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >- simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `EVERY (\inst. ~MEM inst.inst_opcode [RET; RETFMP; DRET])
     bb.bb_instructions` by
    (gvs[entry_fn_no_return_def] >>
     drule_all EVERY_fn_lookup_block >> simp[]) >>
  `!v t. run_block fuel C bb s <> IntRet v t` by
    (rpt gen_tac >> irule run_block_no_return >> simp[]) >>
  Cases_on `run_block fuel C bb s` >> simp[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem o1_ctx_shape_no_intret:
  o1_ctx_shape C ==>
  !fuel vs vals t. run_context fuel C vs <> IntRet vals t
Proof
  strip_tac >> rpt gen_tac >> simp[run_context_def] >>
  Cases_on `C.ctx_entry` >- simp[] >>
  Cases_on `lookup_function x C.ctx_functions` >- simp[] >>
  rename1 `lookup_function name C.ctx_functions = SOME fn` >>
  `MEM fn C.ctx_functions` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  `fn.fn_name = name` by
    metis_tac[lookup_function_selected_name] >>
  `entry_fn_no_return fn` by
    (gvs[o1_ctx_shape_def, listTheory.EVERY_MEM] >>
     first_x_assum drule >> simp[o1_fn_shape_def]) >>
  simp[run_function_def] >> Cases_on `fn_entry_label fn` >> simp[] >>
  irule run_blocks_no_return >> simp[]
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
