Theory fnStaticAbortBodyFacts
Ancestors
  fnStaticAbortBoundary fnBlockBodySteps contextStaticAbortRel
  venomExecProps venomWf venomExecSemantics venomInst
  contextCodegenRel fnBlockBodyHelpers unitShapeDefs
  fnBlockBodyClasses contextCodegenRelProps

(* Memory is needed only at this instruction, after the pending cut and
   revert-forwarding have been independently excluded. *)
Theorem body_inv_abort_memory:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs ==>
  source_memory_reads_disjoint cpl inst vs /\
  context_source_memory_writes_disjoint cpl inst vs /\
  (!fuel vs1. step_inst fuel ctx inst vs = OK vs1 ==>
     context_spill_step_safe cpl vs vs1)
Proof
  strip_tac >>
  `MEM fn ctx.ctx_functions /\ MEM bb fn.fn_blocks /\
   get_instruction bb vs.vs_inst_idx = SOME inst` by
    (fs[body_inv_abort_def, get_instruction_def] >>
     metis_tac[listTheory.EL_MEM, lookup_block_MEM]) >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def] >> irule MEM_fn_insts_blocks >>
     qexists `bb` >> simp[] >> metis_tac[listTheory.EL_MEM]) >>
  `Inv ctx fn inst vs` by
    (gvs[body_inv_abort_def] >> first_x_assum irule >>
     simp[active_inst_def] >> qexists `bb` >>
     simp[] >> metis_tac[lookup_block_label]) >>
  fs[body_inv_abort_def, codegen_context_obligations_abort_def,
     codegen_memory_obligations_abort_def] >> metis_tac[]
QED

Theorem body_inv_abort_plan:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 ==>
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast
      ra pc_ret rest mem0
Proof
  simp[body_inv_abort_def, body_plan_inv_def,
       codegen_context_obligations_abort_def, codegen_context_obligations_def,
       codegen_memory_obligations_def] >> metis_tac[]
QED

Theorem body_inv_abort_advance:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
    step_inst fuel ctx inst vs = OK vs1 /\
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
        (non_param_insts bb)) ps' = SOME (rest', ps_after) /\
    rest_ops = ops ++ rest' /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 ast1 /\
    ast1.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) ==>
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after (prefix_ops ++ ops) rest' (SUC k) ps'
      pc0 (vs1 with vs_inst_idx := SUC k) ast1 Inv ra pc_ret rest mem0
Proof
  strip_tac >> drule body_inv_abort_plan >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule_all body_plan_advance >> strip_tac >>
  fs[body_inv_abort_def, body_plan_inv_def] >>
  metis_tac[reachability_closed_next]
QED
