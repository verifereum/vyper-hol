(*
 * The step of the fuel induction behind
 * venomToAsmProps$gen_fn_frame_simulation: one non-entry block, run from
 * a block boundary where fn_frame_inv holds, simulated by its DFS code.
 *
 * TOP-LEVEL (proved from the admitted block pieces of fnBlockBody,
 *            fnFrameSteps, fnFrameSinglePred, fnLineageStatic, fnPlanLineage):
 *   fn_block_frame_step - gen_fn_frame_sim_at (SUC fuel) from both
 *                         function theorems at fuel
 *)

Theory fnBlockStep
Ancestors
  fnBlockBody fnFrameSinglePred fnSimSpec fnFrameSteps fnFrameBoundary fnFrameTerminal gasFrameSim
  genFrameSim fnPlanPlace fnPlanCover fnAliasInv fnPlanLineage frameRel
  venomExecSemantics fnBlockStepHelpers contextCodegenRel venomExecProofs

(* run_blocks (SUC fuel) runs the current block with run_block fuel and
   continues with run_blocks fuel from its OK result (run_blocks_unfold);
   an INVOKE inside the block runs its callee with run_function fuel.  So
   the hypotheses are the callee simulation (gen_fn_sim_at fuel) and the
   rest of the run from the successor (gen_fn_frame_sim_at fuel).

   Why it should hold: the block's code is its DFS plan (dfs_block_code_placed),
   and the lineage state the run arrived with regenerates that code
   (lineage_state_block_plan).  The block runs as its PHI prefix
   (phi_prefix_frame_sim), then one instruction at a time against
   fn_frame_inv: gen_inst_frame_sim and gas_inst_frame_sim for ordinary
   steps, gen_invoke_frame_sim with the callee hypothesis for INVOKE, and
   at the end gen_jmp_frame_sim / gen_jnz_frame_sim (successor), the halt
   and abort steps (fnFrameTerminal), revert_forward_frame_sim, or
   gen_ret_frame_sim (IntRet).  At a successor the step re-establishes the
   block-boundary premises of gen_fn_frame_sim_at for it (lineage_entry
   from this block, dfs_block_state, the alias premise by
   lineage_alias_successor), and the successor run's assembly steps are
   added to the block's (asm_steps_add_ok). *)
Theorem fn_block_frame_step:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel ==>
         gen_fn_frame_sim_at (SUC fuel)
Proof
  gen_tac >> strip_tac >> REWRITE_TAC [gen_fn_frame_sim_at_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `generate_context_plan ctx = SOME cpl` >>
  qspecl_then [`vs`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >- suspend "ok"
  >> simp[run_blocks_unfold, run_block_def]
QED

Resume fn_block_frame_step[ok]:
  `run_blocks (SUC fuel) ctx fn vs =
   block_rest fuel ctx fn bb
     (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[run_blocks_unfold, run_block_def, block_rest_def] >>
     Cases_on `exec_block fuel ctx bb
       (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
     simp[]) >>
  pop_assum SUBST1_TAC >>
  `s'.vs_labels = vs.vs_labels /\ s'.vs_call_ctx = vs.vs_call_ctx /\
   s'.vs_current_bb = vs.vs_current_bb` by
    (drule eval_phis_only_updates_vs_vars >>
     disch_then (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  `!inst. active_inst fn inst
            (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions) ==>
          Inv ctx fn inst
            (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (rpt strip_tac >>
     qpat_x_assum `fn_entry_inv _ _ _ _` (irule o REWRITE_RULE [fn_entry_inv_def]) >>
     simp[enters_block_def]) >>
  drule lineage_entry_lineage_state >> strip_tac >>
  drule venomExecPropsTheory.lookup_block_label >> strip_tac >>
  `dfs_block_state liveness dfg cfg fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr)
     bb.bb_label ps_dfs` by
    (qpat_x_assum `bb.bb_label = _` (fn th => REWRITE_TAC [th]) >>
     first_assum ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`unit`, `cpl`, `prog`, `ctx`, `lo`, `o2pc`, `i`, `fn`, `r`,
    `liveness`, `dfg`, `cfg`, `ch`, `growth`, `spill_base`, `lbl_ctr`,
    `fn_ops`, `ps_end`, `bb`, `pred`, `ps`, `ps_dfs`, `block_ops`,
    `ps_dfs_after`, `vs`, `as`, `Inv`, `ra`, `rest`, `mem0`, `s'`]
    block_step_prefix) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  Q.SUBGOAL_THEN `?prefixL prefixD core.
     ps_after.ps_stack = prefixL ++ core /\
     ps_dfs_after.ps_stack = prefixD ++ core /\
     (!v. MEM v (live_vars_at liveness bb.bb_label
                   (LENGTH bb.bb_instructions)) ==>
        ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD)` ASSUME_TAC
  >- (qexistsl_tac [`prefixL`, `prefixD`, `core`] >> rpt conj_tac >>
      first_assum ACCEPT_TAC) >>
  `!i j. revert_forward_pair bb i j ==>
         phi_prefix_length bb.bb_instructions <= i \/
         j < phi_prefix_length bb.bb_instructions` by
    metis_tac[revert_forward_pair_past_phis] >>
  mp_tac (Q.SPECL [`fuel`, `rpolicy`, `unit`, `cpl`, `prog`, `ctx`, `lo`,
    `o2pc`, `i`, `fn`, `r`, `liveness`, `dfg`, `cfg`, `ch`, `growth`,
    `spill_base`, `lbl_ctr`, `fn_ops`, `ps_end`, `bb`, `ps`, `h`, `promised`,
    `ps_dfs`, `block_ops`, `ps_dfs_after`, `ps_after`, `prefix_ops`,
    `rest_ops`, `phi_prefix_length bb.bb_instructions`, `ps1`, `as.as_pc`,
    `s' with vs_inst_idx := phi_prefix_length bb.bb_instructions`, `as1`,
    `Inv`, `ra`, `pc_ret`, `rest`, `mem0`] block_body_frame_sim) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  disch_then assume_tac >>
  match_mp_tac frame_conclusions_prefix >>
  qexistsl_tac [`n`, `as1`] >> conj_tac >> first_assum ACCEPT_TAC
QED

Finalise fn_block_frame_step
