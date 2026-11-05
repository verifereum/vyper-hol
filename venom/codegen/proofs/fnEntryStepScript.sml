(*
 * The step of the fuel induction behind venomToAsmProps$gen_fn_simulation:
 * the entry block, run from fn_entry_state_rel, simulated by the code at
 * the start of the function's region.
 *
 * TOP-LEVEL (CHEATED, a skeleton piece):
 *   fn_entry_block_step - gen_fn_sim_at (SUC fuel) from both function
 *                         theorems at fuel
 *)

Theory fnEntryStep
Ancestors
  fnSimSpec fnFrameSteps fnFrameBoundary fnFrameTerminal gasFrameSim
  genFrameSim fnPlanPlace fnPlanCover fnAliasInv fnPlanLineage frameRel
  venomExecSemantics fnBlockBody fnEntryPlan fnEntryPc fnEntryParams fnRunFields
  unitShapeDefs contextPlanLayoutProps planSpillBounds contextCodegenRel stackPlanGen
  stackPlanTypes

Theorem entry_step_shape[local]:
  !ctx unit Inv cp i fn.
  ctx = unit.cu_context /\ unit_shape_ok unit /\
  codegen_context_obligations Inv ctx cp /\
  i < LENGTH ctx.ctx_functions /\ EL i ctx.ctx_functions = fn ==>
  codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn
Proof
  simp[unit_shape_ok_def, codegen_context_obligations_def, codegen_ready_def,
       listTheory.EVERY_EL, fn_shape_ok_def] >>
  metis_tac[]
QED

Theorem entry_step_spill_bound[local]:
  !ctx cp r lbl param_ops body_ops tail.
  generate_context_plan ctx = SOME cp /\ MEM r cp.cp_regions /\
  r.sr_plan = SOLabel lbl :: param_ops ++ body_ops ++ tail ==>
  !off. MEM (SOSpill off) param_ops ==> off < dimword (:256)
Proof
  rpt strip_tac >>
  drule generate_context_plan_access_bounded >>
  simp[listTheory.EVERY_MEM] >> strip_tac >>
  drule generate_context_plan_spill_gap >> strip_tac >>
  `region_spill_access r off` by
    simp[region_spill_access_def] >>
  `off + 32 <= r.sr_spill_end` by metis_tac[] >>
  qpat_x_assum `!r. MEM r _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  decide_tac
QED

Theorem entry_step_reachable[local]:
  fn_entry_label fn = SOME lbl ==> fn_reachable fn lbl
Proof
  simp[venomWfTheory.fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]
QED

Theorem entry_step_phi_bound[local]:
  codegen_ready_fn fn ==>
  phi_prefix_length (HD fn.fn_blocks).bb_instructions <=
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions)
Proof
  rw[codegen_ready_fn_def] >>
  `fn.fn_blocks <> []` by
    gvs[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def] >>
  gvs[block_entries_ready_def, venomInstTheory.entry_block_def,
      listTheory.NULL_EQ] >>
  Cases_on `(HD fn.fn_blocks).bb_instructions` >>
  gvs[livenessDefsTheory.collect_phis_def, phi_prefix_length_def] >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >> rw[] >>
  simp[phi_prefix_length_def]
QED

(* As for fn_block_frame_step, but for the entry block, which
   gen_fn_frame_sim_at excludes.

   Why it should hold: region i's plan is the function planner's output
   for some label counter (fnEntryPlan$region_fn_plan) and starts with
   the entry block's code, planned from the initial state ps0: its label,
   its parameter code, then its instructions' code
   (fnEntryPlan$entry_block_plan).  The premise's asm_block_at puts that
   code at as.as_pc, which is where the entry label resolves
   (fnEntryPc$entry_pc_placed).  The entry block has no PHIs
   (fnEntryParams$entry_run_block), and the parameter prefix turns
   fn_entry_state_rel into fn_frame_inv at ps1 with mem0 = as.as_memory
   (fnEntryParams$entry_prefix_frame_sim, which also gives Inv, the
   labels and the alias premise at the state vs_p after it).  So
   run_blocks (SUC fuel) from vs is block_rest from vs_p, which
   fnBlockBody$block_body_frame_sim simulates (bb = HD fn.fn_blocks,
   ps_l = ps_dfs = ps0 with its own cleanup fields, k = the parameter
   count, ps = ps1, prefix_ops = the parameter code); its steps are added
   to the prefix's.  Its IntRet clause gives fn_return_state_rel: the
   spill-byte clause is the frame's against mem0, and the call, tx and
   block context, code and prev-hash clauses hold because the run never
   changes those fields (fnRunFields$run_blocks_intret_fields) and
   fn_entry_state_rel equates them with as's. *)
Theorem fn_entry_block_step:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel ==>
         gen_fn_sim_at (SUC fuel)
Proof
  cheat
QED
