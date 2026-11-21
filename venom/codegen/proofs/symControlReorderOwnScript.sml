(* Relocated, code-predicate-parametric control planner framing.
   The successful-run correspondence is discharged at the control join. *)
Theory symControlReorderOwn
Ancestors
  symControlPrefixOwn asmSymBridge[qualified,ignore_grammar] codegenSymRel
  asmSplice asmSymSem frameRel contextCodegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec asmSem dfgDefs symPlannerSim symShuffleSim
  spillPlanSim reorderStages inputMaterialised reduceDepthSim mixedPrefixSim
  fnFrameStepsRevertForward symFrameControlFacts fnFrameDeepJmp
  reorderPreparationProps generatedReorderSim planSpillBounds deepResidualBudget allocMono

(* Parser abbreviations only; no new logical definitions. *)
val control_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", control_bridge_core_tm);
val _ = Parse.temp_overload_on ("control_frame",
  ``\lo code_ok p ctx cp fn ret srest labs0 ps cs ss.
    bridge_core lo code_ok cs ss /\ sym_kinds_ok cp fn ret srest ps ss /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
      FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) p)``);

Theorem sym_frame_inv_release_dead_spills_mode:
  !lo code_ok p ctx cp fn ret srest labs0 ps cs ss nl.
  control_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss ==>
  control_frame lo code_ok p ctx cp fn ret srest labs0
    (release_dead_spills nl ps) cs ss
Proof
  metis_tac[symPostfixSimTheory.sym_kinds_ok_release_dead_spills]
QED

Theorem do_restore_symbolic_prefix_facts:
  !op ps ops ps' initial_fmp lo.
  do_restore op ps = (ops,ps') /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  prefix_spill_wf initial_fmp lo ops ps /\
  EVERY is_prefix_op ops /\
  EVERY (\op. !l d. op <> SOPushOfst l d) ops /\
  (!off. ~MEM (SOSpill off) ops)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  gvs[stackPlanOpsTheory.do_restore_def, mixedPrefixSimTheory.prefix_spill_wf_def,
      mixedPrefixSimTheory.spill_op_wf_def, prefixExecTheory.prefix_wf_def,
      prefixSimTheory.is_prefix_op_def, prefixExecTheory.stack_op_wf_def] >>
  metis_tac[]
QED

Theorem sym_do_restore_frame_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  !cp op ps ops ps' initial_fmp fn ret srest ss ctx labs0 cs r.
  do_restore op ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  control_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cp fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all do_restore_symbolic_prefix_facts >>
  disch_then (qspecl_then [`initial_fmp`, `lo`] strip_assume_tac) >>
  drule doSwapSimTheory.spill_alloc_layout_wf_spilled_separated >> strip_tac >>
  drule_all planAlignTheory.do_restore_ss_align >> strip_tac >>
  rename1 `MEM r cplan.cp_regions` >>
  `!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    (r.sr_spill_base <= b /\ b < r.sr_spill_end) /\
    context_spill_byte cplan b` by simp[] >>
  drule_all sym_prefix_ops_frame_sim_mode_conditional >> strip_tac >>
  qexistsl [`cs'`, `ss'`] >> gvs[sym_kinds_ok_def] >>
  conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]
QED

Theorem do_swap_shallow_symbolic_prefix_facts:
  !d ps ops ps' initial_fmp lo.
  do_swap d ps = (ops,ps') /\ d <= 16 /\ d < LENGTH ps.ps_stack ==>
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  prefix_spill_wf initial_fmp lo ops ps /\
  EVERY is_prefix_op ops /\
  EVERY (\op. !l n. op <> SOPushOfst l n) ops /\
  (!off. ~MEM (SOSpill off) ops)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `d = 0` >>
  gvs[stackPlanOpsTheory.do_swap_def, prefixExecTheory.prefix_wf_def,
      prefixExecTheory.stack_op_wf_def, prefixSimTheory.is_prefix_op_def,
      mixedPrefixSimTheory.prefix_spill_wf_def, mixedPrefixSimTheory.spill_op_wf_def]
QED

Theorem sym_do_swap_shallow_frame_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  !cp d ps ops ps' initial_fmp fn ret srest ss ctx labs0 cs r.
  do_swap d ps = (ops,ps') /\ d <= 16 /\ d < LENGTH ps.ps_stack /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  control_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cp fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all do_swap_shallow_symbolic_prefix_facts >>
  disch_then (qspecl_then [`initial_fmp`, `lo`] strip_assume_tac) >>
  rename1 `MEM r cplan.cp_regions` >>
  `!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    (r.sr_spill_base <= b /\ b < r.sr_spill_end) /\
    context_spill_byte cplan b` by simp[] >>
  drule_all planAlignTheory.do_swap_align >> strip_tac >>
  drule_all sym_prefix_ops_frame_sim_mode_conditional >> strip_tac >>
  qexistsl [`cs'`, `ss'`] >> gvs[] >>
  conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]
QED

Theorem do_spill_at_symbolic_prefix_shape:
  !d ps ops ps' lo.
  do_spill_at d ps = (ops,ps') /\ d <= 16 /\ d < LENGTH ps.ps_stack ==>
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  EVERY is_prefix_op ops /\ EVERY (\op. !l n. op <> SOPushOfst l n) ops
Proof
  rpt gen_tac >> strip_tac >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  drule_all planWfTheory.do_spill_at_wf_len >> simp[] >> strip_tac >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >> Cases_on `d = 0` >>
  gvs[stackPlanOpsTheory.do_spill_at_def, stackPlanOpsTheory.do_spill_tos_def,
      prefixSimTheory.is_prefix_op_def, AllCaseEqs()]
QED

Theorem sym_do_spill_at_frame_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  !cp d ps ops ps' initial_fmp fn ret srest ss ctx labs0 cs r base.
  do_spill_at d ps = (ops,ps') /\ d <= 16 /\ d < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded base ps /\
  (!off. MEM (SOSpill off) ops ==> off < dimword(:256)) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= base /\ ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  control_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cp fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all (Q.ISPEC `(lo:string |-> num)`
    (Q.GEN `lo` (SPEC_ALL do_spill_at_symbolic_prefix_shape))) >>
  disch_then (qspec_then `lo` strip_assume_tac) >>
  drule_all reorderSimTheory.do_spill_at_prefix_spill_wf >>
  disch_then (qspecl_then [`initial_fmp`, `lo`] strip_assume_tac) >>
  drule_all planSpillBoundsTheory.do_spill_at_slots_bounded >> strip_tac >>
  rename1 `MEM r cplan.cp_regions` >>
  `!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    (r.sr_spill_base <= b /\ b < r.sr_spill_end) /\
    context_spill_byte cplan b` by
    (fs[planSpillBoundsTheory.ops_spill_bounded_def, in_mem_range_def,
        contextCodegenRelTheory.context_spill_byte_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  drule_all sym_prefix_ops_frame_sim_mode_conditional >> strip_tac >>
  qexistsl [`cs'`, `ss'`] >> simp[] >>
  drule reorderSimTheory.do_spill_at_relevant_align_layout >>
  disch_then (qspecl_then [`initial_fmp`, `d`, `lo`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[sym_kinds_ok_def] >>
  conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]
QED

Theorem selected_spill_marked_budget:
  !base pending ps dist cand hops ps1.
  residual_budget_wf_marked base pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  16 < dist /\ dist < LENGTH ps.ps_stack /\
  select_spill_candidate ps.ps_stack pending dist (LENGTH pending) = SOME cand /\
  do_spill_at cand ps = (hops,ps1) ==>
  cand <= 16 /\ cand < LENGTH ps.ps_stack /\
  residual_budget_wf_marked base pending ps1 /\
  LENGTH pending <= LENGTH ps1.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  drule_all planWfTheory.select_spill_candidate_bound >> strip_tac >>
  drule deepResidualBudgetTheory.select_spill_candidate_props >> strip_tac >>
  `stack_peek cand ps.ps_stack <> dead_stack_marker` by
    (Cases_on `stack_peek cand ps.ps_stack` >>
     gvs[is_var_operand_def, dead_stack_marker_def]) >>
  drule_all deepResidualBudgetTheory.residual_budget_wf_marked_do_spill_at >>
  strip_tac >> simp[] >>
  drule reduceDepthSimTheory.do_spill_at_stack_length >> simp[] >> decide_tac
QED

Theorem sym_reduce_depth_plan_frame_sim_width[local]:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  !fuel pending op f width ps ops ps' base initial_fmp cp fn ret srest ss ctx labs0 cs r.
  plan_slots_bounded base ps /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  reduce_depth_plan fuel pending op f width ps = (ops,ps') /\
  (!off. MEM (SOSpill off) ops ==> off < dimword(:256)) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= base /\ ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  control_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cp fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> drule sym_do_spill_at_frame_sim_mode_conditional >>
  disch_then (mk_asm "spill") >>
  Induct >> rpt gen_tac >>
  ntac 8 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "frame") strip_assume_tac)
  >- (asm "frame" assume_tac >> gvs[stackPlanOpsTheory.reduce_depth_plan_def, execute_plan_def,
         asm_steps_def, sym_steps_mode_def, asmSpliceTheory.sym_steps_def,
         asmSpliceOwnTheory.sym_steps_own_def] >>
      conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]) >>
  qpat_x_assum `reduce_depth_plan (SUC fuel) _ _ _ _ _ = _` mp_tac >>
  simp[Once stackPlanOpsTheory.reduce_depth_plan_def] >>
  Cases_on `f + 1 < width`
  >- (strip_tac >> asm "frame" assume_tac >> gvs[execute_plan_def, asm_steps_def, sym_steps_mode_def,
         asmSpliceTheory.sym_steps_def, asmSpliceOwnTheory.sym_steps_own_def] >>
      conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]) >>
  Cases_on `stack_get_unfixed_depth op f width ps.ps_stack` >> simp[]
  >- (strip_tac >> asm "frame" assume_tac >> gvs[execute_plan_def, asm_steps_def, sym_steps_mode_def,
         asmSpliceTheory.sym_steps_def, asmSpliceOwnTheory.sym_steps_own_def] >>
      conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]) >>
  rename1 `_ = SOME dist` >> Cases_on `dist <= 16` >> simp[]
  >- (strip_tac >> asm "frame" assume_tac >> gvs[execute_plan_def, asm_steps_def, sym_steps_mode_def,
         asmSpliceTheory.sym_steps_def, asmSpliceOwnTheory.sym_steps_own_def] >>
      conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]) >>
  Cases_on `select_spill_candidate ps.ps_stack pending dist width` >> simp[]
  >- (strip_tac >> asm "frame" assume_tac >> gvs[execute_plan_def, asm_steps_def, sym_steps_mode_def,
         asmSpliceTheory.sym_steps_def, asmSpliceOwnTheory.sym_steps_own_def] >>
      conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]) >>
  pairarg_tac >> rename1 `do_spill_at cand ps = (hops,ps1)` >> gvs[] >>
  pairarg_tac >> rename1 `reduce_depth_plan fuel pending op f width ps1 = (tops,ps2)` >>
  strip_tac >> gvs[] >> suspend "selected_spill"
QED

Resume sym_reduce_depth_plan_frame_sim_width[selected_spill]:
  `dist < LENGTH ps.ps_stack` by
    metis_tac[stackModelTheory.stack_get_unfixed_depth_bound] >>
  `16 < dist` by decide_tac >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  drule_all planWfTheory.select_spill_candidate_bound >> strip_tac >>
  `cand < LENGTH ps.ps_stack` by decide_tac >>
  drule_all planSpillBoundsTheory.do_spill_at_slots_bounded >> strip_tac >>
  drule_all reorderPreparationTracePropsTheory.do_spill_at_layout_wf >> strip_tac >>
  `ps1.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    metis_tac[allocMonoTheory.reduce_depth_plan_next_offset, arithmeticTheory.LESS_EQ_TRANS] >>
  `(!off. MEM (SOSpill off) hops ==> off < dimword(:256)) /\
   (!off. MEM (SOSpill off) tops ==> off < dimword(:256))` by metis_tac[] >>
  gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  `!off. MEM (SOSpill off) hops ==> off < dimword(:256)` by metis_tac[] >>
  asm "frame" (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  asm "spill" (qspecl_then [`cp'`, `cand`, `ps`, `hops`, `ps1`,
    `initial_fmp`, `fn`, `ret`, `srest`, `ss`, `ctx`, `labs0`,
    `cs`, `r`, `base'`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_assum `!i l d j. FLOOKUP ss.sym_mem_labels i = SOME (l,d,j) ==> _`
        (drule_then strip_assume_tac) >> simp[]) >>
  disch_then (qx_choose_then `cs'` (qx_choose_then `ss'`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (mk_asm "frame1") assume_tac))))) >>
  asm "frame1" (map_every assume_tac o CONJUNCTS o SRULE []) >>
  `!off. MEM (SOSpill off) tops ==> off < dimword(:256)` by metis_tac[] >>
  `asm_block_at p cs'.as_pc (execute_plan initial_fmp tops)` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qexistsl [`cs''`, `ss''`] >>
  simp[stackOpSimTheory.asm_steps_add, sym_steps_mode_add] >> (metisTools.METIS_TAC [])
QED

Finalise sym_reduce_depth_plan_frame_sim_width

Theorem sym_reduce_depth_plan_frame_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  !fuel pending op f ps ops ps' base initial_fmp cp fn ret srest ss ctx labs0 cs r.
  residual_budget_wf_marked base pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  reduce_depth_plan fuel pending op f (LENGTH pending) ps = (ops,ps') /\
  (!off. MEM (SOSpill off) ops ==> off < dimword(:256)) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= base /\ ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  control_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cp fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> drule sym_reduce_depth_plan_frame_sim_width >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  fs[deepResidualBudgetTheory.residual_budget_wf_marked_def] >>
  first_x_assum irule >> metis_tac[]
QED

val control_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", control_bridge_core_tm);
val _ = Parse.temp_overload_on ("control_frame",
  ``\lo code_ok p ctx cp fn ret srest labs0 ps cs ss.
    bridge_core lo code_ok cs ss /\ sym_kinds_ok cp fn ret srest ps ss /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
      FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) p)``);

Theorem control_plan_address_bounds:
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops ==>
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  (!off. MEM (SOSpill off) ops ==> off < dimword(:256))
Proof
  rewrite_tac[listTheory.EVERY_MEM] >> strip_tac >> conj_tac >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem sym_reorder_restore_frame_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  !op f pending ps ops ps' initial_fmp cp fn ret srest ss ctx labs0 cs r.
  (case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
     SOME d => ([],ps)
   | NONE => (case FLOOKUP ps.ps_spilled op of
       SOME off => do_restore op ps | NONE => ([],ps))) = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  control_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cp fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> drule sym_do_restore_frame_sim_mode_conditional >>
  disch_then (mk_asm "restore") >> rpt gen_tac >>
  Cases_on `stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack` >> simp[]
  >- (Cases_on `FLOOKUP ps.ps_spilled op` >> simp[]
      >- (strip_tac >> gvs[execute_plan_def, asm_steps_def, sym_steps_mode_def,
           asmSpliceTheory.sym_steps_def, asmSpliceOwnTheory.sym_steps_own_def] >>
          conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]) >>
      ntac 5 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
      disch_then (CONJUNCTS_THEN2 (mk_asm "frame") strip_assume_tac) >>
      asm "frame" (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
      asm "restore" (drule_all o SRULE []) >> simp[]) >>
  strip_tac >> gvs[execute_plan_def, asm_steps_def, sym_steps_mode_def,
      asmSpliceTheory.sym_steps_def, asmSpliceOwnTheory.sym_steps_own_def] >>
  conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]
QED

Theorem sym_asm_plan_runs_compose_mode:
  asm_steps lo o2pc p (LENGTH (execute_plan initial_fmp ops1)) cs = AsmOK mid /\
  sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp ops1)) ss = SymOK smid /\
  mid.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops1) /\
  asm_steps lo o2pc p (LENGTH (execute_plan initial_fmp ops2)) mid = AsmOK final /\
  sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp ops2)) smid = SymOK sfinal /\
  final.as_pc = mid.as_pc + LENGTH (execute_plan initial_fmp ops2) ==>
  asm_steps lo o2pc p (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) cs = AsmOK final /\
  sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) ss = SymOK sfinal /\
  final.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (ops1 ++ ops2))
Proof
  strip_tac >>
  pure_rewrite_tac[stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
  once_rewrite_tac[stackOpSimTheory.asm_steps_add, sym_steps_mode_add] >> simp[]
QED

Theorem sym_reorder_prepare_reduce_frame_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  !spill_base pending ps1 op f reduce_ops ps2 r cp fn ret srest ctx labs0 mid smid
    initial_fmp cs ss restore_ops.
  residual_budget_wf_marked spill_base pending ps1 /\
  LENGTH pending <= LENGTH ps1.ps_stack /\
  reduce_depth_plan (LENGTH ps1.ps_stack) pending op f (LENGTH pending) ps1 =
    (reduce_ops,ps2) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) reduce_ops /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= spill_base /\ ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  control_frame lo code_ok p ctx cp fn ret srest labs0 ps1 mid smid /\
  asm_static_wf p /\
  asm_block_at p (cs.as_pc + LENGTH (execute_plan initial_fmp restore_ops))
    (execute_plan initial_fmp reduce_ops) /\
  asm_steps lo (build_offset_to_pc p) p
    (LENGTH (execute_plan initial_fmp restore_ops)) cs = AsmOK mid /\
  sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp restore_ops)) ss = SymOK smid /\
  mid.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp restore_ops) ==>
  residual_budget_wf_marked spill_base pending ps2 /\
  LENGTH pending <= LENGTH ps2.ps_stack /\
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cp fn ret srest labs0 ps2 cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))
Proof
  strip_tac >> drule sym_reduce_depth_plan_frame_sim_mode_conditional >>
  disch_then (mk_asm "reduce") >> rpt gen_tac >>
  ntac 8 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "frame") strip_assume_tac) >>
  `residual_budget_wf_marked spill_base pending ps2` by
    metis_tac[deepResidualBudgetTheory.reduce_depth_plan_residual_budget_wf_marked] >>
  `LENGTH pending <= LENGTH ps2.ps_stack` by
    metis_tac[deepResidualBudgetTheory.reduce_depth_plan_target_len_floor] >>
  `!off. MEM (SOSpill off) reduce_ops ==> off < dimword(:256)` by
    metis_tac[control_plan_address_bounds] >>
  `asm_block_at p mid.as_pc (execute_plan initial_fmp reduce_ops)` by metis_tac[] >>
  asm "frame" (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  asm "reduce" drule_all >>
  disch_then (qx_choose_then `cs'` (qx_choose_then `ss'`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (mk_asm "frame2") assume_tac))))) >>
  simp[] >> qexistsl [`cs'`, `ss'`] >>
  `asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) cs = AsmOK cs' /\
   sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) ss = SymOK ss' /\
   cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))` by
    (irule sym_asm_plan_runs_compose_mode >>
     conj_tac >- (qexists `mid` >> simp[]) >> qexists `smid` >> simp[]) >>
  asm "frame2" mp_tac >> simp[] >> metis_tac[]
QED

Theorem sym_reorder_prepare_frame_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  !base pending ps op f restore_ops ps1 dist reduce_ops ps2 r cp fn ret srest
    ctx labs0 cs ss initial_fmp.
  residual_budget_wf_marked base pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  (case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
     SOME d => ([],ps)
   | NONE => (case FLOOKUP ps.ps_spilled op of
       SOME off => do_restore op ps | NONE => ([],ps))) = (restore_ops,ps1) /\
  stack_get_unfixed_depth op f (LENGTH pending) ps1.ps_stack = SOME dist /\
  (if dist > 16 then
     reduce_depth_plan (LENGTH ps1.ps_stack) pending op f (LENGTH pending) ps1
   else ([],ps1)) = (reduce_ops,ps2) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (restore_ops ++ reduce_ops) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= base /\ ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  control_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (restore_ops ++ reduce_ops)) ==>
  residual_budget_wf_marked base pending ps2 /\
  LENGTH pending <= LENGTH ps2.ps_stack /\
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cp fn ret srest labs0 ps2 cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))
Proof
  strip_tac >>
  drule (let
    val th = sym_reorder_restore_frame_sim_mode_conditional
    val (_, body) = strip_forall (concl th)
    val (args, _) = strip_forall (snd (dest_imp body))
    val pending = List.find (fn v => fst (dest_var v) = "pending") args
  in INST_TYPE (match_type (type_of (valOf pending)) ``:operand list``) th end) >>
  disch_then (mk_asm "restore") >>
  drule sym_reorder_prepare_reduce_frame_sim_mode_conditional >>
  disch_then (mk_asm "reduce") >> rpt gen_tac >>
  ntac 10 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "frame") strip_assume_tac) >>
  rename1 `residual_budget_wf_marked spill_base pending ps` >>
  `residual_budget_wf_marked spill_base pending ps1 /\
   LENGTH pending <= LENGTH ps1.ps_stack` by
    (drule_all deepResidualBudgetTheory.reorder_restore_residual_budget_wf_marked >>
     disch_then (qspecl_then [`op`, `f`] mp_tac) >> simp[LET_THM] >> gvs[]) >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[deepResidualBudgetTheory.residual_budget_wf_marked_def] >>
  gvs[listTheory.EVERY_APPEND, stackOpSimTheory.execute_plan_append,
    stackOpSimTheory.asm_block_at_append] >>
  `!off. MEM (SORestore off) restore_ops ==> off < dimword(:256)` by
    metis_tac[control_plan_address_bounds] >>
  asm "frame" (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  asm "restore" drule >>
  disch_then drule_all >>
  disch_then (qx_choose_then `mid` (qx_choose_then `smid`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (mk_asm "frame1") assume_tac))))) >>
  qpat_x_assum `residual_budget_wf_marked spill_base pending ps` kall_tac >>
  Cases_on `dist > 16` >> gvs[]
  >- (`asm_block_at p (cs.as_pc + LENGTH (execute_plan initial_fmp restore_ops))
        (execute_plan initial_fmp reduce_ops) /\
       mid.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp restore_ops)` by
        metis_tac[arithmeticTheory.ADD_COMM] >>
      asm "frame1" (map_every assume_tac o CONJUNCTS o SRULE []) >>
      asm "reduce" (drule_all o SRULE []) >>
      pure_rewrite_tac[stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
      simp[]) >>
  `execute_plan initial_fmp [] = []` by simp[execute_plan_def] >>
  qexistsl [`mid`, `smid`] >>
  asm "frame1" (strip_assume_tac o BETA_RULE) >> simp[] >>
  conj_tac >- (qexists `m'` >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

(* Syntax for the exact pair-swap interface supplied by the scratch subject.
   This is an expanded theorem hypothesis, not a logical definition. *)

val _ = Parse.temp_overload_on ("swap_pair_run",
  ``\allow_own lo code_ok p env own.
  !d f ps ops1 ps1 ops2 ps2 r cp fn ret srest labs0 ctx cs ss initial_fmp.
  do_swap d ps = (ops1,ps1) /\ do_swap f ps1 = (ops2,ps2) /\
  d < LENGTH ps.ps_stack /\ f < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (ops1 ++ ops2) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps2.ps_alloc.sa_spill_base /\
  ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  control_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (ops1 ++ ops2)) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cp fn ret srest labs0 ps2 cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (ops1 ++ ops2))``);

Theorem sym_frame_inv_reorder_relabel_mode:
  !lo code_ok p ctx cp fn ret srest labs0 ps cs ss d f op dfg.
  control_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss /\
  d < LENGTH ps.ps_stack /\ f < LENGTH ps.ps_stack /\
  op = stack_peek d ps.ps_stack /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  operand_equiv dfg op (stack_peek f ps.ps_stack) ==>
  control_frame lo code_ok p ctx cp fn ret srest labs0
    (ps with ps_stack := stack_poke f op
      (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack)) cs ss
Proof
  metis_tac[symFrameControlFactsTheory.sym_kinds_ok_reorder_relabel]
QED

Theorem sym_reorder_place_frame_sim_mode_conditional:
  swap_pair_run allow_own lo code_ok p env own ==>
  !op f pending ps ops ps' dfg fn initial_fmp cp r ret srest labs0 ctx cs ss.
  (case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
     NONE => ([],ps)
   | SOME d =>
       if d = f then ([],ps)
       else if f < LENGTH ps.ps_stack /\ operand_equiv dfg op (stack_peek f ps.ps_stack)
       then ([],ps with ps_stack := stack_poke f op
         (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack))
       else
         (case do_swap d ps of (ops1,ps1) =>
          case do_swap f ps1 of (ops2,ps2) => (ops1 ++ ops2,ps2))) = (ops,ps') /\
  f < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  control_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cp fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  disch_then (mk_asm "swap_pair") >> rpt gen_tac >>
  ntac 11 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "frame") strip_assume_tac) >>
  rename1 `MEM r cplan.cp_regions` >>
  Cases_on `stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack`
  >- (gvs[] >> qexistsl [`cs`, `ss`] >>
      pure_rewrite_tac[execute_plan_def, listTheory.MAP, listTheory.FLAT, listTheory.LENGTH,
        asm_steps_def, sym_steps_mode_def, asmSpliceTheory.sym_steps_def,
        asmSpliceOwnTheory.sym_steps_own_def, arithmeticTheory.ADD_CLAUSES] >>
      Cases_on `allow_own` >> simp[] >> asm "frame" (mp_tac o BETA_RULE) >> simp[] >> metis_tac[]) >>
  rename1 `_ = SOME d` >> Cases_on `d = f`
  >- (gvs[] >> qexistsl [`cs`, `ss`] >>
      pure_rewrite_tac[execute_plan_def, listTheory.MAP, listTheory.FLAT, listTheory.LENGTH,
        asm_steps_def, sym_steps_mode_def, asmSpliceTheory.sym_steps_def,
        asmSpliceOwnTheory.sym_steps_own_def, arithmeticTheory.ADD_CLAUSES] >>
      Cases_on `allow_own` >> simp[] >> asm "frame" (mp_tac o BETA_RULE) >> simp[] >> metis_tac[]) >>
  Cases_on `operand_equiv dfg op (stack_peek f ps.ps_stack)`
  >- (`d < LENGTH ps.ps_stack /\ op = stack_peek d ps.ps_stack` by
        metis_tac[stackModelTheory.stack_get_unfixed_depth_props] >>
      `control_frame lo code_ok p ctx cplan fn ret srest labs0
        (ps with ps_stack := stack_poke f op
          (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack)) cs ss` by
        (irule sym_frame_inv_reorder_relabel_mode >>
         asm "frame" (mp_tac o BETA_RULE) >> simp[] >> metis_tac[]) >>
      pop_assum (mk_asm "frame2") >>
      gvs[] >> qexistsl [`cs`, `ss`] >>
      pure_rewrite_tac[execute_plan_def, listTheory.MAP, listTheory.FLAT, listTheory.LENGTH,
        asm_steps_def, sym_steps_mode_def, asmSpliceTheory.sym_steps_def,
        asmSpliceOwnTheory.sym_steps_own_def, arithmeticTheory.ADD_CLAUSES] >>
      Cases_on `allow_own` >> simp[] >>
      asm "frame2" (mp_tac o BETA_RULE) >> simp[] >> metis_tac[]) >>
  gvs[AllCaseEqs()] >>
  `d < LENGTH ps.ps_stack` by metis_tac[stackModelTheory.stack_get_unfixed_depth_bound] >>
  asm "frame" (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  asm "swap_pair" (fn th => qpat_assum `do_swap d ps = _`
    (mp_then Any mp_tac (BETA_RULE th))) >>
  disch_then (drule_all o PURE_REWRITE_RULE [listTheory.EVERY_APPEND]) >>
  simp[]
QED

(* Expression only: control_reorder_place remains defined solely in its owner. *)

val _ = Parse.temp_overload_on ("reorder_place_expr",
  ``\dfg pending op f ps.
    case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
      NONE => ([],ps)
    | SOME d => if d = f then ([],ps)
        else if f < LENGTH ps.ps_stack /\ operand_equiv dfg op (stack_peek f ps.ps_stack)
        then ([],ps with ps_stack := stack_poke f op
          (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack))
        else (case do_swap d ps of (os1,p1) =>
          case do_swap f p1 of (os2,p2) => (os1 ++ os2,p2))``);

Theorem sym_reorder_one_decompose:
  reorder_one dfg pending idx op ps = (ops,ps') ==>
  ?restore_ops ps1.
    (case stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
        (LENGTH pending) ps.ps_stack of
       NONE => (case FLOOKUP ps.ps_spilled op of NONE => ([],ps)
                  | SOME off => do_restore op ps)
     | SOME d => ([],ps)) = (restore_ops,ps1) /\
    ((stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
       (LENGTH pending) ps1.ps_stack = NONE /\ ops = restore_ops /\ ps' = ps1) \/
     ?dist reduce_ops ps2 suffix.
       stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
         (LENGTH pending) ps1.ps_stack = SOME dist /\
       (if dist > 16 then reduce_depth_plan (LENGTH ps1.ps_stack) pending op
         (LENGTH pending - (idx + 1)) (LENGTH pending) ps1
        else ([],ps1)) = (reduce_ops,ps2) /\
       ops = (restore_ops ++ reduce_ops) ++ suffix /\
       ps2.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset /\
       (case stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
          (LENGTH pending) ps2.ps_stack of
          NONE => ([],ps2)
        | SOME d => if d = LENGTH pending - (idx + 1) then ([],ps2)
          else if LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack /\
            operand_equiv dfg op (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)
          then ([], ps2 with ps_stack := stack_poke (LENGTH pending - (idx + 1)) op
            (stack_poke d (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack) ps2.ps_stack))
          else (case do_swap d ps2 of (os1,p1) =>
            case do_swap (LENGTH pending - (idx + 1)) p1 of (os2,p2) => (os1 ++ os2,p2)))
        = (suffix,ps'))
Proof
  rewrite_tac[stackPlanOpsTheory.reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rename1 `LENGTH pending = num_ops` >>
  Cases_on `stack_get_unfixed_depth op (num_ops - (idx + 1)) num_ops ps1.ps_stack` >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >>
  gvs[pairTheory.UNCURRY_pair_CASE, AllCaseEqs()] >>
  metis_tac[allocMonoTheory.do_swap_next_offset, arithmeticTheory.LESS_EQ_TRANS,
    listTheory.APPEND_ASSOC]
QED

Theorem sym_reorder_after_reduce_frame_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  swap_pair_run allow_own lo code_ok p env own ==>
  !spill_base pending ps idx op restore_ops ps1 dist reduce_ops ps2 dfg suffix ps'
    fn r cp ret srest labs0 ctx cs ss initial_fmp.
  residual_budget_wf_marked spill_base pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\ idx < LENGTH pending /\
  (case stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
      (LENGTH pending) ps.ps_stack of
     NONE => (case FLOOKUP ps.ps_spilled op of NONE => ([],ps)
                | SOME off => do_restore op ps)
   | SOME d => ([],ps)) = (restore_ops,ps1) /\
  stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
    (LENGTH pending) ps1.ps_stack = SOME dist /\
  (if dist > 16 then reduce_depth_plan (LENGTH ps1.ps_stack) pending op
     (LENGTH pending - (idx + 1)) (LENGTH pending) ps1
   else ([],ps1)) = (reduce_ops,ps2) /\
  reorder_place_expr dfg pending op (LENGTH pending - (idx + 1)) ps2 = (suffix,ps') /\
  ps2.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T)
      ((restore_ops ++ reduce_ops) ++ suffix) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= spill_base /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  control_frame lo code_ok p ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc
    (execute_plan initial_fmp ((restore_ops ++ reduce_ops) ++ suffix)) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ((restore_ops ++ reduce_ops) ++ suffix))) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp ((restore_ops ++ reduce_ops) ++ suffix))) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cp fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc +
      LENGTH (execute_plan initial_fmp ((restore_ops ++ reduce_ops) ++ suffix))
Proof
  strip_tac >> drule sym_reorder_prepare_frame_sim_mode_conditional >>
  disch_then (mk_asm "prepare") >>
  disch_then (mp_then Any (mk_asm "place") (let
    val th = sym_reorder_place_frame_sim_mode_conditional
    val (_, body) = strip_forall (concl th)
    val (args, _) = strip_forall (snd (dest_imp body))
    val pending = List.find (fn v => fst (dest_var v) = "pending") args
  in INST_TYPE (match_type (type_of (valOf pending)) ``:operand list``) th end)) >>
  rpt gen_tac >> ntac 6 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "placeeq") mp_tac) >>
  ntac 10 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "frame") strip_assume_tac) >>
  rename1 `MEM r cplan.cp_regions` >>
  `ps2.ps_alloc.sa_next_offset <= r.sr_spill_end` by decide_tac >>
  gvs[listTheory.EVERY_APPEND, stackOpSimTheory.execute_plan_append,
    stackOpSimTheory.asm_block_at_append] >>
  `asm_block_at p cs.as_pc (execute_plan initial_fmp (restore_ops ++ reduce_ops))` by
    simp[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  asm "frame" (map_every assume_tac o CONJUNCTS o SRULE []) >>
  `ps2.ps_alloc.sa_next_offset <= r.sr_spill_end` by decide_tac >>
  asm "prepare" (drule_all o SRULE [listTheory.EVERY_APPEND]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `mid` (qx_choose_then `smid`
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
        (CONJUNCTS_THEN2 (mk_asm "frame1") assume_tac))))))) >>
  `asm_block_at p mid.as_pc (execute_plan initial_fmp suffix)` by
    (fs[stackOpSimTheory.execute_plan_append] >>
     metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  `spill_alloc_layout_wf ps2.ps_alloc ps2.ps_spilled` by
    fs[deepResidualBudgetTheory.residual_budget_wf_marked_def] >>
  asm "frame1" (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  asm "placeeq" (assume_tac o SRULE []) >>
  asm "place" (qspecl_then [`op`, `LENGTH pending - (idx + 1)`, `pending`, `ps2`]
    (drule_at Any o SRULE [])) >>
  rpt (disch_then (drule_at Any)) >> simp[] >>
  disch_then (qx_choose_then `final` (qx_choose_then `sfinal`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (mk_asm "frame2") assume_tac))))) >>
  `asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ((restore_ops ++ reduce_ops) ++ suffix))) cs = AsmOK final /\
   sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp ((restore_ops ++ reduce_ops) ++ suffix))) ss = SymOK sfinal /\
   final.as_pc = cs.as_pc +
      LENGTH (execute_plan initial_fmp ((restore_ops ++ reduce_ops) ++ suffix))` by
    (irule sym_asm_plan_runs_compose_mode >>
     conj_tac >- (qexists `mid` >> simp[]) >> qexists `smid` >> simp[]) >>
  qexistsl [`final`, `sfinal`] >>
  asm "frame2" (strip_assume_tac o BETA_RULE) >>
  fs[stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
  conj_tac >- (qexists `m` >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem sym_reorder_one_frame_sim_marked_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  swap_pair_run allow_own lo code_ok p env own ==>
  !base pending ps op idx dfg ops ps' fn r cplan ret srest labs0 ctx cs ss initial_fmp.
  residual_budget_wf_marked base pending ps /\ pending_inventory_wf pending ps /\
  (!at. operand_equiv dfg op at ==> at <> dead_stack_marker) /\
  op <> dead_stack_marker /\ idx < LENGTH pending /\ MEM op pending /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  reorder_one dfg pending idx op ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  control_frame lo code_ok p ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  residual_budget_wf_marked base pending ps' /\ pending_inventory_wf pending ps' /\
  LENGTH pending <= LENGTH ps'.ps_stack /\
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >>
  drule (let
    val th = sym_reorder_restore_frame_sim_mode_conditional
    val (_, body) = strip_forall (concl th)
    val (args, _) = strip_forall (snd (dest_imp body))
    val pending = List.find (fn v => fst (dest_var v) = "pending") args
  in INST_TYPE (match_type (type_of (valOf pending)) ``:operand list``) th end) >>
  disch_then (mk_asm "restore") >>
  drule sym_reorder_after_reduce_frame_sim_mode_conditional >>
  disch_then (fn th => disch_then (mp_then Any (mk_asm "after") th)) >>
  rpt gen_tac >> ntac 16 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "frame") strip_assume_tac) >>
  rename1 `residual_budget_wf_marked spill_base pending ps` >>
  `residual_budget_wf_marked spill_base pending ps' /\
   LENGTH pending <= LENGTH ps'.ps_stack` by
    (drule_all deepResidualBudgetTheory.reorder_one_residual_budget_wf_marked >> simp[]) >>
  `pending_inventory_wf pending ps'` by
    (drule_all deepResidualBudgetTheory.reorder_one_pending_inventory_wf_marked >> simp[]) >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\ r.sr_spill_base <= spill_base` by
    (fs[deepResidualBudgetTheory.residual_budget_wf_marked_def,
      planSpillBoundsTheory.plan_slots_bounded_def,
      planSpillBoundsTheory.alloc_slots_bounded_def] >>
     metis_tac[allocMonoTheory.reorder_one_spill_base]) >>
  simp[] >>
  asm "frame" (map_every assume_tac o CONJUNCTS o SRULE []) >>
  drule sym_reorder_one_decompose >> strip_tac
  >- (gvs[] >>
      drule_all_then strip_assume_tac control_plan_address_bounds >>
      asm "frame" (map_every assume_tac o CONJUNCTS o SRULE []) >>
      asm "restore" (drule_all o SRULE []) >> simp[]) >>
  gvs[] >>
  asm "frame" (map_every assume_tac o CONJUNCTS o SRULE []) >>
  asm "after" (drule_at Any o SRULE [listTheory.APPEND_ASSOC, listTheory.EVERY_APPEND] o
    Q.INST [`dfg` |-> `dfg_build_function fn`] o SPEC_ALL) >>
  rpt (disch_then (drule_at Any)) >> simp[]
QED

Theorem sym_plan_steps_reorder_alloc:
  !items ps ops ps'.
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps = (ops,ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  Induct >- simp[foldlSimTheory.plan_steps_def] >>
  Cases >> rpt gen_tac >>
  simp[Once foldlSimTheory.plan_steps_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >>
  drule allocMonoTheory.reorder_one_spill_base >>
  drule allocMonoTheory.reorder_one_next_offset >> simp[]
QED

Theorem sym_plan_steps_reorder_cons_frame_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  swap_pair_run allow_own lo code_ok p env own ==>
  (!qs tail_ops qs' ac sy.
    residual_budget_wf_marked spill_base pending qs /\ pending_inventory_wf pending qs /\
    LENGTH pending <= LENGTH qs.ps_stack /\
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items qs = (tail_ops,qs') /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) tail_ops /\
    r.sr_spill_base <= qs'.ps_alloc.sa_spill_base /\
    qs'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    control_frame lo code_ok p ctx cplan fn ret srest labs0 qs ac sy /\
    asm_block_at p ac.as_pc (execute_plan initial_fmp tail_ops) ==>
    ?ac' sy'.
      asm_steps lo (build_offset_to_pc p) p
        (LENGTH (execute_plan initial_fmp tail_ops)) ac = AsmOK ac' /\
      sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp tail_ops)) sy = SymOK sy' /\
      control_frame lo code_ok p ctx cplan fn ret srest labs0 qs' ac' sy' /\
      ac'.as_pc = ac.as_pc + LENGTH (execute_plan initial_fmp tail_ops)) ==>
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) pending /\
  residual_budget_wf_marked spill_base pending ps /\ pending_inventory_wf pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\ idx < LENGTH pending /\ MEM op pending /\
  reorder_one dfg pending idx op ps = (step_ops,ps1) /\
  plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps1 = (rest_ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (step_ops ++ rest_ops) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  control_frame lo code_ok p ctx cplan fn ret srest labs0 ps cs ss /\ asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (step_ops ++ rest_ops)) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (step_ops ++ rest_ops))) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp (step_ops ++ rest_ops))) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (step_ops ++ rest_ops))
Proof
  strip_tac >> drule sym_reorder_one_frame_sim_marked_mode_conditional >>
  disch_then (fn th => disch_then (mp_then Any (mk_asm "one") th)) >>
  disch_then (mk_asm "tail") >>
  ntac 16 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "frame") strip_assume_tac) >>
  gvs[listTheory.EVERY_APPEND, stackOpSimTheory.execute_plan_append,
      stackOpSimTheory.asm_block_at_append] >>
  drule_all sym_plan_steps_reorder_alloc >> strip_tac >>
  `r.sr_spill_base <= ps1.ps_alloc.sa_spill_base /\
   ps1.ps_alloc.sa_next_offset <= r.sr_spill_end` by simp[] >>
  `op <> dead_stack_marker /\
   (!at. operand_equiv (dfg_build_function fn) op at ==> at <> dead_stack_marker)` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `!at. operand_equiv _ op at ==> _` (assume_tac o SRULE []) >>
  asm "frame" (map_every assume_tac o CONJUNCTS o SRULE []) >>
  asm "one" (drule_at Any o SRULE [] o
    Q.INST [`dfg` |-> `dfg_build_function fn`] o SPEC_ALL) >>
  rpt (disch_then (drule_at Any)) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `mid` (qx_choose_then `smid`
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
        (CONJUNCTS_THEN2 (mk_asm "frame1") assume_tac)))))))) >>
  `asm_block_at p mid.as_pc (execute_plan initial_fmp rest_ops)` by simp[] >>
  asm "frame1" (map_every assume_tac o CONJUNCTS o SRULE []) >>
  asm "tail" (drule_all o SRULE []) >>
  disch_then (qx_choose_then `final` (qx_choose_then `sfinal`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (mk_asm "frame2") assume_tac))))) >>
  `asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (step_ops ++ rest_ops))) cs = AsmOK final /\
   sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp (step_ops ++ rest_ops))) ss = SymOK sfinal /\
   final.as_pc = cs.as_pc +
      LENGTH (execute_plan initial_fmp (step_ops ++ rest_ops))` by
    (irule sym_asm_plan_runs_compose_mode >>
     conj_tac >- (qexists `mid` >> simp[]) >> qexists `smid` >> simp[]) >>
  qexistsl [`final`, `sfinal`] >>
  asm "frame2" (strip_assume_tac o BETA_RULE) >>
  fs[stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
  conj_tac >- (qexists `m` >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem sym_plan_steps_reorder_frame_sim_marked_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  swap_pair_run allow_own lo code_ok p env own ==>
  !items ps ops ps' cs ss.
    EVERY (\(idx,op). idx < LENGTH pending /\ MEM op pending) items /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) pending /\
    residual_budget_wf_marked spill_base pending ps /\ pending_inventory_wf pending ps /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps = (ops,ps') /\
    dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    control_frame lo code_ok p ctx cplan fn ret srest labs0 ps cs ss /\
    asm_static_wf p /\
    asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
    ?cs' ss'.
      asm_steps lo (build_offset_to_pc p) p
        (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
      sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
      control_frame lo code_ok p ctx cplan fn ret srest labs0 ps' cs' ss' /\
      cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> drule sym_plan_steps_reorder_cons_frame_sim_mode_conditional >>
  disch_then (fn th => disch_then (mp_then Any (mk_asm "cons") th)) >>
  Induct
  >- (simp[foldlSimTheory.plan_steps_def, execute_plan_def, asm_steps_def,
       sym_steps_mode_def, asmSpliceTheory.sym_steps_def, asmSpliceOwnTheory.sym_steps_own_def] >>
      rpt strip_tac >> first_x_assum drule >> simp[]) >>
  rpt gen_tac >> PairCases_on `h` >>
  ntac 14 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "frame") strip_assume_tac) >>
  drule reorderPreparationPropsTheory.plan_steps_cons_result >> strip_tac >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  asm "frame" (map_every assume_tac o CONJUNCTS o SRULE []) >>
  asm "cons" irule >>
  simp[listTheory.EVERY_DEF] >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qexistsl [`h0`, `items`, `h1`, `pending`, `ps`, `ps1`, `r`, `spill_base`] >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[]
QED

Theorem sym_reorder_prepass_frame_sim_mode_conditional[local]:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  reorder_prepare_plan pending ps = (ops,ps') /\
  plan_slots_bounded spill_base ps /\ spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= spill_base /\ ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  (!off. MEM (SOSpill off) ops ==> off < dimword(:256)) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  control_frame lo code_ok p ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >>
  drule sym_do_restore_frame_sim_mode_conditional >>
  disch_then (mk_asm "restore") >>
  drule sym_reduce_depth_plan_frame_sim_width >>
  disch_then (mk_asm "reduce") >>
  ntac 9 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "entry") strip_assume_tac) >>
  asm "entry" (strip_assume_tac o BETA_RULE) >>
  qspecl_then [`pending`, `ps`, `ops`, `ps'`,
    `\st trace post.
      st.ps_alloc.sa_next_offset <= post.ps_alloc.sa_next_offset /\
      (plan_slots_bounded spill_base st /\ spill_alloc_layout_wf st.ps_alloc st.ps_spilled ==>
       plan_slots_bounded spill_base post /\ spill_alloc_layout_wf post.ps_alloc post.ps_spilled) /\
      (!ac sy.
        post.ps_alloc.sa_next_offset <= r.sr_spill_end /\
        plan_slots_bounded spill_base st /\ spill_alloc_layout_wf st.ps_alloc st.ps_spilled /\
        (!off. MEM (SOSpill off) trace ==> off < dimword(:256)) /\
        (!off. MEM (SORestore off) trace ==> off < dimword(:256)) /\
        control_frame lo code_ok p ctx cplan fn ret srest labs0 st ac sy /\
        asm_block_at p ac.as_pc (execute_plan initial_fmp trace) ==>
        ?ac' sy'.
          asm_steps lo (build_offset_to_pc p) p
            (LENGTH (execute_plan initial_fmp trace)) ac = AsmOK ac' /\
          sym_steps_mode allow_own p env own
            (LENGTH (execute_plan initial_fmp trace)) sy = SymOK sy' /\
          control_frame lo code_ok p ctx cplan fn ret srest labs0 post ac' sy' /\
          ac'.as_pc = ac.as_pc + LENGTH (execute_plan initial_fmp trace))`]
    (mp_tac o BETA_RULE) reorder_prepare_trace_relation >>
  impl_tac
  >- (rpt conj_tac
      >- (simp[execute_plan_def, asm_steps_def, sym_steps_mode_def,
               asmSpliceTheory.sym_steps_def, asmSpliceOwnTheory.sym_steps_own_def] >>
          metis_tac[])
      >- (rpt gen_tac >> strip_tac >>
          rpt conj_tac
          >- metis_tac[arithmeticTheory.LESS_EQ_TRANS]
          >- metis_tac[] >>
          rpt gen_tac >> strip_tac >>
          gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append,
              listTheory.MEM_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
          `mid.ps_alloc.sa_next_offset <= r.sr_spill_end` by decide_tac >>
          qpat_x_assum `!ac' sy'. _ /\
            asm_block_at p ac'.as_pc (execute_plan initial_fmp first_ops) ==> _`
            (qspecl_then [`ac`, `sy`] mp_tac) >>
          simp[] >> impl_tac
          >- (conj_tac >- (qexists_tac `m'` >> simp[]) >>
              rpt strip_tac >>
              qpat_assum `!i l d j. FLOOKUP sy.sym_mem_labels i = SOME (l,d,j) ==> _`
                (drule_then strip_assume_tac) >> simp[]) >>
          disch_then (qx_choose_then `ac1` (qx_choose_then `sy1` strip_assume_tac)) >>
          qpat_x_assum `!ac' sy'. _ /\
            asm_block_at p ac'.as_pc (execute_plan initial_fmp rest_ops) ==> _`
            (qspecl_then [`ac1`, `sy1`] mp_tac) >>
          simp[] >> impl_tac
          >- (conj_tac >- (qexists_tac `m''` >> simp[]) >>
              rpt strip_tac >>
              qpat_assum `!i l d j. FLOOKUP sy1.sym_mem_labels i = SOME (l,d,j) ==> _`
                (drule_then strip_assume_tac) >> simp[]) >>
          disch_then (qx_choose_then `ac2` (qx_choose_then `sy2` strip_assume_tac)) >>
          qexistsl_tac [`ac2`, `sy2`] >>
          simp[stackOpSimTheory.asm_steps_add, sym_steps_mode_add] >>
          conj_tac
          >- (rename1 `sy2.sym_base = ac2 with
                <|as_stack := []; as_memory := witness; as_code := []|>` >>
              qexists_tac `witness` >> simp[]) >>
          rpt strip_tac >>
          qpat_assum `!i l d j. FLOOKUP sy2.sym_mem_labels i = SOME (l,d,j) ==> _`
            (drule_then strip_assume_tac) >> simp[])
      >- (rpt gen_tac >> strip_tac >>
          rpt conj_tac
          >- metis_tac[do_restore_next_offset]
          >- metis_tac[do_restore_slots_bounded, spillPlanSimTheory.do_restore_layout_wf] >>
          rpt gen_tac >> strip_tac >>
          asm "restore" (qspecl_then [`cplan`, `op`, `st`, `step_ops`,
            `finish'`, `initial_fmp`, `fn`, `ret`, `srest`, `sy`, `ctx`,
            `labs0`, `ac`, `r`] (mp_tac o BETA_RULE)) >>
          impl_tac
          >- (simp[] >> conj_tac >- (qexists_tac `m'` >> simp[]) >>
              rpt strip_tac >>
              qpat_assum `!i l d j. FLOOKUP sy.sym_mem_labels i = SOME (l,d,j) ==> _`
                (drule_then strip_assume_tac) >> simp[]) >>
          disch_then ACCEPT_TAC)
      >- (rpt gen_tac >> strip_tac >>
          rpt conj_tac
          >- metis_tac[reduce_depth_plan_next_offset]
          >- metis_tac[reduce_depth_plan_slots_bounded, reorderSimTheory.reduce_depth_plan_layout_wf,
                       pairTheory.SND] >>
          rpt gen_tac >> strip_tac >>
          asm "reduce" (qspecl_then [`LENGTH st.ps_stack - LENGTH pending`,
            `pending`, `op`, `0`, `0`, `st`, `step_ops`, `finish'`,
            `spill_base`, `initial_fmp`, `cplan`, `fn`, `ret`, `srest`,
            `sy`, `ctx`, `labs0`, `ac`, `r`] (mp_tac o BETA_RULE)) >>
          impl_tac
          >- (simp[] >> conj_tac >- (qexists_tac `m'` >> simp[]) >>
              rpt strip_tac >>
              qpat_assum `!i l d j. FLOOKUP sy.sym_mem_labels i = SOME (l,d,j) ==> _`
                (drule_then strip_assume_tac) >> simp[]) >>
          disch_then ACCEPT_TAC)
      >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`cs`, `ss`] mp_tac o CONJUNCT2 o CONJUNCT2) >>
  impl_tac
  >- (simp[] >> conj_tac >- (qexists_tac `m` >> simp[]) >>
      rpt strip_tac >>
      qpat_assum `!i l d j. FLOOKUP ss.sym_mem_labels i = SOME (l,d,j) ==> _`
        (drule_then strip_assume_tac) >> simp[]) >>
  disch_then ACCEPT_TAC
QED

Theorem sym_reorder_plan_frame_sim_marked_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  swap_pair_run allow_own lo code_ok p env own ==>
  !spill_base.
    residual_budget_wf_marked spill_base pending ps /\ pending_inventory_wf pending ps /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) pending /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    reorder_plan dfg pending ps = (ops,ps') /\
    dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    control_frame lo code_ok p ctx cplan fn ret srest labs0 ps cs ss /\
    asm_static_wf p /\
    asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
    ?cs' ss'.
      asm_steps lo (build_offset_to_pc p) p
        (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
      sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
      control_frame lo code_ok p ctx cplan fn ret srest labs0 ps' cs' ss' /\
      cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  disch_then (mk_asm "bridge") >>
  disch_then (mk_asm "swap") >>
  gen_tac >> strip_tac >>
  drule reorder_plan_split >> strip_tac >>
  rename1 `reorder_prepare_plan pending ps = (prep,prepared)` >>
  drule sym_plan_steps_reorder_alloc >> strip_tac >>
  `r.sr_spill_base <= spill_base` by
    (drule reorder_plan_spill_base >>
     fs[residual_budget_wf_marked_def, plan_slots_bounded_def,
        alloc_slots_bounded_def]) >>
  drule_all reorder_prepare_residual_budget_wf_marked >> strip_tac >>
  `plan_slots_bounded spill_base ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[residual_budget_wf_marked_def] >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append,
      listTheory.EVERY_APPEND] >>
  drule control_plan_address_bounds >> strip_tac >>
  `(!off. MEM (SOSpill off) prep ==> off < dimword(:256)) /\
   (!off. MEM (SORestore off) prep ==> off < dimword(:256))` by
    metis_tac[control_plan_address_bounds] >>
  `prepared.ps_alloc.sa_next_offset <= r.sr_spill_end` by decide_tac >>
  asm "bridge" (mp_tac o MP
    (Q.INST [`ops` |-> `prep`, `ps'` |-> `prepared`]
      sym_reorder_prepass_frame_sim_mode_conditional)) >>
  impl_tac
  >- (simp[] >> conj_tac >- (qexists_tac `m` >> simp[]) >>
      rpt strip_tac >>
      qpat_assum `!i l d j. FLOOKUP ss.sym_mem_labels i = SOME (l,d,j) ==> _`
        (drule_then strip_assume_tac) >> simp[]) >>
  disch_then (qx_choose_then `cs1` (qx_choose_then `ss1` strip_assume_tac)) >>
  `EVERY (\(idx,op). idx < LENGTH pending /\ MEM op pending)
    (MAPi (\i op. (i,op)) pending)` by
    (simp[listTheory.EVERY_MEM, pairTheory.FORALL_PROD, indexedListsTheory.MEM_MAPi] >>
     rpt strip_tac >> gvs[] >> metis_tac[listTheory.EL_MEM]) >>
  `asm_block_at p cs1.as_pc (execute_plan initial_fmp rest)` by simp[] >>
  asm "bridge" (mp_tac o MP
    (Q.INST [`dfg` |-> `dfg_build_function fn`]
      sym_plan_steps_reorder_frame_sim_marked_mode_conditional)) >>
  asm "swap" (fn th => disch_then (mp_tac o C MP th)) >>
  disch_then (qspecl_then [`MAPi (\i op. (i,op)) pending`, `prepared`,
    `rest`, `ps'`, `cs1`, `ss1`] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac >- (qexists_tac `m'` >> simp[]) >>
      rpt strip_tac >>
      qpat_assum `!i l d j. FLOOKUP ss1.sym_mem_labels i = SOME (l,d,j) ==> _`
        (drule_then strip_assume_tac) >> simp[]) >>
  disch_then (qx_choose_then `cs2` (qx_choose_then `ss2` strip_assume_tac)) >>
  qexistsl_tac [`cs2`, `ss2`] >>
  simp[stackOpSimTheory.asm_steps_add, sym_steps_mode_add] >>
  conj_tac >- (qexists_tac `m''` >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!i l d j. FLOOKUP ss2.sym_mem_labels i = SOME (l,d,j) ==> _`
    (drule_then strip_assume_tac) >> simp[]
QED

Theorem sym_restore_spilled_cons_frame_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  (!qs tail_ops qs' ac sy.
    restore_spilled_plan targets qs = (tail_ops,qs') /\
    spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled /\
    (!off. MEM (SORestore off) tail_ops ==> off < dimword(:256)) /\
    control_frame lo code_ok p ctx cplan fn ret srest labs0 qs ac sy /\
    asm_block_at p ac.as_pc (execute_plan initial_fmp tail_ops) ==>
    ?ac' sy'.
      asm_steps lo (build_offset_to_pc p) p
        (LENGTH (execute_plan initial_fmp tail_ops)) ac = AsmOK ac' /\
      sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp tail_ops)) sy = SymOK sy' /\
      control_frame lo code_ok p ctx cplan fn ret srest labs0 qs' ac' sy' /\
      ac'.as_pc = ac.as_pc + LENGTH (execute_plan initial_fmp tail_ops)) /\
  do_restore op ps = (ops1,ps1) /\
  restore_spilled_plan targets ps1 = (ops2,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SORestore off) ops1 \/ MEM (SORestore off) ops2 ==> off < dimword(:256)) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  control_frame lo code_ok p ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (ops1 ++ ops2)) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (ops1 ++ ops2))
Proof
  strip_tac >> drule sym_do_restore_frame_sim_mode_conditional >>
  disch_then (mk_asm "restore") >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "tail") mp_tac) >>
  ntac 6 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "frame") strip_assume_tac) >>
  drule_all_then strip_assume_tac spillPlanSimTheory.do_restore_layout_wf >>
  gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  `!off. MEM (SORestore off) ops1 ==> off < dimword(:256)` by metis_tac[] >>
  `!off. MEM (SORestore off) ops2 ==> off < dimword(:256)` by metis_tac[] >>
  asm "frame" (map_every assume_tac o CONJUNCTS o SRULE []) >>
  asm "restore" (drule_all o SRULE []) >>
  disch_then (qx_choose_then `mid` (qx_choose_then `smid`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (mk_asm "frame1") assume_tac))))) >>
  `asm_block_at p mid.as_pc (execute_plan initial_fmp ops2)` by simp[] >>
  asm "frame1" (map_every assume_tac o CONJUNCTS o SRULE []) >>
  asm "tail" (drule_all o SRULE []) >>
  disch_then (qx_choose_then `final` (qx_choose_then `sfinal`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (mk_asm "frame2") assume_tac))))) >>
  `asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) cs = AsmOK final /\
   sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) ss = SymOK sfinal /\
   final.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (ops1 ++ ops2))` by
    (irule sym_asm_plan_runs_compose_mode >>
     conj_tac >- (qexists `mid` >> simp[]) >> qexists `smid` >> simp[]) >>
  qexistsl [`final`, `sfinal`] >>
  asm "frame2" (strip_assume_tac o BETA_RULE) >>
  fs[stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
  conj_tac >- (qexists `m` >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem sym_restore_spilled_plan_frame_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  !targets ps ops ps' cs ss.
  restore_spilled_plan targets ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  control_frame lo code_ok p ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> drule sym_restore_spilled_cons_frame_sim_mode_conditional >>
  disch_then (mk_asm "cons") >> Induct
  >- (simp[stackPlanOpsTheory.restore_spilled_plan_def, execute_plan_def, asm_steps_def,
       sym_steps_mode_def, asmSpliceTheory.sym_steps_def, asmSpliceOwnTheory.sym_steps_own_def] >>
      rpt strip_tac >> first_x_assum drule >> simp[]) >>
  rpt gen_tac >>
  simp[stackPlanOpsTheory.restore_spilled_plan_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  ntac 5 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "frame") strip_assume_tac) >>
  gvs[] >>
  asm "frame" (map_every assume_tac o CONJUNCTS o SRULE []) >>
  asm "cons" (drule_at Any o SRULE []) >>
  rpt (disch_then (drule_at Any)) >> simp[] >>
  impl_tac >- (rpt gen_tac >> disch_tac >>
    qpat_x_assum `!qs ops qs' ac sy. restore_spilled_plan _ _ = _ /\ _ ==> _` irule >>
    gvs[] >>
    conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
    conj_tac >- (qexists `m'` >> simp[]) >> qexists `qs` >> simp[]) >> simp[]
QED

Theorem sym_jmp_prepare_frame_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') ==>
  swap_pair_run allow_own lo code_ok p env own ==>
  !base.
  generated_plan_state_wf_marked base ps /\
  pending_inventory_wf pending ps /\
  restore_spilled_plan pending ps = (restore_ops,prepared) /\
  reorder_plan dfg pending prepared = (reorder_ops,arranged) /\
  (!off. MEM (SORestore off) restore_ops ==> off < dimword(:256)) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) reorder_ops /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) pending /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  control_frame lo code_ok p ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (restore_ops ++ reorder_ops)) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reorder_ops))) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reorder_ops))) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cplan fn ret srest labs0 arranged cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (restore_ops ++ reorder_ops))
Proof
  strip_tac >> drule sym_restore_spilled_plan_frame_sim_mode_conditional >>
  disch_then (mk_asm "restore") >>
  drule sym_reorder_plan_frame_sim_marked_mode_conditional >>
  disch_then (fn th => disch_then (mp_then Any (mk_asm "reorder") th)) >>
  gen_tac >> ntac 14 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "frame") strip_assume_tac) >>
  drule_all_then strip_assume_tac restore_spilled_plan_generated_facts_marked >>
  `pending_inventory_wf pending prepared` by metis_tac[] >>
  drule_all_then strip_assume_tac fnPlanLineageInventoryTheory.restore_spilled_plan_length_floor >>
  drule_all_then strip_assume_tac deepResidualSimTheory.generated_plan_state_wf_marked_residual_nil >>
  drule_then (qspec_then `pending` assume_tac) residual_budget_wf_marked_nil_pending >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[fnPlanPrefixTheory.generated_plan_state_wf_marked_def] >>
  gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  asm "frame" (map_every assume_tac o CONJUNCTS o SRULE []) >>
  asm "restore" (drule_all o SRULE []) >>
  disch_then (qx_choose_then `mid` (qx_choose_then `smid`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (mk_asm "frame1") assume_tac))))) >>
  `asm_block_at p mid.as_pc (execute_plan initial_fmp reorder_ops)` by simp[] >>
  qpat_x_assum `residual_budget_wf_marked _ [] prepared` kall_tac >>
  `pending_inventory_wf pending prepared` by metis_tac[] >>
  asm "frame1" (map_every assume_tac o CONJUNCTS o SRULE []) >>
  asm "reorder" (drule_at Any o SRULE [] o
    Q.INST [`dfg` |-> `dfg_build_function fn`] o SPEC_ALL) >>
  rpt (disch_then (drule_at Any)) >>
  disch_then (qx_choose_then `final` (qx_choose_then `sfinal`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (mk_asm "frame2") assume_tac))))) >>
  `asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reorder_ops))) cs = AsmOK final /\
   sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reorder_ops))) ss = SymOK sfinal /\
   final.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (restore_ops ++ reorder_ops))` by
    (irule sym_asm_plan_runs_compose_mode >>
     conj_tac >- (qexists `mid` >> simp[]) >> qexists `smid` >> simp[]) >>
  qexistsl [`final`, `sfinal`] >>
  asm "frame2" (strip_assume_tac o BETA_RULE) >>
  fs[stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
  conj_tac >- (qexists `m` >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED
