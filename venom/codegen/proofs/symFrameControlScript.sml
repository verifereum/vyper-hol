(*
 * Leaf B of the label-discipline proof: the control and terminal steps of
 * a block, run on the symbolic machine without SymBad.  Each statement is
 * codegen's own deep-tier lemma with the symbolic premises and conclusions
 * added, over the same n steps: a step that continues keeps the symbolic
 * frame invariant, a RET leaves the returned values as words above the
 * caller's symbolic stack, and a halt or abort ends the symbolic run.
 *
 * A jump's target is a code label of the program (MEM (AsmLabel l) prog):
 * the symbolic machine jumps only to code labels.
 *
 * TOP-LEVEL:
 *   sym_jmp_frame_sim_deep            - JMP
 *   sym_jnz_frame_sim_deep            - JNZ
 *   sym_ret_frame_sim_deep            - RET
 *   sym_halt_frame_sim_deep           - an instruction that halts
 *   sym_abort_frame_sim_deep          - an instruction that aborts
 *   sym_gas_frame_sim_deep            - GAS
 *   sym_revert_forward_frame_sim_deep - a forwarded revert
 *)
Theory symFrameControl
Ancestors
  codegenSymRel fnFrameDeepJmp fnFrameDeepJnz fnFrameDeepRet fnFrameDeepHalt
  fnFrameDeepAbort fnFrameDeepGas fnFrameStepsRevertForwardDeep asmSymBridge
  asmSymSem frameRel contextCodegenRel codegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec asmSem venomExecSemantics venomState venomInst
  dfgDefs symPlannerSim symShuffleSim

(* Pointwise kind equivalence transports a typed symbolic stack. *)
Theorem list_rel_op_kind_transport:
  !xs vals ys fn ret.
    LIST_REL (op_kind_ok fn ret) xs vals /\
    LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=>
                          op_kind_ok fn ret y sv) xs ys ==>
    LIST_REL (op_kind_ok fn ret) ys vals
Proof
  Induct >> Cases_on `vals` >> Cases_on `ys` >> simp[] >>
  metis_tac[]
QED

Theorem operand_equiv_op_kind:
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  operand_equiv dfg x y ==>
  (op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
Proof
  simp[operand_equiv_def] >>
  metis_tac[op_kind_ok_normalize_operand]
QED

Theorem stack_poke_op_kind_equiv:
  d < LENGTH xs /\
  (!sv. op_kind_ok fn ret (stack_peek d xs) sv <=>
        op_kind_ok fn ret op sv) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=>
                       op_kind_ok fn ret y sv) xs (stack_poke d op xs)
Proof
  rw[listTheory.LIST_REL_EL_EQN, stackModelTheory.stack_poke_def,
     listTheory.EL_LUPDATE] >>
  gvs[stackModelTheory.stack_peek_def] >> metis_tac[]
QED

Theorem stack_exchange_op_kind_equiv:
  d < LENGTH xs /\ f < LENGTH xs /\
  op = stack_peek d xs /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  operand_equiv dfg op (stack_peek f xs) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=>
                       op_kind_ok fn ret y sv)
    xs (stack_poke f op (stack_poke d (stack_peek f xs) xs))
Proof
  strip_tac >> drule_all operand_equiv_op_kind >> strip_tac >>
  rw[listTheory.LIST_REL_EL_EQN, stackModelTheory.stack_poke_def,
     listTheory.EL_LUPDATE] >>
  gvs[stackModelTheory.stack_peek_def] >> metis_tac[]
QED

Theorem sym_kinds_ok_stack_transport:
  !cp fn ret srest ps ss xs.
  sym_kinds_ok cp fn ret srest ps ss /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=>
                       op_kind_ok fn ret y sv) ps.ps_stack xs ==>
  sym_kinds_ok cp fn ret srest (ps with ps_stack := xs) ss
Proof
  rw[sym_kinds_ok_def] >>
  qexists_tac `top` >> simp[] >>
  irule list_rel_op_kind_transport >> goal_assum (drule_at Any) >>
  simp[]
QED

Theorem sym_kinds_ok_reorder_relabel:
  !cp fn ret srest ps ss d f op dfg.
  sym_kinds_ok cp fn ret srest ps ss /\
  d < LENGTH ps.ps_stack /\ f < LENGTH ps.ps_stack /\
  op = stack_peek d ps.ps_stack /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  operand_equiv dfg op (stack_peek f ps.ps_stack) ==>
  sym_kinds_ok cp fn ret srest
    (ps with ps_stack := stack_poke f op
      (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack)) ss
Proof
  rpt gen_tac >> strip_tac >> irule sym_kinds_ok_stack_transport >>
  goal_assum (drule_at Any) >> irule stack_exchange_op_kind_equiv >>
  goal_assum (drule_at Any) >> gvs[]
QED

(* Restore interpretation agrees on the fields observed by symbolic kinds. *)
Theorem restore_spilled_plan_ss_align:
  !targets ps ops ps'.
    restore_spilled_plan targets ps = (ops, ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    !lo. (apply_prefix_ops initial_fmp lo ops ps).ps_stack = ps'.ps_stack /\
         (apply_prefix_ops initial_fmp lo ops ps).ps_spilled = ps'.ps_spilled
Proof
  Induct >> simp[stackPlanOpsTheory.restore_spilled_plan_def,
                 planAlignTheory.apply_prefix_ops_nil] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule doSwapSimTheory.spill_alloc_layout_wf_spilled_separated >> strip_tac >>
  drule_all generatedPrefixSimTheory.do_restore_layout_wf >> strip_tac >>
  drule_all planAlignTheory.do_restore_ss_align >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  gvs[] >> gen_tac >>
  simp[planAlignTheory.apply_prefix_ops_append] >>
  qspecl_then [`ops2`, `lo`] mp_tac
    reorderSimTheory.apply_prefix_ops_ext_stack_spilled >>
  metis_tac[]
QED

(* Projection and exact-stack extraction use sym_kinds_ok_def directly:
 * theorem search checks that simp[sym_kinds_ok_def] closes both interfaces.
 * Releasing spills additionally needs lookup inclusion and stack preservation.
 *)
Theorem sym_frame_inv_release_dead_spills:
  !p env ctx cp fn ret srest labs0 ps cs ss nl.
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss ==>
  sym_frame_inv p env ctx cp fn ret srest labs0
    (release_dead_spills nl ps) cs ss
Proof
  rw[sym_frame_inv_def, sym_kinds_ok_def,
     fnPlanPrefixTheory.release_dead_spills_stack] >>
  metis_tac[fnFrameStepsRevertForwardTheory.rf_release_spill_lookup]
QED

(* Reassemble the frame boundary after a region-local symbolic segment. *)
Theorem sym_frame_inv_region_transfer:
  !p env ctx cp fn ret srest labs0 ps cs ss r cs' ss' ps'.
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  asm_sym_rel p env cs' ss' /\
  sym_kinds_ok cp fn ret srest ps' ss' /\
  (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
       FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
  sym_frame_inv p env ctx cp fn ret srest labs0 ps' cs' ss'
Proof
  rw[sym_frame_inv_def] >>
  `~(r.sr_spill_base <= b /\ b < r.sr_spill_end)` by
    (strip_tac >> fs[closure_spill_byte_def] >>
     metis_tac[fcgDefsTheory.fcg_path_def, relationTheory.RTC_REFL]) >>
  metis_tac[]
QED

(* The symbolic prefix and the concrete endpoint share an explicit count. *)
Theorem sym_selected_prefix_frame_sim_marked:
  !opc operands nl ps iops prepared dfg selected rops arranged spillbase
    fn r cp p env ret srest labs0 ctx cs ss initial_fmp.
  opc <> INVOKE /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spillbase ps /\ residual_budget_wf_marked spillbase [] ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (iops ++ rops)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (iops ++ rops))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (iops ++ rops))) ss =
      SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 arranged cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `MEM r cplan.cp_regions` >>
  `asm_sym_rel p env cs ss /\ sym_kinds_ok cplan fn ret srest ps ss` by
    fs[sym_frame_inv_def] >>
  `ss.sym_base.as_pc = cs.as_pc` by metis_tac[asm_sym_rel_pc] >>
  `asm_block_at p ss.sym_base.as_pc
     (execute_plan initial_fmp (iops ++ rops))` by simp[] >>
  drule_all sym_selected_prefix_sim_marked >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  qexistsl_tac [`cs'`, `ss'`] >> simp[] >>
  conj_tac
  >- (irule sym_frame_inv_region_transfer >> goal_assum (drule_at Any) >>
      metis_tac[]) >>
  drule_all asm_sym_rel_pc >> simp[]
QED

(* Region-local shuffles expose the same frame boundary as input preparation. *)
Theorem sym_prefix_ops_frame_sim:
  !ops initial_fmp p env cp fn ret srest ps ss ctx labs0 cs r.
  prefix_wf (SND (compute_label_offsets p)) (LENGTH ps.ps_stack) ops /\
  prefix_spill_wf initial_fmp (SND (compute_label_offsets p)) ops ps /\
  EVERY is_prefix_op ops /\
  EVERY (\op. !l d. op <> SOPushOfst l d) ops /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    (r.sr_spill_base <= b /\ b < r.sr_spill_end) /\
    context_spill_byte cp b) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0
      (apply_prefix_ops initial_fmp (SND (compute_label_offsets p)) ops ps)
      cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  `asm_sym_rel p env cs ss` by fs[sym_frame_inv_def] >>
  rename1 `MEM r cplan.cp_regions` >>
  `sym_kinds_ok cplan fn ret srest ps ss` by fs[sym_frame_inv_def] >>
  `ss.sym_base.as_pc = cs.as_pc` by metis_tac[asm_sym_rel_pc] >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops)` by simp[] >>
  drule_all (BETA_RULE (Q.INST
    [`R` |-> `\b. r.sr_spill_base <= b /\ b < r.sr_spill_end`]
    (SPEC_ALL sym_prefix_ops_sim))) >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  qexistsl_tac [`cs'`, `ss'`] >> simp[] >>
  conj_tac
  >- (irule sym_frame_inv_region_transfer >> goal_assum (drule_at Any) >>
      metis_tac[]) >>
  drule_all asm_sym_rel_pc >> simp[]
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

(* A physical restore exposes kinds at the actual planner result. *)
Theorem sym_do_restore_frame_sim:
  !cp op ps ops ps' initial_fmp p env fn ret srest ss ctx labs0 cs r.
  do_restore op ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all do_restore_symbolic_prefix_facts >>
  disch_then (qspecl_then [`initial_fmp`, `SND (compute_label_offsets p)`]
    strip_assume_tac) >>
  drule doSwapSimTheory.spill_alloc_layout_wf_spilled_separated >> strip_tac >>
  drule_all planAlignTheory.do_restore_ss_align >> strip_tac >>
  rename1 `MEM r cplan.cp_regions` >>
  `!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    (r.sr_spill_base <= b /\ b < r.sr_spill_end) /\
    context_spill_byte cplan b` by simp[] >>
  drule_all sym_prefix_ops_frame_sim >> strip_tac >>
  qexistsl_tac [`cs'`, `ss'`] >>
  gvs[sym_frame_inv_def, sym_kinds_ok_def]
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

Theorem sym_do_swap_shallow_frame_sim:
  !cp d ps ops ps' initial_fmp p env fn ret srest ss ctx labs0 cs r.
  do_swap d ps = (ops,ps') /\ d <= 16 /\ d < LENGTH ps.ps_stack /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all do_swap_shallow_symbolic_prefix_facts >>
  disch_then (qspecl_then [`initial_fmp`, `SND (compute_label_offsets p)`]
    strip_assume_tac) >>
  rename1 `MEM r cplan.cp_regions` >>
  `!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    (r.sr_spill_base <= b /\ b < r.sr_spill_end) /\
    context_spill_byte cplan b` by simp[] >>
  drule_all planAlignTheory.do_swap_align >> strip_tac >>
  drule_all sym_prefix_ops_frame_sim >> strip_tac >>
  qexistsl_tac [`cs'`, `ss'`] >> gvs[]
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

Theorem sym_do_spill_at_frame_sim:
  !cp d ps ops ps' initial_fmp p env fn ret srest ss ctx labs0 cs r base.
  do_spill_at d ps = (ops,ps') /\ d <= 16 /\ d < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded base ps /\
  (!off. MEM (SOSpill off) ops ==> off < dimword(:256)) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= base /\ ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (Q.ISPEC `SND (compute_label_offsets p)`
    (Q.GEN `lo` (SPEC_ALL do_spill_at_symbolic_prefix_shape))) >>
  disch_then (qspec_then `p` strip_assume_tac) >>
  drule_all reorderSimTheory.do_spill_at_prefix_spill_wf >>
  disch_then (qspecl_then [`initial_fmp`, `SND (compute_label_offsets p)`]
    strip_assume_tac) >>
  drule_all planSpillBoundsTheory.do_spill_at_slots_bounded >> strip_tac >>
  rename1 `MEM r cplan.cp_regions` >>
  `!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    (r.sr_spill_base <= b /\ b < r.sr_spill_end) /\
    context_spill_byte cplan b` by
    (fs[planSpillBoundsTheory.ops_spill_bounded_def, in_mem_range_def,
        contextCodegenRelTheory.context_spill_byte_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  drule_all sym_prefix_ops_frame_sim >> strip_tac >>
  qexistsl_tac [`cs'`, `ss'`] >> simp[] >>
  drule reorderSimTheory.do_spill_at_relevant_align_layout >>
  disch_then (qspecl_then [`initial_fmp`, `d`, `SND (compute_label_offsets p)`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `sym_frame_inv _ _ _ _ _ _ _ _ (apply_prefix_ops _ _ _ _) _ _`
    mp_tac >> pure_rewrite_tac[sym_frame_inv_def, sym_kinds_ok_def] >>
  qpat_x_assum `(apply_prefix_ops _ _ _ _).ps_stack = _` SUBST1_TAC >>
  qpat_x_assum `(apply_prefix_ops _ _ _ _).ps_spilled = _` SUBST1_TAC >>
  rewrite_tac[]
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
  drule reorderSimTheory.do_spill_at_stack_length >> simp[] >> decide_tac
QED

Theorem sym_reduce_depth_plan_frame_sim:
  !fuel pending op f ps ops ps' base initial_fmp p env cp fn ret srest
    ss ctx labs0 cs r.
  residual_budget_wf_marked base pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  reduce_depth_plan fuel pending op f (LENGTH pending) ps = (ops,ps') /\
  (!off. MEM (SOSpill off) ops ==> off < dimword(:256)) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= base /\ ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[stackPlanOpsTheory.reduce_depth_plan_def, execute_plan_def,
         asm_steps_def, sym_steps_def] >>
  qpat_x_assum `reduce_depth_plan (SUC fuel) _ _ _ _ _ = _` mp_tac >>
  simp[Once stackPlanOpsTheory.reduce_depth_plan_def] >>
  Cases_on `f + 1 < LENGTH pending`
  >- (strip_tac >> gvs[execute_plan_def, asm_steps_def, sym_steps_def]) >>
  Cases_on `stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack` >> simp[]
  >- (strip_tac >> gvs[execute_plan_def, asm_steps_def, sym_steps_def]) >>
  rename1 `_ = SOME dist` >> Cases_on `dist <= 16` >> simp[]
  >- (strip_tac >> gvs[execute_plan_def, asm_steps_def, sym_steps_def]) >>
  Cases_on `select_spill_candidate ps.ps_stack pending dist (LENGTH pending)` >> simp[]
  >- (strip_tac >> gvs[execute_plan_def, asm_steps_def, sym_steps_def]) >>
  pairarg_tac >> rename1 `do_spill_at cand ps = (hops,ps1)` >> gvs[] >>
  pairarg_tac >> rename1 `reduce_depth_plan fuel pending op f (LENGTH pending) ps1 = (tops,ps2)` >>
  strip_tac >> gvs[] >> suspend "selected_spill"
QED

Resume sym_reduce_depth_plan_frame_sim[selected_spill]:
  `dist < LENGTH ps.ps_stack` by
    metis_tac[stackModelTheory.stack_get_unfixed_depth_bound] >>
  `16 < dist` by decide_tac >>
  drule_all selected_spill_marked_budget >> strip_tac >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\ plan_slots_bounded base' ps` by
    fs[deepResidualBudgetTheory.residual_budget_wf_marked_def] >>
  `ps1.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    metis_tac[allocMonoTheory.reduce_depth_plan_next_offset, arithmeticTheory.LESS_EQ_TRANS] >>
  `(!off. MEM (SOSpill off) hops ==> off < dimword(:256)) /\
   (!off. MEM (SOSpill off) tops ==> off < dimword(:256))` by metis_tac[] >>
  gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  `cand < LENGTH ps.ps_stack` by
    metis_tac[planWfTheory.select_spill_candidate_bound] >>
  `!off. MEM (SOSpill off) hops ==> off < dimword(:256)` by metis_tac[] >>
  drule_all sym_do_spill_at_frame_sim >> strip_tac >>
  `!off. MEM (SOSpill off) tops ==> off < dimword(:256)` by metis_tac[] >>
  `asm_block_at p cs'.as_pc (execute_plan initial_fmp tops)` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qexistsl_tac [`cs''`, `ss''`] >>
  simp[stackOpSimTheory.asm_steps_add, sym_steps_add] >> decide_tac
QED

Finalise sym_reduce_depth_plan_frame_sim

Theorem mem_label_at_from_bytes:
  (!i. i < 32 ==> FLOOKUP labs (off+i) = SOME (l,d,i)) ==>
  mem_label_at labs off = SOME (l,d)
Proof
  strip_tac >> first_assum (qspec_then `0` assume_tac) >>
  gvs[mem_label_at_def, listTheory.EVERY_MEM, rich_listTheory.MEM_COUNT_LIST]
QED

Theorem scratch_label_store_cell:
  mem_sval_at (labs |++ GENLIST (\i. (off+i,(l,d,i))) 32) off (Lab l d)
Proof
  pure_rewrite_tac[mem_sval_at_def] >> irule mem_label_at_from_bytes >>
  simp[asmSymBridgeTheory.mstore_labels_lookup, Excl "GENLIST"]
QED

Theorem scratch_label_store_outside:
  ~in_mem_range off 32 b ==>
  FLOOKUP (labs |++ GENLIST (\i. (off+i,(l,d,i))) 32) b = FLOOKUP labs b
Proof
  simp[asmSymBridgeTheory.mstore_labels_lookup, in_mem_range_def]
QED

Theorem mem_sval_at_local_cong:
  (!b. in_mem_range off 32 b ==> FLOOKUP labs' b = FLOOKUP labs b) ==>
  (mem_sval_at labs' off sv <=> mem_sval_at labs off sv)
Proof
  strip_tac >>
  `!b. in_mem_range off 32 b ==> (b IN FDOM labs' <=> b IN FDOM labs)` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  `FLOOKUP labs' off = FLOOKUP labs off` by
    (first_x_assum irule >> simp[in_mem_range_def]) >>
  Cases_on `sv` >>
  simp[mem_sval_at_def, mem_label_at_def, listTheory.EVERY_MEM,
       rich_listTheory.MEM_COUNT_LIST] >>
  gvs[in_mem_range_def]
QED

Theorem sym_mstore_word_cell:
  ss.sym_stack = Val off :: Val w :: tail ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = tail /\
    mem_sval_at ss'.sym_mem_labels (w2n off) (Val w) /\
    (!b. ~in_mem_range (w2n off) 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  simp[sym_mstore_def, sym_step_concrete_def, asm_op_arity_def,
       sval_val_def, asm_op_mem_reads_def, asm_op_mem_writes_def,
       mem_labels_hit_def, sym_lift_def, asmOpSimTheory.asm_step_op_mstore,
       asm_op_arity_table_def, log_table_def,
       asm_mstore_def, mem_sval_at_def, mem_labels_clear_def,
       finite_mapTheory.FLOOKUP_DRESTRICT, asm_next_def,
       finite_mapTheory.FDOM_DRESTRICT]
QED

Theorem sym_mstore_label_cell:
  ss.sym_stack = Val off :: Lab l d :: tail ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = tail /\
    mem_sval_at ss'.sym_mem_labels (w2n off) (Lab l d) /\
    (!b. ~in_mem_range (w2n off) 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  qspecl_then [`ss.sym_mem_labels`, `w2n off`, `l`, `d`] assume_tac
    (Q.GENL [`labs`, `off`, `l`, `d`] (SPEC_ALL scratch_label_store_cell)) >>
  qspecl_then [`w2n off`, `ss.sym_mem_labels`, `l`, `d`] mp_tac
    (Q.GENL [`off`, `labs`, `l`, `d`, `b`] (SPEC_ALL scratch_label_store_outside)) >>
  strip_tac >> gvs[sym_mstore_def, sym_lift_def, asm_mstore_def, asm_next_def]
QED

Theorem sym_mload_label_cell:
  ss.sym_stack = Val off :: tail /\
  mem_sval_at ss.sym_mem_labels (w2n off) (Lab l d) ==>
  ?ss'. sym_mload ss = SymOK ss' /\ ss'.sym_stack = Lab l d :: tail /\
        ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  simp[mem_sval_at_def] >> strip_tac >> simp[sym_mload_def]
QED

Theorem scratch_store_preserves_disjoint_cell:
  mem_sval_at labs cell sv /\
  (!b. in_mem_range cell 32 b ==> ~in_mem_range off 32 b) /\
  (!b. ~in_mem_range off 32 b ==> FLOOKUP labs' b = FLOOKUP labs b) ==>
  mem_sval_at labs' cell sv
Proof
  metis_tac[mem_sval_at_local_cong]
QED

Theorem sym_mload_word_cell:
  ss.sym_stack = Val off :: tail /\
  mem_sval_at ss.sym_mem_labels (w2n off) (Val w) /\
  asm_mload (ss.sym_base with as_stack := [off]) = AsmOK loaded /\
  loaded.as_stack = [w] ==>
  ?ss'. sym_mload ss = SymOK ss' /\ ss'.sym_stack = Val w :: tail /\
        ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >>
  `FLOOKUP ss.sym_mem_labels (w2n off) = NONE` by
    (gvs[mem_sval_at_def] >> simp[finite_mapTheory.FLOOKUP_DEF] >>
     first_x_assum irule >> simp[in_mem_range_def]) >>
  simp[sym_mload_def, mem_label_at_def, sym_step_concrete_def,
       asm_op_arity_def, asm_op_arity_table_def, sval_val_def,
       asm_op_mem_reads_def, mem_labels_hit_def,
       asmOpSimTheory.asm_step_op_mload, sym_lift_def] >>
  `~?i. i IN FDOM ss.sym_mem_labels /\ in_mem_range (w2n off) 32 i` by
    metis_tac[mem_sval_at_def] >>
  simp[asm_op_mem_writes_def, mem_labels_clear_def,
       GSYM pred_setTheory.IN_UNIV, finite_mapTheory.DRESTRICT_UNIV] >>
  simp[finite_mapTheory.fmap_eq_flookup, finite_mapTheory.FLOOKUP_DRESTRICT]
QED

(* A branch condition cannot carry either class of symbolic label. *)
Theorem sym_jnz_condition_kind:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  fn_shape_ok fn /\ label_flow_ok ctx /\
  inst.inst_opcode = JNZ /\
  inst.inst_operands = [cond_op; Label if_nz; Label if_z] /\
  ~is_label_operand cond_op /\ cond_op <> dead_stack_marker /\
  op_kind_ok fn ret cond_op sv ==>
  ?w. sv = Val w
Proof
  strip_tac >> Cases_on `cond_op` >>
  gvs[op_kind_ok_def, is_label_operand_def] >>
  rename1 `Var x <> dead_stack_marker` >>
  `~retpc_var fn x` by
    (fs[fn_shape_ok_def, opaque_use_ok_def] >>
     first_x_assum (qspec_then `inst` mp_tac) >>
     simp[retpc_use_ok_def]) >>
  `~code_end_var fn x` by
    (fs[label_flow_ok_def] >>
     first_x_assum (qspecl_then [`fn`, `inst`] mp_tac) >> simp[]) >>
  gvs[]
QED

(* Static code-label resolution agrees with the concrete jump map. *)
Theorem sym_code_label_dest:
  asm_static_wf p /\ MEM (AsmLabel l) p /\
  FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
  FLOOKUP (build_offset_to_pc p) off = SOME pc ==>
  sym_jump_dest p (Lab l 0) = SOME pc
Proof
  strip_tac >>
  Cases_on `INDEX_OF (AsmLabel l) p`
  >- gvs[listTheory.INDEX_OF_eq_NONE] >>
  drule_all asm_static_wf_code_label >>
  simp[sym_jump_dest_def]
QED

(* The symbolic jump consumes only its explicitly typed destination. *)
Theorem sym_jump_steps:
  asm_block_at p ss.sym_base.as_pc [AsmOp "JUMP"] /\
  ss.sym_stack = Lab l 0 :: stk /\
  sym_jump_dest p (Lab l 0) = SOME pc ==>
  sym_steps p env 1 ss =
    SymOK (ss with <|sym_base := ss.sym_base with as_pc := pc;
                    sym_stack := stk|>)
Proof
  strip_tac >>
  rewrite_tac[arithmeticTheory.ONE, sym_steps_def] >>
  gvs[asm_block_at_def, sym_step_def, sym_step_op_def, sym_jump_def]
QED

Theorem sym_jmp_suffix:
  asm_block_at p ss.sym_base.as_pc [AsmPushLabel l; AsmOp "JUMP"] /\
  sym_jump_dest p (Lab l 0) = SOME pc ==>
  sym_steps p env 2 ss =
    SymOK (ss with sym_base := ss.sym_base with as_pc := pc)
Proof
  strip_tac >>
  rewrite_tac[arithmeticTheory.TWO, arithmeticTheory.ONE, sym_steps_def] >>
  gvs[stackOpSimTheory.asm_block_at_cons, sym_step_def, sym_step_op_def,
      sym_set_stack_def, asm_next_def, sym_jump_def]
QED

Theorem sym_jnz_suffix_nonzero:
  asm_block_at p ss.sym_base.as_pc [AsmPushLabel l; AsmOp "JUMPI"] /\
  ss.sym_stack = Val w :: stk /\ w <> 0w /\
  sym_jump_dest p (Lab l 0) = SOME pc ==>
  sym_steps p env 2 ss =
    SymOK (ss with <|sym_base := ss.sym_base with as_pc := pc;
                    sym_stack := stk|>)
Proof
  strip_tac >>
  rewrite_tac[arithmeticTheory.TWO, arithmeticTheory.ONE, sym_steps_def] >>
  gvs[stackOpSimTheory.asm_block_at_cons, sym_step_def, sym_step_op_def,
      sym_set_stack_def, asm_next_def, sym_jumpi_def]
QED

Theorem sym_jnz_suffix_zero:
  asm_block_at p ss.sym_base.as_pc
    [AsmPushLabel ln; AsmOp "JUMPI"; AsmPushLabel lz; AsmOp "JUMP"] /\
  ss.sym_stack = Val 0w :: stk /\
  sym_jump_dest p (Lab lz 0) = SOME pc ==>
  sym_steps p env 4 ss =
    SymOK (ss with <|sym_base := ss.sym_base with as_pc := pc;
                    sym_stack := stk|>)
Proof
  strip_tac >>
  rewrite_tac[numLib.num_CONV ``4:num``, numLib.num_CONV ``3:num``,
              arithmeticTheory.TWO, arithmeticTheory.ONE, sym_steps_def] >>
  gvs[stackOpSimTheory.asm_block_at_cons, sym_step_def, sym_step_op_def,
      sym_set_stack_def, asm_next_def, sym_jumpi_def, sym_jump_def]
QED

Theorem sym_kinds_ok_push:
  !cp fn ret srest ps ss op sv base'.
  sym_kinds_ok cp fn ret srest ps ss /\ op_kind_ok fn ret op sv ==>
  sym_kinds_ok cp fn ret srest
    (ps with ps_stack := SNOC op ps.ps_stack)
    (ss with <|sym_base := base'; sym_stack := sv :: ss.sym_stack|>)
Proof
  rw[sym_kinds_ok_def] >>
  qexists_tac `sv :: top` >> simp[]
QED

Theorem sym_kinds_ok_pop:
  !cp fn ret srest ps ss op sv stk base'.
  sym_kinds_ok cp fn ret srest
    (ps with ps_stack := SNOC op ps.ps_stack) ss /\
  ss.sym_stack = sv :: stk ==>
  sym_kinds_ok cp fn ret srest ps
    (ss with <|sym_base := base'; sym_stack := stk|>)
Proof
  rw[sym_kinds_ok_def] >>
  gvs[listTheory.REVERSE_SNOC, listTheory.LIST_REL_CONS1] >> metis_tac[]
QED

Theorem noncopy_output_not_code_end:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM out inst.inst_outputs /\
  inst.inst_opcode <> ADD /\ inst.inst_opcode <> ASSIGN ==>
  ~code_end_var fn out
Proof
  rpt strip_tac >> drule_all code_end_var_def_inst >> simp[]
QED

Theorem sym_gas_output_not_code_end:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = GAS /\ MEM out inst.inst_outputs ==>
  ~code_end_var fn out
Proof
  strip_tac >> irule noncopy_output_not_code_end >>
  conj_tac >- fs[codegen_ready_fn_def] >>
  qexists_tac `inst` >> simp[]
QED

Theorem sym_gas_output_kind:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = GAS /\ MEM out inst.inst_outputs ==>
  op_kind_ok fn ret (Var out) (Val w)
Proof
  strip_tac >>
  `~retpc_var fn out /\ ~code_end_var fn out` by
    metis_tac[gasFrameSimTheory.gas_output_non_retpc,
              sym_gas_output_not_code_end] >>
  simp[op_kind_ok_def]
QED

(* GAS reads no symbolic operands or memory and produces a word. *)
Theorem sym_step_gas:
  sym_step p env (AsmOp "GAS") ss =
    SymOK (ss with <|
      sym_base := ss.sym_base with <|as_pc := ss.sym_base.as_pc + 1;
        as_stack := []; as_gas_readings := TL ss.sym_base.as_gas_readings|>;
      sym_stack := Val (HD (ss.sym_base.as_gas_readings ++ [0w])) ::
                   ss.sym_stack|>)
Proof
  `asm_op_arity "GAS" = 0 /\
   ALOOKUP dup_table "GAS" = NONE /\
   ALOOKUP swap_table "GAS" = NONE /\
   ALOOKUP log_table "GAS" = NONE` by EVAL_TAC >>
  Cases_on `ss.sym_base.as_gas_readings` >>
  simp[sym_step_def, sym_step_op_def, sym_step_concrete_def,
       mem_labels_hit_def, asm_op_mem_reads_def, mem_labels_clear_def,
       asm_op_mem_writes_def, GSYM pred_setTheory.UNIV_DEF,
       finite_mapTheory.DRESTRICT_UNIV, asm_step_op_def, asm_step_arith_def,
       asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
       asm_step_control_def, asm_step_extcall_def, asm_step_copy_def,
       asm_step_context_def, asm_gas_def, asm_push_val_def, asm_next_def,
       sym_lift_def, sym_state_component_equality, asm_state_component_equality]
QED

Theorem sym_gas_steps:
  asm_block_at p ss.sym_base.as_pc [AsmOp "GAS"] ==>
  sym_steps p env 1 ss =
    SymOK (ss with <|
      sym_base := ss.sym_base with <|as_pc := ss.sym_base.as_pc + 1;
        as_stack := []; as_gas_readings := TL ss.sym_base.as_gas_readings|>;
      sym_stack := Val (HD (ss.sym_base.as_gas_readings ++ [0w])) ::
                   ss.sym_stack|>)
Proof
  strip_tac >>
  rewrite_tac[arithmeticTheory.ONE, sym_steps_def] >>
  gvs[asm_block_at_def, sym_step_gas]
QED

Theorem sym_gas_kinds_steps:
  !cp fn ret srest ps ss p env out.
  sym_kinds_ok cp fn ret srest ps ss /\
  op_kind_ok fn ret (Var out)
    (Val (HD (ss.sym_base.as_gas_readings ++ [0w]))) /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "GAS"] ==>
  ?ss'. sym_steps p env 1 ss = SymOK ss' /\
    sym_kinds_ok cp fn ret srest
      (ps with ps_stack := SNOC (Var out) ps.ps_stack) ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  rpt gen_tac >> strip_tac >>
  drule sym_gas_steps >> disch_then (qspec_then `env` assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >>
  irule sym_kinds_ok_push >> simp[]
QED

Theorem sym_gas_emit_frame_sim:
  !p env ctx cp fn ret srest labs0 ps cs ss inst out.
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = GAS /\ MEM out inst.inst_outputs /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ asm_block_at p cs.as_pc [AsmOp "GAS"] ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      1 cs = AsmOK cs' /\
    sym_steps p env 1 ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0
      (ps with ps_stack := SNOC (Var out) ps.ps_stack) cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss` >>
  `asm_sym_rel p env cs ss /\ sym_kinds_ok cplan fn ret srest ps ss` by
    fs[sym_frame_inv_def] >>
  `op_kind_ok fn ret (Var out)
     (Val (HD (ss.sym_base.as_gas_readings ++ [0w])))` by
    metis_tac[sym_gas_output_kind] >>
  `asm_block_at p ss.sym_base.as_pc [AsmOp "GAS"]` by
    metis_tac[asm_sym_rel_pc] >>
  drule_all sym_gas_kinds_steps >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  qexistsl_tac [`cs'`, `ss'`] >> simp[sym_frame_inv_def] >>
  fs[sym_frame_inv_def]
QED

(* The return suffix removes the opaque PC and preserves all label memory. *)
Theorem sym_ret_suffix_steps:
  !p env ctx cp fn ret srest labs0 ps cs ss values pc.
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ asm_block_at p cs.as_pc [AsmOp "JUMP"] /\
  ss.sym_stack = Lab ret 0 :: (MAP Val (REVERSE values) ++ srest) /\
  sym_jump_dest p (Lab ret 0) = SOME pc ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      1 cs = AsmOK cs' /\
    sym_steps p env 1 ss = SymOK ss' /\ asm_sym_rel p env cs' ss' /\
    cs'.as_pc = pc /\
    ss'.sym_stack = MAP Val (REVERSE values) ++ srest /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
         FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  rpt gen_tac >> strip_tac >>
  `asm_sym_rel p env cs ss` by fs[sym_frame_inv_def] >>
  `asm_block_at p ss.sym_base.as_pc [AsmOp "JUMP"]` by
    metis_tac[asm_sym_rel_pc] >>
  drule_all sym_jump_steps >> disch_then (qspec_then `env` assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  qexistsl_tac [`cs'`, `ss with <|sym_base := ss.sym_base with as_pc := pc;
    sym_stack := MAP Val (REVERSE values) ++ srest|>`] >> simp[] >>
  conj_tac >- (drule_all asm_sym_rel_pc >> simp[]) >>
  fs[sym_frame_inv_def, sym_kinds_ok_def]
QED

Theorem sym_jmp_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   target target_bb target_stack off pc_t
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = JMP /\
    inst.inst_operands = [Label target] /\
    inst.inst_outputs = [] /\
    lookup_block target fn.fn_blocks = SOME target_bb /\
    target_stack =
      MAP Var (input_vars_from bb_label target_bb.bb_instructions
                 (live_vars_at liveness target 0)) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    (!off. MEM (SORestore off) (FST (restore_spilled_plan target_stack ps)) ==>
           off < dimword(:256)) /\
    LENGTH target_stack <=
      LENGTH (SND (restore_spilled_plan target_stack ps)).ps_stack /\
    pending_inventory_wf target_stack ps /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      target_stack /\
    (!op at. MEM op target_stack /\
       (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
       operand_equiv dfg op at ==>
       operand_val (frame_view fn ra vs) lo op =
       operand_val (frame_view fn ra vs) lo at) /\
    FLOOKUP lo target = SOME off /\ off < dimword (:256) /\
    FLOOKUP o2pc off = SOME pc_t /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting
      next_is_term bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    (* SSA: planner-equivalent operands have the same kind. *)
    codegen_ready_fn fn /\
    MEM (AsmLabel target) prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?n as' ss'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        as'.as_pc = pc_t /\
        vs' = jump_to target vs /\
        sym_steps prog env n ss = SymOK ss' /\
        sym_frame_inv prog env ctx cp fn ret srest labs0 ps' as' ss'
Proof
  cheat
QED

Theorem sym_jnz_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   cond_op if_nz if_z off_nz off_z pc_nz pc_z
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = JNZ /\
    inst.inst_operands = [cond_op; Label if_nz; Label if_z] /\
    (* The planner drops label operands of jumps, so a label condition would
       emit nothing; label_positions_ok excludes it. *)
    ~is_label_operand cond_op /\
    inst.inst_outputs = [] /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    1 <= LENGTH (SND (emit_input_plan JNZ [cond_op] next_liveness ps)).ps_stack /\
    (is_var_operand cond_op ==>
      IS_SOME (stack_get_depth cond_op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled cond_op)) /\
    eval_operand cond_op vs = operand_val (frame_view fn ra vs) lo cond_op /\
    (!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
       operand_equiv dfg cond_op at ==>
       operand_val (frame_view fn ra vs) lo cond_op =
       operand_val (frame_view fn ra vs) lo at) /\
    cond_op <> dead_stack_marker /\
    (!at. operand_equiv dfg cond_op at ==> at <> dead_stack_marker) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    FLOOKUP lo if_nz = SOME off_nz /\ off_nz < dimword (:256) /\
    FLOOKUP o2pc off_nz = SOME pc_nz /\
    FLOOKUP lo if_z = SOME off_z /\ off_z < dimword (:256) /\
    FLOOKUP o2pc off_z = SOME pc_z /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting
      next_is_term bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    (* SSA, and the shape facts that keep labels out of the condition. *)
    codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
    MEM (AsmLabel if_nz) prog /\ MEM (AsmLabel if_z) prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?n as' ss'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        ((vs' = jump_to if_nz vs /\ as'.as_pc = pc_nz) \/
         (vs' = jump_to if_z vs /\ as'.as_pc = pc_z)) /\
        sym_steps prog env n ss = SymOK ss' /\
        sym_frame_inv prog env ctx cp fn ret srest labs0 ps' as' ss'
Proof
  cheat
QED

Theorem sym_ret_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' ra rest mem0 pc_ret
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = RET /\
    MEM inst (fn_insts (reachable_fn fn)) /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\
    inst_wf inst /\
    generated_plan_state_wf_marked base ps /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    ps'.ps_stack = [] /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !rv vs'. step_inst fuel ctx inst vs = IntRet rv vs' ==>
      ?n as' ss'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        as'.as_pc = pc_ret /\
        as'.as_stack = REVERSE rv.iret_values ++ rest /\
        context_memory_rel cp vs'.vs_memory as'.as_memory /\
        (!b. context_spill_byte cp b /\
             ~closure_spill_byte ctx cp fn.fn_name b ==>
             read_byte b as'.as_memory = read_byte b mem0) /\
        shared_state_rel vs' as' /\
        sym_steps prog env n ss = SymOK ss' /\
        asm_sym_rel prog env as' ss' /\
        ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
        (!b. context_spill_byte cp b /\
             ~closure_spill_byte ctx cp fn.fn_name b ==>
             FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
        (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  cheat
QED

Theorem sym_halt_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    source_memory_reads_disjoint cp inst vs /\
    opaque_use_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    (* The invariant's region clause for the output planner state, as in
       gen_inst_frame_sim: the prefix's transient spills lie below
       ps'.ps_alloc.sa_next_offset, so this keeps them inside the region
       whose bytes source_memory_reads_disjoint keeps the payload out of.
       fn_frame_inv bounds only ps at entry, which isn't enough
       (fnFrameTerminalPrep$terminal_escape_halt_counterexample). *)
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !vs'. step_inst fuel ctx inst vs = Halt vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmHalt as' /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps prog env n ss)
Proof
  cheat
QED

Theorem sym_abort_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    ~vs.vs_call_ctx.cc_static /\
    source_memory_reads_disjoint cp inst vs /\
    opaque_use_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    (* The invariant's region clause for the output planner state, as in
       gen_inst_frame_sim: the prefix's transient spills lie below
       ps'.ps_alloc.sa_next_offset, so this keeps them inside the region
       whose bytes source_memory_reads_disjoint keeps the payload out of.
       fn_frame_inv bounds only ps at entry, which isn't enough
       (fnFrameTerminalPrep$terminal_escape_halt_counterexample). *)
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    (inst.inst_opcode = ASSERT ==>
     ?off pc. FLOOKUP lo "revert" = SOME off /\ off < dimword (:256) /\
              FLOOKUP o2pc off = SOME pc /\
              asm_block_at prog pc
                (execute_plan cp.cp_initial_fmp revert_postamble)) /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    (inst.inst_opcode = ASSERT ==> MEM (AsmLabel "revert") prog) /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !a vs'. step_inst fuel ctx inst vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps prog env n ss)
Proof
  cheat
QED

Theorem sym_gas_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode = GAS /\
    (* inst_wf doesn't fix the operand count of the read-only opcodes. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* The context-level memory obligations (codegen_memory_obligations). *)
    source_memory_reads_disjoint cp inst vs /\
    context_source_memory_writes_disjoint cp inst vs /\
    (* Return-PC variables are only copied (unit_shape_ok's fn_shape_ok). *)
    opaque_use_ok fn /\ retpc_shape_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    (* The invariant's region clause for the output planner state. *)
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    ~is_terminator inst.inst_opcode /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    (* The EVM has LOG0 to LOG4 only; inst_wf allows larger topic counts. *)
    (inst.inst_opcode = LOG ==>
     ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (* ASSERT's failure branch pushes the shared revert label. *)
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    (* EVM compatibility: DUP depth limit. Dischargeable from evm_compatible
       (LOG tc <= 4, INVOKE args bounded by fn arity). Pipeline obligation. *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth after input emission >= operand count.
       Dischargeable from plan_state invariant (stack tracks emitted inputs). *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Every variable input must be owned by the planner: each is either
       on the stack at any depth or available from the spill map.
       generated_plan_state_wf_marked is structural and does not imply ownership. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    (* SSA freshness: output variables not yet in plan state.
       Dischargeable from ssa_form + plan_state invariant
       (plan tracks defined vars, SSA ensures no redefinition). *)
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (* PHI soundness: stack-found phi var evaluates to resolved phi value.
       Dischargeable from block entry invariant: predecessor placed the
       resolved PHI value at the expected stack position. *)
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val (frame_view fn ra vs) lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op (frame_view fn ra vs)) /\
    (* Spill well-formedness for prefix ops.
       Dischargeable: provable from generate_inst_plan output
       (plan generator produces spill-well-formed prefixes). *)
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          context_spill_step_safe cp vs vs' ==>
      ?n as' ss'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
        sym_steps prog env n ss = SymOK ss' /\
        sym_frame_inv prog env ctx cp fn ret srest labs0 ps' as' ss'
Proof
  cheat
QED

Theorem sym_revert_forward_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn bb i j base ps vs as ops
   ps_end ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\
    LENGTH (get_params bb.bb_instructions) <= i /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions) /\
    generated_plan_state_wf_marked base ps /\
    (!k inst op.
       i <= k /\ get_instruction bb k = SOME inst /\
       MEM op (compute_operands inst) /\ is_var_operand op /\
       (!k' inst' x. i <= k' /\ k' < k /\ get_instruction bb k' = SOME inst' /\
                     op = Var x ==> ~MEM x inst'.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (i - LENGTH (get_params bb.bb_instructions))
      (DROP i bb.bb_instructions) ps = SOME (ops, ps_end) /\
    (!off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops) /\
    (!name. MEM (AsmOp name) (execute_plan cp.cp_initial_fmp ops) ==>
            IS_SOME (evm_opcode_byte name)) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !a vs'. exec_block fuel ctx bb vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps prog env n ss)
Proof
  cheat
QED
