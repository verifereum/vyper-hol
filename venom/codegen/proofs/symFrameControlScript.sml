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
  dfgDefs symPlannerSim symShuffleSim asmSymPc codegenEncodingWf

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

Theorem sym_spill_free_prefix_frame_sim:
  !ops initial_fmp p env cp fn ret srest ps ss ctx labs0 cs.
  prefix_wf (SND (compute_label_offsets p)) (LENGTH ps.ps_stack) ops /\
  prefix_spill_wf initial_fmp (SND (compute_label_offsets p)) ops ps /\
  EVERY is_prefix_op ops /\
  EVERY (\op. !l d. op <> SOPushOfst l d) ops /\
  (!off. ~MEM (SOSpill off) ops) /\
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
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  `asm_sym_rel p env cs ss` by fs[sym_frame_inv_def] >>
  rename1 `sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss` >>
  `sym_kinds_ok cplan fn ret srest ps ss` by fs[sym_frame_inv_def] >>
  `ss.sym_base.as_pc = cs.as_pc` by metis_tac[asm_sym_rel_pc] >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops)` by simp[] >>
  `!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    F /\ context_spill_byte cplan b` by simp[] >>
  drule_all (BETA_RULE (Q.INST [`R` |-> `\b:num. F`]
    (SPEC_ALL sym_prefix_ops_sim))) >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  qexistsl_tac [`cs'`, `ss'`] >> simp[] >>
  conj_tac >- (fs[sym_frame_inv_def] >> metis_tac[]) >>
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

Theorem sym_push_scratch_address:
  off < dimword(:256) ==>
  sym_step p env (AsmPush (encode_num_bytes off)) ss =
    SymOK (ss with <|sym_base := asm_next (ss.sym_base with as_stack := []);
                    sym_stack := Val (n2w off) :: ss.sym_stack|>)
Proof
  simp[sym_step_def, sym_lift_def, asm_step_def,
       spillSimTheory.push_encode_num_roundtrip, asm_next_def] >>
  simp[sym_state_component_equality]
QED

Theorem sym_scratch_store_step:
  ss.sym_stack = Val off :: sv :: tail ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = tail /\
    mem_sval_at ss'.sym_mem_labels (w2n off) sv /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    (!b. ~in_mem_range (w2n off) 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==>
      b IN FDOM ss.sym_mem_labels \/ in_mem_range (w2n off) 32 b)
Proof
  strip_tac >>
  `?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = tail /\
    mem_sval_at ss'.sym_mem_labels (w2n off) sv /\
    (!b. ~in_mem_range (w2n off) 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)` by
    (Cases_on `sv` >- metis_tac[sym_mstore_word_cell] >>
     metis_tac[sym_mstore_label_cell]) >>
  qexists_tac `ss'` >> simp[] >> conj_tac
  >- (irule sym_step_pc_next >>
      qexistsl_tac [`env`, `AsmOp "MSTORE"`, `p`] >>
      simp[sym_step_def, sym_step_op_def]) >>
  metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE]
QED

Theorem sym_scratch_spill_steps:
  off < dimword(:256) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SOSpill off]) /\
  ss.sym_stack = sv :: tail ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan fmp [SOSpill off])) ss = SymOK ss' /\
    ss'.sym_stack = tail /\ mem_sval_at ss'.sym_mem_labels off sv /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
    (!b. ~in_mem_range off 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==>
      b IN FDOM ss.sym_mem_labels \/ in_mem_range off 32 b)
Proof
  strip_tac >>
  qabbrev_tac `pushed = ss with
    <|sym_base := asm_next (ss.sym_base with as_stack := []);
      sym_stack := Val (n2w off) :: ss.sym_stack|>` >>
  `pushed.sym_stack = Val (n2w off) :: sv :: tail` by simp[Abbr `pushed`] >>
  drule sym_scratch_store_step >> strip_tac >> qexists_tac `ss'` >>
  gvs[execute_plan_def, exec_stack_op_def, Abbr `pushed`, asm_next_def,
      wordsTheory.w2n_n2w] >>
  rewrite_tac[arithmeticTheory.TWO, arithmeticTheory.ONE, sym_steps_def] >>
  gvs[stackOpSimTheory.asm_block_at_cons] >>
  simp[sym_push_scratch_address, asm_next_def] >>
  gvs[sym_step_def, sym_step_op_def]
QED

Theorem sym_scratch_load_word_step:
  ss.sym_stack = Val off :: tail /\
  mem_sval_at ss.sym_mem_labels (w2n off) (Val w) ==>
  ?ss' v. sym_mload ss = SymOK ss' /\ ss'.sym_stack = Val v :: tail /\
          ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >>
  `?loaded v. asm_mload (ss.sym_base with as_stack := [off]) = AsmOK loaded /\
              loaded.as_stack = [v]` by simp[asm_mload_def, asm_next_def] >>
  `mem_sval_at ss.sym_mem_labels (w2n off) (Val v)` by gvs[mem_sval_at_def] >>
  drule_all sym_mload_word_cell >> metis_tac[]
QED

Theorem sym_scratch_load_step:
  ss.sym_stack = Val off :: tail /\ mem_sval_at ss.sym_mem_labels (w2n off) sv ==>
  ?ss' sv'. sym_mload ss = SymOK ss' /\ ss'.sym_stack = sv' :: tail /\
    (case sv of Val w => ?v. sv' = Val v | Lab l d => sv' = sv) /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  strip_tac >>
  `?ss' sv'. sym_mload ss = SymOK ss' /\ ss'.sym_stack = sv' :: tail /\
    (case sv of Val w => ?v. sv' = Val v | Lab l d => sv' = sv) /\
    ss'.sym_mem_labels = ss.sym_mem_labels` by
    (Cases_on `sv`
     >- (simp[] >> metis_tac[sym_scratch_load_word_step]) >>
     simp[] >> metis_tac[sym_mload_label_cell]) >>
  qexistsl_tac [`ss'`, `sv'`] >> simp[] >>
  irule sym_step_pc_next >> qexistsl_tac [`env`, `AsmOp "MLOAD"`, `p`] >>
  simp[sym_step_def, sym_step_op_def]
QED

Theorem sym_scratch_restore_steps:
  off < dimword(:256) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SORestore off]) /\
  mem_sval_at ss.sym_mem_labels off sv ==>
  ?ss' sv'. sym_steps p env (LENGTH (execute_plan fmp [SORestore off])) ss = SymOK ss' /\
    ss'.sym_stack = sv' :: ss.sym_stack /\
    (case sv of Val w => ?v. sv' = Val v | Lab l d => sv' = sv) /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 2
Proof
  strip_tac >>
  qabbrev_tac `pushed = ss with
    <|sym_base := asm_next (ss.sym_base with as_stack := []);
      sym_stack := Val (n2w off) :: ss.sym_stack|>` >>
  `pushed.sym_stack = Val (n2w off) :: ss.sym_stack /\
   mem_sval_at pushed.sym_mem_labels (w2n (n2w off : bytes32)) sv` by
    simp[Abbr `pushed`, wordsTheory.w2n_n2w] >>
  drule_all sym_scratch_load_step >> strip_tac >>
  qexistsl_tac [`ss'`, `sv'`] >>
  gvs[execute_plan_def, exec_stack_op_def, Abbr `pushed`, asm_next_def] >>
  rewrite_tac[arithmeticTheory.TWO, arithmeticTheory.ONE, sym_steps_def] >>
  gvs[stackOpSimTheory.asm_block_at_cons] >>
  simp[sym_push_scratch_address, asm_next_def] >>
  gvs[sym_step_def, sym_step_op_def]
QED
Theorem sym_scratch_spill_sim:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  off < dimword(:256) /\
  asm_block_at p cs.as_pc (execute_plan fmp [SOSpill off]) /\
  ss.sym_stack = sv :: tail ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan fmp [SOSpill off])) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan fmp [SOSpill off])) ss = SymOK ss' /\
    asm_sym_rel p env cs' ss' /\
    cs'.as_memory = mem_write32 off (HD cs.as_stack) cs.as_memory /\
    cs'.as_stack = TL cs.as_stack /\
    ss'.sym_stack = tail /\ mem_sval_at ss'.sym_mem_labels off sv /\
    cs'.as_pc = cs.as_pc + 2 /\
    (!b. ~in_mem_range off 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==>
      b IN FDOM ss.sym_mem_labels \/ in_mem_range off 32 b)
Proof
  strip_tac >>
  `ss.sym_base.as_pc = cs.as_pc` by metis_tac[asm_sym_rel_pc] >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SOSpill off])` by simp[] >>
  drule_all sym_scratch_spill_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  `1 <= LENGTH cs.as_stack` by gvs[asm_sym_rel_def] >>
  `asm_block_at p cs.as_pc [AsmPush (encode_num_bytes off); AsmOp "MSTORE"]` by
    gvs[execute_plan_def, exec_stack_op_def] >>
  drule_at (Pos last) spillSimTheory.spill_asm_steps >>
  simp[] >>
  disch_then (qspecl_then [`SND (compute_label_offsets p)`, `build_offset_to_pc p`] strip_assume_tac) >>
  gvs[execute_plan_def, exec_stack_op_def] >> metis_tac[asm_result_11]
QED

Theorem sym_scratch_restore_sim:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  off < dimword(:256) /\
  asm_block_at p cs.as_pc (execute_plan fmp [SORestore off]) /\
  mem_sval_at ss.sym_mem_labels off sv /\
  (case sv of Val w =>
     word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP off (asm_expand_memory (off + 32) cs.as_memory))) = w
   | Lab l d => T) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan fmp [SORestore off])) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan fmp [SORestore off])) ss = SymOK ss' /\
    asm_sym_rel p env cs' ss' /\ ss'.sym_stack = sv :: ss.sym_stack /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\ cs'.as_pc = cs.as_pc + 2 /\
    cs'.as_memory = asm_expand_memory (off + 32) cs.as_memory
Proof
  strip_tac >>
  `ss.sym_base.as_pc = cs.as_pc` by metis_tac[asm_sym_rel_pc] >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SORestore off])` by simp[] >>
  drule_all sym_scratch_restore_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  `asm_block_at p cs.as_pc [AsmPush (encode_num_bytes off); AsmOp "MLOAD"]` by
    gvs[execute_plan_def, exec_stack_op_def] >>
  drule_all spillSimTheory.restore_asm_steps >>
  disch_then (qspecl_then [`SND (compute_label_offsets p)`, `build_offset_to_pc p`] strip_assume_tac) >>
  gvs[execute_plan_def, exec_stack_op_def] >>
  Cases_on `sv` >>
  gvs[asm_sym_rel_def, sval_conc_def]
QED

Theorem sym_scratch_repeated_value_probe:
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SOSpill 0; SOSpill 32]) /\
  ss.sym_stack = sv :: sv :: tail ==>
  ?ss'. sym_steps p env 4 ss = SymOK ss' /\ ss'.sym_stack = tail /\
    mem_sval_at ss'.sym_mem_labels 0 sv /\ mem_sval_at ss'.sym_mem_labels 32 sv /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 4
Proof
  strip_tac >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SOSpill 0]) /\
   asm_block_at p (ss.sym_base.as_pc + 2) (execute_plan fmp [SOSpill 32])` by
    gvs[execute_plan_def, exec_stack_op_def, stackOpSimTheory.asm_block_at_cons] >>
  `0 < dimword(:256) /\ 32 < dimword(:256)` by
    simp[wordsTheory.dimword_def] >>
  drule_all sym_scratch_spill_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  `asm_block_at p ss'.sym_base.as_pc (execute_plan fmp [SOSpill 32])` by simp[] >>
  `ss'.sym_stack = sv :: tail` by simp[] >>
  drule_all sym_scratch_spill_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  `mem_sval_at ss''.sym_mem_labels 0 sv` by
    (irule scratch_store_preserves_disjoint_cell >>
     qexistsl_tac [`ss'.sym_mem_labels`, `32`] >> simp[in_mem_range_def]) >>
  qexists_tac `ss''` >>
  gvs[execute_plan_def, exec_stack_op_def] >>
  mp_tac (Q.SPECL [`2`, `2`, `ss`] sym_steps_add) >> simp[]
QED

Theorem scratch_disjoint_bulk_cell:
  EVERY (\off. h + 32 <= off \/ off + 32 <= h) offsets /\
  (!b. EVERY (\off. ~in_mem_range off 32 b) offsets ==>
    FLOOKUP labs' b = FLOOKUP labs b) /\
  mem_sval_at labs h sv ==>
  mem_sval_at labs' h sv
Proof
  strip_tac >>
  `!b. in_mem_range h 32 b ==> FLOOKUP labs' b = FLOOKUP labs b`
    suffices_by metis_tac[mem_sval_at_local_cong] >> rpt strip_tac >>
  first_x_assum irule >>
  fs[listTheory.EVERY_MEM, in_mem_range_def] >> rpt strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem sym_scratch_spill_bulk_steps:
  !offsets ss.
    LENGTH offsets <= LENGTH ss.sym_stack /\
    EVERY (\off. off < dimword(:256)) offsets /\
    (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
      EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
    asm_block_at p ss.sym_base.as_pc (execute_plan fmp (MAP SOSpill offsets)) ==>
    ?ss'. sym_steps p env (2 * LENGTH offsets) ss = SymOK ss' /\
      ss'.sym_stack = DROP (LENGTH offsets) ss.sym_stack /\
      ss'.sym_base.as_pc = ss.sym_base.as_pc + 2 * LENGTH offsets /\
      (!k. k < LENGTH offsets ==>
        mem_sval_at ss'.sym_mem_labels (EL k offsets) (EL k ss.sym_stack)) /\
      (!b. EVERY (\off. ~in_mem_range off 32 b) offsets ==>
        FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
      (!b. b IN FDOM ss'.sym_mem_labels ==>
        b IN FDOM ss.sym_mem_labels \/
        EXISTS (\off. in_mem_range off 32 b) offsets)
Proof
  Induct >> simp[execute_plan_def, sym_steps_def] >>
  rpt strip_tac >>
  `(!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
      EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
   EVERY (\off. h + 32 <= off \/ off + 32 <= h) offsets` by
    (conj_tac
     >- (rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
     simp[listTheory.EVERY_EL] >> rpt strip_tac >>
     first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  Cases_on `ss.sym_stack` >> gvs[] >>
  rename1 `ss.sym_stack = sv :: tail` >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SOSpill h]) /\
   asm_block_at p (ss.sym_base.as_pc + 2) (execute_plan fmp (MAP SOSpill offsets))` by
    gvs[execute_plan_def, exec_stack_op_def, stackOpSimTheory.asm_block_at_cons] >>
  drule_all sym_scratch_spill_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  first_x_assum (qspec_then `ss'` mp_tac) >> simp[] >>
  strip_tac >> qexists_tac `ss''` >> simp[] >>
  conj_tac
  >- (gvs[execute_plan_def, exec_stack_op_def] >>
      mp_tac (Q.SPECL [`2`, `2 * LENGTH (offsets:num list)`, `ss`] sym_steps_add) >>
      simp[arithmeticTheory.MULT_SUC]) >>
  conj_tac
  >- (Cases >> simp[] >> metis_tac[scratch_disjoint_bulk_cell]) >>
  metis_tac[]
QED

Theorem sym_scratch_restore_bulk_sim:
  !offsets vals cs ss.
    asm_static_wf p /\ asm_sym_rel p env cs ss /\
    EVERY (\off. off < dimword(:256)) offsets /\
    LIST_REL (\off sv. mem_sval_at ss.sym_mem_labels off sv /\
      case sv of Val w => word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP off cs.as_memory)) = w | Lab l d => T) offsets vals /\
    asm_block_at p cs.as_pc (execute_plan fmp (MAP SORestore offsets)) ==>
    ?cs' ss'.
      asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
        (2 * LENGTH offsets) cs = AsmOK cs' /\
      sym_steps p env (2 * LENGTH offsets) ss = SymOK ss' /\
      asm_sym_rel p env cs' ss' /\
      ss'.sym_stack = REVERSE vals ++ ss.sym_stack /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\
      cs'.as_pc = cs.as_pc + 2 * LENGTH offsets
Proof
  Induct >> simp[execute_plan_def, sym_steps_def, asm_steps_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `vals` >> gvs[] >>
  rename1 `mem_sval_at ss.sym_mem_labels h sv` >>
  `asm_block_at p cs.as_pc (execute_plan fmp [SORestore h]) /\
   asm_block_at p (cs.as_pc + 2) (execute_plan fmp (MAP SORestore offsets))` by
    gvs[execute_plan_def, exec_stack_op_def, stackOpSimTheory.asm_block_at_cons] >>
  `case sv of Val w => word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP h (asm_expand_memory (h + 32) cs.as_memory))) = w
    | Lab l d => T` by simp[spillSimTheory.word_of_bytes_take_drop_expand] >>
  drule_all sym_scratch_restore_sim >> strip_tac >>
  first_x_assum (qspecl_then [`t`, `cs'`, `ss'`] mp_tac) >>
  simp[spillSimTheory.word_of_bytes_take_drop_expand] >>
  strip_tac >> qexistsl_tac [`cs''`, `ss''`] >> simp[] >>
  `2 * SUC (LENGTH offsets) = 2 + 2 * LENGTH offsets` by decide_tac >>
  gvs[execute_plan_def, exec_stack_op_def] >>
  conj_tac
  >- (once_rewrite_tac[arithmeticTheory.MULT_SUC] >>
      irule blockSimHelpersTheory.asm_steps_compose_ok >> qexists_tac `cs'` >> simp[]) >>
  mp_tac (Q.SPECL [`2`, `2 * LENGTH (offsets:num list)`, `ss`] sym_steps_add) >>
  simp[arithmeticTheory.MULT_SUC]
QED

Theorem sym_scratch_spill_bulk_sim:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  LENGTH offsets <= LENGTH ss.sym_stack /\
  EVERY (\off. off < dimword(:256)) offsets /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (MAP SOSpill offsets)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (2 * LENGTH offsets) cs = AsmOK cs' /\
    sym_steps p env (2 * LENGTH offsets) ss = SymOK ss' /\
    asm_sym_rel p env cs' ss' /\
    ss'.sym_stack = DROP (LENGTH offsets) ss.sym_stack /\
    cs'.as_pc = cs.as_pc + 2 * LENGTH offsets /\
    LIST_REL (\off sv. mem_sval_at ss'.sym_mem_labels off sv /\
      case sv of Val w => word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP off cs'.as_memory)) = w | Lab l d => T)
      offsets (TAKE (LENGTH offsets) ss.sym_stack) /\
    (!b. EVERY (\off. ~in_mem_range off 32 b) offsets ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==>
      b IN FDOM ss.sym_mem_labels \/ EXISTS (\off. in_mem_range off 32 b) offsets)
Proof
  strip_tac >>
  `ss.sym_base.as_pc = cs.as_pc` by metis_tac[asm_sym_rel_pc] >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp (MAP SOSpill offsets))` by simp[] >>
  drule_all sym_scratch_spill_bulk_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  `LENGTH offsets <= LENGTH cs.as_stack` by
    gvs[asm_sym_rel_def, listTheory.LIST_REL_EL_EQN] >>
  drule_all doSwapSimTheory.raw_spill_bulk_steps >>
  disch_then (qspecl_then [`SND (compute_label_offsets p)`, `build_offset_to_pc p`] mp_tac) >>
  strip_tac >> gvs[] >>
  simp[listTheory.LIST_REL_EL_EQN] >> rpt strip_tac >>
  simp[listTheory.EL_TAKE] >>
  `word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (EL n offsets)
      (FOLDL (\mem p. mem_write32 (FST p) (SND p) mem) cs.as_memory
        (ZIP (offsets, TAKE (LENGTH offsets) cs.as_stack))))) = EL n cs.as_stack` by
    (mp_tac (Q.SPECL [`offsets:num list`, `TAKE (LENGTH (offsets:num list)) cs.as_stack`,
       `cs.as_memory`, `n`] doSwapSimTheory.raw_spill_fold_read_occurrence) >>
     simp[listTheory.EL_TAKE]) >>
  Cases_on `EL n ss.sym_stack` >> simp[] >>
  fs[asm_sym_rel_def, listTheory.LIST_REL_EL_EQN] >>
  qpat_x_assum `!n. n < LENGTH ss.sym_stack ==> _`
    (qspec_then `n` mp_tac) >> simp[sval_conc_def]
QED

Theorem sym_raw_spill_restore_schedule_steps:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  LENGTH offsets <= LENGTH ss.sym_stack /\
  EVERY (\off. off < dimword(:256)) offsets /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
  EVERY (\i. i < LENGTH offsets) desired /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp
    (MAP SOSpill offsets ++ MAP SORestore
      (MAP (\i. EL i offsets) (REVERSE desired)))) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (MAP SOSpill offsets ++
        MAP SORestore (MAP (\i. EL i offsets) (REVERSE desired))))) cs = AsmOK cs' /\
    sym_steps p env
      (LENGTH (execute_plan initial_fmp (MAP SOSpill offsets ++
        MAP SORestore (MAP (\i. EL i offsets) (REVERSE desired))))) ss = SymOK ss' /\
    asm_sym_rel p env cs' ss' /\
    ss'.sym_stack = MAP (\i. EL i (TAKE (LENGTH offsets) ss.sym_stack)) desired ++
      DROP (LENGTH offsets) ss.sym_stack /\
    cs'.as_pc = cs.as_pc + 2 * LENGTH offsets + 2 * LENGTH desired /\
    (!b. EVERY (\off. ~in_mem_range off 32 b) offsets ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==>
      b IN FDOM ss.sym_mem_labels \/ EXISTS (\off. in_mem_range off 32 b) offsets)
Proof
  strip_tac >>
  `asm_block_at p cs.as_pc (execute_plan initial_fmp (MAP SOSpill offsets)) /\
   asm_block_at p (cs.as_pc + 2 * LENGTH offsets) (execute_plan initial_fmp
     (MAP SORestore (MAP (\i. EL i offsets) (REVERSE desired))))` by
    gvs[stackOpSimTheory.asm_block_at_append, stackOpSimTheory.execute_plan_append,
        doSwapSimTheory.execute_plan_map_spill_length] >>
  drule_all sym_scratch_spill_bulk_sim >> strip_tac >>
  `EVERY (\off. off < dimword(:256)) (MAP (\i. EL i offsets) (REVERSE desired)) /\
   LIST_REL (\off sv. mem_sval_at ss'.sym_mem_labels off sv /\
      case sv of Val w => word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP off cs'.as_memory)) = w | Lab l d => T)
     (MAP (\i. EL i offsets) (REVERSE desired))
     (MAP (\i. EL i (TAKE (LENGTH offsets) ss.sym_stack)) (REVERSE desired))` by
    (fs[listTheory.EVERY_EL, listTheory.LIST_REL_EL_EQN] >>
     simp[listTheory.EVERY_MAP, rich_listTheory.EVERY_REVERSE,
          listTheory.EVERY_EL, listTheory.LIST_REL_EL_EQN, listTheory.EL_MAP] >>
     simp[listTheory.EL_REVERSE, listTheory.LENGTH_REVERSE]) >>
  `asm_block_at p cs'.as_pc (execute_plan initial_fmp
     (MAP SORestore (MAP (\i. EL i offsets) (REVERSE desired))))` by gvs[] >>
  drule_all sym_scratch_restore_bulk_sim >> strip_tac >>
  qexistsl [`cs''`, `ss''`] >>
  simp[stackOpSimTheory.execute_plan_append,
       doSwapSimTheory.execute_plan_map_spill_length,
       doSwapSimTheory.execute_plan_map_restore_length] >>
  conj_tac >- (mp_tac (Q.SPECL
    [`SND (compute_label_offsets p)`, `build_offset_to_pc p`, `p`,
     `2 * LENGTH (offsets:num list)`, `2 * LENGTH (desired:num list)`,
     `cs`, `cs'`, `cs''`] blockSimHelpersTheory.asm_steps_compose_ok) >> gvs[]) >>
  mp_tac (Q.SPECL [`2 * LENGTH (offsets:num list)`,
    `2 * LENGTH (desired:num list)`, `ss`] sym_steps_add) >>
  gvs[listTheory.MAP_REVERSE]
QED


Theorem list_rel_index_schedule:
  !R xs ys ids. LIST_REL R xs ys /\ EVERY (\i. i < LENGTH xs) ids ==>
    LIST_REL R (MAP (\i. EL i xs) ids) (MAP (\i. EL i ys) ids)
Proof
  rpt strip_tac >>
  fs[listTheory.LIST_REL_EL_EQN, listTheory.EVERY_EL] >>
  simp[listTheory.LIST_REL_EL_EQN, listTheory.EL_MAP]
QED

Theorem list_rel_reversed_index_schedule:
  LIST_REL R (REVERSE items) vals /\ LENGTH items = d + 1 /\ 0 < d /\
  ids = [d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0] /\
  EVERY (\i. i < LENGTH items) ids ==>
  LIST_REL R (REVERSE (MAP (\i. EL i items) ids))
    (MAP (\i. EL i vals) ids)
Proof
  strip_tac >>
  `REVERSE (MAP (\i. EL i items) ids) =
     MAP (\i. EL i (REVERSE items)) ids` by
    (qpat_x_assum `ids = _` SUBST1_TAC >>
     irule doSwapSimTheory.reverse_desired_values >> simp[]) >>
  qpat_x_assum `REVERSE (MAP _ _) = _`
    (fn th => pure_rewrite_tac[th]) >>
  irule list_rel_index_schedule >> gvs[]
QED

Theorem do_swap_deep_symbolic_resources:
  do_swap d ps = (ops,ps') /\ 16 < d /\ d < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  offsets = FST (spill_alloc_n [] ps.ps_alloc (top_n (d + 1) ps.ps_stack)) /\
  ids = [d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0] ==>
  ops = MAP SOSpill offsets ++
    MAP SORestore (MAP (\i. EL i offsets) (REVERSE ids)) /\
  LENGTH offsets = d + 1 /\ ALL_DISTINCT offsets /\
  EVERY (\i. i < LENGTH offsets) ids /\
  EVERY (\off. off < dimword(:256) /\ ps'.ps_alloc.sa_spill_base <= off /\
    off + 32 <= ps'.ps_alloc.sa_next_offset) offsets /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
  (!i op old. i < LENGTH offsets /\ FLOOKUP ps.ps_spilled op = SOME old ==>
    old + 32 <= EL i offsets \/ EL i offsets + 32 <= old) /\
  ps'.ps_spilled = ps.ps_spilled /\
  ps'.ps_stack = TAKE (LENGTH ps.ps_stack - (d + 1)) ps.ps_stack ++
    MAP (\i. EL i (top_n (d + 1) ps.ps_stack)) ids
Proof
  strip_tac >>
  `LENGTH (top_n (d + 1) ps.ps_stack) = d + 1` by
    simp[stackPlanOpsTheory.top_n_def, listTheory.LENGTH_TAKE] >>
  `ops = MAP SOSpill offsets ++
     MAP SORestore (MAP (\i. EL i offsets) (REVERSE ids)) /\
   ps' = ps with <|
     ps_stack := TAKE (LENGTH ps.ps_stack - (d + 1)) ps.ps_stack ++
       MAP (\i. EL i (top_n (d + 1) ps.ps_stack)) ids;
     ps_alloc := FOLDL (\a off. free_spill_slot off a)
       (SND (spill_alloc_n [] ps.ps_alloc (top_n (d + 1) ps.ps_stack))) offsets |>` by
    (mp_tac (Q.SPECL [`d`, `ps`] doSwapSimTheory.do_swap_big_decompose) >>
     simp[LET_THM] >> metis_tac[]) >>
  `ps'.ps_alloc = FOLDL (\a off. free_spill_slot off a)
    (SND (spill_alloc_n [] ps.ps_alloc (top_n (d + 1) ps.ps_stack))) offsets` by simp[] >>
  drule_all doSwapSimTheory.spill_alloc_n_temporary_layout >> strip_tac >>
  `EVERY (\off. off < dimword(:256)) offsets` by
    (qpat_x_assum `EVERY _ ops` mp_tac >> simp[listTheory.EVERY_MAP]) >>
  `EVERY (\i. i < LENGTH offsets) ids` by
    simp[listTheory.EVERY_GENLIST] >>
  simp[] >>
  conj_tac >- gvs[listTheory.EVERY_MEM] >>
  metis_tac[]
QED

Theorem list_rel_deep_swap_schedule:
  LIST_REL R (REVERSE xs) vals /\ d < LENGTH xs /\ 0 < d /\
  ids = [d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0] /\
  EVERY (\i. i < d + 1) ids ==>
  LIST_REL R
    (REVERSE (TAKE (LENGTH xs - (d + 1)) xs ++
      MAP (\i. EL i (top_n (d + 1) xs)) ids))
    (MAP (\i. EL i (TAKE (d + 1) vals)) ids ++ DROP (d + 1) vals)
Proof
  strip_tac >> pure_rewrite_tac[listTheory.REVERSE_APPEND] >>
  irule rich_listTheory.EVERY2_APPEND_suff >> conj_tac
  >- (irule list_rel_reversed_index_schedule >>
      simp[stackPlanOpsTheory.top_n_def, listTheory.LENGTH_TAKE] >>
      gvs[rich_listTheory.EVERY2_TAKE]) >>
  `REVERSE (TAKE (LENGTH xs - (d + 1)) xs) = DROP (d + 1) (REVERSE xs)` by
    simp[rich_listTheory.DROP_REVERSE, rich_listTheory.BUTLASTN_TAKE_UNCOND] >>
  simp[] >> metis_tac[rich_listTheory.EVERY2_DROP]
QED

Theorem sym_scratch_frame_transfer:
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_sym_rel p env cs' ss' /\ ps'.ps_spilled = ps.ps_spilled /\
  ss'.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  EVERY (\off. r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end) offsets /\
  (!off op old. MEM off offsets /\ FLOOKUP ps.ps_spilled op = SOME old ==>
    old + 32 <= off \/ off + 32 <= old) /\
  (!b. EVERY (\off. ~in_mem_range off 32 b) offsets ==>
    FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  (!b. b IN FDOM ss'.sym_mem_labels ==>
    b IN FDOM ss.sym_mem_labels \/ EXISTS (\off. in_mem_range off 32 b) offsets) ==>
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss'
Proof
  strip_tac >>
  `!b off. MEM off offsets /\ in_mem_range off 32 b ==>
    r.sr_spill_base <= b /\ b < r.sr_spill_end` by
    (fs[listTheory.EVERY_MEM, in_mem_range_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  irule sym_frame_inv_region_transfer >> goal_assum (drule_at Any) >>
  conj_tac
  >- (simp[sym_kinds_ok_def] >> conj_tac
      >- (rpt strip_tac >>
          `?sv. op_kind_ok fn ret op sv /\ mem_sval_at ss.sym_mem_labels off sv` by
            metis_tac[sym_frame_inv_def, sym_kinds_ok_def] >>
          qexists_tac `sv` >> simp[] >> irule scratch_disjoint_bulk_cell >>
          goal_assum (drule_at Any) >> qexists_tac `offsets` >>
          simp[] >> simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
      fs[sym_frame_inv_def, sym_kinds_ok_def, listTheory.EXISTS_MEM] >>
      metis_tac[contextCodegenRelPropsTheory.context_spill_byte_of_region]) >>
  qexistsl [`cs`, `ps`, `r`, `ss`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  simp[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem sym_do_swap_deep_frame_sim:
  do_swap d ps = (ops, ps') /\ 16 < d /\ d < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >>
  qabbrev_tac `offsets = FST (spill_alloc_n [] ps.ps_alloc (top_n (d + 1) ps.ps_stack))` >>
  qabbrev_tac `ids = [d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0]` >>
  `offsets = FST (spill_alloc_n [] ps.ps_alloc (top_n (d + 1) ps.ps_stack)) /\
   ids = [d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0]` by
    simp[Abbr `offsets`, Abbr `ids`] >>
  drule_all do_swap_deep_symbolic_resources >> strip_tac >>
  qpat_x_assum `offsets = FST _` kall_tac >>
  `asm_sym_rel p env cs ss /\
   ?top. ss.sym_stack = top ++ srest /\
     LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top` by
    metis_tac[sym_frame_inv_def, sym_kinds_ok_def] >>
  `LENGTH top = LENGTH ps.ps_stack` by metis_tac[listTheory.LIST_REL_LENGTH, listTheory.LENGTH_REVERSE] >>
  `LENGTH offsets <= LENGTH ss.sym_stack /\
   EVERY (\off. off < dimword(:256)) offsets /\
   asm_block_at p cs.as_pc (execute_plan initial_fmp
     (MAP SOSpill offsets ++ MAP SORestore (MAP (\i. EL i offsets) (REVERSE ids))))` by
    (conj_tac >- (qpat_x_assum `ss.sym_stack = _` (fn th => pure_rewrite_tac[th]) >>
       simp[NoAsms, listTheory.LENGTH_APPEND] >> decide_tac) >>
     conj_tac >- (qpat_x_assum `EVERY (\off. off < dimword(:256) /\ _) offsets` mp_tac >>
       simp[NoAsms, listTheory.EVERY_MEM] >> metis_tac[]) >> metis_tac[]) >>
  drule_all sym_raw_spill_restore_schedule_steps >> strip_tac >>
  `LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack)
    (MAP (\i. EL i (TAKE (d + 1) top)) ids ++ DROP (d + 1) top)` by
    (qpat_x_assum `ps'.ps_stack = _` (fn th => pure_rewrite_tac[th]) >>
     irule list_rel_deep_swap_schedule >>
     `0 < d` by decide_tac >> metis_tac[]) >>
  `LENGTH (execute_plan initial_fmp ops) = 2 * LENGTH offsets + 2 * LENGTH ids` by
    (qpat_x_assum `ops = _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, stackOpSimTheory.execute_plan_append,
       doSwapSimTheory.execute_plan_map_spill_length,
       doSwapSimTheory.execute_plan_map_restore_length]) >>
  qexistsl [`cs'`, `ss'`] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  reverse conj_tac >- decide_tac >>
  irule sym_scratch_frame_transfer >> conj_tac
  >- (goal_assum (drule_at Any) >>
      `d + 1 <= LENGTH top` by decide_tac >>
      `TAKE (d + 1) ss.sym_stack = TAKE (d + 1) top /\
       DROP (d + 1) ss.sym_stack = DROP (d + 1) top ++ srest` by
        metis_tac[listTheory.TAKE_APPEND1, listTheory.DROP_APPEND1] >>
      metis_tac[listTheory.APPEND_ASSOC]) >>
  conj_tac >- metis_tac[] >>
  qexistsl [`cs`, `offsets`, `ps`, `r`, `ss`] >>
  conj_tac >- metis_tac[listTheory.MEM_EL] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  conj_tac >- (qpat_x_assum `EVERY (\off. off < dimword(:256) /\ _) offsets` mp_tac >>
    simp[NoAsms, listTheory.EVERY_MEM] >>
    metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >> metis_tac[]
QED

(* Physical swaps expose a single interface at every depth. *)
Theorem sym_do_swap_frame_sim:
  do_swap d ps = (ops, ps') /\ d < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> Cases_on `d <= 16`
  >- (drule_all sym_do_swap_shallow_frame_sim >> simp[]) >>
  `16 < d` by decide_tac >> drule_all sym_do_swap_deep_frame_sim >> simp[]
QED

Theorem sym_do_swap_pair_frame_sim:
  do_swap d ps = (ops1,ps1) /\ do_swap f ps1 = (ops2,ps2) /\
  d < LENGTH ps.ps_stack /\ f < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (ops1 ++ ops2) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps2.ps_alloc.sa_spill_base /\
  ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (ops1 ++ ops2)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps2 cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (ops1 ++ ops2))
Proof
  strip_tac >>
  `spill_alloc_layout_wf ps1.ps_alloc ps1.ps_spilled` by
    metis_tac[doSwapSimTheory.do_swap_multiplicity_layout] >>
  `f < LENGTH ps1.ps_stack` by metis_tac[planWfTheory.do_swap_length, pairTheory.SND] >>
  `r.sr_spill_base <= ps1.ps_alloc.sa_spill_base /\
   ps1.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    metis_tac[allocMonoTheory.do_swap_spill_base,
      allocMonoTheory.do_swap_next_offset, arithmeticTheory.LESS_EQ_TRANS] >>
  gvs[listTheory.EVERY_APPEND, stackOpSimTheory.execute_plan_append,
    stackOpSimTheory.asm_block_at_append] >>
  drule_all sym_do_swap_frame_sim >> strip_tac >>
  `asm_block_at p cs'.as_pc (execute_plan initial_fmp ops2)` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  drule_at (Pat `do_swap f _ = _`) sym_do_swap_frame_sim >>
  disch_then drule_all >> strip_tac >>
  qexistsl [`cs''`, `ss''`] >>
  simp[stackOpSimTheory.asm_steps_add, sym_steps_add] >> decide_tac
QED

Theorem control_plan_address_bounds:
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops ==>
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  (!off. MEM (SOSpill off) ops ==> off < dimword(:256))
Proof
  rewrite_tac[listTheory.EVERY_MEM] >> strip_tac >> conj_tac >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem sym_reorder_restore_frame_sim:
  (case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
     SOME d => ([],ps)
   | NONE => (case FLOOKUP ps.ps_spilled op of
       SOME off => do_restore op ps | NONE => ([],ps))) = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  Cases_on `stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack` >> simp[]
  >- (Cases_on `FLOOKUP ps.ps_spilled op` >> simp[]
      >- (strip_tac >> gvs[execute_plan_def, asm_steps_def, sym_steps_def]) >>
      strip_tac >> drule_all sym_do_restore_frame_sim >> simp[]) >>
  strip_tac >> gvs[execute_plan_def, asm_steps_def, sym_steps_def]
QED

Theorem sym_reorder_prepare_reduce_frame_sim:
  residual_budget_wf_marked spill_base pending ps1 /\
  LENGTH pending <= LENGTH ps1.ps_stack /\
  reduce_depth_plan (LENGTH ps1.ps_stack) pending op f (LENGTH pending) ps1 =
    (reduce_ops,ps2) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) reduce_ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= spill_base /\ ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps1 mid smid /\
  asm_static_wf p /\
  asm_block_at p (cs.as_pc + LENGTH (execute_plan initial_fmp restore_ops))
    (execute_plan initial_fmp reduce_ops) /\
  asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
    (LENGTH (execute_plan initial_fmp restore_ops)) cs = AsmOK mid /\
  sym_steps p env (LENGTH (execute_plan initial_fmp restore_ops)) ss = SymOK smid /\
  mid.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp restore_ops) ==>
  residual_budget_wf_marked spill_base pending ps2 /\
  LENGTH pending <= LENGTH ps2.ps_stack /\
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps2 cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))
Proof
  strip_tac >>
  `residual_budget_wf_marked spill_base pending ps2` by
    metis_tac[deepResidualBudgetTheory.reduce_depth_plan_residual_budget_wf_marked] >>
  `LENGTH pending <= LENGTH ps2.ps_stack` by
    metis_tac[deepResidualBudgetTheory.reduce_depth_plan_target_len_floor] >>
  `!off. MEM (SOSpill off) reduce_ops ==> off < dimword(:256)` by
    metis_tac[control_plan_address_bounds] >>
  `asm_block_at p mid.as_pc (execute_plan initial_fmp reduce_ops)` by gvs[] >>
  drule_all sym_reduce_depth_plan_frame_sim >> strip_tac >>
  simp[] >> qexistsl [`cs'`, `ss'`] >>
  simp[stackOpSimTheory.execute_plan_append] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  simp[stackOpSimTheory.asm_steps_add, sym_steps_add] >> decide_tac
QED

Theorem sym_reorder_prepare_frame_sim:
  !base.
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
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= base /\ ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (restore_ops ++ reduce_ops)) ==>
  residual_budget_wf_marked base pending ps2 /\
  LENGTH pending <= LENGTH ps2.ps_stack /\
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps2 cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))
Proof
  qx_gen_tac `spill_base` >> strip_tac >>
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
  drule_all sym_reorder_restore_frame_sim >> strip_tac >>
  qpat_x_assum `residual_budget_wf_marked spill_base pending ps` kall_tac >>
  Cases_on `dist > 16` >> gvs[]
  >- (`asm_block_at p (cs.as_pc + LENGTH (execute_plan initial_fmp restore_ops))
        (execute_plan initial_fmp reduce_ops) /\
       cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp restore_ops)` by
        metis_tac[arithmeticTheory.ADD_COMM] >> suspend "reduce") >>
  qexistsl [`cs'`, `ss'`] >> fs[execute_plan_def]
QED

Resume sym_reorder_prepare_frame_sim[reduce]:
  drule_all sym_reorder_prepare_reduce_frame_sim >>
  pure_rewrite_tac[stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
  gvs[]
QED

Finalise sym_reorder_prepare_frame_sim

Theorem sym_frame_inv_reorder_relabel:
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  d < LENGTH ps.ps_stack /\ f < LENGTH ps.ps_stack /\
  op = stack_peek d ps.ps_stack /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  operand_equiv dfg op (stack_peek f ps.ps_stack) ==>
  sym_frame_inv p env ctx cplan fn ret srest labs0
    (ps with ps_stack := stack_poke f op
      (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack)) cs ss
Proof
  strip_tac >> fs[sym_frame_inv_def] >>
  drule_all sym_kinds_ok_reorder_relabel >> simp[]
QED

Theorem sym_reorder_place_frame_sim:
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
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  Cases_on `stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack` >> simp[]
  >- (strip_tac >> gvs[execute_plan_def, asm_steps_def, sym_steps_def]) >>
  rename1 `_ = SOME d` >>
  Cases_on `d = f` >> simp[]
  >- (strip_tac >> gvs[execute_plan_def, asm_steps_def, sym_steps_def]) >>
  Cases_on `operand_equiv dfg op (stack_peek f ps.ps_stack)`
  >- suspend "relabel" >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `d < LENGTH ps.ps_stack` by metis_tac[stackModelTheory.stack_get_unfixed_depth_bound] >>
  drule_all (REWRITE_RULE[listTheory.EVERY_APPEND] sym_do_swap_pair_frame_sim) >> simp[]
QED

Resume sym_reorder_place_frame_sim[relabel]:
  strip_tac >> gvs[execute_plan_def, asm_steps_def, sym_steps_def] >>
  irule sym_frame_inv_reorder_relabel >>
  drule stackModelTheory.stack_get_unfixed_depth_props >> simp[]
QED

Finalise sym_reorder_place_frame_sim

Definition control_reorder_place_def:
  control_reorder_place dfg pending op f ps =
    (case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
       NONE => ([],ps)
     | SOME d => if d = f then ([],ps)
       else if f < LENGTH ps.ps_stack /\ operand_equiv dfg op (stack_peek f ps.ps_stack)
       then ([],ps with ps_stack := stack_poke f op
         (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack))
       else (case do_swap d ps of (ops1,ps1) =>
         case do_swap f ps1 of (ops2,ps2) => (ops1 ++ ops2,ps2)))
End

Theorem control_reorder_place_none:
  stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack = NONE ==>
  control_reorder_place dfg pending op f ps = ([],ps)
Proof
  simp[control_reorder_place_def]
QED

Theorem control_reorder_place_fixed:
  stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack = SOME f ==>
  control_reorder_place dfg pending op f ps = ([],ps)
Proof
  simp[control_reorder_place_def]
QED

Theorem control_reorder_place_frame_sim:
  control_reorder_place dfg pending op f ps = (ops,ps') /\
  f < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rewrite_tac[control_reorder_place_def] >>
  MATCH_ACCEPT_TAC sym_reorder_place_frame_sim
QED

Theorem sym_asm_plan_runs_compose:
  asm_steps lo o2pc p (LENGTH (execute_plan initial_fmp ops1)) cs = AsmOK mid /\
  sym_steps p env (LENGTH (execute_plan initial_fmp ops1)) ss = SymOK smid /\
  mid.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops1) /\
  asm_steps lo o2pc p (LENGTH (execute_plan initial_fmp ops2)) mid = AsmOK final /\
  sym_steps p env (LENGTH (execute_plan initial_fmp ops2)) smid = SymOK sfinal /\
  final.as_pc = mid.as_pc + LENGTH (execute_plan initial_fmp ops2) ==>
  asm_steps lo o2pc p (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) cs = AsmOK final /\
  sym_steps p env (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) ss = SymOK sfinal /\
  final.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (ops1 ++ ops2))
Proof
  strip_tac >>
  pure_rewrite_tac[stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
  once_rewrite_tac[stackOpSimTheory.asm_steps_add, sym_steps_add] >>
  simp[]
QED

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
  Cases_on `stack_get_unfixed_depth op (num_ops - (idx + 1)) num_ops ps1.ps_stack` >> simp[]
  >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `(if _ > 16 then _ else _) = (reduce_ops,ps2)` >>
  suspend "placement"
QED

Resume sym_reorder_one_decompose[placement]:
  gvs[pairTheory.UNCURRY_pair_CASE, AllCaseEqs()] >>
  metis_tac[allocMonoTheory.do_swap_next_offset, arithmeticTheory.LESS_EQ_TRANS,
    listTheory.APPEND_ASSOC]
QED

Finalise sym_reorder_one_decompose

Theorem control_reorder_one_decompose:
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
       control_reorder_place dfg pending op (LENGTH pending - (idx + 1)) ps2 = (suffix,ps'))
Proof
  pure_rewrite_tac[control_reorder_place_def] >>
  MATCH_ACCEPT_TAC sym_reorder_one_decompose
QED

Theorem sym_reorder_after_reduce_frame_sim:
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
  control_reorder_place dfg pending op (LENGTH pending - (idx + 1)) ps2 = (suffix,ps') /\
  ps2.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T)
      ((restore_ops ++ reduce_ops) ++ suffix) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= spill_base /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc
    (execute_plan initial_fmp ((restore_ops ++ reduce_ops) ++ suffix)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ((restore_ops ++ reduce_ops) ++ suffix))) cs = AsmOK cs' /\
    sym_steps p env
      (LENGTH (execute_plan initial_fmp ((restore_ops ++ reduce_ops) ++ suffix))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc +
      LENGTH (execute_plan initial_fmp ((restore_ops ++ reduce_ops) ++ suffix))
Proof
  strip_tac >>
  `ps2.ps_alloc.sa_next_offset <= r.sr_spill_end` by decide_tac >>
  gvs[listTheory.EVERY_APPEND, stackOpSimTheory.execute_plan_append,
    stackOpSimTheory.asm_block_at_append] >>
  `asm_block_at p cs.as_pc (execute_plan initial_fmp (restore_ops ++ reduce_ops))` by
    simp[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  `ps2.ps_alloc.sa_next_offset <= r.sr_spill_end` by decide_tac >>
  drule_all (REWRITE_RULE[listTheory.EVERY_APPEND] sym_reorder_prepare_frame_sim) >> strip_tac >>
  `asm_block_at p cs'.as_pc (execute_plan initial_fmp suffix)` by
    (fs[stackOpSimTheory.execute_plan_append] >>
     metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  `spill_alloc_layout_wf ps2.ps_alloc ps2.ps_spilled` by
    fs[deepResidualBudgetTheory.residual_budget_wf_marked_def] >>
  drule_all (SRULE [] (Q.INST [`dfg` |-> `dfg_build_function fn`] control_reorder_place_frame_sim)) >>
  strip_tac >> qexistsl [`cs''`, `ss''`] >>
  drule_all sym_asm_plan_runs_compose >> simp[stackOpSimTheory.execute_plan_append]
QED

Theorem sym_reorder_one_frame_sim_marked:
  !base.
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
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  residual_budget_wf_marked base pending ps' /\ pending_inventory_wf pending ps' /\
  LENGTH pending <= LENGTH ps'.ps_stack /\
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  qx_gen_tac `spill_base` >> strip_tac >>
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
  drule control_reorder_one_decompose >> strip_tac
  >- (gvs[] >> suspend "restore_only") >>
  suspend "after_reduce"
QED

Resume sym_reorder_one_frame_sim_marked[restore_only]:
  drule_all_then strip_assume_tac control_plan_address_bounds >>
  drule_all sym_reorder_restore_frame_sim >> simp[]
QED

Resume sym_reorder_one_frame_sim_marked[after_reduce]:
  gvs[] >>
  drule_all (SRULE [listTheory.APPEND_ASSOC, listTheory.EVERY_APPEND]
    (Q.INST [`dfg` |-> `dfg_build_function fn`] sym_reorder_after_reduce_frame_sim)) >> simp[]
QED

Finalise sym_reorder_one_frame_sim_marked

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

Theorem sym_plan_steps_reorder_cons_frame_sim:
  (!qs tail_ops qs' ac sy.
    residual_budget_wf_marked spill_base pending qs /\ pending_inventory_wf pending qs /\
    LENGTH pending <= LENGTH qs.ps_stack /\
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items qs = (tail_ops,qs') /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) tail_ops /\
    r.sr_spill_base <= qs'.ps_alloc.sa_spill_base /\
    qs'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 qs ac sy /\
    asm_block_at p ac.as_pc (execute_plan initial_fmp tail_ops) ==>
    ?ac' sy'.
      asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
        (LENGTH (execute_plan initial_fmp tail_ops)) ac = AsmOK ac' /\
      sym_steps p env (LENGTH (execute_plan initial_fmp tail_ops)) sy = SymOK sy' /\
      sym_frame_inv p env ctx cplan fn ret srest labs0 qs' ac' sy' /\
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
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\ asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (step_ops ++ rest_ops)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (step_ops ++ rest_ops))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (step_ops ++ rest_ops))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (step_ops ++ rest_ops))
Proof
  strip_tac >> strip_tac >>
  gvs[listTheory.EVERY_APPEND, stackOpSimTheory.execute_plan_append,
      stackOpSimTheory.asm_block_at_append] >>
  drule_all sym_plan_steps_reorder_alloc >> strip_tac >>
  `r.sr_spill_base <= ps1.ps_alloc.sa_spill_base /\
   ps1.ps_alloc.sa_next_offset <= r.sr_spill_end` by simp[] >>
  `op <> dead_stack_marker /\
   (!at. operand_equiv (dfg_build_function fn) op at ==> at <> dead_stack_marker)` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `!at. operand_equiv _ op at ==> _` (assume_tac o SRULE []) >>
  drule_all (SRULE [] (Q.INST [`dfg` |-> `dfg_build_function fn`]
    sym_reorder_one_frame_sim_marked)) >> strip_tac >>
  `asm_block_at p cs'.as_pc (execute_plan initial_fmp rest_ops)` by simp[] >>
  first_x_assum (qspec_then `ps1` mp_tac) >> disch_then drule_all >> strip_tac >>
  `ac'.as_pc = cs'.as_pc + LENGTH (execute_plan initial_fmp rest_ops)` by simp[] >>
  qexistsl [`ac'`, `sy'`] >>
  drule_all sym_asm_plan_runs_compose >> simp[stackOpSimTheory.execute_plan_append]
QED

Theorem sym_plan_steps_reorder_frame_sim_marked:
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
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
    asm_static_wf p /\
    asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
    ?cs' ss'.
      asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
        (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
      sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
      sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
      cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> gvs[foldlSimTheory.plan_steps_def] >>
      simp[execute_plan_def, asm_steps_def, sym_steps_def]) >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  drule reorderSimTheory.plan_steps_cons_result >> strip_tac >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  suspend "step"
QED

Resume sym_plan_steps_reorder_frame_sim_marked[step]:
  rename1 `(\(idx,op) ps. reorder_one dfg pending idx op ps) (idx,op) ps = (step_ops,ps1)` >>
  irule sym_plan_steps_reorder_cons_frame_sim >>
  simp[listTheory.EVERY_DEF] >>
  qexistsl [`idx`, `items`, `op`, `pending`, `ps`, `ps1`, `r`, `spill_base`] >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[]
QED

Finalise sym_plan_steps_reorder_frame_sim_marked

Theorem sym_reorder_plan_frame_sim_marked:
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
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
    asm_static_wf p /\
    asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
    ?cs' ss'.
      asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
        (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
      sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
      sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
      cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  gen_tac >> strip_tac >>
  `EVERY (\(idx,op). idx < LENGTH pending /\ MEM op pending)
    (MAPi (\i op. (i,op)) pending)` by
    (simp[listTheory.EVERY_MEM, pairTheory.FORALL_PROD, indexedListsTheory.MEM_MAPi] >>
     rpt strip_tac >> gvs[] >> metis_tac[listTheory.EL_MEM]) >>
  qpat_x_assum `reorder_plan _ _ _ = _`
    (assume_tac o REWRITE_RULE [reorderSimTheory.reorder_plan_eq_plan_steps]) >>
  drule_all sym_plan_steps_reorder_frame_sim_marked >> simp[]
QED

Theorem sym_restore_spilled_cons_frame_sim:
  (!qs tail_ops qs' ac sy.
    restore_spilled_plan targets qs = (tail_ops,qs') /\
    spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled /\
    (!off. MEM (SORestore off) tail_ops ==> off < dimword(:256)) /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 qs ac sy /\
    asm_block_at p ac.as_pc (execute_plan initial_fmp tail_ops) ==>
    ?ac' sy'.
      asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
        (LENGTH (execute_plan initial_fmp tail_ops)) ac = AsmOK ac' /\
      sym_steps p env (LENGTH (execute_plan initial_fmp tail_ops)) sy = SymOK sy' /\
      sym_frame_inv p env ctx cplan fn ret srest labs0 qs' ac' sy' /\
      ac'.as_pc = LENGTH (execute_plan initial_fmp tail_ops) + ac.as_pc) /\
  do_restore op ps = (ops1,ps1) /\
  restore_spilled_plan targets ps1 = (ops2,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SORestore off) ops1 \/ MEM (SORestore off) ops2 ==> off < dimword(:256)) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (ops1 ++ ops2)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (ops1 ++ ops2))
Proof
  strip_tac >>
  drule_all_then strip_assume_tac generatedPrefixSimTheory.do_restore_layout_wf >>
  gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  `!off. MEM (SORestore off) ops1 ==> off < dimword(:256)` by metis_tac[] >>
  `!off. MEM (SORestore off) ops2 ==> off < dimword(:256)` by metis_tac[] >>
  drule_all_then strip_assume_tac sym_do_restore_frame_sim >>
  `asm_block_at p cs'.as_pc (execute_plan initial_fmp ops2)` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `sym_frame_inv p env ctx cplan fn ret srest labs0 ps' ac' sy'` >>
  qexistsl [`ac'`, `sy'`] >>
  simp[stackOpSimTheory.asm_steps_add, sym_steps_add] >> decide_tac
QED

Theorem sym_restore_spilled_plan_frame_sim:
  !targets ps ops ps' cs ss.
  restore_spilled_plan targets ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  Induct
  >- simp[stackPlanOpsTheory.restore_spilled_plan_def, execute_plan_def,
          asm_steps_def, sym_steps_def] >>
  rpt gen_tac >>
  simp[stackPlanOpsTheory.restore_spilled_plan_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  suspend "cons"
QED

Resume sym_restore_spilled_plan_frame_sim[cons]:
  drule_all sym_restore_spilled_cons_frame_sim >> simp[]
QED

Finalise sym_restore_spilled_plan_frame_sim

Theorem sym_jmp_prepare_frame_sim:
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
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (restore_ops ++ reorder_ops)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reorder_ops))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (restore_ops ++ reorder_ops))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 arranged cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (restore_ops ++ reorder_ops))
Proof
  gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac restore_spilled_plan_generated_facts_marked >>
  `pending_inventory_wf pending prepared` by metis_tac[] >>
  drule_all_then strip_assume_tac fnPlanLineageInventoryTheory.restore_spilled_plan_length_floor >>
  drule_all_then strip_assume_tac deepResidualSimTheory.generated_plan_state_wf_marked_residual_nil >>
  drule_then (qspec_then `pending` assume_tac) residual_budget_wf_marked_nil_pending >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[fnPlanPrefixTheory.generated_plan_state_wf_marked_def] >>
  gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  drule_all_then strip_assume_tac sym_restore_spilled_plan_frame_sim >>
  `asm_block_at p cs'.as_pc (execute_plan initial_fmp reorder_ops)` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  `pending_inventory_wf pending prepared` by metis_tac[] >>
  qpat_x_assum `residual_budget_wf_marked _ [] prepared` kall_tac >>
  drule_all_then strip_assume_tac (SRULE []
    (Q.INST [`dfg` |-> `dfg_build_function fn`] sym_reorder_plan_frame_sim_marked)) >>
  qexistsl [`cs''`, `ss''`] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  simp[stackOpSimTheory.asm_steps_add, sym_steps_add] >> decide_tac
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

Theorem ret_operand_not_code_end:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  label_flow_ok ctx /\ inst.inst_opcode = RET /\
  MEM (Var x) inst.inst_operands ==> ~code_end_var fn x
Proof
  strip_tac >> fs[label_flow_ok_def] >>
  first_x_assum (qspecl_then [`fn`, `inst`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem ret_payload_var_kind:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\
  inst.inst_opcode = RET /\ inst.inst_operands = front ++ [Var pc] /\
  MEM (Var x) front /\ Var x <> dead_stack_marker /\
  op_kind_ok fn ret (Var x) sv ==> ?w. sv = Val w
Proof
  strip_tac >>
  drule_all_then assume_tac fnFrameBoundaryGenRetTheory.ret_payload_not_retpc >>
  `~code_end_var fn x` by
    (irule ret_operand_not_code_end >> metis_tac[listTheory.MEM_APPEND]) >>
  gvs[op_kind_ok_def]
QED

Theorem ret_payload_op_kind:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ label_positions_ok inst /\
  inst.inst_opcode = RET /\ inst.inst_operands = front ++ [Var pc] /\
  MEM op front /\ op <> dead_stack_marker /\ op_kind_ok fn ret op sv ==>
  ?w. sv = Val w
Proof
  strip_tac >> Cases_on `op`
  >- gvs[op_kind_ok_def]
  >- metis_tac[ret_payload_var_kind] >>
  gvs[op_kind_ok_def, label_positions_ok_def, listTheory.EVERY_APPEND,
      listTheory.EVERY_MEM, is_label_operand_def] >>
  metis_tac[is_label_operand_def]
QED

Theorem ret_compute_operands_last_retpc:
  MEM inst (fn_insts (reachable_fn fn)) /\ retpc_shape_ok fn /\
  inst.inst_opcode = RET ==>
  ?front x. compute_operands inst = front ++ [Var x] /\ retpc_var fn x
Proof
  simp[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def] >>
  metis_tac[retpc_shape_ok_def, reachable_retpc_var, listTheory.MEM]
QED

Theorem ret_source_op_kinds:
  MEM inst (fn_insts (reachable_fn fn)) /\ codegen_ready_fn fn /\
  opaque_use_ok fn /\ retpc_shape_ok fn /\ inst_wf inst /\
  MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  inst.inst_opcode = RET /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) ==>
  ?front x. compute_operands inst = front ++ [Var x] /\ retpc_var fn x /\
    (!op sv. MEM op front /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w)
Proof
  strip_tac >> drule_all_then strip_assume_tac ret_compute_operands_last_retpc >>
  `MEM inst (fn_insts fn)` by
    (irule reachable_fn_insts_nonphi >> simp[]) >>
  gvs[compute_operands_def, python_stack_operands_def,
      ir_specific_operand_order_def, fn_shape_ok_def, listTheory.EVERY_MEM] >>
  `label_positions_ok inst` by metis_tac[inst_shape_ok_def] >>
  rpt strip_tac >> `op <> dead_stack_marker` by metis_tac[] >>
  drule_all ret_payload_op_kind >> simp[]
QED

Theorem word_kind_concretization:
  MEM op ops /\ op_kind_ok fn ret op sv /\
  (!op sv. MEM op ops /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) /\
  sval_conc lo sv = SOME w ==> sv = Val w
Proof
  strip_tac >> `?v. sv = Val v` by metis_tac[] >> gvs[sval_conc_def]
QED

Theorem word_kind_prefix_concretization:
  !ops top values.
  LIST_REL (op_kind_ok fn ret) ops top /\
  (!op sv. MEM op ops /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) /\
  LIST_REL (\sv w. sval_conc lo sv = SOME w)
    (top ++ srest) (values ++ rest) /\ LENGTH values = LENGTH ops ==>
  top = MAP Val values
Proof
  Induct >> Cases_on `top` >> Cases_on `values` >>
  simp[] >> rpt strip_tac >>
  metis_tac[word_kind_concretization, listTheory.MEM]
QED

Theorem ret_prepared_symbolic_stack:
  !p env cs ss cp fn ret srest ps front x ra values rest.
  asm_sym_rel p env cs ss /\ sym_kinds_ok cp fn ret srest ps ss /\
  ps.ps_stack = front ++ [Var x] /\ retpc_var fn x /\
  Var x <> dead_stack_marker /\
  (!op sv. MEM op front /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) /\
  cs.as_stack = ra :: values ++ rest /\ LENGTH values = LENGTH front ==>
  ss.sym_stack = Lab ret 0 :: MAP Val values ++ srest
Proof
  rpt gen_tac >> strip_tac >> fs[sym_kinds_ok_def] >>
  gvs[listTheory.REVERSE_APPEND, listTheory.LIST_REL_CONS1] >>
  qpat_x_assum `op_kind_ok fn ret (Var x) _` mp_tac >>
  simp[op_kind_ok_def] >> strip_tac >> gvs[] >>
  rename1 `LIST_REL (op_kind_ok fn ret) (REVERSE front) payload` >>
  `payload = MAP Val values` by
    (irule word_kind_prefix_concretization >>
     fs[asm_sym_rel_def] >> metis_tac[listTheory.MEM_REVERSE, listTheory.LENGTH_REVERSE]) >>
  simp[]
QED

Theorem source_memory_range_label_free:
  !cp labs inst vs off sz.
  (!b. b IN FDOM labs ==> context_spill_byte cp b) /\
  source_memory_reads_disjoint cp inst vs /\
  MEM (off,sz) (source_memory_read_ranges inst vs) ==>
  ~mem_labels_hit labs (in_mem_range off sz)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  gvs[mem_labels_hit_def, in_mem_range_def] >>
  rename1 `source_memory_reads_disjoint cplan inst vs` >>
  rename1 `byte IN FDOM labs` >>
  `context_spill_byte cplan byte` by metis_tac[] >>
  fs[context_spill_byte_def, source_memory_reads_disjoint_def,
     listTheory.EVERY_MEM] >>
  first_x_assum (qspec_then `(off,sz)` mp_tac) >> simp[] >>
  goal_assum (drule_at Any) >> decide_tac
QED

Theorem terminal_source_memory_reads_safe:
  !cp.
  MEM inst.inst_opcode [STOP; RETURN; SELFDESTRUCT; REVERT; INVALID;
    CREATE; CREATE2; RETURNDATACOPY] /\ inst_wf inst /\
  eval_operands inst.inst_operands vs = SOME args /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  (!b. b IN FDOM labs ==> context_spill_byte cp b) /\
  source_memory_reads_disjoint cp inst vs ==>
  ~mem_labels_hit labs (asm_op_mem_reads name args)
Proof
  gen_tac >> strip_tac >>
  fs[listTheory.MEM] >>
  gvs[venomWfTheory.inst_wf_def, asmIRTheory.venom_to_evm_name_def,
      asm_op_mem_reads_def, asmSemTheory.log_table_def, mem_labels_hit_def,
      listTheory.LENGTH_EQ_NUM_compute, eval_operands_def, AllCaseEqs()] >>
  irule (SRULE [mem_labels_hit_def] source_memory_range_label_free) >>
  goal_assum (drule_at (Pat `source_memory_reads_disjoint _ _ _`)) >>
  simp[contextCodegenRelTheory.source_memory_read_ranges_def,
       contextCodegenRelTheory.memory_range_of_operands_def]
QED

Theorem mem_labels_clear_read_safe:
  ~mem_labels_hit (mem_labels_clear labs P) P
Proof
  simp[mem_labels_hit_def, mem_labels_clear_def, finite_mapTheory.FDOM_DRESTRICT] >>
  metis_tac[]
QED

Theorem sym_steps_terminal_extend:
  sym_terminal (sym_steps p env n ss) ==>
  sym_steps p env (n + k) ss = sym_steps p env n ss
Proof
  simp[sym_steps_add] >> Cases_on `sym_steps p env n ss` >>
  simp[sym_terminal_def]
QED

Theorem sym_step_concrete_word_prefix:
  ss.sym_stack = MAP Val args ++ tail /\ LENGTH args = asm_op_arity name /\
  ~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args) ==>
  sym_step_concrete name ss =
    sym_lift (LENGTH args)
      (mem_labels_clear ss.sym_mem_labels (asm_op_mem_writes name args)) ss
      (asm_step_op FEMPTY name (ss.sym_base with as_stack := args))
Proof
  strip_tac >>
  `OPT_MMAP sval_val (MAP Val args) = SOME args` by
    (POP_ASSUM_LIST (K all_tac) >> Induct_on `args` >> simp[sval_val_def]) >>
  `TAKE (asm_op_arity name) ss.sym_stack = MAP Val args` by
    (qpat_x_assum `LENGTH args = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[rich_listTheory.TAKE_APPEND]) >>
  simp[sym_step_concrete_def]
QED

Theorem sym_step_concrete_word_prefix_not_bad:
  ss.sym_stack = MAP Val args ++ tail /\ LENGTH args = asm_op_arity name /\
  ~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args) ==>
  sym_step_concrete name ss <> SymBad e
Proof
  strip_tac >> drule_all sym_step_concrete_word_prefix >>
  disch_then SUBST1_TAC >>
  Cases_on `asm_step_op FEMPTY name (ss.sym_base with as_stack := args)` >>
  simp[sym_lift_def]
QED

Theorem asm_sym_step_rel_terminal:
  asm_sym_step_rel p env sr cr /\ (!e. sr <> SymBad e) /\
  ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
  sym_terminal sr
Proof
  Cases_on `sr` >> Cases_on `cr` >>
  simp[asm_sym_step_rel_def, sym_terminal_def]
QED

Theorem sym_terminal_opcode_concrete:
  MEM name ["STOP"; "RETURN"; "REVERT"; "INVALID"; "SELFDESTRUCT";
            "CREATE"; "CREATE2"; "RETURNDATACOPY"] ==>
  sym_step_op p env name ss = sym_step_concrete name ss
Proof
  simp[listTheory.MEM] >> strip_tac >>
  gvs[sym_step_op_def, asmSemTheory.dup_table_def, asmSemTheory.swap_table_def]
QED

Theorem sym_terminal_step_runs:
  asm_block_at p ss.sym_base.as_pc [inst] /\
  sym_terminal (sym_step p env inst ss) ==>
  sym_steps p env 1 ss = sym_step p env inst ss
Proof
  strip_tac >> rewrite_tac[arithmeticTheory.ONE, sym_steps_def] >>
  gvs[asm_block_at_def] >>
  Cases_on `sym_step p env (EL ss.sym_base.as_pc p) ss` >> gvs[sym_terminal_def]
QED

Theorem sym_terminal_opcode_safe:
  MEM name ["STOP"; "RETURN"; "REVERT"; "INVALID"; "SELFDESTRUCT";
            "CREATE"; "CREATE2"; "RETURNDATACOPY"] /\
  ss.sym_stack = MAP Val args ++ tail /\ LENGTH args = asm_op_arity name /\
  ~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args) ==>
  !e. sym_step p env (AsmOp name) ss <> SymBad e
Proof
  strip_tac >> simp[sym_step_def, sym_terminal_opcode_concrete] >>
  metis_tac[sym_step_concrete_word_prefix_not_bad]
QED

Theorem sym_terminal_step_transfer:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  asm_block_at p cs.as_pc [inst] /\
  asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p) inst cs = cr /\
  (!e. sym_step p env inst ss <> SymBad e) /\
  ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
  sym_terminal (sym_steps p env 1 ss)
Proof
  strip_tac >> drule asm_sym_rel_pc >> strip_tac >>
  `cs.as_pc < LENGTH p /\ EL cs.as_pc p = inst` by
    fs[asm_block_at_def] >>
  drule_all asm_sym_step >> simp[] >> strip_tac >>
  `sym_terminal (sym_step p env inst ss)` by
    metis_tac[asm_sym_step_rel_terminal] >>
  metis_tac[sym_terminal_step_runs]
QED

Theorem sym_terminal_opcode_transfer:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  asm_block_at p cs.as_pc [AsmOp name] /\
  MEM name ["STOP"; "RETURN"; "REVERT"; "INVALID"; "SELFDESTRUCT";
            "CREATE"; "CREATE2"; "RETURNDATACOPY"] /\
  ss.sym_stack = MAP Val args ++ tail /\ LENGTH args = asm_op_arity name /\
  ~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args) /\
  asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
    (AsmOp name) cs = cr /\
  ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
  sym_terminal (sym_steps p env 1 ss)
Proof
  strip_tac >> irule sym_terminal_step_transfer >>
  drule_all sym_terminal_opcode_safe >> metis_tac[]
QED

Theorem sym_revert_postamble_steps:
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp revert_postamble) ==>
  sym_terminal (sym_steps p env 4 ss)
Proof
  strip_tac >>
  fs[revert_postamble_def, execute_plan_def, exec_stack_op_def,
     stackOpSimTheory.asm_block_at_cons] >>
  rewrite_tac[numLib.num_CONV ``4:num``, numLib.num_CONV ``3:num``,
              arithmeticTheory.TWO, arithmeticTheory.ONE, sym_steps_def] >>
  `word_of_bytes F (0w:bytes32) (REVERSE (encode_num_bytes_fuel 32 0)) = 0w`
    by EVAL_TAC >>
  simp[Once sym_step_def, sym_lift_def, asm_step_def, asm_next_def] >>
  simp[Once sym_step_def, sym_lift_def, asm_step_def, asm_next_def] >>
  simp[Once sym_step_def] >>
  simp[sym_step_op_def, asmSemTheory.dup_table_def, asmSemTheory.swap_table_def,
       sym_dup_def, sym_set_stack_def, asm_next_def] >>
  simp[Once sym_step_def, sym_terminal_opcode_concrete] >>
  simp[sym_step_concrete_def, asm_op_arity_def, asm_op_arity_table_def,
       sval_val_def, asm_op_mem_reads_def, asmSemTheory.log_table_def,
       mem_labels_hit_def, in_mem_range_def] >>
  simp[SRULE [asm_step_def] stackOpAsmSimTheory.asm_step_revert,
       asm_revert_op_def, sym_lift_def, sym_terminal_def]
QED

Theorem sym_step_concrete_clears_written_labels:
  ss.sym_stack = MAP Val args ++ tail /\ LENGTH args = asm_op_arity name /\
  ~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args) /\
  sym_step_concrete name ss = SymOK ss' ==>
  ss'.sym_mem_labels =
    mem_labels_clear ss.sym_mem_labels (asm_op_mem_writes name args)
Proof
  strip_tac >> drule_all sym_step_concrete_word_prefix >>
  Cases_on `asm_step_op FEMPTY name (ss.sym_base with as_stack := args)` >>
  simp[sym_lift_def] >> strip_tac >> gvs[]
QED

Theorem sym_returndatacopy_clears_range:
  ss.sym_stack = Val dst :: Val src :: Val sz :: tail /\
  sym_step p env (AsmOp "RETURNDATACOPY") ss = SymOK ss' ==>
  ~mem_labels_hit ss'.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))
Proof
  strip_tac >>
  `ss'.sym_mem_labels = mem_labels_clear ss.sym_mem_labels
      (asm_op_mem_writes "RETURNDATACOPY" [dst;src;sz])` by
    (irule sym_step_concrete_clears_written_labels >>
     gvs[sym_step_def, sym_terminal_opcode_concrete, asm_op_arity_def,
         asm_op_arity_table_def, asm_op_mem_reads_def, asmSemTheory.log_table_def,
         asm_op_mem_writes_def, mem_labels_hit_def]) >>
  simp[asm_op_mem_writes_def, mem_labels_clear_read_safe]
QED

Theorem asm_sym_step_rel_ok:
  asm_sym_step_rel p env sr (AsmOK cs') /\ (!e. sr <> SymBad e) ==>
  ?ss'. sr = SymOK ss' /\ asm_sym_rel p env cs' ss'
Proof
  Cases_on `sr` >> simp[asm_sym_step_rel_def]
QED

Theorem sym_ok_step_transfer:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  asm_block_at p cs.as_pc [inst] /\
  asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p) inst cs = AsmOK cs' /\
  (!e. sym_step p env inst ss <> SymBad e) ==>
  ?ss'. sym_step p env inst ss = SymOK ss' /\ asm_sym_rel p env cs' ss'
Proof
  strip_tac >>
  `cs.as_pc < LENGTH p /\ EL cs.as_pc p = inst` by fs[asm_block_at_def] >>
  drule_all asm_sym_step >> simp[] >> metis_tac[asm_sym_step_rel_ok]
QED

Theorem sym_returndatacopy_success_inventory:
  ss.sym_stack = Val dst :: Val src :: Val sz :: tail /\
  sym_step p env (AsmOp "RETURNDATACOPY") ss = SymOK ss' ==>
  ss'.sym_stack = tail /\
  (!b. b IN FDOM ss'.sym_mem_labels ==> b IN FDOM ss.sym_mem_labels)
Proof
  strip_tac >>
  `sym_step_concrete "RETURNDATACOPY" ss = SymOK ss'` by
    gvs[sym_step_def, sym_terminal_opcode_concrete] >>
  gvs[sym_step_concrete_def, asm_op_arity_def, asm_op_arity_table_def,
      sval_val_def, asm_op_mem_reads_def, asmSemTheory.log_table_def,
      mem_labels_hit_def] >>
  gvs[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
      asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
      asm_step_extcall_def, asm_step_copy_def, asm_returndatacopy_def] >>
  Cases_on `LENGTH ss.sym_base.as_returndata < w2n src + w2n sz` >>
  Cases_on `sz = 0w` >>
  gvs[sym_lift_def, asm_next_def, mem_labels_clear_def, finite_mapTheory.FDOM_DRESTRICT]
QED

Theorem sym_returndatacopy_success_transfer:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  asm_block_at p cs.as_pc [AsmOp "RETURNDATACOPY"] /\
  ss.sym_stack = Val dst :: Val src :: Val sz :: tail /\
  asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
    (AsmOp "RETURNDATACOPY") cs = AsmOK cs' ==>
  ?ss'. sym_step p env (AsmOp "RETURNDATACOPY") ss = SymOK ss' /\
        asm_sym_rel p env cs' ss' /\
        ~mem_labels_hit ss'.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))
Proof
  strip_tac >>
  `!e. sym_step p env (AsmOp "RETURNDATACOPY") ss <> SymBad e` by
    (irule sym_terminal_opcode_safe >> simp[] >>
     qexistsl [`[dst;src;sz]`, `tail`] >>
     simp[asm_op_arity_def, asm_op_arity_table_def, asm_op_mem_reads_def,
          asmSemTheory.log_table_def, mem_labels_hit_def]) >>
  drule_all sym_ok_step_transfer >> strip_tac >>
  metis_tac[sym_returndatacopy_clears_range]
QED

Theorem restore_swap_sequence_member:
  MEM i idxs ==>
  MEM (SORestore (EL i offsets))
    (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) idxs))
Proof
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[listTheory.MEM]
QED

Theorem deep_dup_restore_sequence_member:
  31 < d ==>
  MEM (SORestore (EL (d - 16) offsets))
    (FLAT (MAP (\i. [SORestore (EL i offsets); SOSwap 1])
      (GENLIST (\i. d - (i + 16)) (d - 15))))
Proof
  strip_tac >> irule restore_swap_sequence_member >>
  simp[listTheory.MEM_GENLIST] >> qexists_tac `0` >> simp[]
QED

Theorem do_dup_no_restore_shallow:
  do_dup d ps = (ops, ps') /\
  (!off. ~MEM (SORestore off) ops) ==> d <= 15
Proof
  Cases_on `d <= 15` >- simp[] >>
  simp[stackPlanOpsTheory.do_dup_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >>
  Cases_on `d <= 31`
  >- (gvs[listTheory.MEM_APPEND, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
      metis_tac[listTheory.MEM]) >>
  fs[listTheory.MEM_APPEND] >>
  metis_tac[deep_dup_restore_sequence_member, arithmeticTheory.NOT_LESS_EQUAL]
QED

Theorem do_dup_read_only_shallow:
  do_dup d ps = (ops, ps') /\ d < LENGTH ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ops) ==> d <= 15
Proof
  Cases_on `d <= 15` >- simp[] >> strip_tac >>
  `d > 15` by decide_tac >>
  drule_all doSwapSimTheory.do_dup_big_decompose >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  gvs[listTheory.MEM_APPEND, listTheory.MEM_MAP] >>
  `FST (spill_alloc_n [] ps.ps_alloc
    (REVERSE (top_n (d - 15) ps.ps_stack))) = []` by
    (Cases_on `FST (spill_alloc_n [] ps.ps_alloc
      (REVERSE (top_n (d - 15) ps.ps_stack)))` >> gvs[] >> metis_tac[listTheory.MEM]) >>
  pop_assum (mp_tac o AP_TERM ``LENGTH:num list -> num``) >>
  simp[doSwapSimTheory.spill_alloc_n_offsets_length, stackPlanOpsTheory.top_n_def] >>
  decide_tac
QED

Theorem do_restore_read_only_replay:
  do_restore op ps = (ops, ps') /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  strip_tac >> Cases_on `FLOOKUP ps.ps_spilled op` >>
  gvs[stackPlanOpsTheory.do_restore_def, mixedPrefixSimTheory.apply_prefix_ops_def,
      mixedPrefixSimTheory.apply_prefix_op_def, mixedPrefixSimTheory.prefix_spill_wf_def,
      mixedPrefixSimTheory.spill_op_wf_def] >>
  rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
  `spill_lookup off ps.ps_spilled = op` by
    (simp[mixedPrefixSimTheory.spill_lookup_def] >>
     metis_tac[planAlignTheory.spill_hilbert_unique]) >> simp[] >> metis_tac[]
QED

Theorem do_dup_read_only_replay:
  do_dup d ps = (ops, ps') /\ d < LENGTH ps.ps_stack /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) ops) ==>
  prefix_spill_wf fmp lo ops qs /\
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  strip_tac >> drule_all do_dup_read_only_shallow >> strip_tac >>
  gvs[stackPlanOpsTheory.do_dup_def, mixedPrefixSimTheory.apply_prefix_ops_def,
      mixedPrefixSimTheory.apply_prefix_op_def, strongPrefixSimTheory.apply_simple_op_def,
      mixedPrefixSimTheory.prefix_spill_wf_def, mixedPrefixSimTheory.spill_op_wf_def,
      stackModelTheory.stack_dup_def, stackModelTheory.stack_peek_def]
QED

Theorem emit_var_input_unspilled_read_only_replay:
  FLOOKUP ps.ps_spilled (Var v) = NONE /\
  emit_one_input opc nl (Var v) ps = (ops, ps') /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) ops) ==>
  prefix_spill_wf fmp lo ops qs /\
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def] >>
  strip_tac >> Cases_on `MEM v nl` >>
  gvs[mixedPrefixSimTheory.apply_prefix_ops_def, mixedPrefixSimTheory.prefix_spill_wf_def] >>
  Cases_on `stack_get_depth (Var v) ps.ps_stack` >>
  gvs[mixedPrefixSimTheory.apply_prefix_ops_def, mixedPrefixSimTheory.prefix_spill_wf_def] >>
  rename1 `stack_get_depth _ _ = SOME dist` >>
  Cases_on `do_dup dist ps` >> gvs[] >>
  metis_tac[do_dup_read_only_replay, planAlignTheory.stack_get_depth_bound]
QED

Theorem emit_var_input_spilled_read_only_replay:
  FLOOKUP ps.ps_spilled (Var v) = SOME off /\
  emit_one_input opc nl (Var v) ps = (ops, ps') /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  strip_tac >>
  `spill_lookup off ps.ps_spilled = Var v` by
    (simp[mixedPrefixSimTheory.spill_lookup_def] >>
     metis_tac[planAlignTheory.spill_hilbert_unique]) >>
  Cases_on `MEM v nl` >>
  gvs[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
      stackPlanOpsTheory.do_restore_def, stackPlanOpsTheory.do_dup_def,
      stackModelTheory.stack_get_depth_def, stackModelTheory.stack_find_def,
      stackModelTheory.stack_push_def, stackModelTheory.stack_dup_def,
      stackModelTheory.stack_peek_def, listTheory.REVERSE_SNOC, listTheory.EL_SNOC,
      mixedPrefixSimTheory.apply_prefix_ops_def, mixedPrefixSimTheory.apply_prefix_op_def,
      strongPrefixSimTheory.apply_simple_op_def,
      mixedPrefixSimTheory.prefix_spill_wf_def, mixedPrefixSimTheory.spill_op_wf_def] >>
  metis_tac[]
QED

Theorem emit_one_input_read_only_replay:
  emit_one_input opc nl op ps = (ops, ps') /\ opc <> INVOKE /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) ops) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  Cases_on `op`
  >- (rpt strip_tac >>
      gvs[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
          mixedPrefixSimTheory.apply_prefix_ops_def, mixedPrefixSimTheory.apply_prefix_op_def,
          strongPrefixSimTheory.apply_simple_op_def, stackModelTheory.stack_push_def,
          mixedPrefixSimTheory.prefix_spill_wf_def, mixedPrefixSimTheory.spill_op_wf_def])
  >- (strip_tac >> rename1 `Var v` >> Cases_on `FLOOKUP ps.ps_spilled (Var v)`
      >- (irule emit_var_input_unspilled_read_only_replay >> simp[] >> metis_tac[]) >>
      irule emit_var_input_spilled_read_only_replay >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
      mixedPrefixSimTheory.apply_prefix_ops_def, mixedPrefixSimTheory.apply_prefix_op_def,
      strongPrefixSimTheory.apply_simple_op_def, stackModelTheory.stack_push_def,
      mixedPrefixSimTheory.prefix_spill_wf_def, mixedPrefixSimTheory.spill_op_wf_def]
QED

Theorem emit_input_plan_read_only_replay:
  !inputs ps qs opc nl ins ps1 fmp lo.
  emit_input_plan opc inputs nl ps = (ins, ps1) /\ opc <> INVOKE /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) ins) /\
  (!off. MEM (SORestore off) ins ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ins qs /\
  (apply_prefix_ops fmp lo ins qs).ps_stack = ps1.ps_stack /\
  (apply_prefix_ops fmp lo ins qs).ps_spilled = ps1.ps_spilled
Proof
  Induct >> simp[emit_input_plan_def, mixedPrefixSimTheory.apply_prefix_ops_def,
                mixedPrefixSimTheory.prefix_spill_wf_def] >> rpt gen_tac >>
  Cases_on `emit_one_input opc (operand_vars inputs ++ nl) h ps` >>
  Cases_on `emit_input_plan opc inputs nl r` >> simp[] >> strip_tac >>
  gvs[listTheory.MEM_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
  drule_all emit_one_input_read_only_replay >>
  disch_then (qspecl_then [`lo`, `fmp`] strip_assume_tac) >>
  `!op1 off1 op2 off2.
    FLOOKUP r.ps_spilled op1 = SOME off1 /\
    FLOOKUP r.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1` by
    (drule_at Any doSwapSimTheory.safe_prefix_spilled_separated >>
     simp[] >> disch_then assume_tac >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[doSwapSimTheory.prefix_spill_wf_append, planAlignTheory.apply_prefix_ops_append] >>
  first_x_assum drule >> disch_then irule >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem do_dup_spill_free_stack_replay:
  do_dup d ps = (ops, ps') /\ qs.ps_stack = ps.ps_stack /\
  (!off. ~MEM (SORestore off) ops) ==>
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack
Proof
  strip_tac >> drule do_dup_no_restore_shallow >> simp[] >> strip_tac >>
  gvs[stackPlanOpsTheory.do_dup_def, mixedPrefixSimTheory.apply_prefix_ops_def,
      mixedPrefixSimTheory.apply_prefix_op_def, strongPrefixSimTheory.apply_simple_op_def,
      stackModelTheory.stack_dup_def, stackModelTheory.stack_peek_def]
QED

Theorem emit_var_input_unspilled_stack_replay:
  FLOOKUP ps.ps_spilled (Var v) = NONE /\
  emit_one_input opc nl (Var v) ps = (ops, ps') /\
  qs.ps_stack = ps.ps_stack /\ (!off. ~MEM (SORestore off) ops) ==>
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack
Proof
  simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def] >>
  strip_tac >> Cases_on `MEM v nl` >>
  gvs[mixedPrefixSimTheory.apply_prefix_ops_def] >>
  Cases_on `stack_get_depth (Var v) ps.ps_stack` >>
  gvs[mixedPrefixSimTheory.apply_prefix_ops_def] >>
  rename1 `stack_get_depth _ _ = SOME dist` >>
  Cases_on `do_dup dist ps` >> gvs[] >>
  metis_tac[do_dup_spill_free_stack_replay]
QED

Theorem emit_var_input_spilled_has_restore:
  FLOOKUP ps.ps_spilled (Var v) = SOME off /\
  emit_one_input opc nl (Var v) ps = (ops, ps') ==>
  MEM (SORestore off) ops
Proof
  simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
       stackPlanOpsTheory.do_restore_def] >>
  strip_tac >> Cases_on `MEM v nl` >> gvs[] >>
  Cases_on `stack_get_depth (Var v) (stack_push (Var v) ps.ps_stack)` >> gvs[] >>
  pairarg_tac >> gvs[]
QED

Theorem emit_one_input_spill_free_stack_replay:
  emit_one_input opc nl op ps = (ops, ps') /\ opc <> INVOKE /\
  qs.ps_stack = ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack
Proof
  Cases_on `op`
  >- (rpt strip_tac >> gvs[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
           mixedPrefixSimTheory.apply_prefix_ops_def, mixedPrefixSimTheory.apply_prefix_op_def,
           strongPrefixSimTheory.apply_simple_op_def, stackModelTheory.stack_push_def])
  >- (rpt strip_tac >> Cases_on `FLOOKUP ps.ps_spilled (Var s)` >>
      metis_tac[emit_var_input_unspilled_stack_replay, emit_var_input_spilled_has_restore]) >>
  rpt strip_tac >> gvs[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
       mixedPrefixSimTheory.apply_prefix_ops_def, mixedPrefixSimTheory.apply_prefix_op_def,
       strongPrefixSimTheory.apply_simple_op_def, stackModelTheory.stack_push_def]
QED

Theorem emit_input_plan_spill_free_stack_replay:
  !inputs ps qs opc nl ins ps1 fmp lo.
  emit_input_plan opc inputs nl ps = (ins, ps1) /\ opc <> INVOKE /\
  qs.ps_stack = ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ins /\ ~MEM (SORestore off) ins) ==>
  (apply_prefix_ops fmp lo ins qs).ps_stack = ps1.ps_stack
Proof
  Induct >> simp[emit_input_plan_def, mixedPrefixSimTheory.apply_prefix_ops_def] >>
  rpt gen_tac >>
  Cases_on `emit_one_input opc (operand_vars inputs ++ nl) h ps` >>
  Cases_on `emit_input_plan opc inputs nl r` >> simp[] >> strip_tac >>
  gvs[listTheory.MEM_APPEND, planAlignTheory.apply_prefix_ops_append] >>
  first_x_assum irule >> simp[] >>
  metis_tac[emit_one_input_spill_free_stack_replay]
QED

Theorem do_restore_read_only_kind_replay:
  do_restore op ps = (ops, ps') /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  strip_tac >> Cases_on `FLOOKUP ps.ps_spilled op` >>
  gvs[stackPlanOpsTheory.do_restore_def, mixedPrefixSimTheory.apply_prefix_ops_def,
      mixedPrefixSimTheory.apply_prefix_op_def, mixedPrefixSimTheory.prefix_spill_wf_def,
      mixedPrefixSimTheory.spill_op_wf_def] >>
  rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
  `spill_lookup off ps.ps_spilled = op` by
    (simp[mixedPrefixSimTheory.spill_lookup_def] >>
     metis_tac[planAlignTheory.spill_hilbert_unique]) >>
  simp[stackModelTheory.stack_push_def, listTheory.LIST_REL_SNOC] >> metis_tac[]
QED

Theorem do_swap_read_only_shallow:
  do_swap d ps = (ops, ps') /\ ps.ps_stack <> [] /\
  (!off. ~MEM (SOSpill off) ops) ==> d <= 16
Proof
  Cases_on `d <= 16` >- simp[] >>
  simp[stackPlanOpsTheory.do_swap_def] >> strip_tac >>
  pairarg_tac >> gvs[listTheory.MEM_APPEND] >>
  spose_not_then strip_assume_tac >>
  qspecl_then [`top_n (d + 1) ps.ps_stack`, `[]`, `[]`, `ps.ps_alloc`]
    mp_tac doSwapSimTheory.spill_foldl_ops_eq_map >> simp[] >> strip_tac >>
  `FST (spill_alloc_n [] ps.ps_alloc (top_n (d + 1) ps.ps_stack)) = []` by
    (Cases_on `FST (spill_alloc_n [] ps.ps_alloc (top_n (d + 1) ps.ps_stack))` >>
     gvs[] >> metis_tac[listTheory.MEM]) >>
  pop_assum (mp_tac o AP_TERM ``LENGTH:num list -> num``) >>
  simp[doSwapSimTheory.spill_alloc_n_offsets_length, stackPlanOpsTheory.top_n_def] >>
  Cases_on `ps.ps_stack` >> gvs[]
QED

Theorem do_swap_no_restore_shallow:
  do_swap d ps = (ops, ps') /\
  (!off. ~MEM (SORestore off) ops) ==> d <= 16
Proof
  Cases_on `d <= 16` >- simp[] >>
  simp[stackPlanOpsTheory.do_swap_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[listTheory.MEM_APPEND, listTheory.MEM_MAP] >>
  metis_tac[listTheory.MEM, listTheory.MEM_REVERSE, listTheory.MEM_APPEND]
QED

Theorem list_rel_stack_swap:
  LIST_REL R xs ys ==> LIST_REL R (stack_swap d xs) (stack_swap d ys)
Proof
  strip_tac >> Cases_on `xs = []`
  >- gvs[stackModelTheory.stack_swap_def, listTheory.LUPDATE_def] >>
  fs[listTheory.LIST_REL_EL_EQN] >>
  rw[listTheory.LIST_REL_EL_EQN, stackModelTheory.stack_swap_def,
     listTheory.EL_LUPDATE] >>
  rpt IF_CASES_TAC >> simp[] >> first_x_assum irule >> decide_tac
QED

Theorem do_swap_spill_free_kind_replay:
  do_swap d ps = (ops, ps') /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  strip_tac >> drule do_swap_no_restore_shallow >> simp[] >> strip_tac >>
  Cases_on `d = 0`
  >- gvs[stackPlanOpsTheory.do_swap_def, mixedPrefixSimTheory.apply_prefix_ops_def] >>
  gvs[stackPlanOpsTheory.do_swap_def, mixedPrefixSimTheory.apply_prefix_ops_def,
      mixedPrefixSimTheory.apply_prefix_op_def, strongPrefixSimTheory.apply_simple_op_def] >>
  irule list_rel_stack_swap >> simp[]
QED

Theorem do_swap_read_only_kind_replay:
  do_swap d ps = (ops, ps') /\ ps.ps_stack <> [] /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) ops) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled /\
  ps'.ps_stack <> []
Proof
  strip_tac >> drule_all do_swap_read_only_shallow >> strip_tac >>
  Cases_on `d = 0`
  >- gvs[stackPlanOpsTheory.do_swap_def, mixedPrefixSimTheory.apply_prefix_ops_def,
         mixedPrefixSimTheory.prefix_spill_wf_def] >>
  gvs[stackPlanOpsTheory.do_swap_def, mixedPrefixSimTheory.apply_prefix_ops_def,
      mixedPrefixSimTheory.apply_prefix_op_def, strongPrefixSimTheory.apply_simple_op_def,
      mixedPrefixSimTheory.prefix_spill_wf_def, mixedPrefixSimTheory.spill_op_wf_def] >>
  conj_tac >- (irule list_rel_stack_swap >> simp[]) >>
  simp[stackModelTheory.stack_swap_def, listTheory.LUPDATE_NIL]
QED

Theorem do_swap_pair_read_only_kind_replay:
  do_swap d ps = (ops1,ps1) /\ do_swap f ps1 = (ops2,ps2) /\
  ps.ps_stack <> [] /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) (ops1 ++ ops2)) ==>
  prefix_spill_wf fmp lo (ops1 ++ ops2) qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo (ops1 ++ ops2) qs).ps_stack ps2.ps_stack /\
  (apply_prefix_ops fmp lo (ops1 ++ ops2) qs).ps_spilled = ps2.ps_spilled
Proof
  simp[listTheory.MEM_APPEND, FORALL_AND_THM] >> strip_tac >>
  drule_all do_swap_read_only_kind_replay >>
  disch_then (qspecl_then [`lo`, `fmp`] strip_assume_tac) >>
  simp[doSwapSimTheory.prefix_spill_wf_append, planAlignTheory.apply_prefix_ops_append] >>
  drule_all do_swap_read_only_kind_replay >>
  disch_then (qspecl_then [`lo`, `fmp`] strip_assume_tac) >> simp[]
QED

Theorem list_rel_op_kind_equiv_trans:
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv) xs ys /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv) ys zs ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv) xs zs
Proof
  rw[listTheory.LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem reorder_restore_no_restore_identity:
  (case stack_get_unfixed_depth op f n ps.ps_stack of
     NONE => (case FLOOKUP ps.ps_spilled op of NONE => ([],ps)
                | SOME off => do_restore op ps)
   | SOME d => ([],ps)) = (ops,ps1) /\
  (!off. ~MEM (SORestore off) ops) ==> ops = [] /\ ps1 = ps
Proof
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[stackPlanOpsTheory.do_restore_def] >> metis_tac[listTheory.MEM]
QED

Theorem do_swap_pair_spill_free_kind_replay:
  do_swap d ps = (ops1,ps1) /\ do_swap f ps1 = (ops2,ps2) /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SORestore off) (ops1 ++ ops2)) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo (ops1 ++ ops2) qs).ps_stack ps2.ps_stack
Proof
  simp[listTheory.MEM_APPEND, planAlignTheory.apply_prefix_ops_append] >>
  metis_tac[do_swap_spill_free_kind_replay]
QED

Theorem stack_exchange_kind_replay:
  stack_get_unfixed_depth op f n ps.ps_stack = SOME d /\
  f < LENGTH ps.ps_stack /\ dfg = dfg_build_function fn /\
  ssa_form fn /\ fn_shape_ok fn /\
  operand_equiv dfg op (stack_peek f ps.ps_stack) /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack (stack_poke f op (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack))
Proof
  strip_tac >> drule stackModelTheory.stack_get_unfixed_depth_props >> strip_tac >>
  metis_tac[stack_exchange_op_kind_equiv, list_rel_op_kind_equiv_trans]
QED

Theorem reorder_swap_pair_case_kind_replay:
  (case do_swap d ps of (ops1,ps1) =>
     case do_swap f ps1 of (ops2,ps2) => (ops1 ++ ops2,ps2)) = (ops,ps') /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  strip_tac >> gvs[AllCaseEqs()] >>
  irule do_swap_pair_spill_free_kind_replay >>
  simp[listTheory.MEM_APPEND] >> metis_tac[]
QED

Theorem reorder_swap_pair_case_read_only_kind_replay:
  (case do_swap d ps of (ops1,ps1) =>
     case do_swap f ps1 of (ops2,ps2) => (ops1 ++ ops2,ps2)) = (ops,ps') /\
  ps.ps_stack <> [] /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) ops) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  strip_tac >> gvs[AllCaseEqs()] >>
  irule do_swap_pair_read_only_kind_replay >>
  simp[listTheory.MEM_APPEND] >> metis_tac[]
QED

Theorem control_reorder_place_read_only_kind_replay:
  control_reorder_place dfg pending op f ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) ops) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  simp[control_reorder_place_def] >>
  Cases_on `stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack` >> simp[]
  >- (rpt strip_tac >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def,
                           mixedPrefixSimTheory.prefix_spill_wf_def]) >>
  rename1 `_ = SOME d` >> Cases_on `d = f` >> simp[]
  >- (rpt strip_tac >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def,
                           mixedPrefixSimTheory.prefix_spill_wf_def]) >>
  Cases_on `f < LENGTH ps.ps_stack /\ operand_equiv dfg op (stack_peek f ps.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def,
                       mixedPrefixSimTheory.prefix_spill_wf_def] >>
      metis_tac[stack_exchange_kind_replay]) >>
  strip_tac >> irule reorder_swap_pair_case_read_only_kind_replay >> simp[] >>
  qexistsl [`d`, `f`, `ps`] >> simp[] >>
  drule stackModelTheory.stack_get_unfixed_depth_props >> strip_tac >>
  Cases_on `ps.ps_stack` >> gvs[]
QED

Theorem control_reorder_place_spill_free_kind_replay:
  control_reorder_place dfg pending op f ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  simp[control_reorder_place_def] >>
  Cases_on `stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack` >> simp[]
  >- (rpt strip_tac >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def]) >>
  rename1 `_ = SOME d` >> Cases_on `d = f` >> simp[]
  >- (rpt strip_tac >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def]) >>
  Cases_on `f < LENGTH ps.ps_stack /\ operand_equiv dfg op (stack_peek f ps.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def] >>
      metis_tac[stack_exchange_kind_replay]) >>
  metis_tac[reorder_swap_pair_case_kind_replay]
QED

Theorem reorder_reduce_no_spill_identity:
  (if (dist:num) > 16 then reduce_depth_plan (LENGTH ps.ps_stack) pending op f n ps
   else ([],ps)) = (ops,ps1) /\
  (!off. ~MEM (SOSpill off) ops) ==> ops = [] /\ ps1 = ps
Proof
  Cases_on `dist > 16` >> simp[] >>
  metis_tac[fnFrameStepsRevertForwardTheory.rf_reduce_spill_free]
QED

Theorem reorder_restore_read_only_kind_replay:
  (case stack_get_unfixed_depth op f n ps.ps_stack of
     NONE => (case FLOOKUP ps.ps_spilled op of NONE => ([],ps)
                | SOME off => do_restore op ps)
   | SOME d => ([],ps)) = (ops,ps') /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[]
  >- (Cases_on `FLOOKUP ps.ps_spilled op` >> simp[]
      >- (rpt strip_tac >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def,
                              mixedPrefixSimTheory.prefix_spill_wf_def]) >>
      metis_tac[do_restore_read_only_kind_replay]) >>
  rpt strip_tac >> gvs[mixedPrefixSimTheory.apply_prefix_ops_def,
                       mixedPrefixSimTheory.prefix_spill_wf_def]
QED

Theorem reorder_one_read_only_decompose:
  reorder_one dfg pending idx op ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops) ==>
  ?restore_ops ps1 suffix.
    (case stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
        (LENGTH pending) ps.ps_stack of
       NONE => (case FLOOKUP ps.ps_spilled op of NONE => ([],ps)
                  | SOME off => do_restore op ps)
     | SOME d => ([],ps)) = (restore_ops,ps1) /\
    ops = restore_ops ++ suffix /\
    control_reorder_place dfg pending op (LENGTH pending - (idx + 1)) ps1 = (suffix,ps')
Proof
  strip_tac >> drule control_reorder_one_decompose >> strip_tac
  >- (qexistsl [`restore_ops`, `ps1`, `[]`] >>
      simp[control_reorder_place_def]) >>
  `reduce_ops = [] /\ ps2 = ps1` by
    (irule reorder_reduce_no_spill_identity >>
     fs[listTheory.MEM_APPEND] >> metis_tac[]) >>
  gvs[] >> metis_tac[]
QED

Theorem reorder_one_read_only_kind_replay:
  reorder_one dfg pending idx op ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) ops) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  strip_tac >> drule_all reorder_one_read_only_decompose >> strip_tac >>
  gvs[listTheory.MEM_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
  drule_all reorder_restore_read_only_kind_replay >>
  disch_then (qspecl_then [`lo`, `fmp`] strip_assume_tac) >>
  simp[doSwapSimTheory.prefix_spill_wf_append, planAlignTheory.apply_prefix_ops_append] >>
  metis_tac[control_reorder_place_read_only_kind_replay]
QED

Theorem reorder_steps_read_only_kind_replay:
  !items ps qs ops ps' dfg pending fn ret fmp lo.
  plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) ops) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  Induct
  >- simp[foldlSimTheory.plan_steps_def, mixedPrefixSimTheory.apply_prefix_ops_def,
          mixedPrefixSimTheory.prefix_spill_wf_def] >>
  Cases_on `h` >> rpt gen_tac >> simp[foldlSimTheory.plan_steps_def] >>
  Cases_on `reorder_one dfg pending q r ps` >>
  rename1 `reorder_one _ _ _ _ _ = (step_ops,mid)` >>
  Cases_on `plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items mid` >>
  simp[] >> strip_tac >>
  gvs[listTheory.MEM_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
  drule_all (SRULE [] (Q.INST [`dfg` |-> `dfg_build_function fn`]
    reorder_one_read_only_kind_replay)) >>
  disch_then (qspecl_then [`lo`, `fmp`] strip_assume_tac) >>
  `!op1 off1 op2 off2.
    FLOOKUP mid.ps_spilled op1 = SOME off1 /\
    FLOOKUP mid.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1` by
    (drule_at Any doSwapSimTheory.safe_prefix_spilled_separated >>
     simp[] >> disch_then assume_tac >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[doSwapSimTheory.prefix_spill_wf_append, planAlignTheory.apply_prefix_ops_append] >>
  first_x_assum drule >> disch_then irule >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem reorder_plan_read_only_kind_replay:
  reorder_plan dfg pending ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) ops) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  rewrite_tac[reorderSimTheory.reorder_plan_eq_plan_steps] >>
  MATCH_ACCEPT_TAC reorder_steps_read_only_kind_replay
QED

Theorem sym_frame_inv_kind_transport:
  !p env ctx cp fn ret srest labs0 ps cs ss qs.
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    ps.ps_stack qs.ps_stack /\ ps.ps_spilled = qs.ps_spilled ==>
  sym_frame_inv p env ctx cp fn ret srest labs0 qs cs ss
Proof
  rpt gen_tac >> simp[sym_frame_inv_def, sym_kinds_ok_def] >> strip_tac >>
  qexists `top` >> simp[] >> irule list_rel_op_kind_transport >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem selected_prefix_read_only_kind_replay:
  !opc inputs nl ps iops ps1 dfg rops ps2 fn ret fmp lo.
  emit_input_plan opc inputs nl ps = (iops,ps1) /\
  reorder_plan dfg inputs ps1 = (rops,ps2) /\ opc <> INVOKE /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) (iops ++ rops)) /\
  (!off. MEM (SORestore off) (iops ++ rops) ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo (iops ++ rops) ps /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo (iops ++ rops) ps).ps_stack ps2.ps_stack /\
  (apply_prefix_ops fmp lo (iops ++ rops) ps).ps_spilled = ps2.ps_spilled
Proof
  rpt gen_tac >>
  simp[listTheory.MEM_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
  `prefix_spill_wf fmp lo iops ps /\
   (apply_prefix_ops fmp lo iops ps).ps_stack = ps1.ps_stack /\
   (apply_prefix_ops fmp lo iops ps).ps_spilled = ps1.ps_spilled` by
    (irule emit_input_plan_read_only_replay >> simp[] >> metis_tac[]) >>
  `!op1 off1 op2 off2.
    FLOOKUP ps1.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps1.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1` by
    (drule_at Any doSwapSimTheory.safe_prefix_spilled_separated >>
     simp[] >> disch_then assume_tac >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[doSwapSimTheory.prefix_spill_wf_append, planAlignTheory.apply_prefix_ops_append] >>
  irule reorder_plan_read_only_kind_replay >> simp[] >>
  qexistsl [`inputs`, `ps1`] >> simp[listTheory.LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem sym_read_only_selected_prefix_frame_sim:
  !opc inputs nl ps iops ps1 dfg rops ps2 fn ret fmp p env ctx cp srest labs0 cs ss.
  emit_input_plan opc inputs nl ps = (iops,ps1) /\
  reorder_plan dfg inputs ps1 = (rops,ps2) /\ opc <> INVOKE /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) (iops ++ rops)) /\
  (!off. MEM (SORestore off) (iops ++ rops) ==> off < dimword(:256)) /\
  prefix_wf (SND (compute_label_offsets p)) (LENGTH ps.ps_stack) (iops ++ rops) /\
  EVERY is_prefix_op (iops ++ rops) /\
  EVERY (\op. !l d. op <> SOPushOfst l d) (iops ++ rops) /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ asm_block_at p cs.as_pc (execute_plan fmp (iops ++ rops)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan fmp (iops ++ rops))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan fmp (iops ++ rops))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 ps2 cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan fmp (iops ++ rops)) /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all selected_prefix_read_only_kind_replay >>
  disch_then (qspecl_then [`ret`, `fmp`, `SND (compute_label_offsets p)`] strip_assume_tac) >>
  drule_all sym_spill_free_prefix_frame_sim >> strip_tac >>
  qexistsl [`cs'`, `ss'`] >> simp[] >>
  irule sym_frame_inv_kind_transport >> goal_assum (drule_at Any) >> simp[]
QED

Theorem sym_ret_prepare_frame_sim:
  !inputs nl ps iops prepared dfg rops arranged fn ret fmp p env ctx cp srest labs0 cs ss base.
  emit_input_plan RET inputs nl ps = (iops,prepared) /\
  reorder_plan dfg inputs prepared = (rops,arranged) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  generated_plan_state_wf_marked base ps /\ LENGTH inputs <= 16 /\
  (!op. MEM op inputs /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  (!l. MEM (Label l) inputs ==> IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l)) /\
  (!off. ~MEM (SOSpill off) (iops ++ rops)) /\
  (!off. MEM (SORestore off) (iops ++ rops) ==> off < dimword(:256)) /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ asm_block_at p cs.as_pc (execute_plan fmp (iops ++ rops)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan fmp (iops ++ rops))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan fmp (iops ++ rops))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 arranged cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan fmp (iops ++ rops)) /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  `prefix_wf (SND (compute_label_offsets p)) (LENGTH ps.ps_stack) (iops ++ rops)` by
    (irule fnFrameStepsRevertForwardTheory.available_preparation_prefix_wf >>
     qexistsl [`dfg`, `inputs`, `nl`, `RET`, `prepared`, `arranged`] >> simp[]) >>
  `EVERY is_prefix_op (iops ++ rops)` by
    metis_tac[planWfTheory.prefix_wf_every_prefix_op] >>
  `EVERY (\op. !l d. op <> SOPushOfst l d) (iops ++ rops)` by
    (simp[listTheory.EVERY_MEM, listTheory.MEM_APPEND] >>
     metis_tac[codegenEncodingWfTheory.emit_input_plan_no_push_ofst,
               codegenEncodingWfTheory.reorder_plan_no_push_ofst]) >>
  irule sym_read_only_selected_prefix_frame_sim >> simp[] >>
  qexistsl [`inputs`, `nl`, `RET`, `ps`, `prepared`] >> simp[] >>
  fs[fnPlanPrefixTheory.generated_plan_state_wf_marked_def] >>
  metis_tac[doSwapSimTheory.spill_alloc_layout_wf_spilled_separated]
QED

Theorem reorder_one_spill_free_placement:
  reorder_one dfg pending idx op ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  control_reorder_place dfg pending op (LENGTH pending - (idx + 1)) ps = (ops,ps')
Proof
  strip_tac >> drule control_reorder_one_decompose >> strip_tac
  >- (`restore_ops = [] /\ ps1 = ps` by
        metis_tac[reorder_restore_no_restore_identity] >>
      gvs[control_reorder_place_def]) >>
  `restore_ops = [] /\ ps1 = ps` by
    (irule reorder_restore_no_restore_identity >>
     fs[listTheory.MEM_APPEND] >> metis_tac[]) >>
  gvs[] >>
  `reduce_ops = [] /\ ps2 = ps` by
    (irule reorder_reduce_no_spill_identity >>
     fs[listTheory.MEM_APPEND] >> metis_tac[]) >>
  gvs[]
QED

Theorem reorder_one_spill_free_kind_replay:
  reorder_one dfg pending idx op ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  metis_tac[reorder_one_spill_free_placement, control_reorder_place_spill_free_kind_replay]
QED

Theorem reorder_steps_spill_free_kind_replay:
  !items ps qs ops ps' dfg pending fn ret fmp lo.
  plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  Induct
  >- simp[foldlSimTheory.plan_steps_def, mixedPrefixSimTheory.apply_prefix_ops_def] >>
  Cases_on `h` >> rpt gen_tac >>
  simp[foldlSimTheory.plan_steps_def] >>
  Cases_on `reorder_one dfg pending q r ps` >>
  rename1 `reorder_one _ _ _ _ _ = (step_ops,mid)` >>
  Cases_on `plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items mid` >>
  simp[] >> strip_tac >>
  gvs[listTheory.MEM_APPEND, planAlignTheory.apply_prefix_ops_append] >>
  first_x_assum irule >> simp[] >>
  metis_tac[reorder_one_spill_free_kind_replay]
QED

Theorem reorder_plan_spill_free_kind_replay:
  reorder_plan dfg pending ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  rewrite_tac[reorderSimTheory.reorder_plan_eq_plan_steps] >>
  metis_tac[reorder_steps_spill_free_kind_replay]
QED

(* Diagnostic: the spill-free prefix contract needs no spill kinds or budget. *)
Theorem sym_spill_free_stack_only_prefix_sim:
  !ops lo ps ss top srest fn ret cp p fmp env.
  EVERY is_simple_stack_op ops /\
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cp fn ret srest
      (apply_prefix_ops fmp lo ops (ps with ps_spilled := FEMPTY)) ss' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >> rename1 `!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cplan b` >>
  `sym_kinds_ok cplan fn ret srest (ps with ps_spilled := FEMPTY) ss` by
    (simp[sym_kinds_ok_def] >> metis_tac[]) >>
  `prefix_spill_wf fmp lo ops (ps with ps_spilled := FEMPTY)` by
    metis_tac[genBlockSimTheory.simple_prefix_spill_wf] >>
  `!op. is_simple_stack_op op ==> is_prefix_op op /\
     (!l d. op <> SOPushOfst l d) /\ (!off. op <> SOSpill off)` by
    (Cases >> simp[strongPrefixSimTheory.is_simple_stack_op_def,
                  prefixSimTheory.is_prefix_op_def] >>
     Cases_on `o'` >> simp[strongPrefixSimTheory.is_simple_stack_op_def]) >>
  `EVERY is_prefix_op ops /\ EVERY (\op. !l d. op <> SOPushOfst l d) ops /\
   (!off. ~MEM (SOSpill off) ops)` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `prefix_wf lo (LENGTH (ps with ps_spilled := FEMPTY).ps_stack) ops` by simp[] >>
  `!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
     (\b:num. F) b /\ context_spill_byte cplan b` by simp[] >>
  drule_all (Q.INST [`R` |-> `\b:num. F`] (SPEC_ALL sym_prefix_ops_sim)) >>
  simp[] >> metis_tac[]
QED

Theorem sym_rf_preparation_stack_sim:
  !opc inputs nl ps ins ps1 fn ros ps2 (lo:string |-> num) ss top srest ret cp p fmp env.
  emit_input_plan opc inputs nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) inputs ps1 = (ros,ps2) /\
  opc <> INVOKE /\ ssa_form fn /\ fn_shape_ok fn /\
  EVERY is_simple_stack_op (ins ++ ros) /\
  prefix_wf lo (LENGTH ps.ps_stack) (ins ++ ros) /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp (ins ++ ros)) ==>
  ?ss' top'.
    sym_steps p env (LENGTH (execute_plan fmp (ins ++ ros))) ss = SymOK ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps2.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  `!off. ~MEM (SOSpill off) (ins ++ ros) /\
         ~MEM (SORestore off) (ins ++ ros)` by
    (fs[listTheory.EVERY_MEM] >>
     metis_tac[strongPrefixSimTheory.is_simple_stack_op_def]) >>
  `(apply_prefix_ops fmp lo ins (ps with ps_spilled := FEMPTY)).ps_stack = ps1.ps_stack` by
    (irule emit_input_plan_spill_free_stack_replay >>
     simp[] >> fs[listTheory.MEM_APPEND] >> metis_tac[]) >>
  `LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
     (apply_prefix_ops fmp lo (ins ++ ros) (ps with ps_spilled := FEMPTY)).ps_stack
     ps2.ps_stack` by
    (rewrite_tac[planAlignTheory.apply_prefix_ops_append] >>
     irule reorder_plan_spill_free_kind_replay >>
     simp[] >> fs[listTheory.MEM_APPEND] >>
     qexistsl [`inputs`, `ps1`] >> simp[] >>
     irule listTheory.EVERY2_refl >> simp[]) >>
  drule_all sym_spill_free_stack_only_prefix_sim >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  fs[sym_kinds_ok_def] >>
  irule list_rel_op_kind_transport >>
  metis_tac[listTheory.LIST_REL_REVERSE]
QED

Theorem assign_output_op_kind:
  codegen_ready_fn fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs ==>
  (op_kind_ok fn ret rhs sv <=> op_kind_ok fn ret (Var out) sv)
Proof
  strip_tac >>
  `ssa_form fn` by fs[codegen_ready_fn_def] >>
  `dfg_get_def (dfg_build_function fn) out = SOME inst` by
    metis_tac[fnFrameStepsRevertForwardTheory.dfg_build_function_ssa_def,
              listTheory.MEM] >>
  drule_all fnFrameStepsRevertForwardTheory.normalize_operand_codegen_assign >>
  metis_tac[op_kind_ok_normalize_operand]
QED

Theorem assign_prepared_stack_op_kind:
  codegen_ready_fn fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [rhs])) top ==>
  LIST_REL (op_kind_ok fn ret) (REVERSE (stack_push (Var out) tail)) top
Proof
  Cases_on `top` >>
  simp[stackModelTheory.stack_push_def] >>
  metis_tac[assign_output_op_kind]
QED

Theorem simple_do_swap_replay_wf:
  do_swap d ps = (ops,ps') /\ d < LENGTH ps.ps_stack /\
  EVERY is_simple_stack_op ops ==>
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  apply_prefix_ops fmp lo ops ps = ps'
Proof
  strip_tac >>
  `!off. ~MEM (SORestore off) ops` by
    (fs[listTheory.EVERY_MEM] >>
     metis_tac[strongPrefixSimTheory.is_simple_stack_op_def]) >>
  `d <= 16` by metis_tac[do_swap_no_restore_shallow] >>
  metis_tac[do_swap_shallow_symbolic_prefix_facts, planAlignTheory.do_swap_align]
QED

Theorem optimistic_simple_replay_wf:
  optimistic_swap_plan dfg inst nl term ps = (ops,ps') /\
  EVERY is_simple_stack_op ops ==>
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  apply_prefix_ops fmp lo ops ps = ps'
Proof
  simp[optimistic_swap_plan_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  Cases_on `stack_get_depth (Var (LAST nl)) ps.ps_stack` >>
  simp[] >> rpt strip_tac >> gvs[] >>
  simp[mixedPrefixSimTheory.apply_prefix_ops_def, prefixExecTheory.prefix_wf_def] >>
  metis_tac[simple_do_swap_replay_wf, planAlignTheory.stack_get_depth_bound]
QED

Theorem simple_prefix_equal_stack_replay:
  !ops ps qs fmp lo.
  EVERY is_simple_stack_op ops /\ qs.ps_stack = ps.ps_stack ==>
  (apply_prefix_ops fmp lo ops qs).ps_stack =
    (apply_prefix_ops fmp lo ops ps).ps_stack
Proof
  Induct >> simp[mixedPrefixSimTheory.apply_prefix_ops_def] >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[] >>
  Cases_on `h` >>
  gvs[strongPrefixSimTheory.is_simple_stack_op_def,
      mixedPrefixSimTheory.apply_prefix_op_def,
      strongPrefixSimTheory.apply_simple_op_def] >>
  Cases_on `o'` >>
  gvs[strongPrefixSimTheory.is_simple_stack_op_def,
      mixedPrefixSimTheory.apply_prefix_op_def,
      strongPrefixSimTheory.apply_simple_op_def]
QED

Theorem sym_simple_prefix_stack_sim:
  !ops lo ps ps' ss top srest fn ret cp p fmp env.
  EVERY is_simple_stack_op ops /\
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  (apply_prefix_ops fmp lo ops ps).ps_stack = ps'.ps_stack /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp ops) ==>
  ?ss' top'.
    sym_steps p env (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  `(apply_prefix_ops fmp lo ops (ps with ps_spilled := FEMPTY)).ps_stack = ps'.ps_stack` by
    metis_tac[simple_prefix_equal_stack_replay, plan_state_accfupds] >>
  drule_all sym_spill_free_stack_only_prefix_sim >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  fs[sym_kinds_ok_def] >> metis_tac[]
QED

Theorem assign_postfix_simple_replay_wf:
  ps.ps_stack = stack_push (Var out) tail /\
  (if halting then ([],ps)
   else popmany_plan (if MEM out nl then [] else [Var out]) ps) = (pops,ps8) /\
  (if MEM out nl then optimistic_swap_plan dfg inst nl term ps8
   else ([],ps8)) = (opts,ps9) /\
  EVERY is_simple_stack_op (pops ++ opts) ==>
  prefix_wf lo (LENGTH ps.ps_stack) (pops ++ opts) /\
  (apply_prefix_ops fmp lo (pops ++ opts) ps).ps_stack =
    (release_dead_spills nl ps9).ps_stack
Proof
  strip_tac >> Cases_on `MEM out nl`
  >- (`pops = [] /\ ps8 = ps` by
        (Cases_on `halting` >> gvs[stackPlanOpsTheory.popmany_plan_def]) >>
      gvs[] >> drule_all optimistic_simple_replay_wf >>
      disch_then (qspecl_then [`lo`, `fmp`] strip_assume_tac) >>
      gvs[stackModelTheory.stack_push_def, arithmeticTheory.ADD1]) >>
  gvs[] >> Cases_on `halting`
  >- gvs[mixedPrefixSimTheory.apply_prefix_ops_def, prefixExecTheory.prefix_wf_def] >>
  `stack_get_depth (Var out) ps.ps_stack = SOME 0` by
    simp[stackModelTheory.stack_push_def, listTheory.REVERSE_SNOC,
         stackModelTheory.stack_get_depth_def, stackModelTheory.stack_find_def] >>
  `popmany_plan [Var out] ps =
     ([SOPop 1],ps with ps_stack := stack_pop 1 ps.ps_stack)` by
    metis_tac[regularPostfixSimTheory.popmany_plan_top_singleton] >>
  gvs[mixedPrefixSimTheory.apply_prefix_ops_def,
      mixedPrefixSimTheory.apply_prefix_op_def,
      strongPrefixSimTheory.apply_simple_op_def,
      prefixExecTheory.prefix_wf_def, prefixExecTheory.stack_op_wf_def,
      stackModelTheory.stack_push_def, stackModelTheory.stack_pop_def]
QED

Theorem sym_assign_postfix_stack_sim:
  !ps out tail halting nl pops ps8 dfg inst term opts ps9 (lo:string |-> num) ss top srest fn ret cp p fmp env.
  ps.ps_stack = stack_push (Var out) tail /\
  (if halting then ([],ps)
   else popmany_plan (if MEM out nl then [] else [Var out]) ps) = (pops,ps8) /\
  (if MEM out nl then optimistic_swap_plan dfg inst nl term ps8
   else ([],ps8)) = (opts,ps9) /\
  EVERY is_simple_stack_op (pops ++ opts) /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp (pops ++ opts)) ==>
  ?ss' top'.
    sym_steps p env (LENGTH (execute_plan fmp (pops ++ opts))) ss = SymOK ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (release_dead_spills nl ps9).ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `context_spill_byte cp0` >>
  drule_all assign_postfix_simple_replay_wf >>
  disch_then (qspecl_then [`lo`, `fmp`] strip_assume_tac) >>
  irule sym_simple_prefix_stack_sim >> simp[] >>
  conj_tac >- (qexists_tac `cp0` >> simp[]) >>
  qexistsl_tac [`lo`, `ps`] >> simp[]
QED

Theorem rf_assign_preparation_stack_facts:
  emit_input_plan ASSIGN [rhs] nl ps = (ins,ps1) /\
  reorder_plan dfg [rhs] ps1 = (ros,ps2) /\
  ~is_label_operand rhs /\
  (is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled) /\
  (!off. ~MEM (SOSpill off) (ins ++ ros) /\
         ~MEM (SORestore off) (ins ++ ros)) ==>
  EVERY is_simple_stack_op (ins ++ ros) /\
  prefix_wf (lo:string |-> num) (LENGTH ps.ps_stack) (ins ++ ros) /\
  ps2.ps_stack = stack_pop 1 ps2.ps_stack ++ [rhs]
Proof
  strip_tac >> rpt conj_tac
  >- metis_tac[fnFrameStepsRevertForwardTheory.spill_free_preparation_simple]
  >- (irule fnFrameStepsRevertForwardTheory.available_preparation_prefix_wf >>
      qexistsl_tac [`dfg`, `[rhs]`, `nl`, `ASSIGN`, `ps1`, `ps2`] >>
      simp[] >> metis_tac[stackPlanTypesTheory.is_label_operand_def]) >>
  `!op. MEM op [rhs] /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by simp[] >>
  `LENGTH [rhs] <= 16` by simp[] >>
  drule_all fnFrameStepsRevertForwardTheory.rf_preparation_arranged >> simp[]
QED

Theorem sym_assign_prepared_stack_sim:
  !ps2 tail rhs fn inst out ret ss top srest.
  codegen_ready_fn fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs /\
  ps2.ps_stack = tail ++ [rhs] /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps2.ps_stack) top ==>
  LIST_REL (op_kind_ok fn ret)
    (REVERSE (ps2 with ps_stack := stack_push (Var out) tail).ps_stack) top
Proof
  rpt gen_tac >> strip_tac >> simp[] >>
  irule assign_prepared_stack_op_kind >> metis_tac[]
QED

Theorem sym_rf_suffix_preparation_execution:
  !fn ps opc inputs nl ins ps1 ros ps2 ra lo entry s stk st rest prog fmp
   env ss top srest ret cp.
  lo = SND (compute_label_offsets prog) /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  emit_input_plan opc inputs nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) inputs ps1 = (ros,ps2) /\
  opc <> INVOKE /\ LENGTH inputs <= 16 /\
  (!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inputs /\
  rf_inventory_inv fn ra lo entry ps s /\
  (!op. MEM op inputs ==> operand_val (frame_view fn ra s) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) (ins ++ ros) /\
         ~MEM (SORestore off) (ins ++ ros)) /\
  EVERY is_simple_stack_op (ins ++ ros) /\
  prefix_wf lo (LENGTH ps.ps_stack) (ins ++ ros) /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan fmp (ins ++ ros)) /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?mid ss' stk' top'.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp (ins ++ ros))) st = AsmOK mid /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan fmp (ins ++ ros)) /\
    mid.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra s) ps2.ps_stack stk' /\
    rf_inventory_inv fn ra lo entry ps2 s /\
    ps2.ps_stack = stack_pop (LENGTH inputs) ps2.ps_stack ++ inputs /\
    sym_steps prog env (LENGTH (execute_plan fmp (ins ++ ros))) ss = SymOK ss' /\
    asm_sym_rel prog env mid ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps2.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  `ssa_form fn` by fs[codegen_ready_fn_def] >>
  `asm_block_at prog ss.sym_base.as_pc (execute_plan fmp (ins ++ ros))` by
    metis_tac[asm_sym_rel_pc] >>
  drule_all fnFrameStepsRevertForwardTheory.rf_suffix_preparation_execution >>
  disch_then (qspec_then `build_offset_to_pc prog` strip_assume_tac) >>
  drule_all sym_rf_preparation_stack_sim >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem rf_assign_postfix_simple:
  (if halting then ([],ps)
   else popmany_plan (if MEM out nl then [] else [Var out]) ps) = (pops,ps8) /\
  (if MEM out nl then optimistic_swap_plan dfg inst nl term ps8
   else ([],ps8)) = (opts,ps9) /\
  (!off. ~MEM (SOSpill off) (pops ++ opts) /\
         ~MEM (SORestore off) (pops ++ opts)) ==>
  EVERY is_simple_stack_op (pops ++ opts)
Proof
  strip_tac >>
  irule fnFrameStepsRevertForwardTheory.spill_free_postfix_simple >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`dfg`, `~halting`, `inst`,
    `if MEM out nl then [] else [Var out]`, `nl`, `~MEM out nl`,
    `term`, `ps`, `ps8`, `ps9`] >>
  Cases_on `halting` >> Cases_on `MEM out nl` >> gvs[]
QED

Theorem sym_plan_runs_compose:
  sym_steps p env (LENGTH (execute_plan fmp ops1)) ss = SymOK mid /\
  sym_steps p env (LENGTH (execute_plan fmp ops2)) mid = SymOK final ==>
  sym_steps p env (LENGTH (execute_plan fmp (ops1 ++ ops2))) ss = SymOK final
Proof
  simp[stackOpSimTheory.execute_plan_append, sym_steps_add]
QED

Theorem sym_rf_assign_plan_execution:
  !fn inst ps rhs out ra lo entry s fuel ctx s' lv cfg nl halting term lbl ops ps'
   stk st rest prog fmp env ss top srest ret cp.
  lo = SND (compute_label_offsets prog) /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  rf_spills_separated ps /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs /\
  (is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled) /\
  rf_inventory_inv fn ra lo entry ps s /\
  operand_val (frame_view fn ra s) lo rhs =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] rhs) /\
  step_inst fuel ctx inst s = OK s' /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?st' ss' stk' top'.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmOK st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan fmp ops) /\
    st'.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra s') ps'.ps_stack stk' /\
    sym_steps prog env (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    asm_sym_rel prog env st' ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  rpt gen_tac >> strip_tac >> rename1 `context_spill_byte cplan` >>
  Cases_on `emit_input_plan ASSIGN [rhs] nl ps` >> rename1 `_ = (ins,ps1)` >>
  Cases_on `reorder_plan (dfg_build_function fn) [rhs] ps1` >>
  rename1 `_ = (ros,ps2)` >>
  drule_all fnFrameStepsRevertForwardTheory.rf_assign_plan_result >> strip_tac >>
  `asm_block_at prog st.as_pc (execute_plan fmp (ins ++ ros)) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan fmp (ins ++ ros)))
     (execute_plan fmp (pops ++ opts))` by
    gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append,
        listTheory.APPEND_ASSOC] >>
  `!off. ~MEM (SOSpill off) (ins ++ ros) /\
    ~MEM (SORestore off) (ins ++ ros)` by fs[listTheory.MEM_APPEND] >>
  `!off. ~MEM (SOSpill off) (pops ++ opts) /\
    ~MEM (SORestore off) (pops ++ opts)` by fs[listTheory.MEM_APPEND] >>
  drule_all rf_assign_preparation_stack_facts >>
  disch_then (qspec_then `lo` strip_assume_tac) >>
  `ASSIGN <> INVOKE /\ LENGTH [rhs] <= 16 /\
   EVERY (\op. ~is_label_operand op) [rhs] /\
   (!op. MEM op [rhs] /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
   (!op. MEM op [rhs] ==> operand_val (frame_view fn ra s) lo op =
     operand_val entry lo (normalize_operand (dfg_build_function fn) [] op))` by gvs[] >>
  drule_all sym_rf_suffix_preparation_execution >> strip_tac >>
  rename1 `sym_steps prog env _ ss = SymOK ss1` >>
  rename1 `ss1.sym_stack = prepared_top ++ srest` >>
  qabbrev_tac `pushed = ps2 with ps_stack :=
    stack_push (Var out) (stack_pop 1 ps2.ps_stack)` >>
  `LIST_REL (op_kind_ok fn ret) (REVERSE pushed.ps_stack) prepared_top` by
    (simp[Abbr `pushed`] >> irule assign_prepared_stack_op_kind >> metis_tac[]) >>
  `EVERY is_simple_stack_op (pops ++ opts)` by metis_tac[rf_assign_postfix_simple] >>
  `!b. b IN FDOM ss1.sym_mem_labels ==> context_spill_byte cplan b` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  `asm_block_at prog ss1.sym_base.as_pc (execute_plan fmp (pops ++ opts))` by
    metis_tac[asm_sym_rel_pc] >>
  `pushed.ps_stack = stack_push (Var out) (stack_pop 1 ps2.ps_stack)` by simp[Abbr `pushed`] >>
  drule_all sym_assign_postfix_stack_sim >>
  disch_then (qspecl_then [`lo`, `env`] strip_assume_tac) >>
  `sym_steps prog env (LENGTH (execute_plan fmp ops)) ss = SymOK ss'` by
    (qpat_assum `sym_steps prog env _ ss = SymOK ss1`
       (mp_then Any mp_tac sym_plan_runs_compose) >>
     disch_then (qspecl_then [`pops ++ opts`, `ss'`] mp_tac) >>
     simp[listTheory.APPEND_ASSOC]) >>
  drule_all fnFrameStepsRevertForwardTheory.rf_assign_plan_execution >>
  disch_then (qspec_then `build_offset_to_pc prog` strip_assume_tac) >>
  qspecl_then [`LENGTH (execute_plan fmp ops)`, `st`, `ss`, `ss'`]
    mp_tac (Q.INST [`p` |-> `prog`] asm_sym_steps_lockstep) >>
  simp[] >> strip_tac >> gvs[] >>
  metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE]
QED

Theorem label_flow_noncopy_operand_not_code_end:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\ label_flow_ok ctx /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> CODECOPY /\
  MEM (Var x) inst.inst_operands ==> ~code_end_var fn x
Proof
  strip_tac >> fs[label_flow_ok_def] >>
  first_x_assum (qspecl_then [`fn`, `inst`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem ordinary_noncopy_operand_word_kind:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\
  inst.inst_opcode <> RET /\ inst.inst_opcode <> RETFMP /\
  inst.inst_opcode <> DRET /\ inst.inst_opcode <> CODECOPY /\
  MEM op inst.inst_operands /\ ~is_label_operand op /\
  op <> dead_stack_marker /\ op_kind_ok fn ret op sv ==>
  ?w. sv = Val w
Proof
  strip_tac >> Cases_on `op` >>
  gvs[op_kind_ok_def, is_label_operand_def] >>
  drule_all frameViewFactsTheory.ordinary_operand_not_retpc >>
  drule_all label_flow_noncopy_operand_not_code_end >> metis_tac[]
QED

Theorem terminal_operand_word_kind:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ label_positions_ok inst /\
  MEM inst.inst_opcode
    [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT; ASSERT_UNREACHABLE;
     INVALID; CREATE; CREATE2; RETURNDATACOPY] /\
  MEM op (compute_operands inst) /\ op <> dead_stack_marker /\
  op_kind_ok fn ret op sv ==> ?w. sv = Val w
Proof
  strip_tac >>
  `MEM op inst.inst_operands /\ ~is_label_operand op /\
   inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\
   inst.inst_opcode <> RET /\ inst.inst_opcode <> RETFMP /\
   inst.inst_opcode <> DRET /\ inst.inst_opcode <> CODECOPY` by
    (gvs[listTheory.MEM, compute_operands_def] >>
     gvs[label_positions_ok_def, listTheory.EVERY_MEM]) >>
  drule_all ordinary_noncopy_operand_word_kind >> simp[]
QED

Theorem word_prepared_symbolic_stack:
  asm_sym_rel p env cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  ps.ps_stack = tail ++ operands /\
  (!op sv. MEM op operands /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) /\
  cs.as_stack = values ++ rest /\ LENGTH values = LENGTH operands ==>
  ?suffix. ss.sym_stack = MAP Val values ++ suffix
Proof
  strip_tac >> fs[sym_kinds_ok_def, listTheory.REVERSE_APPEND] >>
  qpat_assum `LIST_REL _ _ top`
    (mp_then Any (qspec_then `LENGTH operands` mp_tac)
       rich_listTheory.EVERY2_TAKE) >>
  simp[] >> strip_tac >>
  `TAKE (LENGTH operands) (REVERSE operands) = REVERSE operands` by
    metis_tac[listTheory.TAKE_LENGTH_ID, listTheory.LENGTH_REVERSE] >>
  `TAKE (LENGTH operands) top = MAP Val values` by
    (irule word_kind_prefix_concretization >>
     conj_tac
     >- (qexistsl [`fn`, `REVERSE operands`, `ret`] >>
         gvs[listTheory.MEM_REVERSE, listTheory.TAKE_APPEND1] >> gvs[]) >>
     qexistsl [`SND (compute_label_offsets p)`, `rest`,
               `DROP (LENGTH operands) top ++ srest`] >>
     gvs[asm_sym_rel_def]) >>
  metis_tac[listTheory.TAKE_DROP, listTheory.APPEND_ASSOC]
QED

Theorem arranged_word_prepared_symbolic_stack:
  venom_asm_rel lo ps vs mid /\
  ps.ps_stack = tail ++ operands /\
  EVERY (\op. op <> dead_stack_marker) operands /\
  (!op. MEM op operands ==> eval_operand op vs = operand_val vs lo op) /\
  eval_operands (REVERSE operands) vs = SOME values /\
  asm_sym_rel p env (mid with as_stack := mid.as_stack ++ rest) ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  (!op sv. MEM op operands /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) ==>
  mid.as_stack = values ++ DROP (LENGTH operands) mid.as_stack /\
  ?suffix. ss.sym_stack = MAP Val values ++ suffix
Proof
  strip_tac >>
  `mid.as_stack = values ++ DROP (LENGTH operands) mid.as_stack` by
    (irule (emitSimTheory.arranged_eval_operands_stack |> Q.INST
       [`operands` |-> `REVERSE operands`] |> SRULE []) >>
     conj_tac >- gvs[listTheory.EVERY_MEM] >>
     qexistsl [`lo`, `ps`, `tail`, `vs`] >> gvs[]) >>
  simp[] >> irule word_prepared_symbolic_stack >>
  conj_tac
  >- (qexistsl [`mid with as_stack := mid.as_stack ++ rest`, `env`, `p`,
        `DROP (LENGTH operands) mid.as_stack ++ rest`] >> gvs[]) >>
  qexistsl [`cplan`, `fn`, `operands`, `ps`, `ret`, `srest`, `tail`] >>
  gvs[] >> metis_tac[fnFrameBoundaryInvokeTheory.eval_operands_some_length,
                     listTheory.LENGTH_REVERSE]
QED

Theorem sym_frame_entry_selected_prefix_sim_marked:
  opc <> INVOKE /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  generated_plan_state_wf_marked spillbase ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  ops = iops ++ rops ++ suffix /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  asm_static_wf prog /\
  sym_frame_inv prog env ctx cplan fn ret srest labs0 ps st ss ==>
  plan_state_residual_wf_marked spillbase selected (LENGTH selected) arranged /\
  arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected /\
  ?mid ss_mid.
    asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) st =
      AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
    venom_asm_rel lo arranged
      (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
    context_memory_rel cplan vs.vs_memory mid.as_memory /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) /\
    venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
    sym_steps prog env (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) ss =
      SymOK ss_mid /\
    sym_frame_inv prog env ctx cplan fn ret srest labs0 arranged
      (mid with as_stack := mid.as_stack ++ rest) ss_mid
Proof
  strip_tac >> drule_all frame_entry_selected_prefix_sim_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  `!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    metis_tac[deepInstSimTheory.marked_operand_owned] >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
   plan_slots_bounded spillbase ps /\ residual_budget_wf_marked spillbase [] ps` by
    metis_tac[fnPlanPrefixTheory.generated_plan_state_wf_marked_def,
              deepResidualSimTheory.generated_plan_state_wf_marked_residual_nil] >>
  `r.sr_spill_base <= ps.ps_alloc.sa_spill_base` by
    metis_tac[allocMonoTheory.reorder_plan_spill_base,
              allocMonoTheory.emit_input_plan_spill_base] >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
     | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
   asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    gvs[listTheory.EVERY_APPEND, stackOpSimTheory.execute_plan_append,
        stackOpSimTheory.asm_block_at_append] >>
  `arranged.ps_alloc.sa_next_offset <= r.sr_spill_end` by decide_tac >>
  drule_all sym_selected_prefix_frame_sim_marked >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem terminal_operands_not_retpc:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode
    [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT; ASSERT_UNREACHABLE;
     INVALID; CREATE; CREATE2; RETURNDATACOPY] /\
  MEM (Var x) (compute_operands inst) ==> ~retpc_var fn x
Proof
  strip_tac >> irule frameViewFactsTheory.ordinary_operand_not_retpc >>
  conj_tac >- gvs[listTheory.MEM] >>
  qexists `inst` >> gvs[compute_operands_def, listTheory.MEM]
QED

Theorem terminal_arranged_word_stack:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ label_positions_ok inst /\
  MEM inst.inst_opcode
    [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT; ASSERT_UNREACHABLE;
     INVALID; CREATE; CREATE2; RETURNDATACOPY] /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  arranged.ps_stack = tail ++ compute_operands inst /\
  venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := m) mid /\
  asm_sym_rel prog env (mid with as_stack := mid.as_stack ++ rest) ss /\
  sym_kinds_ok cplan fn ret srest arranged ss /\
  eval_operands (REVERSE (compute_operands inst)) vs = SOME values ==>
  (mid.as_stack ++ rest = values ++
     DROP (LENGTH (compute_operands inst)) (mid.as_stack ++ rest)) /\
  ?suffix. ss.sym_stack = MAP Val values ++ suffix
Proof
  strip_tac >>
  `!x. MEM (Var x) (compute_operands inst) ==> ~retpc_var fn x` by
    metis_tac[terminal_operands_not_retpc] >>
  `eval_operands (REVERSE (compute_operands inst))
      (frame_view fn ra vs with vs_memory := m) = SOME values` by
    metis_tac[frameViewFactsTheory.eval_operands_frame_view, listTheory.MEM_REVERSE] >>
  `!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op` by
    simp[venomMemPropsTheory.eval_operand_with_memory,
         genFrameSimTheory.operand_val_memory_update] >>
  `!op sv. MEM op (compute_operands inst) /\ op_kind_ok fn ret op sv ==>
    ?w. sv = Val w` by
    (rpt strip_tac >>
     `op <> dead_stack_marker` by
       (qpat_x_assum `EVERY _ _` (mp_tac o REWRITE_RULE [listTheory.EVERY_MEM]) >>
        disch_then (qspec_then `op` mp_tac) >> simp[]) >>
     drule_all terminal_operand_word_kind >> simp[]) >>
  drule_all arranged_word_prepared_symbolic_stack >> strip_tac >>
  `LENGTH values = LENGTH (compute_operands inst)` by
    metis_tac[fnFrameBoundaryInvokeTheory.eval_operands_some_length,
              listTheory.LENGTH_REVERSE] >>
  `LENGTH (compute_operands inst) <= LENGTH mid.as_stack` by
    metis_tac[listTheory.LENGTH_APPEND, arithmeticTheory.LE_ADD] >>
  `LENGTH (compute_operands inst) - LENGTH mid.as_stack = 0` by decide_tac >>
  simp[listTheory.DROP_APPEND] >>
  qpat_x_assum `mid.as_stack = values ++ _`
    (mp_tac o AP_TERM ``\xs:bytes32 list. xs ++ rest``) >>
  simp[listTheory.APPEND_ASSOC]
QED

Theorem sym_frame_terminal_prefix_setup_marked:
  !cp base.
  (inst.inst_opcode = STOP \/ inst.inst_opcode = RETURN \/
    inst.inst_opcode = SELFDESTRUCT) /\ inst_wf inst /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  dfg = dfg_build_function fn /\ codegen_ready_fn fn /\
  MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps st ss ==>
  ?n mid name ss_mid.
    asm_steps lo o2pc prog n st = AsmOK mid /\
    asm_block_at prog mid.as_pc [AsmOp name] /\
    venom_to_evm_name inst.inst_opcode = SOME name /\
    context_memory_rel cp vs.vs_memory mid.as_memory /\
    venom_asm_terminal_rel vs mid /\ mid.as_call_ctx = vs.vs_call_ctx /\
    (!values. eval_operands (REVERSE (compute_operands inst)) vs = SOME values ==>
      mid.as_stack = values ++ DROP (LENGTH (compute_operands inst)) mid.as_stack /\
      ?suffix. ss_mid.sym_stack = MAP Val values ++ suffix) /\
    sym_steps prog env n ss = SymOK ss_mid /\
    asm_sym_rel prog env mid ss_mid /\
    (!b. b IN FDOM ss_mid.sym_mem_labels ==> context_spill_byte cp b)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `MEM r cplan.cp_regions` >>
  `?name. venom_to_evm_name inst.inst_opcode = SOME name /\
    inst.inst_outputs = [] /\ ~is_commutative inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term label ps =
      (ops,final)` by
    (gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def,
        venomWfTheory.inst_wf_def, asmIRTheory.venom_to_evm_name_def,
        venomEffectsTheory.is_commutative_def, compute_operands_def]) >>
  drule_all fnFrameTerminalHaltTheory.output_free_regular_plan >> strip_tac >>
  `ssa_form fn /\ label_positions_ok inst` by
    metis_tac[stackPlanGenTheory.codegen_ready_fn_def,
              unitShapeDefsTheory.fn_shape_ok_def,
              unitShapeDefsTheory.inst_shape_ok_def, listTheory.EVERY_MEM] >>
  `PERM (compute_operands inst) (compute_operands inst) /\
   LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack /\
   arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset` by gvs[] >>
  drule_all sym_frame_entry_selected_prefix_sim_marked >>
  strip_tac >>
  qexistsl [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))`,
    `mid with as_stack := mid.as_stack ++ rest`, `name`, `ss_mid`] >>
  simp[] >>
  `asm_block_at prog mid.as_pc [AsmOp name]` by
    gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append,
        execute_plan_def, exec_stack_op_def] >>
  `asm_sym_rel prog env (mid with as_stack := mid.as_stack ++ rest) ss_mid /\
   sym_kinds_ok cplan fn ret srest arranged ss_mid /\
   (!b. b IN FDOM ss_mid.sym_mem_labels ==> context_spill_byte cplan b)` by
    metis_tac[sym_frame_inv_def, sym_kinds_ok_def] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  simp[] >> conj_tac
  >- (qpat_x_assum `venom_asm_rel _ _ _ mid` mp_tac >>
      simp[venom_asm_rel_def, frame_view_def]) >>
  gen_tac >> disch_tac >>
  `EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
   MEM inst.inst_opcode
     [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT; ASSERT_UNREACHABLE;
      INVALID; CREATE; CREATE2; RETURNDATACOPY]` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all terminal_arranged_word_stack >> simp[]
QED

Theorem assert_selected_prefix_decompose:
  inst.inst_opcode = ASSERT /\ inst_wf inst /\ inst.inst_operands = [cond] /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,final) ==>
  compute_operands inst = [cond] /\
  ?iops prepared rops arranged.
    emit_input_plan inst.inst_opcode (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++ [SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"] /\
    arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset
Proof
  strip_tac >> drule_all genBlockSimTheory.assert_plan_decompose >> strip_tac >>
  rename1 `emit_input_plan ASSERT [cond] nl ps = (iops,prepared)` >>
  rename1 `reorder_plan dfg [cond] prepared = (rops,arranged)` >>
  conj_tac >- simp[] >> qexistsl [`iops`, `prepared`, `rops`, `arranged`] >>
  gvs[allocMonoTheory.release_dead_spills_spill_base, allocMonoTheory.release_dead_spills_next_offset]
QED

Theorem assert_unreachable_selected_prefix_decompose:
  inst.inst_opcode = ASSERT_UNREACHABLE /\ inst_wf inst /\ inst.inst_operands = [cond] /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,final) ==>
  compute_operands inst = [cond] /\
  ?iops prepared rops arranged lbl.
    emit_input_plan inst.inst_opcode (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++ [SOPushLabel lbl; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel lbl] /\
    arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset
Proof
  strip_tac >> drule_all genBlockSimTheory.assert_unreachable_plan_decompose >> strip_tac >>
  rename1 `emit_input_plan ASSERT_UNREACHABLE [cond] nl ps = (iops,prepared)` >>
  rename1 `reorder_plan dfg [cond] prepared = (rops,arranged)` >>
  rename1 `fresh_label "reachable" _ = (endlabel,after)` >>
  conj_tac >- simp[] >> qexistsl [`iops`, `prepared`, `rops`, `arranged`, `endlabel`] >>
  gvs[allocMonoTheory.release_dead_spills_spill_base, allocMonoTheory.release_dead_spills_next_offset,
      fresh_label_def, plan_state_component_equality]
QED

Theorem sym_conditional_abort_frame_prefix_deep:
  !base.
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst_wf inst /\ inst.inst_operands = [cond] /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  asm_static_wf prog /\ sym_frame_inv prog env ctx cplan fn ret srest labs0 ps st ss ==>
  ?pre arranged mid ss_mid suffix.
    ops = pre ++ suffix /\
    ((inst.inst_opcode = ASSERT /\
      suffix = [SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"]) \/
     (inst.inst_opcode = ASSERT_UNREACHABLE /\ ?lbl.
      suffix = [SOPushLabel lbl; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel lbl])) /\
    arranged.ps_stack = stack_pop 1 arranged.ps_stack ++ [cond] /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp pre)) st =
      AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
    venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
    venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
    asm_block_at prog mid.as_pc (execute_plan cplan.cp_initial_fmp suffix) /\
    sym_steps prog env (LENGTH (execute_plan cplan.cp_initial_fmp pre)) ss = SymOK ss_mid /\
    sym_frame_inv prog env ctx cplan fn ret srest labs0 arranged
      (mid with as_stack := mid.as_stack ++ rest) ss_mid
Proof
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `?iops prepared rops arranged suffix.
    emit_input_plan inst.inst_opcode (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++ suffix /\
    arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset /\
    compute_operands inst = [cond] /\
    ((inst.inst_opcode = ASSERT /\
      suffix = [SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"]) \/
     (inst.inst_opcode = ASSERT_UNREACHABLE /\ ?lbl.
      suffix = [SOPushLabel lbl; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel lbl]))` by
    (Cases_on `inst.inst_opcode = ASSERT`
     >- (drule_all assert_selected_prefix_decompose >> metis_tac[])
     >> metis_tac[assert_unreachable_selected_prefix_decompose]) >>
  `inst.inst_opcode <> INVOKE /\
   PERM (compute_operands inst) (compute_operands inst) /\
   LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack` by gvs[] >>
  drule_all sym_frame_entry_selected_prefix_sim_marked >> strip_tac >>
  qexistsl [`iops ++ rops`, `arranged`, `mid`, `ss_mid`, `suffix`] >> simp[] >>
  qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
  simp[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >> gvs[]
QED

Theorem sym_regular_abort_frame_prefix_deep:
  !base.
  venom_to_evm_name inst.inst_opcode = SOME name /\
  inst.inst_opcode <> INVOKE /\ ~is_commutative inst.inst_opcode /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halting term label ps = (ops,final) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  asm_static_wf prog /\ sym_frame_inv prog env ctx cplan fn ret srest labs0 ps st ss ==>
  ?pre arranged mid ss_mid.
    arranged.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack ++
      compute_operands inst /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp pre)) st =
      AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
    venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
    venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
    asm_block_at prog mid.as_pc [AsmOp name] /\
    sym_steps prog env (LENGTH (execute_plan cplan.cp_initial_fmp pre)) ss = SymOK ss_mid /\
    sym_frame_inv prog env ctx cplan fn ret srest labs0 arranged
      (mid with as_stack := mid.as_stack ++ rest) ss_mid
Proof
  gen_tac >> strip_tac >>
  drule_all generatedPrefixSimTheory.regular_plan_selected_prefix >> strip_tac >>
  `selected = compute_operands inst` by metis_tac[] >>
  `emitted.ps_alloc = arranged.ps_alloc` by
    simp[generatedPrefixSimTheory.emit_output_fold_alloc] >>
  `emitted.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
   emitted.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset` by
    (drule_all generatedPrefixSimTheory.regular_postfix_alloc_frame >> simp[]) >>
  `arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
   arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset /\
   PERM (compute_operands inst) selected /\
   LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack /\
   ops = iops ++ rops ++ ([SOEmit name] ++ popops ++ optops)` by
    gvs[listTheory.APPEND_ASSOC] >>
  drule_all sym_frame_entry_selected_prefix_sim_marked >> strip_tac >>
  qexistsl [`iops ++ rops`, `arranged`, `mid`, `ss_mid`] >> simp[] >>
  qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
  simp[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append,
       execute_plan_def, exec_stack_op_def] >> gvs[]
QED

Theorem sym_rf_copy_preparation_execution:
  !cp.
  lo = SND (compute_label_offsets prog) /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?mid ss' stk' top'.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp (ins ++ ros))) st = AsmOK mid /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan fmp (ins ++ ros)) /\
    mid.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs) ps2.ps_stack stk' /\
    ps2.ps_stack = stack_pop 3 ps2.ps_stack ++ [zop;sop;dop] /\
    sym_steps prog env (LENGTH (execute_plan fmp (ins ++ ros))) ss = SymOK ss' /\
    asm_sym_rel prog env mid ss' /\ ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps2.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    asm_block_at prog mid.as_pc [AsmOp "RETURNDATACOPY"] /\
    ops = ins ++ ros ++ [SOEmit "RETURNDATACOPY"] /\
    ps' = release_dead_spills nl (ps2 with ps_stack := stack_pop 3 ps2.ps_stack)
Proof
  gen_tac >> strip_tac >>
  `compute_operands inst = [zop;sop;dop]` by
    simp[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def] >>
  `ops = ins ++ ros ++ [SOEmit "RETURNDATACOPY"] /\
   ps' = release_dead_spills nl (ps2 with ps_stack := stack_pop 3 ps2.ps_stack)` by
    (drule_all fnFrameStepsRevertForwardTheory.rf_copy_plan_result >>
     disch_then (fn th => fs[th])) >>
  `asm_block_at prog st.as_pc (execute_plan fmp (ins ++ ros)) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan fmp (ins ++ ros)))
     [AsmOp "RETURNDATACOPY"]` by
    gvs[stackOpSimTheory.execute_plan_append, execute_plan_def, exec_stack_op_def,
        stackOpSimTheory.asm_block_at_append] >>
  `!off. ~MEM (SOSpill off) (ins ++ ros) /\
         ~MEM (SORestore off) (ins ++ ros)` by fs[listTheory.MEM_APPEND] >>
  `RETURNDATACOPY <> INVOKE /\ LENGTH (compute_operands inst) <= 16 /\
   EVERY (\op. ~is_label_operand op) (compute_operands inst)` by gvs[] >>
  `EVERY is_simple_stack_op (ins ++ ros)` by
    metis_tac[fnFrameStepsRevertForwardTheory.spill_free_preparation_simple] >>
  `prefix_wf lo (LENGTH ps.ps_stack) (ins ++ ros)` by
    (irule fnFrameStepsRevertForwardTheory.available_preparation_prefix_wf >>
     qexistsl [`dfg_build_function fn`, `compute_operands inst`, `nl`, `RETURNDATACOPY`,
               `ps1`, `ps2`] >>
     simp[] >> gvs[] >> metis_tac[is_label_operand_def]) >>
  drule_all sym_rf_suffix_preparation_execution >> strip_tac >>
  qexistsl [`mid`, `ss'`, `stk'`, `top'`] >> gvs[]
QED

Theorem sym_rf_copy_operand_kind:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = RETURNDATACOPY /\
  MEM op inst.inst_operands /\ ~is_label_operand op /\
  op_kind_ok fn ret op sv ==> ?w. sv = Val w
Proof
  strip_tac >>
  `op <> dead_stack_marker` by
    (strip_tac >> gvs[dead_stack_marker_def, is_label_operand_def]) >>
  drule ordinary_noncopy_operand_word_kind >>
  disch_then drule >> simp[] >> metis_tac[]
QED

Theorem sym_rf_copy_prepared_stack:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dop;sop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  asm_sym_rel prog env cs ss /\ cs.as_stack = dst :: src :: sz :: rest /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;sop;dop])) top ==>
  ?suffix. ss.sym_stack = MAP Val [dst;src;sz] ++ suffix
Proof
  strip_tac >>
  gvs[listTheory.REVERSE_APPEND, listTheory.LIST_REL_CONS1] >>
  rename1 `op_kind_ok fn ret dop sd` >>
  rename1 `op_kind_ok fn ret sop sr` >>
  rename1 `op_kind_ok fn ret zop szv` >>
  `(?w. sd = Val w) /\ (?w. sr = Val w) /\ (?w. szv = Val w)` by
    (rpt conj_tac >> irule sym_rf_copy_operand_kind >> metis_tac[listTheory.MEM]) >>
  gvs[asm_sym_rel_def, sval_conc_def]
QED

Theorem sym_rf_copy_success_stack:
  !cp.
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dop;sop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  asm_static_wf prog /\ asm_sym_rel prog env cs ss /\
  cs.as_stack = dst :: src :: sz :: rest /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;sop;dop])) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at prog cs.as_pc [AsmOp "RETURNDATACOPY"] /\
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (AsmOp "RETURNDATACOPY") cs = AsmOK cs' ==>
  ?ss' top'.
    sym_step prog env (AsmOp "RETURNDATACOPY") ss = SymOK ss' /\
    asm_sym_rel prog env cs' ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE tail) top' /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b) /\
    ~mem_labels_hit ss'.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))
Proof
  gen_tac >> strip_tac >>
  drule_all sym_rf_copy_prepared_stack >> strip_tac >>
  `ss.sym_stack = Val dst :: Val src :: Val sz :: suffix` by simp[] >>
  drule_all sym_returndatacopy_success_transfer >> strip_tac >>
  drule_all sym_returndatacopy_success_inventory >> strip_tac >>
  gvs[listTheory.REVERSE_APPEND, listTheory.LIST_REL_CONS1] >>
  metis_tac[listTheory.CONS_11, listTheory.APPEND]
QED

Theorem sym_rf_copy_prepared_success:
  !cp.
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dop;sop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  plan_stack_rel (SND (compute_label_offsets prog)) current
    (tail ++ [zop;sop;dop]) stk /\
  operand_val current (SND (compute_label_offsets prog)) dop = SOME dst /\
  operand_val current (SND (compute_label_offsets prog)) sop = SOME src /\
  operand_val current (SND (compute_label_offsets prog)) zop = SOME sz /\
  cs.as_stack = stk ++ rest /\ asm_static_wf prog /\ asm_sym_rel prog env cs ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;sop;dop])) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at prog cs.as_pc [AsmOp "RETURNDATACOPY"] /\
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (AsmOp "RETURNDATACOPY") cs = AsmOK cs' ==>
  ?ss' top'.
    sym_steps prog env 1 ss = SymOK ss' /\
    asm_sym_rel prog env cs' ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE tail) top' /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b) /\
    ~mem_labels_hit ss'.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))
Proof
  gen_tac >> strip_tac >>
  `dop <> dead_stack_marker /\ sop <> dead_stack_marker /\ zop <> dead_stack_marker` by
    (rpt strip_tac >> gvs[dead_stack_marker_def, is_label_operand_def]) >>
  `?d s z residual. stk = d :: s :: z :: residual /\
    operand_val current (SND (compute_label_offsets prog)) dop = SOME d /\
    operand_val current (SND (compute_label_offsets prog)) sop = SOME s /\
    operand_val current (SND (compute_label_offsets prog)) zop = SOME z` by
    (irule emitSimTheory.asm_stack_top3_from_plan >> simp[] >>
     qexists `tail` >> simp[]) >>
  gvs[] >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by simp[] >>
  drule_all sym_rf_copy_success_stack >> strip_tac >>
  qexistsl [`ss'`, `top'`] >> simp[] >>
  `ss.sym_base.as_pc = cs.as_pc` by metis_tac[asm_sym_rel_pc] >>
  fs[asm_block_at_def] >>
  pure_rewrite_tac[arithmeticTheory.ONE, sym_steps_def] >> simp[]
QED

Theorem sym_rf_copy_success_execution:
  !cp.
  lo = SND (compute_label_offsets prog) /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo sop = SOME src /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  vs' = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs /\
  w2n src + w2n sz <= LENGTH vs.vs_returndata /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?out ss_out stk_out top_out.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmOK out /\
    out.as_pc = st.as_pc + LENGTH (execute_plan fmp ops) /\
    out.as_stack = stk_out ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs') ps'.ps_stack stk_out /\
    venom_asm_terminal_rel vs' out /\
    TAKE (w2n sz) (DROP (w2n dst) vs'.vs_memory) =
      TAKE (w2n sz) (DROP (w2n dst) out.as_memory) /\
    sym_steps prog env (LENGTH (execute_plan fmp ops)) ss = SymOK ss_out /\
    asm_sym_rel prog env out ss_out /\ ss_out.sym_stack = top_out ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top_out /\
    (!b. b IN FDOM ss_out.sym_mem_labels ==> context_spill_byte cp b) /\
    ~mem_labels_hit ss_out.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))
Proof
  qx_gen_tac `cplan` >> strip_tac >>
  drule_all fnFrameStepsRevertForwardTheory.rf_suffix_copy_execution >>
  disch_then (qspec_then `build_offset_to_pc prog` mp_tac) >> simp[] >> strip_tac >>
  rename1 `asm_steps _ _ _ (LENGTH (execute_plan fmp ops)) st = AsmOK out` >>
  rename1 `out.as_stack = stk_out ++ rest` >>
  drule_all sym_rf_copy_preparation_execution >> strip_tac >>
  rename1 `mid.as_stack = stk_mid ++ rest` >>
  rename1 `ss'.sym_stack = top_mid ++ srest` >>
  `LENGTH (execute_plan fmp ops) = LENGTH (execute_plan fmp (ins ++ ros)) + 1` by
    simp[stackOpSimTheory.execute_plan_append, execute_plan_def, exec_stack_op_def,
         listTheory.APPEND_ASSOC] >>
  `asm_steps lo (build_offset_to_pc prog) prog 1 mid = AsmOK out` by
    (qpat_assum `asm_steps _ _ _ _ st = AsmOK mid`
       (mp_then Any (qspec_then `1` mp_tac) stackOpSimTheory.asm_steps_add_ok) >>
     gvs[]) >>
  `asm_step lo (build_offset_to_pc prog) (AsmOp "RETURNDATACOPY") mid = AsmOK out` by
    (qpat_x_assum `asm_steps _ _ _ 1 mid = _` mp_tac >>
     pure_rewrite_tac[arithmeticTheory.ONE, asmSemTheory.asm_steps_def] >>
     gvs[asm_block_at_def, AllCaseEqs()]) >>
  `plan_stack_rel lo (frame_view fn ra vs)
     (stack_pop 3 ps2.ps_stack ++ [zop;sop;dop]) stk_mid /\
   LIST_REL (op_kind_ok fn ret)
     (REVERSE (stack_pop 3 ps2.ps_stack ++ [zop;sop;dop])) top_mid` by metis_tac[] >>
  `ss'.sym_mem_labels = ss.sym_mem_labels` by
    metis_tac[finite_mapTheory.FLOOKUP_EXT] >>
  `!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cplan b` by simp[] >>
  qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  drule_all sym_rf_copy_prepared_success >> strip_tac >>
  rename1 `sym_steps prog env 1 ss' = SymOK ss_out` >>
  rename1 `ss_out.sym_stack = top_out ++ srest` >>
  qexistsl [`out`, `ss_out`, `stk_out`, `top_out`] >>
  gvs[fnPlanPrefixTheory.release_dead_spills_stack, sym_steps_add]
QED

Theorem sym_rf_copy_fault_stack:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dop;sop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  asm_static_wf prog /\ asm_sym_rel prog env cs ss /\
  cs.as_stack = dst :: src :: sz :: rest /\ ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;sop;dop])) top /\
  asm_block_at prog cs.as_pc [AsmOp "RETURNDATACOPY"] /\
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (AsmOp "RETURNDATACOPY") cs = AsmFault cs' ==>
  sym_terminal (sym_steps prog env 1 ss)
Proof
  strip_tac >> drule_all sym_rf_copy_prepared_stack >> strip_tac >>
  irule sym_terminal_opcode_transfer >>
  conj_tac >- simp[] >>
  qexistsl [`[dst;src;sz]`, `AsmFault cs'`, `cs`, `"RETURNDATACOPY"`, `suffix`] >>
  simp[asm_op_arity_def, asm_op_mem_reads_def, mem_labels_hit_def,
       asm_op_arity_table_def, log_table_def]
QED

Theorem sym_rf_copy_fault_execution:
  !cp.
  lo = SND (compute_label_offsets prog) /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo sop = SOME src /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  w2n src + w2n sz > LENGTH vs.vs_returndata /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?out.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmFault out /\
    venom_asm_terminal_rel (halt_state (set_returndata [] vs)) out /\
    sym_terminal (sym_steps prog env (LENGTH (execute_plan fmp ops)) ss)
Proof
  qx_gen_tac `cplan` >> strip_tac >>
  drule_all (SRULE [] (Q.INST
    [`vs'` |-> `write_memory_with_expansion (w2n dst)
       (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs`]
    fnFrameStepsRevertForwardTheory.rf_suffix_copy_execution)) >>
  disch_then (qspec_then `build_offset_to_pc prog` mp_tac) >> simp[] >> strip_tac >>
  rename1 `asm_steps _ _ _ (LENGTH (execute_plan fmp ops)) st = AsmFault out` >>
  drule_all sym_rf_copy_preparation_execution >> strip_tac >>
  rename1 `mid.as_stack = stk_mid ++ rest` >>
  rename1 `ss'.sym_stack = top_mid ++ srest` >>
  `LENGTH (execute_plan fmp ops) = LENGTH (execute_plan fmp (ins ++ ros)) + 1` by
    simp[stackOpSimTheory.execute_plan_append, execute_plan_def, exec_stack_op_def,
         listTheory.APPEND_ASSOC] >>
  `asm_steps lo (build_offset_to_pc prog) prog 1 mid = AsmFault out` by
    (qpat_assum `asm_steps _ _ _ _ st = AsmOK mid`
       (mp_then Any (qspec_then `1` mp_tac) stackOpSimTheory.asm_steps_add_ok) >> gvs[]) >>
  `asm_step lo (build_offset_to_pc prog) (AsmOp "RETURNDATACOPY") mid = AsmFault out` by
    (qpat_x_assum `asm_steps _ _ _ 1 mid = _` mp_tac >>
     pure_rewrite_tac[arithmeticTheory.ONE, asmSemTheory.asm_steps_def] >>
     gvs[asm_block_at_def, AllCaseEqs()]) >>
  `dop <> dead_stack_marker /\ sop <> dead_stack_marker /\ zop <> dead_stack_marker` by
    (rpt strip_tac >> gvs[dead_stack_marker_def, is_label_operand_def]) >>
  `?d s z residual. stk_mid = d :: s :: z :: residual /\
    operand_val (frame_view fn ra vs) lo dop = SOME d /\
    operand_val (frame_view fn ra vs) lo sop = SOME s /\
    operand_val (frame_view fn ra vs) lo zop = SOME z` by
    (irule emitSimTheory.asm_stack_top3_from_plan >> simp[] >>
     qexists `stack_pop 3 ps2.ps_stack` >> metis_tac[]) >>
  gvs[] >>
  `LIST_REL (op_kind_ok fn ret)
    (REVERSE (stack_pop 3 ps2.ps_stack ++ [zop;sop;dop])) top_mid` by metis_tac[] >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by simp[] >>
  `asm_block_at prog mid.as_pc [AsmOp "RETURNDATACOPY"]` by metis_tac[] >>
  drule_all sym_rf_copy_fault_stack >> simp[sym_steps_add]
QED

Theorem sym_rf_entry_copy_execution:
  !cp.
  lo = SND (compute_label_offsets prog) /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
    operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] at)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo sop = SOME src /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  vs' = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  if w2n src + w2n sz <= LENGTH vs.vs_returndata then
  (?out ss_out stk_out top_out.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmOK out /\
    out.as_pc = st.as_pc + LENGTH (execute_plan fmp ops) /\
    out.as_stack = stk_out ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs') ps'.ps_stack stk_out /\
    venom_asm_terminal_rel vs' out /\
    TAKE (w2n sz) (DROP (w2n dst) vs'.vs_memory) =
      TAKE (w2n sz) (DROP (w2n dst) out.as_memory) /\
    sym_steps prog env (LENGTH (execute_plan fmp ops)) ss = SymOK ss_out /\
    asm_sym_rel prog env out ss_out /\ ss_out.sym_stack = top_out ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top_out /\
    (!b. b IN FDOM ss_out.sym_mem_labels ==> context_spill_byte cp b) /\
    ~mem_labels_hit ss_out.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)))
  else
  (?out. asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmFault out /\
    venom_asm_terminal_rel (halt_state (set_returndata [] vs)) out /\
    sym_terminal (sym_steps prog env (LENGTH (execute_plan fmp ops)) ss))
Proof
  gen_tac >> strip_tac >>
  `rf_inventory_inv fn ra lo (frame_view fn ra vs) ps vs` by
    (irule fnFrameStepsRevertForwardTheory.rf_inventory_inv_entry >> gvs[]) >>
  `!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] op)` by
    (rpt strip_tac >>
     irule fnFrameStepsRevertForwardTheory.rf_inventory_inv_input_value >>
     qexists `ps` >> simp[]) >>
  Cases_on `w2n src + w2n sz <= LENGTH vs.vs_returndata` >> simp[]
  >- (drule_all sym_rf_copy_success_execution >> simp[]) >>
  `w2n src + w2n sz > LENGTH vs.vs_returndata` by simp[] >>
  drule_all sym_rf_copy_fault_execution >> simp[]
QED

Theorem sym_revert_operand_kind:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = REVERT /\
  MEM op inst.inst_operands /\ ~is_label_operand op /\
  op_kind_ok fn ret op sv ==>
  ?w. sv = Val w
Proof
  strip_tac >>
  `op <> dead_stack_marker` by
    (strip_tac >> gvs[dead_stack_marker_def, is_label_operand_def]) >>
  drule ordinary_noncopy_operand_word_kind >>
  disch_then drule >> simp[] >> metis_tac[]
QED

Theorem sym_revert_prepared_stack:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = REVERT /\
  inst.inst_operands = [dop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  asm_sym_rel prog env cs ss /\ cs.as_stack = dst :: sz :: rest /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;dop])) top ==>
  ?suffix. ss.sym_stack = MAP Val [dst;sz] ++ suffix
Proof
  strip_tac >>
  gvs[listTheory.REVERSE_APPEND, listTheory.LIST_REL_CONS1] >>
  rename1 `op_kind_ok fn ret dop sd` >>
  rename1 `op_kind_ok fn ret zop szv` >>
  `(?w. sd = Val w) /\ (?w. szv = Val w)` by
    (conj_tac >> irule sym_revert_operand_kind >> metis_tac[listTheory.MEM]) >>
  gvs[asm_sym_rel_def, sval_conc_def]
QED

Theorem sym_revert_prepared_terminal:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = REVERT /\
  inst.inst_operands = [dop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  plan_stack_rel (SND (compute_label_offsets prog)) current (tail ++ [zop;dop]) stk /\
  operand_val current (SND (compute_label_offsets prog)) dop = SOME dst /\
  operand_val current (SND (compute_label_offsets prog)) zop = SOME sz /\
  cs.as_stack = stk ++ rest /\ asm_sym_rel prog env cs ss /\ asm_static_wf prog /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;dop])) top /\
  ~mem_labels_hit ss.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)) /\
  asm_block_at prog cs.as_pc [AsmOp "REVERT"] /\
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (AsmOp "REVERT") cs = AsmRevert out ==>
  sym_terminal (sym_steps prog env 1 ss)
Proof
  strip_tac >>
  `dop <> dead_stack_marker /\ zop <> dead_stack_marker` by
    (rpt strip_tac >> gvs[dead_stack_marker_def, is_label_operand_def]) >>
  `?d z residual. stk = d :: z :: residual /\
    operand_val current (SND (compute_label_offsets prog)) dop = SOME d /\
    operand_val current (SND (compute_label_offsets prog)) zop = SOME z` by
    (irule emitSimTheory.asm_stack_top2_from_plan >> simp[] >>
     qexists `tail` >> simp[]) >>
  gvs[] >> rename1 `cs.as_stack = dst :: sz :: remaining` >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by simp[] >>
  drule_all sym_revert_prepared_stack >> strip_tac >>
  irule sym_terminal_opcode_transfer >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`[dst;sz]`, `AsmRevert out`, `cs`, `"REVERT"`, `suffix`] >>
  simp[asm_op_arity_def, asm_op_arity_table_def, asm_op_mem_reads_def,
       asmSemTheory.log_table_def]
QED

Theorem sym_rf_suffix_revert_abort:
  !cp.
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  rf_spills_separated ps /\
  inst.inst_opcode = REVERT /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  TAKE (w2n sz) (DROP (w2n dst) vs.vs_memory) =
    TAKE (w2n sz) (DROP (w2n dst) st.as_memory) /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
  step_inst fuel ctx inst vs = Abort a vs' /\
  MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  ~mem_labels_hit ss.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)) ==>
  a = Revert_abort /\
  ?out. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
    AsmRevert out /\ venom_asm_terminal_rel vs' out /\
    sym_terminal (sym_steps prog env (LENGTH (execute_plan initial_fmp ops)) ss)
Proof
  gen_tac >> strip_tac >>
  drule_all fnFrameStepsRevertForwardTheory.rf_suffix_revert_abort >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  simp[] >>
  Cases_on `emit_input_plan REVERT (compute_operands inst) nl ps` >>
  rename1 `_ = (ins,ps1)` >>
  Cases_on `reorder_plan (dfg_build_function fn) (compute_operands inst) ps1` >>
  rename1 `_ = (ros,ps2)` >>
  `compute_operands inst = [zop;dop]` by
    simp[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def] >>
  `ops = ins ++ ros ++ [SOEmit "REVERT"]` by
    gvs[generate_regular_inst_plan_def, venomEffectsTheory.is_commutative_def,
        generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def] >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp (ins ++ ros)) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp (ins ++ ros)))
     [AsmOp "REVERT"]` by
    gvs[stackOpSimTheory.execute_plan_append, execute_plan_def, exec_stack_op_def,
        stackOpSimTheory.asm_block_at_append, listTheory.APPEND_ASSOC] >>
  `!off. ~MEM (SOSpill off) (ins ++ ros) /\
         ~MEM (SORestore off) (ins ++ ros)` by fs[listTheory.MEM_APPEND] >>
  `REVERT <> INVOKE /\ LENGTH (compute_operands inst) <= 16 /\
   EVERY (\op. ~is_label_operand op) (compute_operands inst)` by gvs[] >>
  `EVERY is_simple_stack_op (ins ++ ros)` by
    metis_tac[fnFrameStepsRevertForwardTheory.spill_free_preparation_simple] >>
  `prefix_wf lo (LENGTH ps.ps_stack) (ins ++ ros)` by
    (irule fnFrameStepsRevertForwardTheory.available_preparation_prefix_wf >>
     qexistsl [`dfg_build_function fn`, `compute_operands inst`, `nl`, `REVERT`,
               `ps1`, `ps2`] >>
     simp[] >> gvs[] >> metis_tac[is_label_operand_def]) >>
  drule_all sym_rf_suffix_preparation_execution >> strip_tac >>
  `asm_steps lo (build_offset_to_pc prog) prog 1 mid = AsmRevert out` by
    (qpat_assum `asm_steps _ _ _ _ st = AsmOK mid`
       (mp_then Any (qspec_then `1` mp_tac) stackOpSimTheory.asm_steps_add_ok) >>
     gvs[stackOpSimTheory.execute_plan_append, execute_plan_def, exec_stack_op_def,
         listTheory.APPEND_ASSOC]) >>
  `asm_block_at prog mid.as_pc [AsmOp "REVERT"]` by metis_tac[] >>
  `asm_step lo (build_offset_to_pc prog) (AsmOp "REVERT") mid = AsmRevert out` by
    (qpat_x_assum `asm_steps _ _ _ 1 mid = _` mp_tac >>
     pure_rewrite_tac[arithmeticTheory.ONE, asmSemTheory.asm_steps_def] >>
     gvs[asm_block_at_def, AllCaseEqs()]) >>
  `ss'.sym_mem_labels = ss.sym_mem_labels` by
    metis_tac[finite_mapTheory.FLOOKUP_EXT] >>
  `sym_terminal (sym_steps prog env 1 ss')` by
    (`plan_stack_rel lo (frame_view fn ra vs)
        (stack_pop 2 ps2.ps_stack ++ [zop;dop]) stk' /\
      LIST_REL (op_kind_ok fn ret)
        (REVERSE (stack_pop 2 ps2.ps_stack ++ [zop;dop])) top'` by
       (qpat_assum `compute_operands inst = _` (fn eq =>
          qpat_assum `ps2.ps_stack = _`
            (fn th => pure_rewrite_tac[GSYM (SRULE [eq] th)])) >> simp[]) >>
     metis_tac[sym_revert_prepared_terminal]) >>
  `LENGTH (execute_plan initial_fmp ops) =
     LENGTH (execute_plan initial_fmp (ins ++ ros)) + 1` by
    simp[stackOpSimTheory.execute_plan_append, execute_plan_def, exec_stack_op_def,
         listTheory.APPEND_ASSOC] >>
  asm_simp_tac (srw_ss()) [sym_steps_add]
QED

Theorem sym_plan_stack_rel_inst_idx:
  plan_stack_rel lo (frame_view fn ra (s with vs_inst_idx := k)) ops stk <=>
  plan_stack_rel lo (frame_view fn ra s) ops stk
Proof
  simp[codegenRelTheory.plan_stack_rel_def] >>
  AP_TERM_TAC >> AP_TERM_TAC >> ABS_TAC >>
  Cases_on `EL i (REVERSE ops)` >>
  simp[frame_view_def, codegenRelTheory.operand_val_def, venomStateTheory.lookup_var_def]
QED

Theorem sym_terminal_rel_inst_idx:
  venom_asm_terminal_rel (s with vs_inst_idx := k) st <=>
  venom_asm_terminal_rel s st
Proof
  simp[venom_asm_terminal_rel_def]
QED

Theorem sym_assign_success_state:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ step_inst fuel ctx inst s = OK s' ==>
  ?w. s' = s with vs_vars := s.vs_vars |+ (out,w)
Proof
  strip_tac >>
  `step_inst fuel ctx inst s = step_inst_base inst s` by
    gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  once_rewrite_tac[step_inst_base_def] >>
  simp[] >> Cases_on `eval_operand rhs s` >>
  simp[venomStateTheory.update_var_def] >> metis_tac[]
QED

Theorem sym_assign_block_abort_continuation:
  s.vs_inst_idx = k /\ get_instruction bb k = SOME inst /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ exec_block fuel ctx bb s = Abort a s_end ==>
  ?s'. step_inst fuel ctx inst s = OK s' /\
    exec_block fuel ctx bb (s' with vs_inst_idx := SUC k) = Abort a s_end
Proof
  strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def, is_terminator_def] >>
  Cases_on `eval_operand rhs s` >>
  `step_inst fuel ctx inst s = step_inst_base inst s` by
    gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  pop_assum SUBST1_TAC >> once_rewrite_tac[step_inst_base_def] >>
  qpat_assum `inst.inst_opcode = ASSIGN` SUBST1_TAC >>
  qpat_assum `inst.inst_operands = [rhs]` SUBST1_TAC >>
  qpat_assum `inst.inst_outputs = [out]` SUBST1_TAC >> simp[]
QED

Theorem sym_rf_future_non_phi:
  revert_forward_pair bb i j /\ i < k ==>
  !r ti. SUC k <= r /\ r <= j /\ get_instruction bb r = SOME ti ==>
    ti.inst_opcode <> PHI
Proof
  rpt strip_tac >>
  `ti.inst_opcode =
    (if r = i then RETURNDATACOPY else if r = j then REVERT else ASSIGN)` by
    (irule fnFrameStepsRevertForwardTheory.rf_forward_instruction_opcode >>
     conj_tac >- decide_tac >> simp[] >> qexists `bb` >> simp[]) >>
  Cases_on `r = i` >> fs[] >> Cases_on `r = j` >> fs[]
QED

Theorem sym_rf_assign_continuation_execution:
  !cp. lo = SND (compute_label_offsets prog) /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  rf_spills_separated ps /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs /\
  (is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled) /\
  rf_inventory_inv fn ra lo entry ps s /\
  operand_val (frame_view fn ra s) lo rhs =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] rhs) /\
  step_inst fuel ctx inst s = OK s' /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel s st /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?st' ss' stk' top'.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmOK st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan fmp ops) /\
    st'.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra (s' with vs_inst_idx := k)) ps'.ps_stack stk' /\
    st'.as_memory = st.as_memory /\ s'.vs_memory = s.vs_memory /\
    venom_asm_terminal_rel (s' with vs_inst_idx := k) st' /\
    sym_steps prog env (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    asm_sym_rel prog env st' ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  gen_tac >> strip_tac >>
  drule_all sym_rf_assign_plan_execution >> strip_tac >>
  drule_all fnFrameStepsRevertForwardTheory.rf_assign_plan_execution >>
  disch_then (qspec_then `build_offset_to_pc prog` strip_assume_tac) >>
  `st'.as_memory = st.as_memory /\ venom_asm_terminal_rel s st'` by
    gvs[venom_asm_terminal_rel_def] >>
  drule_all sym_assign_success_state >> strip_tac >>
  qexistsl [`st'`,`ss'`,`stk'`,`top'`] >>
  gvs[sym_plan_stack_rel_inst_idx, sym_terminal_rel_inst_idx,
      venom_asm_terminal_rel_def]
QED

Theorem sym_rf_strict_suffix_abort:
  !k s st ps stk ops ps_end ss top.
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\ i < k /\ k <= j /\ s.vs_inst_idx = k /\
  LENGTH (get_params bb.bb_instructions) <= k /\
  get_instruction bb i = SOME copy /\ copy.inst_operands = [cdop;csop;czop] /\
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] cdop) = SOME dst /\
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] czop) = SOME sz /\
  EVERY (\ti. EVERY (\op. ~is_label_operand op) ti.inst_operands)
    (DROP i bb.bb_instructions) /\
  rf_spills_separated ps /\ rf_value_inv fn ra bb j lo entry k s /\
  rf_inventory_inv fn ra lo entry ps s /\
  (!op. rf_live_use bb k j op /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel s st /\
  TAKE (w2n sz) (DROP (w2n dst) s.vs_memory) =
    TAKE (w2n sz) (DROP (w2n dst) st.as_memory) /\
  generate_block_insts_plan (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
    (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
    (k - LENGTH (get_params bb.bb_instructions)) (DROP k bb.bb_instructions)
    ps = SOME (ops,ps_end) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
  MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cplan b) /\
  ~mem_labels_hit ss.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)) ==>
  exec_block fuel ctx bb s = Abort a s_end ==>
  a = Revert_abort /\
  ?n out. asm_steps lo o2pc prog n st = AsmRevert out /\
    venom_asm_terminal_rel s_end out /\ sym_terminal (sym_steps prog env n ss)
Proof
  measureInduct_on `j - k` >> rpt gen_tac >> strip_tac >> disch_tac >>
  `i <= k` by decide_tac >>
  `?inst. get_instruction bb k = SOME inst` by
    (irule fnFrameStepsRevertForwardTheory.rf_forward_instruction_exists >> metis_tac[]) >>
  `MEM inst (fn_insts fn)` by
    (irule allocaRemapSSATheory.mem_fn_insts_intro >> qexists `bb` >>
     fs[get_instruction_def] >> metis_tac[livenessTransferProofsTheory.lookup_block_mem, listTheory.EL_MEM]) >>
  drule_all fnFrameStepsRevertForwardTheory.rf_forward_instruction_opcode >> strip_tac >>
  drule_all fnFrameStepsRevertForwardTheory.rf_forward_instruction_shape >> strip_tac >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by
    (irule fnFrameStepsRevertForwardTheory.rf_suffix_instruction_no_labels >> metis_tac[]) >>
  `!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra s) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)` by
    (rpt strip_tac >> gvs[fnFrameStepsRevertForwardTheory.rf_value_inv_def] >> first_x_assum irule >>
     irule fnFrameStepsRevertForwardTheory.rf_live_use_current >> metis_tac[]) >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     irule fnFrameStepsRevertForwardTheory.rf_live_use_current >> metis_tac[]) >>
  drule_all fnFrameStepsRevertForwardTheory.rf_block_plan_step >> strip_tac >>
  `generate_regular_inst_plan (liveness_analyze fn) (dfg_build_function fn)
     (cfg_analyze fn) fn inst
     (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) (bb_is_halting bb)
     (case DROP (SUC k) bb.bb_instructions of
        [] => F | next_i::tail => is_terminator next_i.inst_opcode)
     bb.bb_label ps = (step_ops,ps1)` by
    (irule fnFrameStepsRevertForwardTheory.rf_forward_regular_plan_result >>
     conj_tac >- first_assum ACCEPT_TAC >> qexistsl [`bb`,`i`,`j`,`k`] >> simp[]) >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp step_ops) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp step_ops))
     (execute_plan initial_fmp rest_ops)` by
    gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  `!off. ~MEM (SOSpill off) step_ops /\ ~MEM (SORestore off) step_ops` by
    fs[listTheory.MEM_APPEND] >>
  Cases_on `k = j` >- suspend "revert" >>
  suspend "assign"
QED

Resume sym_rf_strict_suffix_abort[revert]:
  pop_last_assum kall_tac >>
  `inst.inst_opcode = REVERT /\ inst.inst_outputs = []` by gvs[] >>
  `?dop zop. inst.inst_operands = [dop;zop]` by
    gvs[listTheory.LENGTH_EQ_NUM_compute] >>
  `operand_val (frame_view fn ra s) lo dop = SOME dst /\
   operand_val (frame_view fn ra s) lo zop = SOME sz` by
    (irule fnFrameStepsRevertForwardTheory.rf_forward_revert_range >> metis_tac[]) >>
  `step_inst fuel ctx inst s = Abort a s_end` by
    (qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
     gvs[Once exec_block_def, is_terminator_def, AllCaseEqs()]) >>
  drule_all sym_rf_suffix_revert_abort >> strip_tac >>
  simp[] >> qexistsl [`LENGTH (execute_plan initial_fmp step_ops)`,`out`] >> gvs[]
QED

Resume sym_rf_strict_suffix_abort[assign]:
  `k < j /\ inst.inst_opcode = ASSIGN` by gvs[] >>
  `?rhs out. inst.inst_operands = [rhs] /\ inst.inst_outputs = [out]` by metis_tac[] >>
  `~is_label_operand rhs` by fs[] >>
  drule_all sym_assign_block_abort_continuation >> strip_tac >>
  `!r ti. SUC k <= r /\ r <= j /\ get_instruction bb r = SOME ti ==>
    ti.inst_opcode <> PHI` by metis_tac[sym_rf_future_non_phi] >>
  drule_all fnFrameStepsRevertForwardTheory.rf_assign_success_invariants >> strip_tac >>
  `is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled` by
    (strip_tac >> first_x_assum irule >>
     simp[compute_operands_def, python_stack_operands_def]) >>
  `operand_val (frame_view fn ra s) lo rhs =
   operand_val entry lo (normalize_operand (dfg_build_function fn) [] rhs)` by
    (first_x_assum irule >> simp[compute_operands_def, python_stack_operands_def]) >>
  drule_all sym_rf_assign_continuation_execution >>
  disch_then (qspec_then `SUC k` strip_assume_tac) >>
  `!off. ~MEM (SOSpill off) rest_ops /\ ~MEM (SORestore off) rest_ops` by
    fs[listTheory.MEM_APPEND] >>
  `asm_block_at prog st'.as_pc (execute_plan initial_fmp rest_ops)` by metis_tac[] >>
  `~mem_labels_hit ss'.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))` by
    (`ss'.sym_mem_labels = ss.sym_mem_labels` by
      metis_tac[finite_mapTheory.FLOOKUP_EXT] >> simp[]) >>
  `j - SUC k < j - k` by decide_tac >>
  qpat_x_assum `!y. j - y < j - k ==> _`
    (qspec_then `SUC k` mp_tac) >>
  simp[] >>
  disch_then (qspec_then `s' with vs_inst_idx := SUC k` mp_tac) >>
  gvs[] >> disch_then (qspec_then `st'` mp_tac) >>
  simp[] >> disch_then drule_all >> strip_tac >> simp[] >>
  qexistsl [`LENGTH (execute_plan initial_fmp step_ops) + n`, `out'`] >>
  conj_tac
  >- (qpat_assum `asm_steps _ _ _ _ st = AsmOK _`
        (mp_then Any (qspec_then `n` mp_tac) stackOpSimTheory.asm_steps_add_ok) >> gvs[]) >>
  simp[sym_steps_add]
QED

Finalise sym_rf_strict_suffix_abort

Theorem sym_rf_current_normalized_value:
  rf_value_inv fn ra bb j lo entry k s /\
  get_instruction bb k = SOME inst /\ k <= j /\
  MEM op (compute_operands inst) /\
  operand_val (frame_view fn ra s) lo op = value ==>
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] op) = value
Proof
  simp[fnFrameStepsRevertForwardTheory.rf_value_inv_def] >>
  metis_tac[fnFrameStepsRevertForwardTheory.rf_live_use_current]
QED

Theorem sym_rf_copy_normalized_range:
  rf_value_inv fn ra bb j lo entry i s /\
  get_instruction bb i = SOME inst /\ i <= j /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [dop;sop;zop] /\
  operand_val (frame_view fn ra s) lo dop = SOME dst /\
  operand_val (frame_view fn ra s) lo zop = SOME sz ==>
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] dop) = SOME dst /\
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] zop) = SOME sz
Proof
  rpt strip_tac >>
  `MEM dop (compute_operands inst) /\ MEM zop (compute_operands inst)` by
    simp[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def] >>
  metis_tac[sym_rf_current_normalized_value]
QED

Theorem sym_rf_abort_source_fault:
  revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\ i <= j /\
  get_instruction bb i = SOME inst /\ exec_block fuel ctx bb vs = Abort a vs_end /\
  step_inst fuel ctx inst vs = Abort ExHalt_abort fault ==>
  a = ExHalt_abort /\ vs_end = fault
Proof
  rpt strip_tac >>
  `i <= vs.vs_inst_idx /\ vs.vs_inst_idx <= j /\
   get_instruction bb vs.vs_inst_idx = SOME inst` by simp[] >>
  drule_all fnFrameStepsRevertForwardTheory.rf_forward_exec_abort_cases >> simp[]
QED

Theorem sym_rf_abort_source_success:
  revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\ i <= j /\
  get_instruction bb i = SOME inst /\ exec_block fuel ctx bb vs = Abort a vs_end /\
  step_inst fuel ctx inst vs = OK copied ==>
  exec_block fuel ctx bb (copied with vs_inst_idx := SUC i) = Abort a vs_end
Proof
  rpt strip_tac >>
  `i <= vs.vs_inst_idx /\ vs.vs_inst_idx <= j /\
   get_instruction bb vs.vs_inst_idx = SOME inst` by simp[] >>
  drule_all fnFrameStepsRevertForwardTheory.rf_forward_exec_abort_cases >> simp[]
QED

Theorem sym_rf_revert_runs_compose:
  asm_steps lo o2pc prog n1 ast = AsmOK mid /\
  asm_steps lo o2pc prog n2 mid = AsmRevert out /\
  sym_steps prog env n1 ss = SymOK ss_mid /\
  sym_terminal (sym_steps prog env n2 ss_mid) ==>
  asm_steps lo o2pc prog (n1 + n2) ast = AsmRevert out /\
  sym_terminal (sym_steps prog env (n1 + n2) ss)
Proof
  rpt strip_tac >-
    (irule blockSimHelpersTheory.asm_steps_compose_revert >> metis_tac[]) >>
  simp[sym_steps_add]
QED

Theorem sym_rf_entry_fault_terminal:
  revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\ i <= j /\
  get_instruction bb i = SOME inst /\ exec_block fuel ctx bb vs = Abort a vs_end /\
  step_inst fuel ctx inst vs = Abort ExHalt_abort fault /\
  asm_steps lo o2pc prog n ast = AsmFault out /\
  venom_asm_terminal_rel fault out /\ sym_terminal (sym_steps prog env n ss) ==>
  ?m ast_end.
    ((a = Revert_abort /\ asm_steps lo o2pc prog m ast = AsmRevert ast_end) \/
     (a = ExHalt_abort /\ asm_steps lo o2pc prog m ast = AsmFault ast_end)) /\
    venom_asm_terminal_rel vs_end ast_end /\ sym_terminal (sym_steps prog env m ss)
Proof
  rpt strip_tac >> drule_all sym_rf_abort_source_fault >> strip_tac >>
  qexistsl [`n`,`out`] >> simp[]
QED

Theorem sym_rf_entry_future_non_phi:
  revert_forward_pair bb i j ==>
  !r ti. SUC i <= r /\ r <= j /\ get_instruction bb r = SOME ti ==>
    ti.inst_opcode <> PHI
Proof
  rpt strip_tac >>
  `i <= r /\ r <> i` by decide_tac >>
  drule_all fnFrameStepsRevertForwardTheory.rf_forward_instruction_opcode >>
  simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem sym_rf_entry_success_terminal:
  !cp.
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\ i < j /\
  LENGTH (get_params bb.bb_instructions) <= i /\
  get_instruction bb i = SOME inst /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  EVERY (\ti. EVERY (\op. ~is_label_operand op) ti.inst_operands)
    (DROP i bb.bb_instructions) /\
  rf_spills_separated ps /\
  rf_value_inv fn ra bb j lo (frame_view fn ra vs) i vs /\
  rf_inventory_inv fn ra lo (frame_view fn ra vs) ps vs /\
  (!op. rf_live_use bb i j op /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  generate_regular_inst_plan (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn inst (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
    halting term bb.bb_label ps = (step_ops,ps1) /\
  (!off. ~MEM (SOSpill off) step_ops /\ ~MEM (SORestore off) step_ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  step_inst fuel ctx inst vs = OK copied /\
  exec_block fuel ctx bb vs = Abort a vs_end /\
  asm_steps lo (build_offset_to_pc prog) prog
    (LENGTH (execute_plan fmp step_ops)) ast = AsmOK out /\
  out.as_pc = ast.as_pc + LENGTH (execute_plan fmp step_ops) /\
  out.as_stack = stk_out ++ rest /\
  plan_stack_rel lo (frame_view fn ra copied) ps1.ps_stack stk_out /\
  venom_asm_terminal_rel copied out /\
  TAKE (w2n sz) (DROP (w2n dst) copied.vs_memory) =
    TAKE (w2n sz) (DROP (w2n dst) out.as_memory) /\
  generate_block_insts_plan (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
    (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
    (SUC i - LENGTH (get_params bb.bb_instructions)) (DROP (SUC i) bb.bb_instructions)
    ps1 = SOME (rest_ops,ps_end) /\
  (!off. ~MEM (SOSpill off) rest_ops /\ ~MEM (SORestore off) rest_ops) /\
  asm_block_at prog (ast.as_pc + LENGTH (execute_plan fmp step_ops))
    (execute_plan fmp rest_ops) /\
  MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\
  sym_steps prog env (LENGTH (execute_plan fmp step_ops)) ss = SymOK ss_out /\
  asm_sym_rel prog env out ss_out /\ ss_out.sym_stack = top_out ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps1.ps_stack) top_out /\
  (!b. b IN FDOM ss_out.sym_mem_labels ==> context_spill_byte cp b) /\
  ~mem_labels_hit ss_out.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)) ==>
  ?n ast_end.
    ((a = Revert_abort /\ asm_steps lo o2pc prog n ast = AsmRevert ast_end) \/
     (a = ExHalt_abort /\ asm_steps lo o2pc prog n ast = AsmFault ast_end)) /\
    venom_asm_terminal_rel vs_end ast_end /\ sym_terminal (sym_steps prog env n ss)
Proof
  gen_tac >> strip_tac >>
  `i <= j` by decide_tac >>
  drule_all sym_rf_abort_source_success >> disch_tac >>
  `LENGTH (compute_operands inst) <= 16` by
    simp[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def] >>
  drule sym_rf_entry_future_non_phi >> disch_tac >>
  drule_all fnFrameStepsRevertForwardTheory.rf_suffix_copy_success_invariants >> strip_tac >>
  drule_all sym_rf_copy_normalized_range >> strip_tac >>
  `i < SUC i /\ SUC i <= j /\ LENGTH (get_params bb.bb_instructions) <= SUC i` by decide_tac >>
  `plan_stack_rel lo (frame_view fn ra (copied with vs_inst_idx := SUC i)) ps1.ps_stack stk_out /\
   venom_asm_terminal_rel (copied with vs_inst_idx := SUC i) out /\
   TAKE (w2n sz) (DROP (w2n dst) (copied with vs_inst_idx := SUC i).vs_memory) =
     TAKE (w2n sz) (DROP (w2n dst) out.as_memory)` by
    simp[sym_plan_stack_rel_inst_idx, sym_terminal_rel_inst_idx] >>
  `(copied with vs_inst_idx := SUC i).vs_inst_idx = SUC i` by simp[] >>
  `asm_block_at prog out.as_pc (execute_plan fmp rest_ops)` by metis_tac[] >>
  qpat_assum `rf_inventory_inv _ _ _ _ ps1 _`
    (mp_then (Pat `rf_inventory_inv _ _ _ _ _ _`) mp_tac
      (Q.SPEC `SUC i` sym_rf_strict_suffix_abort)) >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  qpat_x_assum `o2pc = _` SUBST_ALL_TAC >>
  drule_all sym_rf_revert_runs_compose >> strip_tac >>
  qexistsl [`LENGTH (execute_plan fmp step_ops) + n`, `out'`] >>
  ASM_SIMP_TAC bool_ss []
QED

Theorem sym_rf_entry_forward_abort:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn bb i j ps vs ast ops
   ps_end ra rest mem0 a vs_end env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\
    LENGTH (get_params bb.bb_instructions) <= i /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions) /\ rf_spills_separated ps /\
    (!k inst op. i <= k /\ get_instruction bb k = SOME inst /\
       MEM op (compute_operands inst) /\ is_var_operand op /\
       (!k' inst' x. i <= k' /\ k' < k /\ get_instruction bb k' = SOME inst' /\
                     op = Var x ==> ~MEM x inst'.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (i - LENGTH (get_params bb.bb_instructions))
      (DROP i bb.bb_instructions) ps = SOME (ops, ps_end) /\
    (!off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops) /\
    (!name. MEM (AsmOp name) (execute_plan cp.cp_initial_fmp ops) ==>
            IS_SOME (evm_opcode_byte name)) /\
    asm_block_at prog ast.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps ast ss /\
    exec_block fuel ctx bb vs = Abort a vs_end ==>
    ?n ast_end.
      ((a = Revert_abort /\ asm_steps lo o2pc prog n ast = AsmRevert ast_end) \/
       (a = ExHalt_abort /\ asm_steps lo o2pc prog n ast = AsmFault ast_end)) /\
      venom_asm_terminal_rel vs_end ast_end /\
      sym_terminal (sym_steps prog env n ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnFrameStepsRevertForwardTheory.rf_entry_copy_setup >> strip_tac >>
  drule_all fnFrameStepsRevertForwardTheory.rf_copy_source_alignment >>
  disch_then (qspec_then `fuel` (qspec_then `ctx` assume_tac)) >>
  Cases_on `emit_input_plan RETURNDATACOPY (compute_operands inst)
    (live_vars_at liveness bb.bb_label (SUC i)) ps` >>
  rename1 `_ = (ins,prep)` >>
  Cases_on `reorder_plan (dfg_build_function fn) (compute_operands inst) prep` >>
  rename1 `_ = (ros,arr)` >>
  qpat_x_assum `liveness = _` SUBST_ALL_TAC >>
  qpat_x_assum `dfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  `!off. ~MEM (SOSpill off) step_ops /\ ~MEM (SORestore off) step_ops` by metis_tac[] >>
  `?top. asm_sym_rel prog env ast ss /\ ss.sym_stack = top ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
    (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp' b)` by
    fs[sym_frame_inv_def, sym_kinds_ok_def] >>
  qabbrev_tac `copied = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs` >>
  `copied = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs` by simp[Abbr `copied`] >>
  `!off. ~MEM (SOSpill off) rest_ops /\ ~MEM (SORestore off) rest_ops` by metis_tac[] >>
  drule_all sym_rf_entry_copy_execution >>
  reverse (Cases_on `w2n src + w2n sz <= LENGTH vs.vs_returndata`) >>
  pure_asm_rewrite_tac[COND_CLAUSES] >> strip_tac >>
  qpat_x_assum `step_inst fuel ctx inst vs = _` mp_tac >>
  pure_asm_rewrite_tac[COND_CLAUSES] >> disch_tac >>
  qpat_x_assum `copied = write_memory_with_expansion _ _ _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
  qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  qpat_x_assum `o2pc = _` SUBST_ALL_TAC
  >- suspend "fault" >> suspend "success"
QED

Resume sym_rf_entry_forward_abort[fault]:
  `i <= j` by decide_tac >>
  drule_all sym_rf_entry_fault_terminal >> simp[]
QED

Resume sym_rf_entry_forward_abort[success]:
  drule_all (SRULE [] (Q.INST
    [`lo` |-> `SND (compute_label_offsets prog)`,
     `o2pc` |-> `build_offset_to_pc prog`] sym_rf_entry_success_terminal)) >> simp[]
QED

Finalise sym_rf_entry_forward_abort

Theorem sym_jmp_suffix_frame_sim:
  !p env ctx cp fn ret srest labs0 ps cs ss l pc.
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc [AsmPushLabel l; AsmOp "JUMP"] /\
  sym_jump_dest p (Lab l 0) = SOME pc ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p 2 cs = AsmOK cs' /\
    sym_steps p env 2 ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 ps cs' ss' /\
    cs'.as_pc = pc
Proof
  rpt gen_tac >> strip_tac >>
  `ss.sym_base.as_pc = cs.as_pc` by
    metis_tac[sym_frame_inv_def, asm_sym_rel_pc] >>
  `sym_steps p env 2 ss = SymOK (ss with sym_base := ss.sym_base with as_pc := pc)` by
    (irule sym_jmp_suffix >> metis_tac[]) >>
  drule_all_then strip_assume_tac (cj 1 (iffLR sym_frame_inv_def)) >>
  drule_all_then strip_assume_tac asm_sym_steps_lockstep >>
  qexistsl [`cs'`, `ss with sym_base := ss.sym_base with as_pc := pc`] >>
  gvs[sym_frame_inv_def, sym_kinds_ok_def] >>
  drule_then mp_tac asm_sym_rel_pc >> simp[]
QED

Theorem sym_jmp_plan_decompose:
  inst.inst_opcode = JMP /\ inst.inst_operands = [Label target] /\
  inst.inst_outputs = [] /\
  lookup_block target fn.fn_blocks = SOME target_bb /\
  targets = MAP Var (input_vars_from lbl target_bb.bb_instructions
                       (live_vars_at lv target 0)) /\
  generate_inst_plan lv dfg cfg fn inst nl ih nit lbl ps = SOME (ops, qs) ==>
  ?rops prepared sops arranged.
    restore_spilled_plan targets ps = (rops, prepared) /\
    reorder_plan dfg targets prepared = (sops, arranged) /\
    ops = rops ++ sops ++ [SOPushLabel target; SOEmit "JUMP"] /\
    qs = release_dead_spills nl arranged
Proof
  strip_tac >>
  gvs[genFrameSimTheory.generate_inst_plan_jmp,
      generate_regular_inst_plan_def, compute_operands_def,
      asmIRTheory.get_non_label_operands_def, venomEffectsTheory.is_commutative_def,
      asmIRTheory.venom_to_evm_name_def, generate_emit_ops_def, stackModelTheory.stack_pop_def,
      join_target_ops_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem sym_jmp_plan_frame_sim:
  !base.
  generated_plan_state_wf_marked base ps /\
  pending_inventory_wf pending ps /\
  restore_spilled_plan pending ps = (rops, prepared) /\
  reorder_plan dfg pending prepared = (sops, arranged) /\
  ops = rops ++ sops ++ [SOPushLabel target; SOEmit "JUMP"] /\
  qs = release_dead_spills nl arranged /\
  (!off. MEM (SORestore off) rops ==> off < dimword(:256)) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) pending /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ MEM (AsmLabel target) p /\
  FLOOKUP (SND (compute_label_offsets p)) target = SOME off /\
  FLOOKUP (build_offset_to_pc p) off = SOME pc /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?ac sy.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK ac /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK sy /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 qs ac sy /\
    ac.as_pc = pc
Proof
  gen_tac >> strip_tac >>
  `sym_jump_dest p (Lab target 0) = SOME pc` by
    (irule sym_code_label_dest >> metis_tac[]) >>
  `execute_plan initial_fmp [SOPushLabel target; SOEmit "JUMP"] =
   [AsmPushLabel target; AsmOp "JUMP"]` by
    simp[execute_plan_def, exec_stack_op_def] >>
  gvs[allocMonoTheory.release_dead_spills_spill_base,
      allocMonoTheory.release_dead_spills_next_offset,
      stackOpSimTheory.execute_plan_append,
      stackOpSimTheory.asm_block_at_append, listTheory.EVERY_APPEND] >>
  `asm_block_at p cs.as_pc (execute_plan initial_fmp (rops ++ sops))` by
    simp[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  drule_all_then strip_assume_tac (SRULE []
    (Q.INST [`dfg` |-> `dfg_build_function fn`] sym_jmp_prepare_frame_sim)) >>
  `asm_block_at p cs'.as_pc [AsmPushLabel target; AsmOp "JUMP"]` by
    (simp[stackOpSimTheory.execute_plan_append] >>
     metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  drule_all_then strip_assume_tac sym_jmp_suffix_frame_sim >>
  drule_then assume_tac sym_frame_inv_release_dead_spills >>
  qexistsl [`cs''`, `ss''`] >>
  gvs[stackOpSimTheory.execute_plan_append] >>
  pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
  pure_once_rewrite_tac[stackOpSimTheory.asm_steps_add, sym_steps_add] >> simp[]
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
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac gen_jmp_frame_sim_deep_exact >>
  drule_all_then strip_assume_tac sym_jmp_plan_decompose >>
  `ssa_form fn` by fs[codegen_ready_fn_def] >>
  gvs[] >>
  drule_all_then strip_assume_tac (SRULE []
    (Q.INST [`dfg` |-> `dfg_build_function fn`,
             `ops` |-> `rops ++ sops ++ [SOPushLabel target; SOEmit "JUMP"]`,
             `qs` |-> `release_dead_spills nl arranged`] sym_jmp_plan_frame_sim)) >>
  gvs[] >> metis_tac[]
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
