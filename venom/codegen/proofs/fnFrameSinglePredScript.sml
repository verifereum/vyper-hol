(*
 * The prefix of a block with exactly one predecessor, against
 * frameRel$fn_frame_inv: clean_stack_plan's cleanup, then the PHI prefix
 * (possibly empty: nothing keeps PHIs out of such a block).  The join
 * case, with no cleanup, is fnFrameSteps$phi_prefix_frame_sim.
 *
 * The cleanup is fnFrameCleanStack$clean_stack_plan_frame_sim; the PHI
 * prefix is the shared fnFrameStepsPhi$phi_prefix_hits_frame_sim, whose
 * stack premise single_pred_phi_hits gives for any stack.
 *
 * TOP-LEVEL:
 *   single_pred_phi_hits         - CHEATED (a piece helper)
 *   single_pred_prefix_frame_sim - the cleanup, then the PHI prefix
 *)

Theory fnFrameSinglePred
Ancestors
  fnFrameCleanStack fnFrameStepsPhi allocMono stackOpSim venomWf cfgAnalysisProps
  stackModel list fnPlanPrefix fnFrameSteps genFrameSim fnPlanLineage frameRel
  contextCodegenRel codegenRel unitShapeDefs genBlockSim stackPlanGen
  stackPlanTypes planExec asmSem venomExecSemantics venomState venomInst
  livenessDefs dfgDefs cfgDefs cfgCorrectnessProof

(* The first phi_prefix_length instructions of a block survive the
   parameter filter as a prefix, and are PHIs. *)
Theorem phi_prefix_filter_mem:
  !l phis body inst.
    FILTER (\i. ~is_param_opcode i.inst_opcode) l = phis ++ body /\
    LENGTH phis = phi_prefix_length l /\ MEM inst phis ==>
    MEM inst l /\ inst.inst_opcode = PHI
Proof
  Induct >> simp[phi_prefix_length_def] >> rpt gen_tac >>
  reverse (Cases_on `h.inst_opcode = PHI`) >> simp[] >> strip_tac
  >- gvs[] >>
  `~is_param_opcode h.inst_opcode` by simp[is_param_opcode_def] >>
  Cases_on `phis` >> gvs[] >>
  Cases_on `inst = h` >> gvs[] >> metis_tac[]
QED

(* fn_cfg_edge is cfg_analyze's predecessor relation. *)
Theorem fn_cfg_edge_cfg_preds:
  !fn p l.
    wf_function fn ==>
    (fn_cfg_edge fn p l <=> MEM p (cfg_preds_of (cfg_analyze fn) l))
Proof
  rw[fn_cfg_edge_def, GSYM cfg_edge_symmetry_uncond] >> eq_tac >> strip_tac
  >- (drule_all cfg_analyze_preserves_bb_succs >> strip_tac >> gvs[]) >>
  `MEM p (fn_labels fn)` by
    metis_tac[cfg_analyze_pred_labels, cfg_edge_symmetry_uncond] >>
  gvs[fn_labels_def, MEM_MAP] >>
  rename1 `MEM bb' fn.fn_blocks` >> qexists_tac `bb'` >>
  drule_all cfg_analyze_preserves_bb_succs >> strip_tac >> gvs[]
QED

Theorem phi_well_formed_pairs:
  !ops.
    phi_well_formed ops ==>
    ops = FLAT (MAP (\(l,v). [Label l; Var v]) (phi_pairs ops))
Proof
  recInduct phi_pairs_ind >> rw[phi_well_formed_def, phi_pairs_def] >>
  gvs[phi_well_formed_def]
QED

(* In a block whose only predecessor is pred, each PHI is `phi pred, %v`
   (venomWf$phi_edge_uses_wf, from def_dominates_uses: its labels are
   distinct and exactly the CFG predecessors). *)
Theorem single_pred_phi_operands:
  !fn bb pred inst.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    cfg_preds_of (cfg_analyze fn) bb.bb_label = [pred] /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
    ?v. inst.inst_operands = [Label pred; Var v]
Proof
  rw[codegen_ready_fn_def, def_dominates_uses_def] >>
  first_x_assum drule_all >> rw[phi_edge_uses_wf_def] >>
  `!p. (?q. MEM q (phi_pairs inst.inst_operands) /\ FST q = p) <=> p = pred`
    by metis_tac[fn_cfg_edge_cfg_preds, MEM] >>
  drule phi_well_formed_pairs >> strip_tac >>
  Cases_on `phi_pairs inst.inst_operands` >- metis_tac[MEM] >>
  rename1 `_ = q :: qs` >> Cases_on `qs`
  >- (PairCases_on `q` >> gvs[] >> metis_tac[pairTheory.FST, MEM]) >>
  rename1 `_ = q :: q2 :: _` >>
  `FST q = pred /\ FST q2 = pred` by metis_tac[MEM] >>
  gvs[]
QED

(* So the operand stack_get_phi_depth finds is the one resolve_phi pred
   reads, whatever the stack. *)
Theorem single_pred_phi_hits:
  !cfg fn lbl bb pred phis body inst stk dist.
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    LENGTH (cfg_preds_of cfg bb.bb_label) = 1 /\
    MEM bb.bb_label (cfg_succs_of cfg pred) /\
    non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    MEM inst phis /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) stk =
      SOME dist ==>
    resolve_phi pred inst.inst_operands = SOME (stack_peek dist stk)
Proof
  rw[] >>
  `MEM bb fn.fn_blocks` by
    (gvs[lookup_block_def] >> drule FIND_SOME_MEM >> simp[]) >>
  `cfg_preds_of (cfg_analyze fn) bb.bb_label = [pred]` by
    (gvs[cfg_edge_symmetry_uncond] >>
     Cases_on `cfg_preds_of (cfg_analyze fn) bb.bb_label` >> gvs[] >>
     gvs[LENGTH_NIL]) >>
  `MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI` by
    (irule phi_prefix_filter_mem >> gvs[non_param_insts_def] >> metis_tac[]) >>
  drule_all single_pred_phi_operands >> strip_tac >>
  gvs[is_var_operand_def, resolve_phi_def, stack_get_phi_depth_def] >>
  `stack_get_depth (Var v) stk = SOME dist` by
    gvs[stack_get_depth_def] >>
  drule stack_get_depth_props >> simp[]
QED

(* The operand form of single_pred_phi_hits: with one predecessor a PHI's
   only variable operand is the one it selects from pred. *)
Theorem single_pred_phi_operand_hits:
  !cfg fn lbl bb pred phis body inst op.
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    LENGTH (cfg_preds_of cfg bb.bb_label) = 1 /\
    MEM bb.bb_label (cfg_succs_of cfg pred) /\
    non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    MEM inst phis /\ is_var_operand op /\ MEM op inst.inst_operands ==>
    resolve_phi pred inst.inst_operands = SOME op
Proof
  rw[] >>
  `MEM bb fn.fn_blocks` by
    (gvs[lookup_block_def] >> drule FIND_SOME_MEM >> simp[]) >>
  `cfg_preds_of (cfg_analyze fn) bb.bb_label = [pred]` by
    (gvs[cfg_edge_symmetry_uncond] >>
     Cases_on `cfg_preds_of (cfg_analyze fn) bb.bb_label` >> gvs[] >>
     gvs[LENGTH_NIL]) >>
  `MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI` by
    (irule phi_prefix_filter_mem >> gvs[non_param_insts_def] >> metis_tac[]) >>
  drule_all single_pred_phi_operands >> strip_tac >>
  Cases_on `op` >> gvs[is_var_operand_def, resolve_phi_def]
QED


(* Used at the start of a non-entry block whose only predecessor is pred
   (so generate_block_plan runs clean_stack_plan before its instructions).
   As in phi_prefix_frame_sim, ps is the lineage entry state from pred with
   the cleanup fields lineage_state_block_plan chose, and the PHI prefix is
   stated whole because the Venom side has no state between two PHIs.  The
   well-formedness premise allows repeated dead_stack_marker slots, which
   earlier cleanup elisions on the path leave; it and the premise that no
   slot stands for one of bb's own outputs (which the PHIs would rebind)
   come from fnLineageStatic$lineage_state_static.

   Why it should hold: the cleanup only pops dead variables (popmany_plan,
   by swaps, with spills when deeper than 16) or marks retained ones dead
   (mark_dead_stack, no code), so the stack values the invariant relates
   are unchanged; the PHIs then run as in phi_prefix_frame_sim, with the
   value resolve_phi pred reads already on the stack. *)
Theorem single_pred_prefix_frame_sim:
  !ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb
   pred ps_l h promised ps base vs as s_phi clean_ops ps2 phis body ops ps3
   r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\
    LENGTH (cfg_preds_of cfg bb.bb_label) = 1 /\
    vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    ps = ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |> /\
    generated_plan_state_wf_marked base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) (clean_ops ++ ops) \/
           MEM (SORestore off) (clean_ops ++ ops) ==>
           off < dimword (:256)) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    clean_stack_plan liveness cfg fn bb ps = (clean_ops, ps2) /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (phis ++ body) ps2 = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp (clean_ops ++ ops))
    ==>
    ?phi_ops ps1 body_ops n as'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (LENGTH phis) (phis ++ body) ps2 =
        SOME (phi_ops, ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (LENGTH phis) body ps1 =
        SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc +
        LENGTH (execute_plan cp.cp_initial_fmp (clean_ops ++ phi_ops)) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := LENGTH phis) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at))
Proof
  rpt strip_tac >>
  `MEM bb.bb_label (cfg_succs_of cfg pred)` by
    (qpat_x_assum `lineage_entry _ _ _ _ _ _ _ _` mp_tac >>
     simp[lineage_entry_def] >> strip_tac) >>
  `ps2.ps_alloc.sa_spill_base = ps3.ps_alloc.sa_spill_base /\
   ps2.ps_alloc.sa_next_offset <= ps3.ps_alloc.sa_next_offset` by
    (drule generate_block_insts_plan_spill_base >>
     drule generate_block_insts_plan_next_offset >> simp[]) >>
  qpat_x_assum `asm_block_at _ _ _`
    (strip_assume_tac o REWRITE_RULE [execute_plan_append, asm_block_at_append]) >>
  `r.sr_spill_base <= ps2.ps_alloc.sa_spill_base /\
   ps2.ps_alloc.sa_next_offset <= r.sr_spill_end` by simp[] >>
  `!off. MEM (SOSpill off) clean_ops \/ MEM (SORestore off) clean_ops ==>
         off < dimword (:256)` by
    (rpt strip_tac >> qpat_x_assum `!off. _ ==> off < dimword (:256)` irule >>
     simp[]) >>
  `!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==>
         off < dimword (:256)` by
    (rpt strip_tac >> qpat_x_assum `!off. MEM _ (_ ++ _) \/ _ ==> _` irule >>
     simp[]) >>
  drule_all clean_stack_plan_frame_sim >> strip_tac >>
  `!inst op. MEM inst phis /\ is_var_operand op /\ MEM op inst.inst_operands /\
     MEM op ps2.ps_stack ==>
     resolve_phi pred inst.inst_operands = SOME op` by
    (rpt strip_tac >> drule_all single_pred_phi_operand_hits >> simp[]) >>
  `normalize_operand dfg [] dead_stack_marker = dead_stack_marker` by
    simp[dead_stack_marker_def, normalize_operand_def] >>
  `!op v. (MEM op ps2.ps_stack \/ op IN FDOM ps2.ps_spilled) /\
     ~(MEM op ps2.ps_stack /\
       ?inst. MEM inst (collect_phis bb.bb_instructions) /\
              resolve_phi pred inst.inst_operands = SOME op) /\
     (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
     ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by
    metis_tac[operand_distinct, dead_stack_marker_def] >>
  `!at. MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled ==>
     operand_val (frame_view fn ra vs) lo at =
     operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)` by
    metis_tac[] >>
  qpat_x_assum `asm_block_at _ (_ + _) _` mp_tac >>
  qpat_x_assum `as2.as_pc = _` (fn th => SUBST1_TAC (SYM th) >> assume_tac th) >>
  strip_tac >>
  drule_all phi_prefix_hits_frame_sim >> strip_tac >>
  qpat_x_assum `asm_steps _ _ _ n as = _`
    (assume_tac o Q.SPEC `n'` o MATCH_MP asm_steps_add_ok) >>
  qexistsl_tac [`phi_ops`, `ps1`, `body_ops`, `n + n'`, `as'`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  gvs[execute_plan_append]
QED
