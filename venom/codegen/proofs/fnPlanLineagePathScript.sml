Theory fnPlanLineagePath
Ancestors
  fnPlanLineagePhiActivation fnPlanLineageLiveness fnPlanLineageDemandSupport stackPlanGen livenessDefs
  livenessAnalysisProps cfgAnalysisProps removeUnusedProofs
  removeUnusedSsaProofs codegenReadyCompute venomWfProps

Theorem analyzed_ready_live_through_edge:
  !fn lbl bb pred pred_bb v.
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ bb.bb_label = lbl /\
  phi_block_ready (liveness_analyze fn) bb /\
  EVERY (\inst. ~MEM v (inst_defs inst)) bb.bb_instructions /\
  MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)) /\
  cfg_reachable_of (cfg_analyze fn) pred /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) ==>
  MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pred_bb.bb_instructions))
Proof
  rpt gen_tac >> strip_tac >>
  qspec_then `bb.bb_instructions` strip_assume_tac collect_phis_prefix >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions` by
    (qpat_assum `bb.bb_instructions = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH (collect_phis bb.bb_instructions)))` by
    (drule livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
     disch_then (qspecl_then [`lbl`, `bb`, `LENGTH (collect_phis bb.bb_instructions)`,
       `LENGTH bb.bb_instructions`, `v`] mp_tac) >>
     gvs[listTheory.EVERY_EL] >> metis_tac[]) >>
  `EVERY (\inst. ~MEM v (inst_defs inst)) (collect_phis bb.bb_instructions)` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[livenessTransferProofsTheory.collect_phis_mem]) >>
  drule_all analyzed_ready_phi_live_through_edge >>
  disch_then (qspec_then `pred` assume_tac) >>
  drule_all analyzed_live_out_edge_subset >>
  simp[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

(* Symbolic producer ledger (C3.2.2.21):
   - reachable_phi_incoming_live_out supplies the actual predecessor seed.
   - analyzed_ready_live_through_edge above transports an exit seed through
     a ready block with no definition of v, without any incoming-use seed.
   - Existing native path bridge: dominates_path_no_revisit in
     venom/passes/remove_unused/proofs/removeUnusedProofsScript.sml
     (lines 1734-1752) already proves, under wf_function fn and
     fn_dominates fn d p, existence of a native path d::tail ending at p
     with ~MEM d tail. It uses local rtc_to_is_fn_path,
     last_occurrence_split and is_fn_path_suffix. Do not duplicate it.
     Exported at its single definition site for reuse here, along with
     ssa_unique_var_defined_at; their proof dependencies stay local.
     The remaining strengthened interface must additionally supply vertex
     reachability, lookup witnesses and analyzed-CFG edge membership.
     Empty tail covers d=p.
   - SSA must identify the available definition with the prefix definition,
     and rule out v definitions in all tail blocks and after its head PHIs.
     Then induction on the path applies the edge boundary; at the head only
     propagate to LENGTH collect_phis, never across the defining PHI.
   - fn_cfg_edge must be converted to analyzed cfg_succs membership, with
     reachability/lookup facts for each path vertex. Existing remove-unused
     live_backward_along_path is not reusable: its remove_unused_phi_vars
     exclusion is precisely the incoming-alias situation at issue.
   These are explicit remaining symbolic proof obligations, not premises
   added to the frozen theorem or an assertion of global alias exclusion.
*)

Theorem dominates_analyzed_path_no_revisit:
  !fn d p.
    wf_function fn /\ fn_dominates fn d p ==>
    ?tail. is_fn_path fn (d::tail) /\ LAST (d::tail) = p /\
      ~MEM d tail /\
      EVERY (\lbl. fn_reachable fn lbl /\
        cfg_reachable_of (cfg_analyze fn) lbl /\
        MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
        ?bb. lookup_block lbl fn.fn_blocks = SOME bb) (d::tail)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dominates_path_no_revisit >> strip_tac >>
  qexists_tac `path` >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  `fn_reachable fn d` by
    metis_tac[fn_dominates_dom_reachable_compute] >>
  rewrite_tac[listTheory.EVERY_MEM] >> qx_gen_tac `lbl` >> strip_tac >>
  `fn_reachable fn lbl` by
    (irule is_fn_path_all_reachable >>
     qexists_tac `d::path` >> simp[]) >>
  `cfg_reachable_of (cfg_analyze fn) lbl` by
    metis_tac[fn_reachable_cfg_analyze] >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  metis_tac[fn_reachable_has_block]
QED

Theorem ssa_output_position_unique:
  !fn d bb j v lbl bb' k.
    ssa_form fn /\
    lookup_block d fn.fn_blocks = SOME bb /\
    j < LENGTH bb.bb_instructions /\
    MEM v (EL j bb.bb_instructions).inst_outputs /\
    lookup_block lbl fn.fn_blocks = SOME bb' /\
    k < LENGTH bb'.bb_instructions /\
    MEM v (EL k bb'.bb_instructions).inst_outputs ==>
    lbl = d /\ k = j
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks /\ MEM bb' fn.fn_blocks /\
   bb.bb_label = d /\ bb'.bb_label = lbl` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
              venomExecPropsTheory.lookup_block_label] >>
  metis_tac[ssa_form_position]
QED

Theorem ssa_phi_prefix_unique_definition:
  !fn d bb j v lbl bb' k.
    ssa_form fn /\
    lookup_block d fn.fn_blocks = SOME bb /\
    j < LENGTH (collect_phis bb.bb_instructions) /\
    MEM v (EL j (collect_phis bb.bb_instructions)).inst_outputs /\
    lookup_block lbl fn.fn_blocks = SOME bb' /\
    k < LENGTH bb'.bb_instructions /\
    MEM v (EL k bb'.bb_instructions).inst_outputs ==>
    lbl = d /\ k = j
Proof
  rpt gen_tac >> strip_tac >>
  qspec_then `bb.bb_instructions` strip_assume_tac collect_phis_prefix >>
  `j < LENGTH bb.bb_instructions` by
    (qpat_assum `bb.bb_instructions = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  `EL j bb.bb_instructions = EL j (collect_phis bb.bb_instructions)` by
    (qpat_assum `bb.bb_instructions = _`
       (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     simp[listTheory.EL_APPEND_EQN]) >>
  `MEM v (EL j bb.bb_instructions).inst_outputs` by simp[] >>
  metis_tac[ssa_output_position_unique]
QED

Theorem ssa_phi_prefix_other_block_no_defs:
  !fn d bb j v lbl bb'.
    ssa_form fn /\
    lookup_block d fn.fn_blocks = SOME bb /\
    j < LENGTH (collect_phis bb.bb_instructions) /\
    MEM v (EL j (collect_phis bb.bb_instructions)).inst_outputs /\
    lookup_block lbl fn.fn_blocks = SOME bb' /\ lbl <> d ==>
    EVERY (\inst. ~MEM v (inst_defs inst)) bb'.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  simp[listTheory.EVERY_EL, venomInstTheory.inst_defs_def] >>
  metis_tac[ssa_phi_prefix_unique_definition]
QED

Theorem ssa_phi_prefix_tail_no_defs:
  !fn d bb j v k.
    ssa_form fn /\
    lookup_block d fn.fn_blocks = SOME bb /\
    j < LENGTH (collect_phis bb.bb_instructions) /\
    MEM v (EL j (collect_phis bb.bb_instructions)).inst_outputs /\
    LENGTH (collect_phis bb.bb_instructions) <= k /\
    k < LENGTH bb.bb_instructions ==>
    ~MEM v (inst_defs (EL k bb.bb_instructions))
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[venomInstTheory.inst_defs_def] >> strip_tac >>
  `k = j` by metis_tac[ssa_phi_prefix_unique_definition] >>
  decide_tac
QED

Theorem ssa_phi_prefix_available_dominates:
  !fn d bb j v pb.
    ssa_form fn /\
    lookup_block d fn.fn_blocks = SOME bb /\
    j < LENGTH (collect_phis bb.bb_instructions) /\
    MEM v (EL j (collect_phis bb.bb_instructions)).inst_outputs /\
    def_available_at fn pb NONE v ==>
    fn_dominates fn d pb.bb_label
Proof
  rpt gen_tac >> strip_tac >>
  gvs[venomWfTheory.def_available_at_def] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = d` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
              venomExecPropsTheory.lookup_block_label] >>
  `MEM (EL j (collect_phis bb.bb_instructions)) bb.bb_instructions` by
    metis_tac[listTheory.EL_MEM, livenessTransferProofsTheory.collect_phis_mem] >>
  `bb = def_bb` by
    metis_tac[ssa_form_position, listTheory.MEM_EL] >>
  gvs[]
QED

Theorem analyzed_live_backward_no_kill_path:
  !tail fn d head_bb end_bb v.
    wf_function fn /\ is_fn_path fn (d::tail) /\
    EVERY (\lbl. cfg_reachable_of (cfg_analyze fn) lbl /\
      MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
      ?bb. lookup_block lbl fn.fn_blocks = SOME bb) (d::tail) /\
    EVERY (\lbl. !bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
      phi_block_ready (liveness_analyze fn) bb /\
      EVERY (\inst. ~MEM v (inst_defs inst)) bb.bb_instructions) tail /\
    lookup_block d fn.fn_blocks = SOME head_bb /\
    lookup_block (LAST (d::tail)) fn.fn_blocks = SOME end_bb /\
    MEM v (live_vars_at (liveness_analyze fn) (LAST (d::tail))
      (LENGTH end_bb.bb_instructions)) ==>
    MEM v (live_vars_at (liveness_analyze fn) d (LENGTH head_bb.bb_instructions))
Proof
  Induct_on `tail` >- (simp[] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  gvs[listTheory.EVERY_DEF] >>
  `fn_cfg_edge fn d h /\ is_fn_path fn (h::tail)` by
    gvs[venomWfTheory.is_fn_path_def] >>
  `MEM v (live_vars_at (liveness_analyze fn) h (LENGTH bb.bb_instructions))` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `bb.bb_label = h` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `MEM h (cfg_succs_of (cfg_analyze fn) d)` by
    metis_tac[fn_cfg_edge_cfg_analyze] >>
  irule analyzed_ready_live_through_edge >> simp[] >>
  qexists_tac `bb` >> simp[]
QED

Theorem analyzed_live_out_to_post_phis:
  !fn d bb v.
    wf_function fn /\ MEM d (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block d fn.fn_blocks = SOME bb /\
    (!k. LENGTH (collect_phis bb.bb_instructions) <= k /\
         k < LENGTH bb.bb_instructions ==>
         ~MEM v (inst_defs (EL k bb.bb_instructions))) /\
    MEM v (live_vars_at (liveness_analyze fn) d (LENGTH bb.bb_instructions)) ==>
    MEM v (live_vars_at (liveness_analyze fn) d
      (LENGTH (collect_phis bb.bb_instructions)))
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions` by
    (qspec_then `bb.bb_instructions` strip_assume_tac collect_phis_prefix >>
     qpat_assum `bb.bb_instructions = _`
       (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  drule livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
  disch_then (qspecl_then [`d`, `bb`] mp_tac) >>
  simp[] >> disch_then irule >> simp[] >>
  qexists_tac `LENGTH bb.bb_instructions` >> simp[]
QED

Theorem analyzed_phi_output_dominance_live_out_to_post_phis:
  !fn d bb j v p pb.
    codegen_ready_fn fn /\ lookup_block d fn.fn_blocks = SOME bb /\
    j < LENGTH (collect_phis bb.bb_instructions) /\
    MEM v (EL j (collect_phis bb.bb_instructions)).inst_outputs /\
    fn_dominates fn d p /\ lookup_block p fn.fn_blocks = SOME pb /\
    MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions)) ==>
    MEM v (live_vars_at (liveness_analyze fn) d
      (LENGTH (collect_phis bb.bb_instructions)))
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn /\ ssa_form fn /\ phi_operands_ready fn` by
    gvs[codegen_ready_fn_def] >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `EVERY (phi_block_ready (liveness_analyze fn)) fn.fn_blocks` by
    (gvs[phi_operands_ready_def] >>
     gvs[listTheory.EVERY_MEM, combinTheory.o_DEF] >>
     Cases_on `collect_phis bb.bb_instructions` >> gvs[] >>
     qpat_x_assum `!b. MEM b fn.fn_blocks ==> NULL _`
       (qspec_then `bb` mp_tac) >> simp[]) >>
  drule_all dominates_analyzed_path_no_revisit >> strip_tac >>
  `MEM d (cfg_analyze fn).cfg_dfs_pre` by gvs[] >>
  `MEM v (live_vars_at (liveness_analyze fn) d (LENGTH bb.bb_instructions))` by
    (irule analyzed_live_backward_no_kill_path >> simp[] >>
     qexistsl_tac [`pb`, `tail`] >> simp[] >>
     reverse conj_tac >- (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
     simp[listTheory.EVERY_MEM] >> qx_gen_tac `lbl` >> strip_tac >>
     qx_gen_tac `bb'` >> strip_tac >>
     conj_tac >- metis_tac[venomExecPropsTheory.lookup_block_MEM, listTheory.EVERY_MEM] >>
     `lbl <> d` by metis_tac[] >>
     `EVERY (\inst. ~MEM v (inst_defs inst)) bb'.bb_instructions` by
       (irule ssa_phi_prefix_other_block_no_defs >> simp[] >>
        goal_assum (drule_at Any) >>
        qexistsl_tac [`bb`, `fn`, `j`] >> simp[]) >>
     gvs[listTheory.EVERY_MEM]) >>
  irule analyzed_live_out_to_post_phis >> simp[] >>
  metis_tac[ssa_phi_prefix_tail_no_defs]
QED

Theorem reachable_phi_prefix_no_output_use_alias:
  !fn entry lbl bb out_phi in_phi v.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    fn_reachable fn lbl /\ lbl <> entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM out_phi (collect_phis bb.bb_instructions) /\
    MEM v out_phi.inst_outputs /\
    MEM in_phi (collect_phis bb.bb_instructions) ==>
    ~MEM v (inst_uses in_phi)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  `wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\ phi_operands_ready fn` by
    gvs[codegen_ready_fn_def] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
              venomExecPropsTheory.lookup_block_label] >>
  `MEM in_phi bb.bb_instructions /\ in_phi.inst_opcode = PHI` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  `venomWf$phi_edge_uses_wf fn bb in_phi` by
    (gvs[venomWfTheory.def_dominates_uses_def] >> metis_tac[]) >>
  `?pred. MEM (pred,v) (phi_pairs in_phi.inst_operands)` by
    (irule venomWfTheory.phi_well_formed_var_pair >>
     gvs[venomWfTheory.phi_edge_uses_wf_def, venomInstTheory.inst_uses_def,
         passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `?j. j < LENGTH (collect_phis bb.bb_instructions) /\
    EL j (collect_phis bb.bb_instructions) = out_phi` by
    metis_tac[listTheory.MEM_EL] >>
  `?i. i < LENGTH (collect_phis bb.bb_instructions) /\
    EL i (collect_phis bb.bb_instructions) = in_phi` by
    metis_tac[listTheory.MEM_EL] >>
  `ALL_DISTINCT (MAP FST (phi_pairs in_phi.inst_operands)) /\
   ?pb. MEM pb fn.fn_blocks /\ pb.bb_label = pred /\
     fn_cfg_edge fn pred lbl /\ def_available_at fn pb NONE v` by
    (gvs[venomWfTheory.phi_edge_uses_wf_def] >> metis_tac[]) >>
  `lookup_block pred fn.fn_blocks = SOME pb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]) >>
  `fn_dominates fn lbl pred` by
    (`fn_dominates fn lbl pb.bb_label` suffices_by simp[] >>
     irule ssa_phi_prefix_available_dominates >>
     goal_assum (drule_at Any) >> simp[] >> qexists_tac `j` >> simp[] >>
     qexists_tac `v` >> simp[]) >>
  `FIND (\(l,w). l = pred) (phi_pairs in_phi.inst_operands) = SOME (pred,v)` by
    (qspec_then `FST : string # string -> string`
      (qspecl_then [`phi_pairs in_phi.inst_operands`, `(pred,v)`] mp_tac)
      fnPlanLineagePhiMapsTheory.distinct_key_FIND_member >> simp[] >>
     simp[pairTheory.LAMBDA_PROD]) >>
  `cfg_reachable_of (cfg_analyze fn) pred` by
    (gvs[venomWfTheory.fn_dominates_def] >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  `MEM lbl (cfg_succs_of (cfg_analyze fn) pred)` by
    metis_tac[fn_cfg_edge_cfg_analyze] >>
  `MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))` by
    (irule reachable_phi_incoming_live_out >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`bb`, `i`, `lbl`] >> simp[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl
     (LENGTH (collect_phis bb.bb_instructions)))` by
    (irule analyzed_phi_output_dominance_live_out_to_post_phis >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac >- (qexists_tac `j` >> simp[]) >>
     qexistsl_tac [`pred`, `pb`] >> simp[]) >>
  gvs[phi_operands_ready_def, phi_block_ready_def, listTheory.EVERY_MEM,
      combinTheory.o_DEF]
  >- (qpat_x_assum `!b. MEM b fn.fn_blocks ==> NULL _`
        (qspec_then `bb` mp_tac) >> simp[listTheory.NULL_EQ] >>
      metis_tac[listTheory.MEM]) >>
  qpat_x_assum `!e. MEM e fn.fn_blocks ==> _`
    (qspec_then `bb` mp_tac) >> simp[] >> metis_tac[]
QED

(* Position-local SSA exclusion, not a claim about a replay residual prefix. *)
Theorem current_output_not_demand_available:
  !fn bb i v.
    ssa_form fn /\ MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
    MEM v (EL i bb.bb_instructions).inst_outputs ==>
    ~demand_available fn bb i v
Proof
  rpt strip_tac >> gvs[demand_available_def] >>
  `?j. j < LENGTH db.bb_instructions /\ EL j db.bb_instructions = di` by
    metis_tac[listTheory.MEM_EL] >>
  `db = bb /\ j = i` by metis_tac[ssa_form_position] >>
  gvs[] >>
  `k < LENGTH bb.bb_instructions` by decide_tac >>
  `k = i` by metis_tac[ssa_form_position] >> decide_tac
QED

(* Native premise audit (C3.3.native_premise_audit).
 *
 * Checked above: ssa_form alone excludes a current output from
 * demand_available fn bb i. This is static position exclusion, not freshness
 * in an arbitrary residual prefix on a loop revisit.
 *
 * Missing public-query producer (not assumed here): for a ready function,
 * reachable member block bb, i <= LENGTH bb.bb_instructions and a PHI-free
 * DROP i bb.bb_instructions, prove
 *   EVERY (demand_available fn bb i)
 *     (live_vars_at (liveness_analyze fn) bb.bb_label i).
 * projected_demand_ordinary_suffix currently proves this only for
 *   df_at [] (liveness_block fn.fn_blocks (cfg_analyze fn) bb.bb_label
 *              (liveness_recompute fn)) bb.bb_label i.
 * livenessConvergenceProofs.liveness_recompute_convergence identifies only
 * endpoint SETS: same_vars (df_at [] (liveness_recompute fn) lbl
 * (LENGTH (liveness_instrs fn.fn_blocks lbl)))
 * (liveness_out fn.fn_blocks (cfg_analyze fn) lbl (liveness_recompute fn)).
 * It does not directly identify all interior queries. A position-wise
 * same_vars bridge would suffice, or a direct backward proof using public
 * live_vars_at_transfer, endpoint convergence and projected_demand_live_out.
 *
 * Actual regular callers: stackPlanGen.generate_block_insts_plan supplies
 * next_live at i+n_params+1 (or block_len for the last instruction), with
 * n_params = LENGTH (get_params bb.bb_instructions), and a suffix from
 * non_param_insts bb. Position alignment still needs a wf/parameter-prefix
 * producer. Readiness gives the <=16 bound and operand marker exclusion;
 * compute_operands branches through get_non_label_operands, TL for LOG,
 * or python_stack_operands. Its variable-support-in-inst_uses bridge must
 * be supplied before applying public liveness transfer. Distinct outputs
 * already have genBlockSim.codegen_ready_inst_outputs_distinct; do not copy
 * that theorem into a planner leaf merely to avoid its heavy imports.
 *
 * Native upper support is a separate missing producer: marker-free core
 * and spilled variables must be supported by the appropriate demand/live
 * set. Only then does current_output_not_demand_available yield dynamic
 * core/spill freshness. residual_budget_wf alone does not supply support.
 * Native_regular_live_inventory also needs support bounded by current
 * operand variables UNION next-live; transfer is needed to supply this.
 *
 * IMPORTANT: halting is bb_is_halting bb for EVERY instruction in the
 * block, not just the terminator. generate_regular_inst_plan retains a
 * dead singleton output whenever that flag is true. Thus the premise
 * (~halting \/ LENGTH outputs > 1 \/ EVERY (MEM-in-nl) outputs) is not
 * supplied by the caller, even at interior positions. Terminal-only weaker
 * endpoints alone do not address dead outputs of earlier instructions in
 * a halting block. A future producer must account for these retained dead
 * names (or show they are impossible from the actual source contract);
 * do not silently assert exact live inventory at those intermediate states.
 * This is not a counterexample to lineage_state_block_plan.
 *
 * Consumers checked: fnBlockPlanStatic.block_plan_state_static requests
 * generated_plan_state_wf_marked and output absence at k < block length,
 * including in halting blocks. fnLineageStatic.lineage_state_static requests
 * it at block entry. fnPlanPrefix's predicate is structural (distinct
 * non-markers, disjoint spill domain, allocator bounds), not exact liveness.
 * Therefore structural resources can remain useful for retained dead
 * outputs, but the exact-live upper invariant needs redesign/qualification
 * before global instruction induction. No frozen theorem/definition changed.
 *)

Theorem definition_support_output_fresh:
  !fn bb i ps.
    ssa_form fn /\ MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      demand_available fn bb i v) ==>
    EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
      (EL i bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >> simp[listTheory.EVERY_MEM] >>
  metis_tac[current_output_not_demand_available]
QED
