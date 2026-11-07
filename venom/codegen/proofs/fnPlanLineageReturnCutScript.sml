Theory fnPlanLineageReturnCut
Ancestors
  fnPlanLineagePath fnPlanLineageCallers fnPlanLineageEdge venomWf
  fnPlanLineageDemand

(* Exact copy of the local rtc_to_fn_path in removeUnusedSsaProofs.
   Its local status prevents importing the fact through the existing ancestor. *)
Theorem rtc_to_fn_path:
  !fn x y. (fn_cfg_edge fn)^* x y ==>
    ?path. is_fn_path fn path /\ path <> [] /\ HD path = x /\ LAST path = y
Proof
  gen_tac >> ho_match_mp_tac relationTheory.RTC_INDUCT >> rw[]
  >- (qexists_tac `[x]` >> simp[is_fn_path_def])
  >- (qexists_tac `x::path` >> Cases_on `path` >> gvs[is_fn_path_def])
QED

Theorem fn_path_cut:
  !pre fn x suf.
    is_fn_path fn (pre ++ x::suf) ==>
    is_fn_path fn (pre ++ [x]) /\ is_fn_path fn (x::suf) /\
    (pre <> [] ==> fn_cfg_edge fn (LAST pre) x)
Proof
  Induct >> simp[is_fn_path_def] >>
  rpt gen_tac >> Cases_on `pre` >> gvs[is_fn_path_def] >>
  metis_tac[]
QED

Theorem first_intersection_split:
  !xs ys. (?x. MEM x xs /\ MEM x ys) ==>
    ?pre j post. xs = pre ++ j::post /\ MEM j ys /\
      EVERY (\x. ~MEM x ys) pre
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `MEM h ys`
  >- (qexistsl_tac [`[]`, `h`, `xs`] >> simp[]) >>
  gvs[] >>
  first_x_assum (qspec_then `ys` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  qexistsl_tac [`h::pre`, `j`, `post`] >> simp[]
QED

Theorem fn_walk_predecessor:
  !tail d j. MEM j tail ==>
    ?pre a post. d::tail = pre ++ a::j::post /\ MEM a (d::tail)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `j = h`
  >- (gvs[] >> qexistsl_tac [`[]`, `d`, `tail`] >> simp[]) >>
  `MEM j tail` by gvs[] >>
  first_x_assum (qspecl_then [`h`, `j`] mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`d::pre`, `a`, `post`] >> simp[]
QED

Theorem fn_return_intersection:
  !fn entry d tail.
    RTC (fn_cfg_edge fn) entry d /\ tail <> [] /\
    is_fn_path fn (d::tail) /\ LAST tail = d /\
    (!a. ~fn_cfg_edge fn a entry) ==>
    ?before a j after b path.
      d::tail = before ++ a::j::after /\
      fn_cfg_edge fn a j /\ fn_cfg_edge fn b j /\ a <> b /\
      is_fn_path fn path /\ path <> [] /\ HD path = entry /\ LAST path = j /\
      (j = d \/ ~MEM d path)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM d tail` by metis_tac[rich_listTheory.MEM_LAST_NOT_NIL] >>
  `!j. MEM j tail ==> ?a. fn_cfg_edge fn a j` by
    (rpt strip_tac >> drule fn_walk_predecessor >>
     disch_then (qspec_then `d` strip_assume_tac) >>
     `is_fn_path fn (pre ++ a::j::post)` by metis_tac[] >>
     drule fn_path_cut >> simp[is_fn_path_def] >> metis_tac[]) >>
  `~MEM entry tail` by metis_tac[] >>
  drule rtc_to_fn_path >> strip_tac >>
  `?x. MEM x path /\ MEM x tail` by
    (qexists_tac `d` >> metis_tac[rich_listTheory.MEM_LAST_NOT_NIL]) >>
  qspecl_then [`path`, `tail`] mp_tac first_intersection_split >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `pre <> []` by (Cases_on `pre` >> gvs[]) >>
  `is_fn_path fn (pre ++ [j]) /\ fn_cfg_edge fn (LAST pre) j` by
    (metis_tac[fn_path_cut]) >>
  `~MEM (LAST pre) tail` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[rich_listTheory.MEM_LAST_NOT_NIL]) >>
  drule fn_walk_predecessor >>
  disch_then (qspec_then `d` strip_assume_tac) >>
  `is_fn_path fn (pre' ++ a::j::post')` by metis_tac[] >>
  `fn_cfg_edge fn a j` by
    (drule fn_path_cut >> simp[is_fn_path_def]) >>
  qexistsl_tac [`pre'`, `a`, `j`, `post'`, `LAST pre`, `pre ++ [j]`] >>
  simp[] >>
  conj_tac >- metis_tac[listTheory.MEM] >>
  conj_tac >- (Cases_on `pre` >> gvs[]) >>
  Cases_on `j = d` >> gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem ready_entry_no_incoming:
  !fn entry.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry ==>
    !a. ~fn_cfg_edge fn a entry
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[stackPlanGenTheory.codegen_ready_fn_def] >>
  `cfg_preds_of (cfg_analyze fn) entry = []` by
    (Cases_on `fn.fn_blocks` >>
     gvs[venomInstTheory.fn_entry_label_def,
         stackPlanGenTheory.codegen_ready_fn_def,
         stackPlanGenTheory.block_entries_ready_def,
         venomInstTheory.entry_block_def, listTheory.NULL_EQ]) >>
  metis_tac[codegenReadyComputeTheory.fn_cfg_edge_cfg_analyze,
            cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond, listTheory.MEM]
QED

Theorem first_return_join_cut:
  !fn d tail.
    codegen_ready_fn fn /\ fn_reachable fn d /\ tail <> [] /\
    is_fn_path fn (d::tail) /\ LAST tail = d /\ ~MEM d (FRONT tail) ==>
    ?before a j after.
      d::tail = before ++ a::j::after /\
      1 < LENGTH (cfg_preds_of (cfg_analyze fn) j) /\
      (j = d \/ ~fn_dominates fn d j)
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[stackPlanGenTheory.codegen_ready_fn_def] >>
  qpat_x_assum `fn_reachable fn d` mp_tac >>
  rewrite_tac[fn_reachable_def] >> strip_tac >>
  drule_all ready_entry_no_incoming >> strip_tac >>
  drule_all fn_return_intersection >> strip_tac >>
  `MEM a (cfg_preds_of (cfg_analyze fn) j) /\
   MEM b (cfg_preds_of (cfg_analyze fn) j)` by
    metis_tac[codegenReadyComputeTheory.fn_cfg_edge_cfg_analyze,
              cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  `1 < LENGTH (cfg_preds_of (cfg_analyze fn) j)` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) j` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  qexistsl_tac [`before`, `a`, `j`, `after`] >> simp[] >>
  Cases_on `j = d` >> gvs[fn_dominates_def] >> metis_tac[]
QED

Theorem first_return_jmp_join_cut:
  !fn d tail.
    codegen_ready_fn fn /\ fn_reachable fn d /\ tail <> [] /\
    is_fn_path fn (d::tail) /\ LAST tail = d /\ ~MEM d (FRONT tail) ==>
    ?before a j after pa jb.
      d::tail = before ++ a::j::after /\
      1 < LENGTH (cfg_preds_of (cfg_analyze fn) j) /\
      (j = d \/ ~fn_dominates fn d j) /\
      fn_reachable fn a /\ fn_reachable fn j /\
      lookup_block a fn.fn_blocks = SOME pa /\
      lookup_block j fn.fn_blocks = SOME jb /\
      MEM j (cfg_succs_of (cfg_analyze fn) a) /\
      pa.bb_instructions <> [] /\
      (LAST pa.bb_instructions).inst_opcode = JMP
Proof
  rpt gen_tac >> strip_tac >>
  drule_all first_return_join_cut >> strip_tac >>
  `wf_function fn` by gvs[stackPlanGenTheory.codegen_ready_fn_def] >>
  `fn_reachable fn a /\ fn_reachable fn j` by
    (conj_tac >> irule removeUnusedSsaProofsTheory.is_fn_path_all_reachable >>
     qexists_tac `d::tail` >>
     simp[] >> metis_tac[listTheory.MEM_APPEND, listTheory.MEM]) >>
  `?pa. lookup_block a fn.fn_blocks = SOME pa` by
    metis_tac[removeUnusedSsaProofsTheory.fn_reachable_has_block] >>
  `?jb. lookup_block j fn.fn_blocks = SOME jb` by
    metis_tac[removeUnusedSsaProofsTheory.fn_reachable_has_block] >>
  `fn_cfg_edge fn a j` by
    (qpat_x_assum `is_fn_path fn (d::tail)` mp_tac >>
     qpat_x_assum `d::tail = _` SUBST1_TAC >>
     disch_tac >> drule fn_path_cut >> simp[is_fn_path_def]) >>
  `MEM j (cfg_succs_of (cfg_analyze fn) a)` by
    metis_tac[codegenReadyComputeTheory.fn_cfg_edge_cfg_analyze] >>
  drule_all ready_join_edge_terminator >> strip_tac >>
  qexistsl_tac [`before`, `a`, `j`, `after`, `pa`, `jb`] >> simp[]
QED

(* The prefix-order condition is the PHI clause of bb_well_formed. *)
Theorem ordered_phis_ordinary_suffix:
  !insts.
    (!i j. i < j /\ j < LENGTH insts /\
      (EL j insts).inst_opcode = PHI ==> (EL i insts).inst_opcode = PHI) ==>
    EVERY (\inst. inst.inst_opcode <> PHI)
      (DROP (LENGTH (collect_phis insts)) insts)
Proof
  Induct >- simp[livenessDefsTheory.collect_phis_def] >>
  rpt strip_tac >> Cases_on `h.inst_opcode = PHI`
  >- (simp[livenessDefsTheory.collect_phis_def] >> first_x_assum irule >>
      rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
  simp[livenessDefsTheory.collect_phis_def, listTheory.EVERY_EL] >>
  rpt strip_tac >> Cases_on `n` >> gvs[] >>
  first_x_assum (qspecl_then [`0`, `SUC n'`] mp_tac) >> simp[]
QED

Theorem ordinary_output_post_phi_demand_exclusion:
  !fn d db k v j jb.
    codegen_ready_fn fn /\ lookup_block d fn.fn_blocks = SOME db /\
    k < LENGTH db.bb_instructions /\
    LENGTH (collect_phis db.bb_instructions) <= k /\
    MEM v (EL k db.bb_instructions).inst_outputs /\
    lookup_block j fn.fn_blocks = SOME jb /\ fn_reachable fn j /\
    (j = d \/ ~fn_dominates fn d j) ==>
    ~MEM v (live_vars_at (liveness_analyze fn) j
      (LENGTH (collect_phis jb.bb_instructions)))
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn /\ ssa_form fn` by gvs[stackPlanGenTheory.codegen_ready_fn_def] >>
  `MEM jb fn.fn_blocks /\ jb.bb_label = j` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
              venomExecPropsTheory.lookup_block_label] >>
  `EVERY (\inst. inst.inst_opcode <> PHI)
      (DROP (LENGTH (collect_phis jb.bb_instructions)) jb.bb_instructions)` by
    (irule ordered_phis_ordinary_suffix >>
     fs[wf_function_def, bb_well_formed_def] >> metis_tac[]) >>
  `LENGTH (collect_phis jb.bb_instructions) <= LENGTH jb.bb_instructions` by
    (qspec_then `jb.bb_instructions` strip_assume_tac
       fnPlanLineageLivenessTheory.collect_phis_prefix >>
     qpat_x_assum `jb.bb_instructions = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  `EVERY (demand_available fn jb (LENGTH (collect_phis jb.bb_instructions)))
    (live_vars_at (liveness_analyze fn) j (LENGTH (collect_phis jb.bb_instructions)))` by
    (qpat_assum `jb.bb_label = j` (fn th => rewrite_tac[GSYM th]) >>
     irule analyzed_ordinary_suffix_demand >> fs[]) >>
  strip_tac >>
  `demand_available fn jb (LENGTH (collect_phis jb.bb_instructions)) v` by
    metis_tac[listTheory.EVERY_MEM] >>
  `MEM db fn.fn_blocks /\ db.bb_label = d` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
              venomExecPropsTheory.lookup_block_label] >>
  gvs[fnPlanLineageDemandSupportTheory.demand_available_def] >>
  `?q. q < LENGTH db'.bb_instructions /\ EL q db'.bb_instructions = di` by
    metis_tac[listTheory.MEM_EL] >>
  `db' = db /\ q = k` by metis_tac[removeUnusedProofsTheory.ssa_form_position] >>
  gvs[] >>
  `k' < LENGTH db.bb_instructions` by decide_tac >>
  `k' = k` by metis_tac[removeUnusedProofsTheory.ssa_form_position] >> decide_tac
QED

(* Static reset boundary only: incoming PHI demands and physical resources
   are deliberately not asserted to vanish at this cut. *)
Theorem first_return_jmp_join_demand_cut:
  !fn d tail db k v.
    codegen_ready_fn fn /\ fn_reachable fn d /\ tail <> [] /\
    is_fn_path fn (d::tail) /\ LAST tail = d /\ ~MEM d (FRONT tail) /\
    lookup_block d fn.fn_blocks = SOME db /\
    k < LENGTH db.bb_instructions /\
    LENGTH (collect_phis db.bb_instructions) <= k /\
    MEM v (EL k db.bb_instructions).inst_outputs ==>
    ?before a j after pa jb.
      d::tail = before ++ a::j::after /\
      1 < LENGTH (cfg_preds_of (cfg_analyze fn) j) /\
      (j = d \/ ~fn_dominates fn d j) /\
      fn_reachable fn a /\ fn_reachable fn j /\
      lookup_block a fn.fn_blocks = SOME pa /\
      lookup_block j fn.fn_blocks = SOME jb /\
      MEM j (cfg_succs_of (cfg_analyze fn) a) /\
      pa.bb_instructions <> [] /\
      (LAST pa.bb_instructions).inst_opcode = JMP /\
      ~MEM v (live_vars_at (liveness_analyze fn) j
        (LENGTH (collect_phis jb.bb_instructions)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all first_return_jmp_join_cut >> strip_tac >>
  `~MEM v (live_vars_at (liveness_analyze fn) j
      (LENGTH (collect_phis jb.bb_instructions)))` by
    metis_tac[ordinary_output_post_phi_demand_exclusion] >>
  qexistsl_tac [`before`, `a`, `j`, `after`, `pa`, `jb`] >> simp[]
QED

(* First-return physical audit (diagnostic; no new theorem or invariant).

   Specialization. Let d be the label of db and v an ordinary output at k,
   with k < LENGTH db.bb_instructions and LENGTH (collect_phis
   db.bb_instructions) <= k. A first return is a nonempty tail with
   is_fn_path fn (d::tail), LAST tail = d, ~MEM d (FRONT tail).
   first_return_jmp_join_demand_cut supplies a -> j on that walk, >1
   predecessors of j, an actual predecessor block pa ending in JMP, and
   ~MEM v (live_vars_at (liveness_analyze fn) j nphi).
   It separates j=d from ~fn_dominates fn d j. Both cases have this same
   post-PHI *static* exclusion. Neither case has a physical conclusion.
   If the defining position is itself PHI, the ordinary-output theorem is
   inapplicable: first_return_jmp_join_cut still supplies the cut, but a
   separate PHI-result demand argument is required. Do not silently use
   ordinary_output_post_phi_demand_exclusion for that case.

   Classification at a -> j. Write om = FST (build_phi_maps a phis), where
   phis = collect_phis jb.bb_instructions. These are comment abbreviations.
   - FLOOKUP om v = NONE: ready_unrenamed_phi_partition identifies entry
     membership with post-PHI demand AND absence of PHI definitions. Thus
     for this ordinary output v the cut's exclusion rules out an unrenamed
     ordinary-live target. ready_join_target_counts then makes its target
     count zero (membership implies zero count, not global distinctness).
   - FLOOKUP om v = SOME i: v is a class-i alternative. It may be the
     predecessor-selected representative, or an unselected alternative;
     non-domination of j does NOT decide which. The checked maps' selected
     count bound is <=1 in the target suffix, not in the whole stack.
     A selected alternative occurs in input_vars_from only when its class
     is emitted; an alternative not selected for a has target count zero.
   - Residual-only: in either zero-target case v may still be present below
     the target suffix. None of the cut/demand/classification results bounds
     this residual count. These cases are not physical erasure certificates.

   Native transition/premise matrix:
   row                 availability / upper / representative / exclusion
   initialized entry   EntryProduction.initialized_entry_boundary_resources
                       produces ordinary live coverage and unit upper bounds;
                       initialized_entry_jmp_residual_zero is the checked JMP
                       base. No cyclic PHI initialization is claimed.
   JMP at arbitrary a  Edge.analyzed_join_edge_spilled_empty gives empty
                       spills, and successful join suffix gives target cells.
                       EntryProduction.generate_inst_plan_jmp_live_terminal
                       gives residual-zero ONLY for next-live names, assuming
                       their preterminal stack+spill count <=1. Upper counts
                       at this arbitrary a are an UNSUPPLIED native producer.
                       Non-next-live residual v is not covered even by that
                       conditional theorem. Restore/reorder is not a filter.
   PHI at j, class i   PhiSchedule.successful_join_edge_native_phi_coverage
                       supplies class representatives in the native suffix.
                       analyzed_native_phi_schedule_classes/dead_range make
                       selected inputs dead and outputs outside input classes.
                       PhiResources.dead_phi_selected_erased needs a HIT at v,
                       whole-stack count 1, empty v spill, and output <> v.
                       The last two static/native facts are available at a
                       join, but whole-stack count and selection of THIS v
                       are not implied by target-suffix counts.
   retained PHI write  dead_phi_retained_count_balance gives the exact equation
                       count_after(w)+[w=selected]=count_before(w)+[w=result].
                       In particular, two old copies of selected v become one,
                       not zero. An old residual copy of an unselected v is
                       unchanged. This equation does not manufacture freshness.
   dead PHI result     generate_phi_plan_write_phase writes first, then queries
                       the RESULT for popmany. This pop cannot be replaced by
                       a pop of every input-class alternative. Physical input
                       erasure still needs the selected-unique premise above.
   paired PHI suffix  successful_join_edges_phi_common_suffix_rebased needs
                       two successful native predecessor calls and equal
                       allocator after rebasing; it gives equal ops, shared
                       suffix, and UNCHANGED arbitrary prefixes. It needs no
                       whole-prefix uniqueness. It does not erase those prefixes
                       or assert their future shielding. This is the viable
                       existing relational result, not a whole-state reset.
   ordinary suffix    Setup.native_regular_singleton_bottom_frame handles
                       scalar outputs, including retained dead outputs, under
                       computed-input availability in the core, <=16 operands,
                       non-JMP, and exclusion of NEXT-live names from prefix.
                       No fresh-output clause is needed for a dead singleton:
                       the newly pushed top result shields its immediate pop.
                       native_regular_bottom_frame for general outputs still
                       requires prefix exclusion of nl ++ outputs. Neither is
                       an incoming-resource producer. Inventory's variable-
                       origin/absence boundaries require their operand coverage
                       and physical-access bounds; static demand exclusion alone
                       cannot discharge them.
   rebase/next block  NativePhases exposes exact states and contexts only.
                       Cleanup preserves input resources, not creates them.
                       Stack/spill preservation during rebase transports a
                       proved assertion, not a missing one.

   Assertion before the next definition of v. A unit-resource proof would
   need ~MEM (Var v) ps.ps_stack AND Var v NOTIN FDOM ps.ps_spilled before
   pushing/renaming a retained result v. That WHOLE-STATE assertion is stronger
   than replay requires. A relational replacement can leave old v in arbitrary
   prefixes if every ensuing query for it hits the common suffix first (or
   misses both prefixes), and all physical windows lie within that suffix.
   At the defining step, a newly written dead scalar v can shield its own pop
   without prior absence. For a live result, a common suffix hit can likewise
   hide older copies, but this is NOT the prefix-exclusion premise required
   by the current scalar frame, since v belongs to next-live. A generalized
   hit-sensitive temporal consumer and its native producer remain unproved.

   Source-level obstruction to the proposed static-reset chain:
   take a physical stack P ++ targets with an old Var v in P, v absent from
   post-PHI demand at j, and empty spills. For residual-only v the JMP suffix
   equation allows P unchanged; no class-i write targets that residual cell.
   Even if v is selected in a suffix cell, the retained PHI count equation
   only subtracts one v; it does not delete a second copy in P. Paired PHI
   common-suffix replay explicitly preserves P. Thus post-PHI demand exclusion
   plus the existing native suffix/PHI facts cannot imply whole-state absence.
   This is a symbolic interface obstruction, NOT a claimed reachable-state
   witness or counterexample to the frozen theorem.

   Induction dependency ledger (missing cells must not become hypotheses):
   A. Ordinary live coverage/upper at every phase: base is initialized entry;
      cleanup exact transport is available; PHI result upper needs pre-write
      physical freshness; ordinary result upper needs the same or a replacement.
   B. Whole-state future-output freshness: proposed return-cut proof uses A at
      the earlier predecessor for selected next-live v, AND needs control of
      residual-only/unselected v not covered by A. At PHI outputs, A itself
      calls B. An induction only on static block definitions is circular on
      revisits. The cut is earlier on the *return segment*, not necessarily
      earlier than the first occurrence whose freshness A is trying to prove.
   C. Relational shielding: PHI common-suffix initialization is unconditional
      on prefix inventory (given paired native calls), but ordinary consumers
      require additional next-live exclusion/core availability. No established
      earlier-phase theorem produces those for arbitrary return paths.
   Consequently there is no complete noncircular global induction supplied
   by these interfaces. The precise failed bridge is native residual control
   (or hit-sensitive temporal shielding), not entry initialization, PHI stack
   hit existence, or liveness non-domination. A future strategy must choose
   and prove that bridge before the frozen theorem is authorized; adding A/B/C
   as resource fields of a reachability constructor would merely assume it.
*)

(* Entry and joins root single-predecessor regions, including cyclic CFGs.
   P is label-parametric: no physical state or transfer is assumed here. *)
Theorem ready_reachable_region_induction:
  !fn entry P.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    P entry /\
    (!lbl. fn_reachable fn lbl /\
      1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) ==> P lbl) /\
    (!pred lbl. fn_reachable fn pred /\
      cfg_preds_of (cfg_analyze fn) lbl = [pred] /\ P pred ==> P lbl) ==>
    !lbl. fn_reachable fn lbl ==> P lbl
Proof
  rpt gen_tac >> strip_tac >>
  `!src lbl. RTC (fn_cfg_edge fn) src lbl ==> src = entry ==> P lbl` suffices_by
    (simp[fn_reachable_def] >> metis_tac[]) >>
  ho_match_mp_tac relationTheory.RTC_STRONG_INDUCT_RIGHT1 >>
  conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  strip_tac >> gvs[] >>
  `wf_function fn` by gvs[stackPlanGenTheory.codegen_ready_fn_def] >>
  `fn_reachable fn lbl /\ fn_reachable fn lbl'` by
    (simp[fn_reachable_def] >>
     metis_tac[relationTheory.RTC_RULES_RIGHT1]) >>
  `MEM lbl (cfg_preds_of (cfg_analyze fn) lbl')` by
    metis_tac[codegenReadyComputeTheory.fn_cfg_edge_cfg_analyze,
              cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  Cases_on `1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl')`
  >- metis_tac[] >>
  `cfg_preds_of (cfg_analyze fn) lbl' = [lbl]` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) lbl'` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  metis_tac[]
QED
