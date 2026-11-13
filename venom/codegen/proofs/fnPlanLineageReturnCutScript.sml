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
    (conj_tac >> irule venomWfPropsTheory.is_fn_path_all_reachable >>
     qexists_tac `d::tail` >>
     simp[] >> metis_tac[listTheory.MEM_APPEND, listTheory.MEM]) >>
  `?pa. lookup_block a fn.fn_blocks = SOME pa` by
    metis_tac[venomWfPropsTheory.fn_reachable_has_block] >>
  `?jb. lookup_block j fn.fn_blocks = SOME jb` by
    metis_tac[venomWfPropsTheory.fn_reachable_has_block] >>
  `fn_cfg_edge fn a j` by
    (qpat_x_assum `is_fn_path fn (d::tail)` mp_tac >>
     qpat_x_assum `d::tail = _` SUBST1_TAC >>
     disch_tac >> drule fn_path_cut >> simp[is_fn_path_def]) >>
  `MEM j (cfg_succs_of (cfg_analyze fn) a)` by
    metis_tac[codegenReadyComputeTheory.fn_cfg_edge_cfg_analyze] >>
  drule_all ready_join_edge_terminator >> strip_tac >>
  qexistsl_tac [`before`, `a`, `j`, `after`, `pa`, `jb`] >> simp[]
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
    (irule fnPlanLineageLivenessTheory.ordered_phis_ordinary_suffix >>
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

(* Backward consumer slice (C3.exclusion.history.close.consumer).
   This is a hypothesis ledger, NOT a new invariant or a proof of replay.
   P ++ C and Q ++ C below have common planner fields except stack and
   cleanup bookkeeping. C is a physical suffix, not a filtered live list.

   Static arities: codegen_ready_fn_def supplies EVERY codegen_ready_inst,
   fn_inst_wf and ssa_form. codegen_ready_inst_def gives <=16 COMPUTED
   operands for non-PHI instructions, not <=16 JMP targets. inst_wf_def
   gives BUMP two outputs and INVOKE unrestricted output arity. Thus a
   singleton-only consumer cannot cover this task. ssa_form_def makes the
   flattened output list distinct, hence each instruction's outputs distinct;
   it does not prohibit old copies of those names on a returning stack.

   1. Entry/dispatch. generate_block_plan tests bb = HD fn.fn_blocks, then
   prepares parameters; otherwise it leaves the state alone. Entry has no
   predecessors under block_entries_ready, so a lineage entry is the initial
   state, not an arbitrary returning suffix. PARAM/FMP_PARAM/RETPC_PARAM and
   NOP dispatch are no-ops; OFFSET pushes its output, observing only literal
   and label operands. No stack query or output-freshness premise is needed
   for OFFSET. Pre-codegen and malformed INVOKE branches fail bilaterally.

   2. Cleanup. clean_stack_plan queries depth of every MAP Var to_pop,
   where to_pop = FILTER (not in inputs) predecessor-live-out. It then uses
   below_all_live: each physical candidate's depth is compared with depths
   of ALL inputs (a missing input passes this comparison). Matching ordinary
   operand queries alone therefore does not imply matching cleanup. It also
   tests cleanup_elision_safe at LENGTH stack - LENGTH to_cleanup. Equal
   heights must NOT be assumed. Inventory.clean_stack_plan_arbitrary_core_replay
   solves these observations for REPLICATE m marker ++ C versus REPLICATE n
   marker ++ C: choose h = NONE and promised = reference ok (the disjunction
   of its promise and height test). With NONE the candidate height test is
   false, so the candidate follows precisely reference ok. The output promise
   need not equal the reference promise. Its empty-input branch marks the
   WHOLE stack; its other elision branch popmany's to_cleanup then marks all
   occurrences of retained names. Spills never change in any branch.
   RelationalTail.lineage_block_setup_nonentry_core_replay packages this with
   equal alloc/spilled. For arbitrary P,Q this interface does not apply:
   core-hit or bilateral-miss is needed for every cleanup lookup, all pops
   must remain inside C, and retained-name marking transforms P,Q as well.
   The cleanup branch choice can be aligned with the same h/promise recipe;
   it cannot align unequal physical/deletion observations. Producer: MISSING
   for residual prefixes, established for marker prefixes only.

   3. PHI prefix. stack_get_phi_depth searches FILTER is_var_operand over
   ALL alternatives; shielding only the edge-selected variable is insufficient
   unless the slot/class schedule proves that it is the first class hit.
   The chosen stack_peek decides retain/dup from next-live membership. Dead
   result deletion queries the result AFTER phi_write_phase. Temporal's
   generate_phi_plan_observation_frame requires equal distances, in-bounds
   accesses, equal alloc, equal selected-live truth values, and equal result
   deletion depths. It concludes code/alloc equality, not a suffix invariant.
   PhiSchedule.successful_join_edges_phi_state_replay supplies the stronger
   slot-based simulation from TWO successful native predecessor calls, with
   rebased stacks and equal alloc. It preserves arbitrary prefixes; no prefix
   uniqueness is required. successful_join_edges_phi_common_suffix_rebased
   supplies an equal suffix covering post-PHI live values exactly once. Its
   updates touch only stack/alloc, hence preserve input spill equality. This
   is an available paired-native producer at a join, NOT yet an induction
   over arbitrary lineage histories. PHIs occur only at joins (phis_at_joins).

   4. Ordinary preparation, excluding JMP. Setup.lineage_regular_prepare_bottom_frame
   permits any prefix when each computed variable operand is in C or the
   common spill map, and computed arity <=16. Input restoration consults the
   spill map before looking for stack copies; equality of maps is essential.
   Emission materializes the operand window; the commutative dry runs then
   have equal costs and choose the same reorder. Inventory's shielded and
   materialised reorder frames confine unfixed-depth searches, peeks and
   swaps to the core. Selective spilling scans offsets up to
   MIN 16 (MIN (target_dist-1) (LENGTH stack-1)), excludes forbidden targets
   and finalized windows, and tests is_var_operand at each peek. Equal
   successful operand hits alone is not a general bound for this scan.
   The <=16 materialised frame supplies that bound for ordinary preparation.
   Bulk do_swap/do_dup allocate/free temporary slots but do not write spilled;
   a distance outside the shared suffix would still break code/alloc replay.
   Producer: ordinary positive availability is checked, but its localization
   to a shared C rather than a residual prefix still needs a history proof.

   5. Output/deletion/optimistic tail. Fresh pushes shield old output copies.
   Setup.popmany_plan_output_suffix_bottom_frame covers MULTIPLE distinct
   dead outputs, including BUMP and INVOKE: requests lie in the just-pushed
   output suffix. No whole-state output freshness is necessary. The current
   legacy native_regular_singleton_bottom_frame's exclusion of every nl name
   is used by the live-output optimistic branch, not preparation or the dead
   singleton pop. RelationalTail.native_regular_conditional_shared_core_replay
   already factors this into paired preparation, confined deletion, and one
   enabled observation: nl=[] OR LAST nl hits the post-deletion C OR misses
   both P,Q. The query is skipped when term, no outputs, no live outputs, or
   operand_equiv of LAST outputs and LAST nl. Setup's shielded optimistic
   frame handles the remaining hit/miss case and its bounded do_swap.
   lineage_regular_preoptimistic_live_coverage gives stack OR spill coverage;
   a spill-only LAST nl does NOT give a core hit or bilateral prefix miss.
   This is a precise remaining producer gap even after removing freshness.
   release_dead_spills folds only over common map and next-live, so equal
   input map/allocator gives equal release effects, independently of P,Q.

   6. Terminal JMP. compute_operands is empty and inst_wf gives no outputs.
   join_target_ops reads successor input_vars_from; restore_spilled_plan has
   an unconditional bottom frame for equal map/alloc. Reorder then queries
   unfixed occurrences and selective-spill candidates, as above. A successful
   reference join_reached proves a FINAL target suffix only; it does not
   constrain earlier queries in the other stack. reorder_plan_bottom_frame
   needs target exclusion from prefixes plus target length <= core height;
   reorder_plan_materialised_bottom_frame instead needs target multiplicity
   coverage AND <=16 targets. Neither bound on target count follows from
   codegen_ready_inst's empty JMP operands. Thus arbitrary residual-prefix
   replay of large joins remains a distinct window/shielding obligation.
   Revert-block spill rejection finally depends on emitted code only; equal
   chunks imply equal rejection, with no extra resource invariant.

   Proposed LOCAL simulation contract (not asserted here): given two states
   p,q with equal alloc/spilled and stacks P++C,Q++C, a non-JMP non-PHI
   instruction with <=16 computed operands, distinct outputs, and each
   computed variable in C or the common spill map; let t be its preparation
   followed by enabled dead-output deletion on the core state. If the enabled
   optimistic query LAST nl hits t.stack or misses both P and Q, then there
   exist ops, C', al', sp' such that the two regular calls return
   (ops,p with <|stack=P++C'; alloc=al'; spilled=sp'|>) and
   (ops,q with <|stack=Q++C'; alloc=al'; spilled=sp'|>) respectively
   (field names here omit the ps_ prefix). Other fields are preserved on
   their own side, not asserted equal. Both alloc AND spilled outputs agree.
   Preparation and
   deletion premises can be discharged by the existing frames above; this
   contract still needs integration, not a new replay-readiness relation.
   PHI has the separate class-slot contract in item 3; cleanup and JMP cannot
   be hidden inside this local ordinary contract.

   Smallest outstanding implication for that ordinary contract: at the
   actual preoptimistic phase, if LAST nl has no common-core stack hit, no
   residual-only occurrence may be observed on either side. Equal spills and
   positive availability allow a spill-only value and do not prove this.
   The broader block producer must additionally localize cleanup observations
   and large-JMP access windows. Exact history continuity and the first-return
   demand cut supply none of these physical facts. No decreasing-history
   producer is justified by this audit; return to the strategy checkpoint
   before proving more conditional machinery or starting the frozen theorem.
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
