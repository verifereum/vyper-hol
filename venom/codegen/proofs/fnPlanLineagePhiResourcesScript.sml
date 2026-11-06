Theory fnPlanLineagePhiResources
Ancestors fnPlanLineagePhiInventory

Theorem dead_phi_selected_erased:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  stack_peek d ps.ps_stack = Var v /\
  LENGTH (FILTER (\op. op = Var v) ps.ps_stack) = 1 /\
  Var v NOTIN FDOM ps.ps_spilled /\ ~MEM v next /\
  HD inst.inst_outputs <> v /\
  generate_phi_plan inst next halting ps = (ops,qs) ==>
  ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  strip_tac >>
  `~MEM (operand_to_string (Var v)) next` by
    simp[stackPlanTypesTheory.operand_to_string_def] >>
  drule_all dead_phi_spilled_unchanged >> strip_tac >>
  conj_tac >- (strip_tac >> drule_all dead_phi_stack_inventory >> simp[]) >>
  simp[]
QED

Theorem lupdate_elem_count_balance:
  !(xs:'a list) n y z.
    n < LENGTH xs ==>
    LIST_ELEM_COUNT z (LUPDATE y n xs) + (if z = EL n xs then 1 else 0) =
    LIST_ELEM_COUNT z xs + (if z = y then 1 else 0)
Proof
  Induct >> simp[] >> gen_tac >> Cases_on `n`
  >- (rpt gen_tac >> simp[listTheory.LUPDATE_def,
        rich_listTheory.LIST_ELEM_COUNT_DEF] >>
      rpt (IF_CASES_TAC >> simp[])) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `n'` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`y`,`z`] mp_tac) >>
  simp[listTheory.LUPDATE_def, rich_listTheory.LIST_ELEM_COUNT_DEF] >>
  rpt (IF_CASES_TAC >> simp[]) >> decide_tac
QED

Theorem stack_poke_count_balance:
  d < LENGTH stk ==>
  LIST_ELEM_COUNT z (stack_poke d y stk) +
    (if z = stack_peek d stk then 1 else 0) =
  LIST_ELEM_COUNT z stk + (if z = y then 1 else 0)
Proof
  strip_tac >> simp[stackModelTheory.stack_poke_def, stackModelTheory.stack_peek_def] >>
  irule lupdate_elem_count_balance >> simp[]
QED

(* Exact balance deliberately permits old copies of the output. *)
Theorem dead_phi_retained_count_balance:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  stack_peek d ps.ps_stack = Var v /\ ~MEM v next /\
  (halting \/ MEM (HD inst.inst_outputs) next) /\
  generate_phi_plan inst next halting ps = (ops,qs) ==>
  !w. LIST_ELEM_COUNT (Var w) qs.ps_stack + (if w = v then 1 else 0) =
    LIST_ELEM_COUNT (Var w) ps.ps_stack +
    (if w = HD inst.inst_outputs then 1 else 0)
Proof
  strip_tac >>
  `d < LENGTH ps.ps_stack` by
    (fs[stackModelTheory.stack_get_phi_depth_def] >>
     drule planAlignTheory.stack_find_bound >> simp[]) >>
  drule fnPlanLineagePhiTemporalTheory.generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`next`,`halting`] mp_tac) >>
  simp[fnPlanLineagePhiTemporalTheory.phi_write_phase_def,
       stackPlanTypesTheory.operand_to_string_def] >> strip_tac >> gvs[] >>
  gen_tac >> drule stack_poke_count_balance >>
  disch_then (qspecl_then [`Var w`,`Var (HD inst.inst_outputs)`] mp_tac) >> simp[]
QED

Theorem dead_phi_fresh_result_resource:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  stack_peek d ps.ps_stack = Var v /\ ~MEM v next /\
  (halting \/ MEM (HD inst.inst_outputs) next) /\
  ~MEM (Var (HD inst.inst_outputs)) ps.ps_stack /\
  Var (HD inst.inst_outputs) NOTIN FDOM ps.ps_spilled /\
  generate_phi_plan inst next halting ps = (ops,qs) ==>
  LIST_ELEM_COUNT (Var (HD inst.inst_outputs)) qs.ps_stack +
    (if Var (HD inst.inst_outputs) IN FDOM qs.ps_spilled then 1 else 0) = 1
Proof
  strip_tac >>
  `~MEM (operand_to_string (Var v)) next` by
    simp[stackPlanTypesTheory.operand_to_string_def] >>
  drule_all dead_phi_spilled_unchanged >> strip_tac >>
  `!w. LIST_ELEM_COUNT (Var w) qs.ps_stack + (if w = v then 1 else 0) =
    LIST_ELEM_COUNT (Var w) ps.ps_stack +
    (if w = HD inst.inst_outputs then 1 else 0)` by
    (irule dead_phi_retained_count_balance >> conj_tac
     >- (qexists_tac `d` >> simp[]) >>
     qexistsl_tac [`halting`,`next`,`ops`] >> simp[]) >>
  pop_assum (qspec_then `HD inst.inst_outputs` mp_tac) >>
  `MEM (Var v) ps.ps_stack` by
    (fs[stackModelTheory.stack_get_phi_depth_def] >>
     drule planAlignTheory.stack_find_bound >> strip_tac >>
     fs[stackModelTheory.stack_peek_def] >>
     `LENGTH ps.ps_stack - (d+1) < LENGTH ps.ps_stack` by decide_tac >>
     metis_tac[listTheory.EL_MEM]) >>
  `HD inst.inst_outputs <> v` by metis_tac[] >>
  `LIST_ELEM_COUNT (Var (HD inst.inst_outputs)) ps.ps_stack = 0` by
    (fs[GSYM rich_listTheory.LIST_ELEM_COUNT_MEM]) >> simp[]
QED

Theorem dead_phi_other_resource_unchanged:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  stack_peek d ps.ps_stack = Var v /\ ~MEM v next /\
  (halting \/ MEM (HD inst.inst_outputs) next) /\
  generate_phi_plan inst next halting ps = (ops,qs) /\
  w <> v /\ w <> HD inst.inst_outputs ==>
  LIST_ELEM_COUNT (Var w) qs.ps_stack +
    (if Var w IN FDOM qs.ps_spilled then 1 else 0) =
  LIST_ELEM_COUNT (Var w) ps.ps_stack +
    (if Var w IN FDOM ps.ps_spilled then 1 else 0)
Proof
  strip_tac >>
  `~MEM (operand_to_string (Var v)) next` by
    simp[stackPlanTypesTheory.operand_to_string_def] >>
  drule_all dead_phi_spilled_unchanged >> strip_tac >>
  `LIST_ELEM_COUNT (Var w) qs.ps_stack + (if w = v then 1 else 0) =
    LIST_ELEM_COUNT (Var w) ps.ps_stack +
    (if w = HD inst.inst_outputs then 1 else 0)` by
    (irule dead_phi_retained_count_balance >> conj_tac
     >- (qexists_tac `d` >> simp[]) >>
     qexistsl_tac [`halting`,`next`,`ops`] >> simp[]) >> gvs[]
QED

(* Native initialization audit (diagnostic, NOT additional proved lemmas).

   Source interfaces checked:
   - NativePhases.native_block_trace_def: parameter preparation ps -> ps1,
     conditional single-predecessor cleanup ps1 -> ps2, native instructions.
   - stackPlanGen.codegen_ready_fn_def (479-492), block_entries_ready_def,
     phis_at_joins_def: entry and <=1-predecessor blocks have no PHIs.
   - livenessDefs.input_vars_from_def (83-100): a class index is placed once;
     repeated alternatives within ONE PHI are allowed. phi_uses_disjoint
     forbids a name belonging to TWO different PHIs, not that repetition.
   - PhiMaps.build_phi_maps_operand_class, matching_index, matching_total,
     input_vars_from_selected_count; NativeTargets.ready_join_target_counts.
   - PhiSchedule.successful_join_edge_native_phi_coverage supplies an actual
     stack representative for EVERY class, not raw union-live coverage.
   - Edge.analyzed_join_edge_spilled_empty supplies empty incoming spills.

   Proposed contracts below use metavariable abbreviations only in this
   comment: phis = collect_phis sb.bb_instructions; cls = native_phi_class
   pred phis; c(ps,v) = LIST_ELEM_COUNT (Var v) ps.ps_stack +
   (if Var v IN FDOM ps.ps_spilled then 1 else 0).
   These are NOT definitions or asserted theorems.

   ENTRY preparation contract (already proved):
     codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
     ps = SND (prepare_params_plan (liveness_analyze fn) fn
       (init_cleanup_plan_state ch growth spill_base lbl_ctr)) ==>
     entry_boundary_resources fn (HD fn.fn_blocks)
       (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) ps
   This is EntryProduction.initialized_entry_boundary_resources, exactly.
   Readiness and successful function planning supply the entry case's static
   premises; no PHI family is initialized here. Entry cleanup is identity
   because readiness makes the predecessor list empty. This entry-only
   chronological-origin theorem is NOT a revisit initializer.

   SINGLE predecessor contract (still missing, no PHIs):
     codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
     LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 /\
     (!v. MEM v (live_vars_at (liveness_analyze fn) lbl 0) ==>
       c(ps,v) = 1) /\
     clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb ps =
       (ops,qs) ==>
     !v. MEM v (live_vars_at (liveness_analyze fn) lbl 0) ==>
       c(qs,v) = 1
   The resource premise is a still-unproved incoming native producer, NOT a
   task hypothesis. Cleanup removes non-input names or marks retained dead
   slots; it cannot manufacture coverage. Physical future-output exclusion
   needs its own incoming producer. There are no PHI representatives here.

   JOIN contract: with codegen_ready_fn fn, fn_entry_label fn = SOME entry,
   fn_reachable fn succ, succ <> entry, both block lookups, the CFG edge,
   >1 predecessors, and a successful predecessor generate_block_plan call,
   existing Edge/PhiSchedule theorems give
     (?prefix. psAfter.ps_stack = prefix ++ MAP Var
       (input_vars_from pred sb.bb_instructions
         (live_vars_at (liveness_analyze fn) succ 0))) /\
     psAfter.ps_spilled = FEMPTY /\
     (!i. i < LENGTH phis ==> ?op. MEM op psAfter.ps_stack /\ cls op = SOME i).
   Reachability and static premises must be derived from frozen lineage/DFS
   hypotheses; the predecessor call is native execution, not a new resource
   assumption. At this non-entry join preparation and cleanup are identities.
   Rebase must preserve stack/spills to transport these conclusions.

   First missing strengthening at THIS join boundary (proposed HOL shape):
     [the same native join premises] ==>
     !v i. native_phi_class pred (collect_phis sb.bb_instructions) (Var v) = SOME i /\
       MEM (Var v) psAfter.ps_stack ==>
       LIST_ELEM_COUNT (Var v) psAfter.ps_stack = 1
   This would initialize candidate R's whole-union upper counts; it is NOT
   supplied by ready_join_target_counts. That theorem bounds only the target
   suffix. Writing count_after(v)=count_prefix(v)+count_targets(v) exposes the
   gap. EntryProduction.generate_inst_plan_jmp_live_terminal eliminates prefix
   copies of predecessor next-live names only under a preterminal unit-count
   hypothesis. An unselected alternative need not be next-live on this edge;
   its residual-prefix copies are not excluded by this result. Nor does SSA
   imply physical absence of a previously generated result on a revisit.

   Symbolic PHI schedule, position i:
   - analyzed_native_phi_schedule_classes identifies all queried operands
     with class i, proves the output has class NONE and selected input is
     dead in next-live. Earlier PHI outputs also have class NONE.
   - For every j>i a representative of class j in the common suffix survives:
     the poke changes only a class-i cell; a dead-result pop removes only the
     new result, which belongs to no input class. Existing origin schedule
     readiness/extinction and common-suffix replay prove this without any
     whole-stack uniqueness premise (PhiSchedule 139-246, 385-438).
   - If a whole-stack class upper count is available, a retained-result step
     satisfies count_after(w)+[w=v]=count_before(w)+[w=out]
     (dead_phi_retained_count_balance). For a union-class w, w<>out, so its
     count does not increase. Spills are unchanged in the dead-input branch.
     In the dead-result branch popmany cannot introduce union names. Thus
     representatives and union-name upper counts are separate obligations.
   - A selected unique unspilled v is physically erased by
     dead_phi_selected_erased. Unit result resources additionally require
     fresh output in BOTH inventory locations (dead_phi_fresh_result_resource).
     Readiness/SSA gives no standalone physical freshness premise on revisits.

   Minimal missing native producers, not certified by this audit:
   (1) whole-union residual exclusion or a weaker relational replacement;
   (2) ordinary demand coverage/multiplicity through cleanup and every native
       opcode, including repeated unrenamed liveness targets at JMP;
   (3) physical future-result exclusion, including revisits, and its actual
       no-reintroduction preservation; (4) cross-edge/rebase transport.
   PHI stack-hit existence, empty join spills, and relational PHI common-core
   transport already have interfaces: do not duplicate them as new machinery.
   This is a limitation of candidate R, NOT a counterexample to the frozen
   theorem. Global closure and the frozen proof remain unauthorized.
*)

(* The exact-name cut is already dead_phi_selected_erased above; its
   length-one premise is weaker than FILTER ... = [Var v].  The native
   producer must still supply unique selection, absent spill, output
   inequality and deadness; these local transitions supply none of them. *)
Theorem dead_phi_resource_nonincrease:
  !inst next halting ps d v ops qs w.
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
    stack_peek d ps.ps_stack = Var v /\ ~MEM v next /\
    generate_phi_plan inst next halting ps = (ops,qs) /\
    w <> HD inst.inst_outputs ==>
    LIST_ELEM_COUNT (Var w) qs.ps_stack +
      (if Var w IN FDOM qs.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT (Var w) ps.ps_stack +
      (if Var w IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  `d < LENGTH ps.ps_stack` by
    (fs[stackModelTheory.stack_get_phi_depth_def] >>
     drule planAlignTheory.stack_find_bound >> simp[]) >>
  `~MEM (operand_to_string (Var v)) next` by
    simp[stackPlanTypesTheory.operand_to_string_def] >>
  drule fnPlanLineagePhiTemporalTheory.generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`next`,`halting`] mp_tac) >>
  simp[fnPlanLineagePhiTemporalTheory.phi_write_phase_def] >> strip_tac >>
  `LIST_ELEM_COUNT (Var w) (stack_poke d (Var (HD inst.inst_outputs)) ps.ps_stack) <=
     LIST_ELEM_COUNT (Var w) ps.ps_stack` by
    (drule stack_poke_count_balance >>
     disch_then (qspecl_then [`Var w`,`Var (HD inst.inst_outputs)`] mp_tac) >>
     simp[] >> Cases_on `w = v` >> simp[]) >>
  Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next` >> gvs[]
  >- (pairarg_tac >> gvs[] >>
      drule fnPlanLineageInventoryTheory.popmany_plan_resource_nonincrease >>
      disch_then (qspec_then `Var w` mp_tac) >> simp[] >> decide_tac) >>
  simp[]
QED
