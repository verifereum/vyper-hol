Theory fnPlanLineagePhiTemporal
Ancestors
  fnPlanLineageReplay fnPlanLineageInventory fnPlanLineagePhiSlots fnPlanLineagePhiMaps
  fnPlanLineageLiveness doSwapSim sorting stackPlanGen stackPlanOps stackModel rich_list list

(* A schedule contains the instruction and the already computed next-live
   set/halting flag. No liveness or reachability assertion is built into it.
   These traces are exact execution projections, NOT a synchronization
   invariant. In particular, they never discard physically dead cells. *)
Definition phi_schedule_run_def:
  phi_schedule_run [] ps = ([], ps) /\
  phi_schedule_run ((inst,next,halting)::steps) ps =
    let (ops, ps1) = generate_phi_plan inst next halting ps in
    let (rest, ps2) = phi_schedule_run steps ps1 in
      (ops ++ rest, ps2)
End

Definition phi_paired_run_def:
  phi_paired_run [] ps qs = (([],ps),([],qs)) /\
  phi_paired_run ((inst,next,halting)::steps) ps qs =
    let (ops_p, ps1) = generate_phi_plan inst next halting ps in
    let (ops_q, qs1) = generate_phi_plan inst next halting qs in
    let ((rest_p,ps2),(rest_q,qs2)) = phi_paired_run steps ps1 qs1 in
      ((ops_p ++ rest_p,ps2),(ops_q ++ rest_q,qs2))
End

Theorem phi_paired_run_projections:
  !steps ps qs.
    phi_paired_run steps ps qs =
      (phi_schedule_run steps ps, phi_schedule_run steps qs)
Proof
  Induct >> simp[phi_paired_run_def, phi_schedule_run_def] >>
  Cases_on `h` >> Cases_on `r` >>
  simp[phi_paired_run_def, phi_schedule_run_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem phi_paired_run_left:
  !steps ps qs.
    FST (phi_paired_run steps ps qs) = phi_schedule_run steps ps
Proof
  simp[phi_paired_run_projections]
QED

Theorem phi_paired_run_right:
  !steps ps qs.
    SND (phi_paired_run steps ps qs) = phi_schedule_run steps qs
Proof
  simp[phi_paired_run_projections]
QED

(* Separate the incoming-name test from the later output-name query.
   This phase is the actual pre-pop computation, including deep do_dup. *)
Definition phi_write_phase_def:
  phi_write_phase inst next d ps =
    if MEM (operand_to_string (stack_peek d ps.ps_stack)) next then
      let (ops, ps1) = stackPlanOps$do_dup d ps in
        (ops ++ [SOPoke 0 (Var (HD inst.inst_outputs))],
         ps1 with ps_stack :=
           stack_poke 0 (Var (HD inst.inst_outputs)) ps1.ps_stack)
    else
      ([SOPoke d (Var (HD inst.inst_outputs))],
       ps with ps_stack := stack_poke d (Var (HD inst.inst_outputs)) ps.ps_stack)
End

Theorem generate_phi_plan_write_phase:
  !inst next halting ps d.
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack =
      SOME d ==>
    generate_phi_plan inst next halting ps =
      let (ops, ps1) = phi_write_phase inst next d ps in
      if ~halting /\ ~MEM (HD inst.inst_outputs) next then
        let (pops, ps2) = stackPlanOps$popmany_plan [Var (HD inst.inst_outputs)] ps1 in
          (ops ++ pops, ps2)
      else (ops, ps1)
Proof
  rpt strip_tac >> simp[generate_phi_plan_def, phi_write_phase_def]
QED

(* Producer ledger (not theorem premises smuggled in as invariants).

   Checked: the arbitrary-schedule projections above are exactly two real
   executions. They do NOT prove that the executions have synchronized edits.
   phi_write_phase isolates the selected incoming's next-live test; the
   subsequent popmany query is on its resulting stack, not the entry stack.

   The phi_origin_cell representation and its write/pop projections below
   retain unequal Original cells and Common written cells. The guarded
   phi_origin_trace below now composes their synchronized physical edits.
   Phase/singleton-pop stack bridges handle opaque lower residuals;
   independent phi_paired_run projections alone would not suffice.

   Initialization producer: transfer-generated input_vars_from entry slots,
   edge coverage, disjoint incoming classes, and explicit class emission.
   SSA output uniqueness alone does not constrain residual occurrences.

   Preservation obligation: after a synchronized write at the common incoming
   depth, any first hit for Var (HD inst.inst_outputs) above that write must
   itself be a common cell, or be excluded by transfer order / remaining-use
   liveness. Equal incoming search results do not establish this fact.

   Checked operational framing below: bounded do_dup/do_swap observations
   depend only on the allocator and the scratch item COUNT, not operands.
   Thus unequal cells in those windows do not by themselves block replay.
   Singleton popmany has the same observation frame, including bulk swap 1.
   No absence of variable names in residuals, no bounded depth, no distinct
   inventory, and no persistent-spill preservation is assumed here.
*)

(* Scratch allocation observes only the number of physical cells, not their
   operands. Bounds ensure the requested scratch window really exists. *)
Theorem do_dup_observation_frame:
  !d ps qs.
    d < LENGTH ps.ps_stack /\ d < LENGTH qs.ps_stack /\
    ps.ps_alloc = qs.ps_alloc ==>
    FST (do_dup d ps) = FST (do_dup d qs) /\
    (SND (do_dup d ps)).ps_alloc = (SND (do_dup d qs)).ps_alloc
Proof
  rpt gen_tac >> strip_tac >> Cases_on `d <= 15`
  >- simp[do_dup_def] >>
  `LENGTH (REVERSE (top_n (d - 15) ps.ps_stack)) =
   LENGTH (REVERSE (top_n (d - 15) qs.ps_stack))` by
    simp[top_n_def, LENGTH_TAKE] >>
  `spill_alloc_n [] ps.ps_alloc (REVERSE (top_n (d - 15) ps.ps_stack)) =
   spill_alloc_n [] qs.ps_alloc (REVERSE (top_n (d - 15) qs.ps_stack))` by
    (gvs[] >> irule spill_alloc_n_length_cong >> simp[top_n_def, LENGTH_TAKE]) >>
  qspecl_then [`d`, `ps`] mp_tac do_dup_big_decompose >>
  qspecl_then [`d`, `qs`] mp_tac do_dup_big_decompose >>
  simp[] >> rpt strip_tac >> gvs[]
QED

Theorem do_swap_observation_frame:
  !d ps qs.
    d < LENGTH ps.ps_stack /\ d < LENGTH qs.ps_stack /\
    ps.ps_alloc = qs.ps_alloc ==>
    FST (do_swap d ps) = FST (do_swap d qs) /\
    (SND (do_swap d ps)).ps_alloc = (SND (do_swap d qs)).ps_alloc
Proof
  rpt gen_tac >> strip_tac >> Cases_on `d = 0`
  >- simp[do_swap_def] >>
  Cases_on `d <= 16`
  >- simp[do_swap_def] >>
  `spill_alloc_n [] ps.ps_alloc (top_n (d + 1) ps.ps_stack) =
   spill_alloc_n [] qs.ps_alloc (top_n (d + 1) qs.ps_stack)` by
    (gvs[] >> irule spill_alloc_n_length_cong >> simp[top_n_def, LENGTH_TAKE]) >>
  qspecl_then [`d`, `ps`] mp_tac do_swap_big_decompose >>
  qspecl_then [`d`, `qs`] mp_tac do_swap_big_decompose >>
  simp[] >> rpt strip_tac >> gvs[]
QED

Theorem popmany_singleton_observation_frame:
  !ret ps qs.
    stack_get_depth ret ps.ps_stack = stack_get_depth ret qs.ps_stack /\
    ps.ps_alloc = qs.ps_alloc ==>
    FST (popmany_plan [ret] ps) = FST (popmany_plan [ret] qs) /\
    (SND (popmany_plan [ret] ps)).ps_alloc =
      (SND (popmany_plan [ret] qs)).ps_alloc
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_depth ret qs.ps_stack`
  >- simp[popmany_plan_def, popmany_individual_def, QSORT_DEF, PARTITION_DEF, PART_DEF] >>
  `x < LENGTH ps.ps_stack /\ x < LENGTH qs.ps_stack` by
    metis_tac[stack_get_depth_props] >>
  `FST (do_swap x ps) = FST (do_swap x qs) /\
   (SND (do_swap x ps)).ps_alloc = (SND (do_swap x qs)).ps_alloc` by
    (irule do_swap_observation_frame >> simp[]) >>
  simp[popmany_plan_def, popmany_individual_def, is_contiguous_top_def,
       QSORT_DEF, PARTITION_DEF, PART_DEF] >>
  Cases_on `x = 1` >> gvs[] >>
  Cases_on `x = 0`
  >- gvs[do_swap_def] >>
  simp[] >> rpt (pairarg_tac >> gvs[])
QED

Theorem phi_write_phase_observation_frame:
  !inst next d ps qs.
    d < LENGTH ps.ps_stack /\ d < LENGTH qs.ps_stack /\
    ps.ps_alloc = qs.ps_alloc /\
    (MEM (operand_to_string (stack_peek d ps.ps_stack)) next <=>
     MEM (operand_to_string (stack_peek d qs.ps_stack)) next) ==>
    FST (phi_write_phase inst next d ps) =
      FST (phi_write_phase inst next d qs) /\
    (SND (phi_write_phase inst next d ps)).ps_alloc =
      (SND (phi_write_phase inst next d qs)).ps_alloc
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `MEM (operand_to_string (stack_peek d qs.ps_stack)) next`
  >- (drule_all do_dup_observation_frame >> strip_tac >>
      simp[phi_write_phase_def] >> rpt (pairarg_tac >> gvs[])) >>
  simp[phi_write_phase_def]
QED

Theorem generate_phi_plan_observation_frame:
  !inst next halting ps qs d.
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) qs.ps_stack = SOME d /\
    d < LENGTH ps.ps_stack /\ d < LENGTH qs.ps_stack /\
    ps.ps_alloc = qs.ps_alloc /\
    (MEM (operand_to_string (stack_peek d ps.ps_stack)) next <=>
     MEM (operand_to_string (stack_peek d qs.ps_stack)) next) /\
    (~halting /\ ~MEM (HD inst.inst_outputs) next ==>
     stack_get_depth (Var (HD inst.inst_outputs))
       (SND (phi_write_phase inst next d ps)).ps_stack =
     stack_get_depth (Var (HD inst.inst_outputs))
       (SND (phi_write_phase inst next d qs)).ps_stack) ==>
    FST (generate_phi_plan inst next halting ps) =
      FST (generate_phi_plan inst next halting qs) /\
    (SND (generate_phi_plan inst next halting ps)).ps_alloc =
      (SND (generate_phi_plan inst next halting qs)).ps_alloc
Proof
  rpt gen_tac >> strip_tac >>
  drule_all phi_write_phase_observation_frame >>
  disch_then (qspec_then `inst` strip_assume_tac) >>
  drule generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`next`, `halting`] assume_tac) >>
  rev_drule generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`next`, `halting`] assume_tac) >>
  Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next` >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all popmany_singleton_observation_frame >> simp[]
QED

(* Provenance is physical: an Original cell remains tagged even after its
   variable becomes dead. Only a real write replaces it with a Common cell. *)
Datatype:
  phi_origin_cell = PhiOriginal num operand operand | PhiCommon operand
End

Definition phi_cell_value_def:
  phi_cell_value left (PhiOriginal slot p q) = (if left then p else q) /\
  phi_cell_value left (PhiCommon op) = op
End

Definition phi_origin_write_def:
  phi_origin_write keep d ret cells =
    if keep then stack_poke 0 (PhiCommon ret) (stack_dup d cells)
    else stack_poke d (PhiCommon ret) cells
End

Definition phi_origin_pop_def:
  phi_origin_pop d cells = stack_pop 1 (stack_swap d cells)
End

Theorem stack_poke_map:
  !f d x xs.
    MAP f (stack_poke d x xs) = stack_poke d (f x) (MAP f xs)
Proof
  simp[stack_poke_def, LUPDATE_MAP]
QED

Theorem stack_dup_map:
  !f d xs. d < LENGTH xs ==>
    MAP f (stack_dup d xs) = stack_dup d (MAP f xs)
Proof
  rpt strip_tac >> simp[stack_dup_def, stack_peek_def, EL_MAP, MAP_SNOC]
QED

Theorem stack_swap_map:
  !f d xs. d < LENGTH xs ==>
    MAP f (stack_swap d xs) = stack_swap d (MAP f xs)
Proof
  rpt strip_tac >> simp[stack_swap_def, LUPDATE_MAP, EL_MAP]
QED

Theorem phi_origin_write_projection:
  !left keep d ret cells.
    d < LENGTH cells ==>
    MAP (phi_cell_value left) (phi_origin_write keep d ret cells) =
      if keep then
        stack_poke 0 ret (stack_dup d (MAP (phi_cell_value left) cells))
      else stack_poke d ret (MAP (phi_cell_value left) cells)
Proof
  rpt strip_tac >> Cases_on `keep` >>
  simp[phi_origin_write_def, stack_poke_map, stack_dup_map, phi_cell_value_def]
QED

Theorem phi_origin_pop_projection:
  !left d cells.
    d < LENGTH cells ==>
    MAP (phi_cell_value left) (phi_origin_pop d cells) =
      stack_pop 1 (stack_swap d (MAP (phi_cell_value left) cells))
Proof
  rpt strip_tac >>
  simp[phi_origin_pop_def, stack_pop_def, MAP_TAKE, stack_swap_map,
       stack_swap_def, LENGTH_LUPDATE, LUPDATE_MAP, EL_MAP]
QED

Theorem stack_pop_bottom_extension:
  !n prefix core. n <= LENGTH core ==>
    stack_pop n (prefix ++ core) = prefix ++ stack_pop n core
Proof
  rpt strip_tac >> simp[stack_pop_def, TAKE_APPEND]
QED

Theorem phi_origin_write_suffix_projection:
  !left keep d ret prefix cells.
    d < LENGTH cells ==>
    prefix ++ MAP (phi_cell_value left) (phi_origin_write keep d ret cells) =
      if keep then
        stack_poke 0 ret (stack_dup d (prefix ++ MAP (phi_cell_value left) cells))
      else stack_poke d ret (prefix ++ MAP (phi_cell_value left) cells)
Proof
  rpt strip_tac >> Cases_on `keep` >>
  simp[phi_origin_write_projection, stack_dup_bottom_extension,
       stack_poke_bottom_extension, stack_dup_def, SNOC_APPEND]
QED

Theorem phi_origin_pop_suffix_projection:
  !left d prefix cells.
    d < LENGTH cells ==>
    prefix ++ MAP (phi_cell_value left) (phi_origin_pop d cells) =
      stack_pop 1 (stack_swap d (prefix ++ MAP (phi_cell_value left) cells))
Proof
  rpt strip_tac >>
  simp[phi_origin_pop_projection, stack_swap_bottom_extension] >>
  irule (GSYM stack_pop_bottom_extension) >>
  simp[stack_swap_def]
QED

Theorem phi_write_phase_stack_projection:
  !left inst next d ps prefix cells keep.
    ps.ps_stack = prefix ++ MAP (phi_cell_value left) cells /\
    d < LENGTH cells /\
    keep = MEM (operand_to_string (stack_peek d ps.ps_stack)) next ==>
    (SND (phi_write_phase inst next d ps)).ps_stack =
      prefix ++ MAP (phi_cell_value left)
        (phi_origin_write keep d (Var (HD inst.inst_outputs)) cells)
Proof
  rpt gen_tac >> strip_tac >>
  `d < LENGTH ps.ps_stack` by simp[] >>
  drule do_dup_stack_exact >> strip_tac >>
  simp[phi_origin_write_suffix_projection] >>
  Cases_on `keep` >> gvs[phi_write_phase_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[stack_dup_def, SNOC_APPEND]
QED

Theorem popmany_singleton_stack_projection:
  !ret ps d.
    stack_get_depth ret ps.ps_stack = SOME d ==>
    (SND (popmany_plan [ret] ps)).ps_stack =
      stack_pop 1 (stack_swap d ps.ps_stack)
Proof
  rpt strip_tac >>
  `d < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_props] >>
  drule do_swap_stack_result >> strip_tac >>
  simp[popmany_plan_def, popmany_individual_def, is_contiguous_top_def,
       QSORT_DEF, PARTITION_DEF, PART_DEF] >>
  Cases_on `d = 1`
  >- (gvs[] >> rpt (pairarg_tac >> gvs[])) >>
  Cases_on `d = 0`
  >- gvs[stack_swap_def, LUPDATE_SAME] >>
  gvs[] >> rpt (pairarg_tac >> gvs[])
QED

(* These are named local obligations, not an established invariant. The
   separation matters: incoming predicate agreement alone is insufficient. *)
Definition phi_origin_incoming_def:
  phi_origin_incoming inst p q cells d <=>
    d < LENGTH cells /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
      (p ++ MAP (phi_cell_value T) cells) = SOME d /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
      (q ++ MAP (phi_cell_value F) cells) = SOME d
End

Definition phi_origin_selected_def:
  phi_origin_selected next p q cells d keep <=>
    keep = MEM (operand_to_string
      (stack_peek d (p ++ MAP (phi_cell_value T) cells))) next /\
    keep = MEM (operand_to_string
      (stack_peek d (q ++ MAP (phi_cell_value F) cells))) next
End

Definition phi_origin_output_def:
  phi_origin_output ret p q cells <=>
    stack_get_depth ret (p ++ MAP (phi_cell_value T) cells) =
      stack_get_depth ret (q ++ MAP (phi_cell_value F) cells)
End

Definition phi_origin_stage_ready_def:
  phi_origin_stage_ready inst next halting p q cells d keep <=>
    phi_origin_incoming inst p q cells d /\
    phi_origin_selected next p q cells d keep /\
    (~halting /\ ~MEM (HD inst.inst_outputs) next ==>
      phi_origin_output (Var (HD inst.inst_outputs)) p q
        (phi_origin_write keep d (Var (HD inst.inst_outputs)) cells))
End

Theorem phi_origin_stage_observations:
  !inst next halting p q cells d keep ps qs.
    phi_origin_stage_ready inst next halting p q cells d keep /\
    ps.ps_stack = p ++ MAP (phi_cell_value T) cells /\
    qs.ps_stack = q ++ MAP (phi_cell_value F) cells /\
    ps.ps_alloc = qs.ps_alloc ==>
    FST (generate_phi_plan inst next halting ps) =
      FST (generate_phi_plan inst next halting qs) /\
    (SND (generate_phi_plan inst next halting ps)).ps_alloc =
      (SND (generate_phi_plan inst next halting qs)).ps_alloc
Proof
  rpt gen_tac >> strip_tac >>
  fs[phi_origin_stage_ready_def, phi_origin_incoming_def,
     phi_origin_selected_def] >>
  irule generate_phi_plan_observation_frame >>
  simp[] >> conj_tac
  >- metis_tac[] >>
  strip_tac >>
  `keep = MEM (operand_to_string (stack_peek d ps.ps_stack)) next /\
   keep = MEM (operand_to_string (stack_peek d qs.ps_stack)) next` by metis_tac[] >>
  drule_all phi_write_phase_stack_projection >>
  disch_then (qspec_then `inst` assume_tac) >>
  rev_drule_all phi_write_phase_stack_projection >>
  disch_then (qspec_then `inst` assume_tac) >>
  gvs[phi_origin_output_def]
QED

(* Remaining universal producer obligation, stated without an unproved theorem:
   after a transfer-generated entry and any already justified origin edits,
   prove phi_origin_stage_ready for the current PHI. Its third conjunct is
   the smallest outstanding ordering implication: equal incoming first hits
   and selected-live tests must imply equal ret first hits AFTER the common
   write. The static premises (distinct outputs, disjoint incoming classes,
   coverage, terminal incoming absence, entry emission) have not yet been
   shown to produce this conjunct, nor the next stage's incoming conjunct.
   Arbitrary lower residuals p and q are still explicit in all three guards.
   Below, physical edits are composed and projected to phi_schedule_run by
   induction. Existence from static analyzed inputs remains separate from
   that conditional soundness; see the final producer ledger. *)


(* A physical stage has explicit witnesses for both searches.  The pop
   witness lies in the written suffix, so the opaque residual is untouched.
   Existence of these witnesses is a producer obligation, not a conclusion
   of the projection theorem. *)
Definition phi_origin_stage_def:
  phi_origin_stage inst next halting p q cells cells' <=>
    ?d keep written.
      phi_origin_incoming inst p q cells d /\
      phi_origin_selected next p q cells d keep /\
      written = phi_origin_write keep d (Var (HD inst.inst_outputs)) cells /\
      if ~halting /\ ~MEM (HD inst.inst_outputs) next then
        ?e. e < LENGTH written /\
          stack_get_depth (Var (HD inst.inst_outputs))
            (p ++ MAP (phi_cell_value T) written) = SOME e /\
          stack_get_depth (Var (HD inst.inst_outputs))
            (q ++ MAP (phi_cell_value F) written) = SOME e /\
          cells' = phi_origin_pop e written
      else cells' = written
End

Theorem phi_origin_stage_stack_projection:
  !inst next halting p q cells cells' left ps.
    phi_origin_stage inst next halting p q cells cells' /\
    ps.ps_stack = (if left then p else q) ++ MAP (phi_cell_value left) cells ==>
    (SND (generate_phi_plan inst next halting ps)).ps_stack =
      (if left then p else q) ++ MAP (phi_cell_value left) cells'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `phi_origin_stage _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[phi_origin_stage_def, phi_origin_incoming_def, phi_origin_selected_def] >>
  strip_tac >>
  `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
   keep = MEM (operand_to_string (stack_peek d ps.ps_stack)) next` by
    (Cases_on `left` >> gvs[]) >>
  drule_all phi_write_phase_stack_projection >>
  disch_then (qspec_then `inst` assume_tac) >>
  drule generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`next`, `halting`] assume_tac) >>
  reverse (Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next`)
  >- (gvs[] >> rpt (pairarg_tac >> gvs[])) >>
  gvs[] >>
  `stack_get_depth (Var (HD inst.inst_outputs))
      (SND (phi_write_phase inst next d ps)).ps_stack = SOME e` by
    (Cases_on `left` >> gvs[]) >>
  drule popmany_singleton_stack_projection >>
  simp[phi_origin_pop_suffix_projection] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem phi_origin_stage_ready:
  !inst next halting p q cells cells'.
    phi_origin_stage inst next halting p q cells cells' ==>
    ?d keep. phi_origin_stage_ready inst next halting p q cells d keep
Proof
  rpt gen_tac >> rewrite_tac[phi_origin_stage_def] >> strip_tac >>
  qexistsl [`d`, `keep`] >>
  simp[phi_origin_stage_ready_def] >> strip_tac >>
  gvs[phi_origin_output_def]
QED

(* A guarded trace carries the actual intermediate states AND the physical
   origin list.  No emitted-code equality is part of its guard. *)
Definition phi_origin_trace_def:
  (phi_origin_trace [] p q cells ps qs cells_end result_p result_q <=>
    cells_end = cells /\ result_p = ([],ps) /\ result_q = ([],qs) /\
    ps.ps_stack = p ++ MAP (phi_cell_value T) cells /\
    qs.ps_stack = q ++ MAP (phi_cell_value F) cells) /\
  (phi_origin_trace ((inst,next,halting)::steps) p q cells ps qs
    cells_end result_p result_q <=>
    ps.ps_stack = p ++ MAP (phi_cell_value T) cells /\
    qs.ps_stack = q ++ MAP (phi_cell_value F) cells /\
    ?cells1 ops_p ps1 ops_q qs1 rest_p ps2 rest_q qs2.
      phi_origin_stage inst next halting p q cells cells1 /\
      generate_phi_plan inst next halting ps = (ops_p,ps1) /\
      generate_phi_plan inst next halting qs = (ops_q,qs1) /\
      phi_origin_trace steps p q cells1 ps1 qs1 cells_end
        (rest_p,ps2) (rest_q,qs2) /\
      result_p = (ops_p ++ rest_p,ps2) /\
      result_q = (ops_q ++ rest_q,qs2))
End

Theorem phi_origin_trace_projections:
  !steps p q cells ps qs cells_end result_p result_q.
    phi_origin_trace steps p q cells ps qs cells_end result_p result_q ==>
    result_p = phi_schedule_run steps ps /\
    result_q = phi_schedule_run steps qs
Proof
  Induct
  >- simp[phi_origin_trace_def, phi_schedule_run_def] >>
  Cases_on `h` >> Cases_on `r` >>
  rpt gen_tac >> simp[phi_origin_trace_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[phi_schedule_run_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem phi_origin_trace_final_stacks:
  !steps p q cells ps qs cells_end result_p result_q.
    phi_origin_trace steps p q cells ps qs cells_end result_p result_q ==>
    (SND result_p).ps_stack = p ++ MAP (phi_cell_value T) cells_end /\
    (SND result_q).ps_stack = q ++ MAP (phi_cell_value F) cells_end
Proof
  Induct
  >- simp[phi_origin_trace_def] >>
  Cases_on `h` >> Cases_on `r` >>
  rpt gen_tac >> simp[phi_origin_trace_def] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem phi_origin_trace_observations:
  !steps p q cells ps qs cells_end result_p result_q.
    phi_origin_trace steps p q cells ps qs cells_end result_p result_q /\
    ps.ps_alloc = qs.ps_alloc ==>
    FST result_p = FST result_q /\
    (SND result_p).ps_alloc = (SND result_q).ps_alloc
Proof
  Induct
  >- simp[phi_origin_trace_def] >>
  Cases_on `h` >> Cases_on `r` >>
  rpt gen_tac >> simp[phi_origin_trace_def] >> strip_tac >>
  drule phi_origin_stage_ready >> strip_tac >>
  drule_all phi_origin_stage_observations >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

(* Pure ghost feasibility is separate from real execution and never mentions
   emitted operations or allocator equality.  Establishing this predicate
   from transfer-generated entry slots is the missing universal producer. *)
Definition phi_origin_schedule_ready_def:
  (phi_origin_schedule_ready [] p q cells cells_end <=> cells_end = cells) /\
  (phi_origin_schedule_ready ((inst,next,halting)::steps) p q cells cells_end <=>
    ?cells1. phi_origin_stage inst next halting p q cells cells1 /\
      phi_origin_schedule_ready steps p q cells1 cells_end)
End

Theorem phi_origin_schedule_trace:
  !steps p q cells cells_end ps qs.
    phi_origin_schedule_ready steps p q cells cells_end /\
    ps.ps_stack = p ++ MAP (phi_cell_value T) cells /\
    qs.ps_stack = q ++ MAP (phi_cell_value F) cells ==>
    phi_origin_trace steps p q cells ps qs cells_end
      (phi_schedule_run steps ps) (phi_schedule_run steps qs)
Proof
  Induct
  >- simp[phi_origin_schedule_ready_def, phi_origin_trace_def, phi_schedule_run_def] >>
  Cases_on `h` >> Cases_on `r` >> rpt gen_tac >>
  simp[phi_origin_schedule_ready_def] >> strip_tac >>
  rename1 `phi_origin_stage inst next halting lower_p lower_q cells cells1` >>
  `!left st.
     st.ps_stack = (if left then lower_p else lower_q) ++ MAP (phi_cell_value left) cells ==>
     (SND (generate_phi_plan inst next halting st)).ps_stack =
       (if left then lower_p else lower_q) ++ MAP (phi_cell_value left) cells1` by
    (rpt strip_tac >> irule phi_origin_stage_stack_projection >>
     goal_assum drule >> simp[]) >>
  pop_assum (mk_asm "stage_projection") >>
  simp[phi_origin_trace_def, phi_schedule_run_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qexists `cells1` >> simp[] >>
  `ps1.ps_stack = lower_p ++ MAP (phi_cell_value T) cells1` by
    (asm "stage_projection" (qspecl_then [`T`, `ps`] mp_tac) >> simp[]) >>
  `ps1'.ps_stack = lower_q ++ MAP (phi_cell_value F) cells1` by
    (asm "stage_projection" (qspecl_then [`F`, `qs`] mp_tac) >> simp[]) >>
  first_x_assum drule >>
  disch_then (qspecl_then [`ps1`, `ps1'`] mp_tac) >> simp[]
QED

Theorem phi_origin_schedule_replay:
  !steps p q cells cells_end ps qs.
    phi_origin_schedule_ready steps p q cells cells_end /\
    ps.ps_stack = p ++ MAP (phi_cell_value T) cells /\
    qs.ps_stack = q ++ MAP (phi_cell_value F) cells /\
    ps.ps_alloc = qs.ps_alloc ==>
    FST (phi_schedule_run steps ps) = FST (phi_schedule_run steps qs) /\
    (SND (phi_schedule_run steps ps)).ps_alloc =
      (SND (phi_schedule_run steps qs)).ps_alloc
Proof
  rpt gen_tac >> strip_tac >>
  drule_all phi_origin_schedule_trace >> strip_tac >>
  drule_all phi_origin_trace_observations >> simp[]
QED

(* Universal producer / preservation ledger, after the checked composition.

   The operational experiment is now complete: phi_origin_stage edits the
   physical suffix, phi_origin_stage_stack_projection realizes those edits,
   and phi_origin_schedule_trace connects arbitrary feasible ghost prefixes
   to both real executions.  Trace observations are proved consequences,
   never feasibility premises.  Original cells are not retired on death.

   Exact outstanding producer target:
     for transfer-generated entry slots cells0 and the analyzed schedule,
     establish ?cells_end.
       phi_origin_schedule_ready steps p q cells0 cells_end.
   This is NOT asserted as a theorem here.  Its base case is trivial; its
   step requires witnesses cells1 for phi_origin_stage and feasibility of
   the tail.  Schedule feasibility is a consumer, not an ordering invariant.

   Initialization obligations:
   - realize the two input_vars_from lists by common indexed Original cells;
   - derive incoming first hits within this suffix from entry class emission,
     coverage and disjoint incoming classes (not from arbitrary residuals);
   - derive selected-next-live agreement from temporal incoming death (or
     equality of selected common values).  SSA uniqueness is not freshness
     of dynamic occurrences, including occurrences in residuals.

   Exact extra physical output obligation in a popping stage:
     with written = phi_origin_write keep d ret cells, find e such that
       e < LENGTH written and BOTH realized stack_get_depth ret = SOME e.
   The previous phi_origin_stage_ready only demanded equality of queries.
   Physical origin preservation additionally needs the hit inside written.
   A new ret was physically written there, but an older ret above it may
   be an unequal Original cell.  Transfer order / remaining-use liveness
   must exclude such asymmetric earlier hits or prove they are common.
   This is the smallest unresolved output-ordering implication, not a fact
   proved by incoming-depth agreement or terminal absence alone.

   Preservation obligations after the actual write and optional swap/pop:
   - keep every surviving unequal Original cell at its actual position;
   - re-establish the next incoming first hits and selected-live agreement;
   - preserve the output-ordering property just described for future ret.
   No predicate here supplies these producers.  Their universal derivation
   remains open; this local experiment does not establish cleanup, persistent
   spills, JMP reset, DFS splicing, or the frozen lineage theorem.
*)

(* Equal cells may contain the output; unequal Original cells may not.
   This is query shielding, not a temporal invariant producer. *)
Theorem phi_cell_output_predicate:
  !ret cell.
    (!slot p q. cell = PhiOriginal slot p q ==>
      p = q \/ (p <> ret /\ q <> ret)) ==>
    (phi_cell_value T cell = ret <=> phi_cell_value F cell = ret)
Proof
  rpt gen_tac >> Cases_on `cell` >> simp[phi_cell_value_def] >> metis_tac[]
QED

Theorem phi_origin_output_suffix_shield:
  !ret cells p q.
    EVERY (\cell. !slot a b. cell = PhiOriginal slot a b ==>
      a = b \/ (a <> ret /\ b <> ret)) cells /\
    MEM ret (MAP (phi_cell_value T) cells) ==>
    ?d. d < LENGTH cells /\
      stack_get_depth ret (p ++ MAP (phi_cell_value T) cells) = SOME d /\
      stack_get_depth ret (q ++ MAP (phi_cell_value F) cells) = SOME d
Proof
  rpt gen_tac >> strip_tac >>
  `stack_get_depth ret (MAP (phi_cell_value T) cells) =
   stack_get_depth ret (MAP (phi_cell_value F) cells)` by
    (rewrite_tac[stack_get_depth_def] >>
     irule slot_realization_reverse_search >>
     gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     irule phi_cell_output_predicate >> metis_tac[]) >>
  `IS_SOME (stack_get_depth ret (MAP (phi_cell_value T) cells))` by
    simp[stack_get_depth_is_some] >>
  Cases_on `stack_get_depth ret (MAP (phi_cell_value T) cells)` >> gvs[] >>
  `stack_get_depth ret (MAP (phi_cell_value T) cells) = SOME x` by metis_tac[] >>
  qexists_tac `x` >>
  drule stack_get_depth_props >> strip_tac >>
  metis_tac[fnPlanLineageSuffixTheory.stack_get_depth_suffix_hit, LENGTH_MAP]
QED

Theorem phi_origin_write_every:
  !P cells keep d ret.
    EVERY P cells /\ P (PhiCommon ret) /\ d < LENGTH cells ==>
    EVERY P (phi_origin_write keep d ret cells)
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY P (stack_dup d cells)` by
    (`MEM (EL (LENGTH cells - (d + 1)) cells) cells` by
       (irule listTheory.EL_MEM >> decide_tac) >>
     gvs[stack_dup_def, stack_peek_def, listTheory.EVERY_SNOC,
         listTheory.EVERY_MEM] >> metis_tac[]) >>
  Cases_on `keep` >> simp[phi_origin_write_def, stack_poke_def] >>
  gvs[listTheory.EVERY_MEM, listTheory.MEM_LUPDATE] >>
  metis_tac[listTheory.EL_MEM]
QED

Theorem phi_origin_pop_every:
  !P cells d. EVERY P cells /\ d < LENGTH cells ==>
    EVERY P (phi_origin_pop d cells)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (EL (LENGTH cells - (d + 1)) cells) cells /\
   MEM (EL (LENGTH cells - 1) cells) cells` by
    (conj_tac >> irule listTheory.EL_MEM >> decide_tac) >>
  `EVERY P (stack_swap d cells)` by
    (gvs[stack_swap_def, listTheory.EVERY_MEM, listTheory.MEM_LUPDATE,
         listTheory.EL_LUPDATE] >> metis_tac[listTheory.EL_MEM]) >>
  gvs[phi_origin_pop_def, stack_pop_def, listTheory.EVERY_MEM] >>
  metis_tac[rich_listTheory.MEM_TAKE]
QED

Theorem phi_origin_write_output_shield:
  !ret cells keep d p q.
    EVERY (\cell. !slot a b. cell = PhiOriginal slot a b ==>
      a = b \/ (a <> ret /\ b <> ret)) cells /\ d < LENGTH cells ==>
    ?e. e < LENGTH (phi_origin_write keep d ret cells) /\
      stack_get_depth ret
        (p ++ MAP (phi_cell_value T) (phi_origin_write keep d ret cells)) = SOME e /\
      stack_get_depth ret
        (q ++ MAP (phi_cell_value F) (phi_origin_write keep d ret cells)) = SOME e
Proof
  rpt gen_tac >> strip_tac >> irule phi_origin_output_suffix_shield >>
  conj_tac
  >- (irule phi_origin_write_every >> simp[] >>
      goal_assum (drule_at Any)) >>
  `MEM (PhiCommon ret) (phi_origin_write keep d ret cells)` suffices_by
    metis_tac[listTheory.MEM_MAP, phi_cell_value_def] >>
  Cases_on `keep` >>
  simp[phi_origin_write_def, stack_poke_def, stack_dup_def, listTheory.MEM_LUPDATE] >>
  decide_tac
QED

(* A persistent, static cell certificate: unequal originals retain two
   representatives of one class. Equal live-through originals are unrestricted. *)
Definition phi_origin_classes_def:
  phi_origin_classes class_of cells <=>
    EVERY (\cell. !slot a b. cell = PhiOriginal slot a b ==>
      a = b \/ (class_of a = SOME slot /\ class_of b = SOME slot)) cells
End

Definition phi_origin_tagged_def:
  phi_origin_tagged class_of cells <=>
    EVERY (\c. case c of
      PhiCommon op => class_of op = NONE
    | PhiOriginal i a b => class_of a = SOME i /\ class_of b = SOME i) cells
End

Theorem phi_origin_tagged_classes:
  !class_of cells.
    phi_origin_tagged class_of cells ==> phi_origin_classes class_of cells
Proof
  simp[phi_origin_tagged_def, phi_origin_classes_def, listTheory.EVERY_MEM] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem phi_origin_tagged_stage:
  !class_of inst next halting p q cells cells1.
    phi_origin_stage inst next halting p q cells cells1 /\
    phi_origin_tagged class_of cells /\
    class_of (Var (HD inst.inst_outputs)) = NONE ==>
    phi_origin_tagged class_of cells1
Proof
  rpt gen_tac >> rewrite_tac[phi_origin_stage_def, phi_origin_tagged_def] >>
  strip_tac >>
  `phi_origin_tagged class_of written` by
    (simp[phi_origin_tagged_def] >> gvs[] >>
     irule phi_origin_write_every >> simp[] >> fs[phi_origin_incoming_def]) >>
  Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next`
  >- (gvs[phi_origin_tagged_def] >> irule phi_origin_pop_every >> simp[]) >>
  gvs[phi_origin_tagged_def]
QED

Theorem phi_origin_classes_edits:
  !class_of cells keep d ret e.
    phi_origin_classes class_of cells /\ d < LENGTH cells /\
    e < LENGTH (phi_origin_write keep d ret cells) ==>
    phi_origin_classes class_of (phi_origin_write keep d ret cells) /\
    phi_origin_classes class_of
      (phi_origin_pop e (phi_origin_write keep d ret cells))
Proof
  rpt gen_tac >> simp[phi_origin_classes_def] >> strip_tac >>
  conj_asm1_tac
  >- (irule phi_origin_write_every >> simp[] >> goal_assum (drule_at Any)) >>
  irule phi_origin_pop_every >> simp[]
QED

Theorem phi_origin_classes_output_safe:
  !class_of cells ret.
    phi_origin_classes class_of cells /\ class_of ret = NONE ==>
    EVERY (\cell. !slot a b. cell = PhiOriginal slot a b ==>
      a = b \/ (a <> ret /\ b <> ret)) cells
Proof
  simp[phi_origin_classes_def, listTheory.EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!cell. MEM cell cells ==> _` drule >>
  disch_then (qspecl_then [`slot`, `a`, `b`] mp_tac) >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem phi_origin_classes_incoming_predicates:
  !class_of cells alternatives k.
    phi_origin_classes class_of cells /\
    (!op. MEM op alternatives <=> class_of op = SOME k) ==>
    EVERY (\cell. MEM (phi_cell_value T cell) alternatives <=>
                  MEM (phi_cell_value F cell) alternatives) cells
Proof
  simp[phi_origin_classes_def, listTheory.EVERY_MEM] >> rpt strip_tac >>
  Cases_on `cell` >> gvs[phi_cell_value_def] >> metis_tac[]
QED

Theorem phi_origin_classes_incoming_shield:
  !class_of cells alternatives k d p q.
    phi_origin_classes class_of cells /\
    (!op. MEM op alternatives <=> class_of op = SOME k) /\
    stack_get_phi_depth alternatives (MAP (phi_cell_value T) cells) = SOME d ==>
    stack_get_phi_depth alternatives (p ++ MAP (phi_cell_value T) cells) = SOME d /\
    stack_get_phi_depth alternatives (q ++ MAP (phi_cell_value F) cells) = SOME d
Proof
  rpt gen_tac >> strip_tac >>
  `stack_get_phi_depth alternatives (MAP (phi_cell_value T) cells) =
   stack_get_phi_depth alternatives (MAP (phi_cell_value F) cells)` by
    (rewrite_tac[stack_get_phi_depth_def] >>
     irule slot_realization_reverse_search >> BETA_TAC >>
     irule phi_origin_classes_incoming_predicates >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  metis_tac[fnPlanLineageSuffixTheory.stack_get_phi_depth_suffix_hit]
QED

Theorem phi_origin_alias_free_stage:
  !class_of inst next halting p q cells d keep.
    phi_origin_classes class_of cells /\
    class_of (Var (HD inst.inst_outputs)) = NONE /\
    phi_origin_incoming inst p q cells d /\
    phi_origin_selected next p q cells d keep ==>
    ?cells'. phi_origin_stage inst next halting p q cells cells' /\
             phi_origin_classes class_of cells'
Proof
  rpt gen_tac >> strip_tac >>
  `d < LENGTH cells` by gvs[phi_origin_incoming_def] >>
  `EVERY (\cell. !slot a b. cell = PhiOriginal slot a b ==>
      a = b \/ (a <> Var (HD inst.inst_outputs) /\
                b <> Var (HD inst.inst_outputs))) cells` by
    (irule phi_origin_classes_output_safe >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all phi_origin_write_output_shield >>
  disch_then (qspecl_then [`keep`, `p`, `q`] strip_assume_tac) >>
  drule_all phi_origin_classes_edits >> strip_tac >>
  Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next`
  >- (qexists_tac `phi_origin_pop e (phi_origin_write keep d
        (Var (HD inst.inst_outputs)) cells)` >> simp[phi_origin_stage_def] >>
      qexistsl_tac [`d`, `keep`] >> simp[] >> metis_tac[]) >>
  qexists_tac `phi_origin_write keep d (Var (HD inst.inst_outputs)) cells` >>
  simp[phi_origin_stage_def] >> qexistsl_tac [`d`, `keep`] >> simp[]
QED

Theorem phi_origin_classes_selected_cell:
  !class_of cells cell k next.
    phi_origin_classes class_of cells /\ MEM cell cells /\
    class_of (phi_cell_value T cell) = SOME k /\
    (!op. class_of op = SOME k ==> ~MEM (operand_to_string op) next) ==>
    (MEM (operand_to_string (phi_cell_value T cell)) next <=>
     MEM (operand_to_string (phi_cell_value F cell)) next)
Proof
  simp[phi_origin_classes_def, listTheory.EVERY_MEM] >> rpt strip_tac >>
  Cases_on `cell` >> gvs[phi_cell_value_def] >> metis_tac[]
QED

Theorem stack_poke_preserves_other_member:
  !cells x d y.
    MEM x cells /\ x <> stack_peek d cells ==>
    MEM x (stack_poke d y cells)
Proof
  rpt gen_tac >> strip_tac >>
  `?j. j < LENGTH cells /\ EL j cells = x` by metis_tac[listTheory.MEM_EL] >>
  `j <> LENGTH cells - (d + 1)` by
    (strip_tac >> gvs[stack_peek_def]) >>
  `EL j (stack_poke d y cells) = x` by
    simp[stack_poke_def, listTheory.EL_LUPDATE] >>
  metis_tac[listTheory.EL_MEM, listTheory.LENGTH_LUPDATE, stack_poke_def]
QED

Theorem phi_origin_write_preserves_other_member:
  !cells x d ret keep.
    MEM x cells /\ x <> stack_peek d cells ==>
    MEM x (phi_origin_write keep d ret cells)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `keep`
  >- (simp[phi_origin_write_def, stack_poke_def, stack_dup_def,
           listTheory.MEM_LUPDATE] >>
      `?j. j < LENGTH cells /\ EL j cells = x` by metis_tac[listTheory.MEM_EL] >>
      disj2_tac >> qexists_tac `j` >> simp[listTheory.EL_SNOC]) >>
  simp[phi_origin_write_def, stack_poke_preserves_other_member]
QED

Theorem phi_origin_pop_preserves_other_member:
  !cells x d.
    d < LENGTH cells /\ MEM x cells /\ x <> stack_peek d cells ==>
    MEM x (phi_origin_pop d cells)
Proof
  rpt gen_tac >> strip_tac >>
  `?j. j < LENGTH cells /\ EL j cells = x` by metis_tac[listTheory.MEM_EL] >>
  `j <> LENGTH cells - (d + 1)` by
    (strip_tac >> gvs[stack_peek_def]) >>
  Cases_on `j = LENGTH cells - 1`
  >- (`0 < d` by decide_tac >>
      `LENGTH cells - (d + 1) < LENGTH cells - 1` by decide_tac >>
      `EL (LENGTH cells - (d + 1)) (phi_origin_pop d cells) = x` by
        (simp[phi_origin_pop_def, stack_pop_def, stack_swap_def,
             listTheory.EL_TAKE, listTheory.EL_LUPDATE] >> metis_tac[]) >>
      `LENGTH (phi_origin_pop d cells) = LENGTH cells - 1` by
        simp[phi_origin_pop_def, stack_pop_def, stack_swap_def] >>
      metis_tac[listTheory.EL_MEM]) >>
  `j < LENGTH cells - 1` by decide_tac >>
  `EL j (phi_origin_pop d cells) = x` by
    simp[phi_origin_pop_def, stack_pop_def, stack_swap_def,
         listTheory.EL_TAKE, listTheory.EL_LUPDATE] >>
  `LENGTH (phi_origin_pop d cells) = LENGTH cells - 1` by
    simp[phi_origin_pop_def, stack_pop_def, stack_swap_def] >>
  metis_tac[listTheory.EL_MEM]
QED

Theorem stack_peek_suffix_map:
  !d prefix f cells. d < LENGTH cells ==>
    stack_peek d (prefix ++ MAP f cells) = f (stack_peek d cells)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH prefix + LENGTH cells - (d + 1) =
   LENGTH prefix + (LENGTH cells - (d + 1))` by decide_tac >>
  `LENGTH cells - (d + 1) < LENGTH cells` by decide_tac >>
  pure_rewrite_tac[stack_peek_def, listTheory.LENGTH_APPEND, listTheory.LENGTH_MAP] >>
  qpat_x_assum `_ = LENGTH prefix + _`
    (fn th => pure_once_rewrite_tac[th]) >>
  simp[listTheory.EL_APPEND_EQN, listTheory.EL_MAP]
QED

Theorem phi_origin_classes_selected:
  !class_of cells d k next p q.
    phi_origin_classes class_of cells /\ d < LENGTH cells /\
    class_of (phi_cell_value T (stack_peek d cells)) = SOME k /\
    (!op. class_of op = SOME k ==> ~MEM (operand_to_string op) next) ==>
    phi_origin_selected next p q cells d F
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (stack_peek d cells) cells` by
    (simp[stack_peek_def] >> irule listTheory.EL_MEM >> decide_tac) >>
  drule_all phi_origin_classes_selected_cell >> strip_tac >>
  simp[phi_origin_selected_def, stack_peek_suffix_map] >> metis_tac[]
QED

Theorem phi_origin_future_member_survives:
  !class_of cells x d ret keep k j e p.
    MEM x cells /\ class_of (phi_cell_value T x) = SOME j /\
    class_of (phi_cell_value T (stack_peek d cells)) = SOME k /\ j <> k /\
    class_of ret = NONE /\
    e < LENGTH (phi_origin_write keep d ret cells) /\
    stack_get_depth ret
      (p ++ MAP (phi_cell_value T) (phi_origin_write keep d ret cells)) = SOME e ==>
    MEM x (phi_origin_write keep d ret cells) /\
    MEM x (phi_origin_pop e (phi_origin_write keep d ret cells))
Proof
  rpt gen_tac >> strip_tac >>
  `x <> stack_peek d cells` by (strip_tac >> gvs[]) >>
  `MEM x (phi_origin_write keep d ret cells)` by
    metis_tac[phi_origin_write_preserves_other_member] >>
  drule stack_get_depth_props >> strip_tac >>
  `phi_cell_value T (stack_peek e (phi_origin_write keep d ret cells)) = ret` by
    metis_tac[stack_peek_suffix_map] >>
  `x <> stack_peek e (phi_origin_write keep d ret cells)` by
    metis_tac[optionTheory.NOT_NONE_SOME] >>
  simp[] >> irule phi_origin_pop_preserves_other_member >> simp[]
QED

Theorem phi_origin_classes_incoming_covered:
  !class_of cells alternatives k cell p q.
    phi_origin_classes class_of cells /\
    (!op. MEM op alternatives <=> class_of op = SOME k) /\
    MEM cell cells /\ class_of (phi_cell_value T cell) = SOME k ==>
    ?d. d < LENGTH cells /\
      stack_get_phi_depth alternatives (p ++ MAP (phi_cell_value T) cells) = SOME d /\
      stack_get_phi_depth alternatives (q ++ MAP (phi_cell_value F) cells) = SOME d
Proof
  rpt gen_tac >> strip_tac >>
  `MEM T (MAP (\c. MEM (phi_cell_value T c) alternatives) cells)` by
    (simp[listTheory.MEM_MAP] >> qexists_tac `cell` >> simp[]) >>
  `IS_SOME (stack_get_depth T
     (MAP (\c. MEM (phi_cell_value T c) alternatives) cells))` by
    simp[stack_get_depth_is_some] >>
  `stack_get_depth T (MAP (\c. MEM (phi_cell_value T c) alternatives) cells) =
   stack_get_phi_depth alternatives (MAP (phi_cell_value T) cells)` by
    (rewrite_tac[stack_get_depth_def, stack_get_phi_depth_def] >>
     irule slot_realization_reverse_search >> simp[]) >>
  Cases_on `stack_get_depth T
    (MAP (\c. MEM (phi_cell_value T c) alternatives) cells)` >> gvs[] >>
  `stack_get_depth T
    (MAP (\c. MEM (phi_cell_value T c) alternatives) cells) = SOME x` by
      (simp[] >> metis_tac[]) >>
  drule stack_get_depth_props >> strip_tac >>
  qexists_tac `x` >> conj_tac >- gvs[] >>
  irule phi_origin_classes_incoming_shield >>
  conj_tac >- metis_tac[] >> qexistsl_tac [`class_of`, `k`] >> simp[]
QED

Theorem phi_origin_incoming_class:
  !class_of inst p q cells d k.
    phi_origin_incoming inst p q cells d /\ d < LENGTH cells /\
    (!op. MEM op (FILTER is_var_operand inst.inst_operands) <=>
      class_of op = SOME k) ==>
    class_of (phi_cell_value T (stack_peek d cells)) = SOME k
Proof
  rpt gen_tac >> strip_tac >>
  `stack_get_depth T (MAP (\op. MEM op (FILTER is_var_operand inst.inst_operands))
       (p ++ MAP (phi_cell_value T) cells)) = SOME d` by
    (`stack_get_depth T (MAP (\op. MEM op (FILTER is_var_operand inst.inst_operands))
          (p ++ MAP (phi_cell_value T) cells)) =
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
          (p ++ MAP (phi_cell_value T) cells)` by
       (rewrite_tac[stack_get_depth_def, stack_get_phi_depth_def] >>
        irule stack_find_predicate_vector >>
        simp[listTheory.MAP_REVERSE, listTheory.MAP_MAP_o, combinTheory.o_DEF]) >>
     metis_tac[phi_origin_incoming_def]) >>
  drule stack_get_depth_props >> strip_tac >>
  qpat_x_assum `stack_peek d (MAP _ _) = T` mp_tac >>
  `MAP (\op. MEM op (FILTER is_var_operand inst.inst_operands))
      (p ++ MAP (phi_cell_value T) cells) =
    MAP (\op. MEM op (FILTER is_var_operand inst.inst_operands)) p ++
    MAP (\c. MEM (phi_cell_value T c) (FILTER is_var_operand inst.inst_operands)) cells`
     by simp[listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  simp[stack_peek_suffix_map]
QED

Theorem phi_origin_stage_from_classes:
  !class_of cells inst next halting k cell p q.
    phi_origin_classes class_of cells /\
    (!op. MEM op (FILTER is_var_operand inst.inst_operands) <=>
          class_of op = SOME k) /\
    class_of (Var (HD inst.inst_outputs)) = NONE /\
    (!op. class_of op = SOME k ==> ~MEM (operand_to_string op) next) /\
    MEM cell cells /\ class_of (phi_cell_value T cell) = SOME k ==>
    ?cells'. phi_origin_stage inst next halting p q cells cells' /\
      phi_origin_classes class_of cells' /\
      (!x j. MEM x cells /\ class_of (phi_cell_value T x) = SOME j /\ j <> k ==>
        MEM x cells')
Proof
  rpt gen_tac >> strip_tac >>
  drule_all phi_origin_classes_incoming_covered >>
  disch_then (qspecl_then [`p`, `q`] strip_assume_tac) >>
  `phi_origin_incoming inst p q cells d` by simp[phi_origin_incoming_def] >>
  `class_of (phi_cell_value T (stack_peek d cells)) = SOME k` by
    (irule phi_origin_incoming_class >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `phi_origin_selected next p q cells d F` by
    (irule phi_origin_classes_selected >> goal_assum (drule_at Any) >>
     qexistsl_tac [`class_of`, `k`] >> simp[]) >>
  `EVERY (\c. !slot a b. c = PhiOriginal slot a b ==>
      a = b \/ (a <> Var (HD inst.inst_outputs) /\
                b <> Var (HD inst.inst_outputs))) cells` by
    (irule phi_origin_classes_output_safe >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all phi_origin_write_output_shield >>
  disch_then (qspecl_then [`F`, `p`, `q`] strip_assume_tac) >>
  drule_all phi_origin_classes_edits >> strip_tac >>
  `!x j. MEM x cells /\ class_of (phi_cell_value T x) = SOME j /\ j <> k ==>
     MEM x (phi_origin_write F d (Var (HD inst.inst_outputs)) cells) /\
     MEM x (phi_origin_pop e (phi_origin_write F d (Var (HD inst.inst_outputs)) cells))` by
    (rpt gen_tac >> strip_tac >>
     irule (INST_TYPE [alpha |-> numSyntax.num] phi_origin_future_member_survives) >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac >- (qexistsl_tac [`class_of`, `j`, `k`] >> simp[]) >>
     qexists_tac `p` >> simp[]) >>
  Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next`
  >- (qexists_tac `phi_origin_pop e (phi_origin_write F d
        (Var (HD inst.inst_outputs)) cells)` >> simp[] >>
      simp[phi_origin_stage_def] >> qexistsl_tac [`d`, `F`] >> simp[] >> metis_tac[]) >>
  qexists_tac `phi_origin_write F d (Var (HD inst.inst_outputs)) cells` >>
  simp[] >> simp[phi_origin_stage_def] >> qexistsl_tac [`d`, `F`] >> simp[]
QED

Theorem phi_origin_schedule_from_classes:
  !steps n class_of cells p q.
    phi_origin_classes class_of cells /\
    (!i inst next halting. i < LENGTH steps /\ EL i steps = (inst,next,halting) ==>
      (!op. MEM op (FILTER is_var_operand inst.inst_operands) <=>
            class_of op = SOME (n+i)) /\
      class_of (Var (HD inst.inst_outputs)) = NONE /\
      (!op. class_of op = SOME (n+i) ==> ~MEM (operand_to_string op) next)) /\
    (!i. i < LENGTH steps ==> ?cell. MEM cell cells /\
      class_of (phi_cell_value T cell) = SOME (n+i)) ==>
    ?cells_end. phi_origin_schedule_ready steps p q cells cells_end /\
      phi_origin_classes class_of cells_end
Proof
  Induct >- simp[phi_origin_schedule_ready_def] >>
  Cases_on `h` >> Cases_on `r` >> rename1 `(inst,next,halting)::steps` >>
  rpt gen_tac >> strip_tac >>
  `(!op. MEM op (FILTER is_var_operand inst.inst_operands) <=> class_of op = SOME n) /\
   class_of (Var (HD inst.inst_outputs)) = NONE /\
   (!op. class_of op = SOME n ==> ~MEM (operand_to_string op) next)` by
    (qpat_x_assum `!i inst next halting. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `?cell. MEM cell cells /\ class_of (phi_cell_value T cell) = SOME n` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all phi_origin_stage_from_classes >>
  disch_then (qspecl_then [`halting`, `p`, `q`] strip_assume_tac) >>
  first_x_assum (qspecl_then [`SUC n`, `class_of`, `cells'`, `p`, `q`] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac
      >- (rpt gen_tac >> strip_tac >>
          qpat_x_assum `!i inst next halting. _` (qspec_then `SUC i` mp_tac) >>
          simp[arithmeticTheory.ADD_CLAUSES]) >>
      rpt strip_tac >>
      qpat_x_assum `!i. i < LENGTH (_::_) ==> _` (qspec_then `SUC i` mp_tac) >>
      simp[arithmeticTheory.ADD_CLAUSES] >> strip_tac >>
      qexists_tac `cell'` >> simp[] >>
      first_x_assum irule >> qexists_tac `SUC (n+i)` >> simp[]) >>
  strip_tac >> qexists_tac `cells_end` >> simp[phi_origin_schedule_ready_def] >>
  qexists_tac `cells'` >> simp[]
QED

(* Alias-free symbolic validation ledger (supersedes the open local
   output-ordering question recorded above; NOT global schedule production).

   Static induction certificate (abstract producer checked above):
   - one fixed operand-to-incoming-class map class_of; each unequal Original
     retains two representatives of its indexed class, while equal originals
     and Common cells are unrestricted (phi_origin_classes);
   - for every unprocessed PHI class, a cell in the physical suffix whose
     left realization is in that class; alternatives are exactly the class;
   - all PHI output operands map to NONE; current incoming class is dead in
     the current next-live set. Residuals p,q are completely unrestricted.
   This does not mention future searches, operation equality or stage guards.

   Checked symbolic interfaces, with no bound on physical stack depth:
   - classes_incoming_covered derives a bounded common first hit from class
     exactness and ONE representative, using slot_realization_reverse_search;
   - classes_selected derives keep=F from class death at a selected cell;
     equal live-through cells are allowed, not silently assumed fresh;
   - write_output_shield supplies a common bounded ret hit after either write
     branch. Unequal Original cells cannot intercept ret; earlier equal cells
     may intercept it identically. Arbitrary residuals cannot intercept it;
   - alias_free_stage witnesses the actual write and optional retirement and
     preserves the static class certificate, composing the existing stage;
   - future_member_survives protects each different-class representative
     through overwrite and retirement. No Original is discarded on death.
     These are membership/safety interfaces, not physical-order deletion rules.

   Producer/assembly status (updated after E0096):
   1. Native class construction and operand exactness are discharged in
      fnPlanLineagePhiClasses and fnPlanLineagePhiMaps; reuse these boundaries
      rather than introducing a second map implementation.
   2. Common physical cell suffix production is discharged by
      successful_join_edges_common_cells (fnPlanLineageJoinEntry) and
      lineage_dfs_join_common_cells (after the frozen lineage declarations).
      These derive actual successful predecessor origins and edge totality;
      they do not restrict lower prefixes or spilled maps. Connecting the
      independent activation coverage to the evolving temporal schedule
      remains assembly work, not another assumed entry correspondence.
   3. Derive output class_of=NONE using the accepted global
      reachable_phi_prefix_no_output_use_alias, and derive current class death
      using analyzed_phi_incoming_dead_after. The abstract class premises in
      the lemmas above do NOT discharge these analyzed producer obligations.
   4. phi_origin_stage_from_classes now derives the selected-cell class,
      common searches and preservation of every other-class member.
      phi_origin_schedule_from_classes composes these stages for arbitrary
      schedules from static coverage, exactness, output exclusion and death.
      Instantiating those premises for the native analyzed schedule remains
      separate work; predicate safety alone is not entry coverage.
   5. Final physical suffix, live-through layout, cleanup/window bounds,
      persistent spill maps, allocation history, join reset and DFS/lineage
      lifting remain independent global obligations. Observation-frame and
      stage projections do not prove spill-map equality.
*)

Theorem do_dup_state_frame:
  !d ps. SND (do_dup d ps) = ps with
    <|ps_stack := (SND (do_dup d ps)).ps_stack;
      ps_alloc := (SND (do_dup d ps)).ps_alloc|>
Proof
  rpt gen_tac >> simp[do_dup_def] >>
  Cases_on `d <= 15` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> simp[]
QED

Theorem do_swap_state_frame:
  !d ps. SND (do_swap d ps) = ps with
    <|ps_stack := (SND (do_swap d ps)).ps_stack;
      ps_alloc := (SND (do_swap d ps)).ps_alloc|>
Proof
  rpt gen_tac >> simp[do_swap_def] >>
  Cases_on `d = 0` >> simp[] >>
  Cases_on `d <= 16` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> simp[]
QED

Theorem popmany_singleton_state_frame:
  !ret ps. SND (popmany_plan [ret] ps) = ps with
    <|ps_stack := (SND (popmany_plan [ret] ps)).ps_stack;
      ps_alloc := (SND (popmany_plan [ret] ps)).ps_alloc|>
Proof
  rpt gen_tac >> Cases_on `stack_get_depth ret ps.ps_stack`
  >- simp[popmany_plan_def, popmany_individual_def, QSORT_DEF, PARTITION_DEF, PART_DEF] >>
  mp_tac (Q.SPECL [`x`, `ps`] do_swap_state_frame) >>
  simp[popmany_plan_def, popmany_individual_def, is_contiguous_top_def,
       QSORT_DEF, PARTITION_DEF, PART_DEF] >>
  Cases_on `x = 1` >> simp[] >>
  Cases_on `x = 0` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[stackPlanTypesTheory.plan_state_component_equality]
QED

Theorem phi_write_phase_state_frame:
  !inst next d ps. SND (phi_write_phase inst next d ps) = ps with
    <|ps_stack := (SND (phi_write_phase inst next d ps)).ps_stack;
      ps_alloc := (SND (phi_write_phase inst next d ps)).ps_alloc|>
Proof
  rpt gen_tac >> mp_tac (Q.SPECL [`d`, `ps`] do_dup_state_frame) >>
  simp[phi_write_phase_def] >>
  Cases_on `MEM (operand_to_string (stack_peek d ps.ps_stack)) next` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[stackPlanTypesTheory.plan_state_component_equality]
QED

Theorem generate_phi_plan_state_frame:
  !inst next halting ps. SND (generate_phi_plan inst next halting ps) = ps with
    <|ps_stack := (SND (generate_phi_plan inst next halting ps)).ps_stack;
      ps_alloc := (SND (generate_phi_plan inst next halting ps)).ps_alloc|>
Proof
  rpt gen_tac >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- simp[generate_phi_plan_def] >>
  drule generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`next`, `halting`] assume_tac) >>
  mp_tac (Q.SPECL [`inst`, `next`, `x`, `ps`] phi_write_phase_state_frame) >>
  Cases_on `phi_write_phase inst next x ps` >> gvs[] >>
  mp_tac (Q.SPECL [`Var (HD inst.inst_outputs)`, `r`] popmany_singleton_state_frame) >>
  Cases_on `popmany_plan [Var (HD inst.inst_outputs)] r` >> gvs[] >>
  Cases_on `halting` >> simp[] >>
  Cases_on `MEM (HD inst.inst_outputs) next` >> simp[] >>
  simp[stackPlanTypesTheory.plan_state_component_equality]
QED

Theorem phi_schedule_run_state_frame:
  !steps ps. SND (phi_schedule_run steps ps) = ps with
    <|ps_stack := (SND (phi_schedule_run steps ps)).ps_stack;
      ps_alloc := (SND (phi_schedule_run steps ps)).ps_alloc|>
Proof
  Induct >> simp[phi_schedule_run_def] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  mp_tac (Q.SPECL [`h0`, `h1`, `h2`, `ps`] generate_phi_plan_state_frame) >>
  Cases_on `generate_phi_plan h0 h1 h2 ps` >> gvs[] >>
  first_x_assum (qspec_then `r` mp_tac) >>
  simp[phi_schedule_run_def] >>
  Cases_on `phi_schedule_run steps r` >> gvs[] >>
  simp[stackPlanTypesTheory.plan_state_component_equality]
QED

Theorem phi_origin_schedule_state_replay:
  !steps p q cells cells_end ps qs.
    phi_origin_schedule_ready steps p q cells cells_end /\
    ps.ps_stack = p ++ MAP (phi_cell_value T) cells /\
    qs.ps_stack = q ++ MAP (phi_cell_value F) cells /\
    ps.ps_alloc = qs.ps_alloc ==>
    ?ops al.
      phi_schedule_run steps ps =
        (ops, ps with <|ps_stack := p ++ MAP (phi_cell_value T) cells_end; ps_alloc := al|>) /\
      phi_schedule_run steps qs =
        (ops, qs with <|ps_stack := q ++ MAP (phi_cell_value F) cells_end; ps_alloc := al|>)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all phi_origin_schedule_trace >> strip_tac >>
  drule phi_origin_trace_final_stacks >> strip_tac >>
  drule_all phi_origin_schedule_replay >> strip_tac >>
  qspec_then `ps` mp_tac (Q.SPEC `steps` phi_schedule_run_state_frame) >>
  qspec_then `qs` mp_tac (Q.SPEC `steps` phi_schedule_run_state_frame) >>
  Cases_on `phi_schedule_run steps ps` >>
  Cases_on `phi_schedule_run steps qs` >> gvs[] >>
  rpt strip_tac >> goal_assum (drule_at Any) >> simp[]
QED

Theorem phi_origin_classes_filter_projection:
  !class_of cells live.
    phi_origin_classes class_of cells /\
    (!op k. class_of op = SOME k ==> ~live op) ==>
    FILTER live (MAP (phi_cell_value T) cells) =
    FILTER live (MAP (phi_cell_value F) cells)
Proof
  gen_tac >> Induct >> simp[phi_origin_classes_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `h` >>
  gvs[phi_cell_value_def] >> metis_tac[]
QED

Theorem phi_origin_classes_mark_projection:
  !class_of cells live.
    phi_origin_classes class_of cells /\
    (!op k. class_of op = SOME k ==> ~live op) ==>
    MAP (\op. if live op then op else dead_stack_marker) (MAP (phi_cell_value T) cells) =
    MAP (\op. if live op then op else dead_stack_marker) (MAP (phi_cell_value F) cells)
Proof
  gen_tac >> Induct >> simp[phi_origin_classes_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `h` >>
  gvs[phi_cell_value_def] >> metis_tac[]
QED

(* Single-stage extinction is about surviving origins, not DFG roots.
   before/after encode uniqueness of the selected tag; lower prefixes are
   unrestricted and are not removed by this interface. *)
Theorem phi_origin_write_selected_extinction:
  !before after i a b ret.
    EVERY (\c. !x y. c <> PhiOriginal i x y) before /\
    EVERY (\c. !x y. c <> PhiOriginal i x y) after ==>
    EVERY (\c. !x y. c <> PhiOriginal i x y)
      (phi_origin_write F (LENGTH after) ret
        (before ++ [PhiOriginal i a b] ++ after))
Proof
  rpt strip_tac >>
  simp[phi_origin_write_def, stack_poke_def, LENGTH_APPEND] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.LUPDATE_APPEND2, listTheory.LUPDATE_def]
QED

Theorem phi_origin_stage_every:
  !P inst next halting p q cells cells1.
    phi_origin_stage inst next halting p q cells cells1 /\
    EVERY P cells /\ (!op. P (PhiCommon op)) ==>
    EVERY P cells1
Proof
  rpt gen_tac >> rewrite_tac[phi_origin_stage_def] >> strip_tac >>
  `EVERY P written` by
    (gvs[] >> irule phi_origin_write_every >> fs[phi_origin_incoming_def]) >>
  Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next`
  >- (gvs[] >> irule phi_origin_pop_every >> simp[]) >>
  gvs[]
QED

Theorem phi_origin_stage_selected_extinction:
  !inst next halting p q before after i a b cells1.
    EVERY (\c. !x y. c <> PhiOriginal i x y) before /\
    EVERY (\c. !x y. c <> PhiOriginal i x y) after /\
    phi_origin_incoming inst p q (before ++ [PhiOriginal i a b] ++ after) (LENGTH after) /\
    phi_origin_selected next p q (before ++ [PhiOriginal i a b] ++ after) (LENGTH after) F /\
    phi_origin_stage inst next halting p q
      (before ++ [PhiOriginal i a b] ++ after) cells1 ==>
    EVERY (\c. !x y. c <> PhiOriginal i x y) cells1
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `phi_origin_stage _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[phi_origin_stage_def] >> strip_tac >>
  `d = LENGTH after` by fs[phi_origin_incoming_def] >>
  `keep = F` by fs[phi_origin_selected_def] >>
  gvs[] >>
  `EVERY (\c. !x y. c <> PhiOriginal i x y)
    (phi_origin_write F (LENGTH after) (Var (HD inst.inst_outputs))
      (before ++ [PhiOriginal i a b] ++ after))` by
    (irule phi_origin_write_selected_extinction >> simp[]) >>
  Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next`
  >- (gvs[] >> irule phi_origin_pop_every >> simp[]) >>
  gvs[]
QED

Theorem phi_origin_keep_retains_selected:
  phi_origin_write T 0 (Var "out") [PhiOriginal 0 (Var "a") (Var "b")] =
    [PhiOriginal 0 (Var "a") (Var "b"); PhiCommon (Var "out")]
Proof
  EVAL_TAC
QED

(* Extinction probe premise ledger:
   - phi_origin_stage_selected_extinction encodes a unique selected tag by
     before/after EVERY exclusion, and binds the actual search using
     phi_origin_incoming at LENGTH after.  Determinism of that search and
     phi_origin_selected forces each stage witness to use that depth and F.
   - phi_origin_classes_selected supplies the selected branch agreement;
     analyzed_native_phi_class_dead_after / _dead_range in PhiClasses supply
     native class death at analyzed indices.  Integrating these with a
     still-present unique Original at the selected depth is NOT done here.
   - phi_slot_step (PhiSlots) emits INR i only when i is absent from placed,
     immediately adding i to placed.  Thus its fold suppresses repeated i;
     no universal multiplicity producer theorem is asserted by this audit.
   - keep=T duplicates then pokes the new top: the old Original survives,
     as the negative-control equation certifies.  keep=F overwrites it.
     A pop only permutes/deletes.  phi_origin_stage_every specializes to
     exclusion of any absent Original, hence certifies no new Original tag
     even in keep=T stages; it does not prevent copying an existing tag.
   - Arbitrary p/q lower prefixes remain untouched and unrestricted.  Tag
     extinction in the suffix does not establish prefix shielding, native
     schedule existence, root exclusion, or ordinary-instruction replay. *)

Definition phi_origin_count_def:
  phi_origin_count i cells = LENGTH (FILTER (\c.
    case c of PhiOriginal j a b => j = i | PhiCommon op => F) cells)
End

Theorem phi_origin_count_zero:
  !i cells. phi_origin_count i cells = 0 <=>
    EVERY (\c. !x y. c <> PhiOriginal i x y) cells
Proof
  gen_tac >> Induct >> simp[phi_origin_count_def] >>
  Cases_on `h` >> simp[] >> Cases_on `n = i` >> gvs[phi_origin_count_def]
QED

Theorem phi_origin_count_split_unique:
  !i before after a b.
    phi_origin_count i (before ++ [PhiOriginal i a b] ++ after) <= 1 ==>
    EVERY (\c. !x y. c <> PhiOriginal i x y) before /\
    EVERY (\c. !x y. c <> PhiOriginal i x y) after
Proof
  rpt gen_tac >> rewrite_tac[GSYM phi_origin_count_zero] >>
  simp[phi_origin_count_def, listTheory.FILTER_APPEND_DISTRIB] >>
  rewrite_tac[GSYM listTheory.LENGTH_NIL] >> decide_tac
QED

Theorem phi_origin_count_reverse:
  !i cells. phi_origin_count i (REVERSE cells) = phi_origin_count i cells
Proof
  simp[phi_origin_count_def, listTheory.FILTER_REVERSE]
QED

Theorem filter_lupdate_count:
  !xs n P x. n < LENGTH xs ==>
    LENGTH (FILTER P (LUPDATE x n xs)) + (if P (EL n xs) then 1 else 0) =
    LENGTH (FILTER P xs) + (if P x then 1 else 0)
Proof
  Induct >> simp[] >> Cases_on `n` >> simp[listTheory.LUPDATE_def] >> rpt strip_tac
  >- (Cases_on `P h` >> Cases_on `P x` >> simp[]) >>
  first_x_assum drule >> disch_then (qspecl_then [`P`, `x`] mp_tac) >>
  Cases_on `P h` >> Cases_on `P x` >> simp[] >> decide_tac
QED

Theorem filter_take_count_le:
  !xs n P. LENGTH (FILTER P (TAKE n xs)) <= LENGTH (FILTER P xs)
Proof
  Induct >> Cases_on `n` >> simp[] >> rpt gen_tac >>
  Cases_on `P h` >> simp[]
QED

Theorem phi_origin_write_keep:
  !d ret cells. phi_origin_write T d ret cells = cells ++ [PhiCommon ret]
Proof
  simp[phi_origin_write_def, stack_poke_def, stack_dup_def,
    listTheory.SNOC_APPEND, rich_listTheory.LUPDATE_APPEND2, listTheory.LUPDATE_def]
QED

Theorem filter_stack_swap_count:
  !P d xs. LENGTH (FILTER P (stack_swap d xs)) = LENGTH (FILTER P xs)
Proof
  rpt gen_tac >> Cases_on `xs = []` >- gvs[stack_swap_def, listTheory.LUPDATE_def] >>
  `LENGTH xs - 1 < LENGTH xs /\ LENGTH xs - 1 - d < LENGTH xs` by
    (Cases_on `xs` >> gvs[]) >>
  qspecl_then [`xs`, `LENGTH xs - 1`, `P`, `EL (LENGTH xs - 1 - d) xs`]
    mp_tac filter_lupdate_count >> simp[] >> strip_tac >>
  qspecl_then [`LUPDATE (EL (LENGTH xs - 1 - d) xs) (LENGTH xs - 1) xs`,
    `LENGTH xs - 1 - d`, `P`, `EL (LENGTH xs - 1) xs`]
    mp_tac filter_lupdate_count >>
  simp[listTheory.EL_LUPDATE, stack_swap_def] >>
  Cases_on `P (EL (LENGTH xs - 1) xs)` >>
  Cases_on `P (EL (LENGTH xs - 1 - d) xs)` >> gvs[] >> decide_tac
QED

Theorem phi_origin_write_count_le:
  !i keep d ret cells.
    phi_origin_count i (phi_origin_write keep d ret cells) <= phi_origin_count i cells
Proof
  rpt gen_tac >> Cases_on `keep`
  >- simp[phi_origin_write_keep, phi_origin_count_def, listTheory.FILTER_APPEND_DISTRIB] >>
  simp[phi_origin_write_def, stack_poke_def, phi_origin_count_def] >>
  Cases_on `LENGTH cells - 1 - d < LENGTH cells`
  >- (drule filter_lupdate_count >>
      disch_then (qspecl_then [`\c. case c of PhiOriginal j a b => j = i | PhiCommon op => F`,
                              `PhiCommon ret`] mp_tac) >> simp[] >> decide_tac) >>
  Cases_on `cells` >> gvs[listTheory.LUPDATE_def]
QED

Theorem phi_origin_pop_count_le:
  !i d cells. phi_origin_count i (phi_origin_pop d cells) <= phi_origin_count i cells
Proof
  rpt gen_tac >> simp[phi_origin_pop_def, phi_origin_count_def, stack_pop_def] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  irule_at Any filter_take_count_le >> simp[filter_stack_swap_count]
QED

Theorem phi_origin_stage_count_le:
  !inst next halting p q cells cells1 i.
    phi_origin_stage inst next halting p q cells cells1 ==>
    phi_origin_count i cells1 <= phi_origin_count i cells
Proof
  rpt gen_tac >> rewrite_tac[phi_origin_stage_def] >> strip_tac >>
  `phi_origin_count i written <= phi_origin_count i cells` by
    (gvs[] >> irule phi_origin_write_count_le) >>
  Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next`
  >- (gvs[] >> irule arithmeticTheory.LESS_EQ_TRANS >>
      goal_assum (drule_at Any) >> irule phi_origin_pop_count_le) >>
  gvs[]
QED

Theorem phi_origin_stage_unique:
  !inst next halting p q cells cells1 i.
    phi_origin_stage inst next halting p q cells cells1 /\
    phi_origin_count i cells <= 1 ==>
    phi_origin_count i cells1 <= 1
Proof
  rpt strip_tac >> drule phi_origin_stage_count_le >>
  disch_then (qspec_then `i` mp_tac) >> decide_tac
QED

Theorem phi_origin_tagged_stage_extinction:
  !class_of cells k inst next halting p q cells1.
    phi_origin_tagged class_of cells /\ phi_origin_count k cells <= 1 /\
    (!op. MEM op (FILTER is_var_operand inst.inst_operands) <=>
          class_of op = SOME k) /\
    (!op. class_of op = SOME k ==> ~MEM (operand_to_string op) next) /\
    phi_origin_stage inst next halting p q cells cells1 ==>
    phi_origin_count k cells1 = 0
Proof
  rpt gen_tac >> strip_tac >>
  `phi_origin_classes class_of cells` by metis_tac[phi_origin_tagged_classes] >>
  qpat_assum `phi_origin_stage _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[phi_origin_stage_def] >> strip_tac >>
  `d < LENGTH cells` by fs[phi_origin_incoming_def] >>
  `class_of (phi_cell_value T (stack_peek d cells)) = SOME k` by
    (irule phi_origin_incoming_class >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `phi_origin_selected next p q cells d F` by
    (irule phi_origin_classes_selected >> goal_assum (drule_at Any) >>
     qexistsl_tac [`class_of`, `k`] >> simp[]) >>
  `keep = F` by fs[phi_origin_selected_def] >>
  `MEM (stack_peek d cells) cells` by
    (simp[stack_peek_def] >> irule listTheory.EL_MEM >> decide_tac) >>
  `?a b. stack_peek d cells = PhiOriginal k a b` by
    (qpat_assum `phi_origin_tagged _ _` mp_tac >>
     rewrite_tac[phi_origin_tagged_def, listTheory.EVERY_MEM] >>
     disch_then (qspec_then `stack_peek d cells` mp_tac) >>
     Cases_on `stack_peek d cells` >> gvs[phi_cell_value_def]) >>
  `phi_origin_count k written = 0` by
    (qspecl_then [`cells`, `LENGTH cells - 1 - d`,
       `\c. case c of PhiOriginal j a b => j = k | PhiCommon op => F`,
       `PhiCommon (Var (HD inst.inst_outputs))`] mp_tac filter_lupdate_count >>
     impl_tac >- decide_tac >>
     gvs[phi_origin_count_def, phi_origin_write_def, stack_poke_def, stack_peek_def] >>
     rewrite_tac[GSYM listTheory.LENGTH_NIL] >> decide_tac) >>
  Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next`
  >- (gvs[] >> qmatch_goalsub_abbrev_tac `phi_origin_pop e ws` >>
      qspecl_then [`k`, `e`, `ws`] mp_tac phi_origin_pop_count_le >>
      gvs[Abbr `ws`]) >>
  gvs[]
QED

Theorem phi_origin_schedule_count_le:
  !steps p q cells cells_end k.
    phi_origin_schedule_ready steps p q cells cells_end ==>
    phi_origin_count k cells_end <= phi_origin_count k cells
Proof
  Induct >- simp[phi_origin_schedule_ready_def] >>
  Cases_on `h` >> Cases_on `r` >>
  simp[phi_origin_schedule_ready_def] >> rpt strip_tac >>
  drule phi_origin_stage_count_le >> disch_then (qspec_then `k` assume_tac) >>
  first_x_assum drule >> disch_then (qspec_then `k` mp_tac) >> decide_tac
QED

Theorem phi_origin_tagged_schedule_extinction:
  !steps n class_of cells p q cells_end.
    phi_origin_schedule_ready steps p q cells cells_end /\
    phi_origin_tagged class_of cells /\
    (!k. phi_origin_count k cells <= 1) /\
    (!i inst next halting. i < LENGTH steps /\ EL i steps = (inst,next,halting) ==>
      (!op. MEM op (FILTER is_var_operand inst.inst_operands) <=>
            class_of op = SOME (n+i)) /\
      class_of (Var (HD inst.inst_outputs)) = NONE /\
      (!op. class_of op = SOME (n+i) ==> ~MEM (operand_to_string op) next)) ==>
    !i. i < LENGTH steps ==> phi_origin_count (n+i) cells_end = 0
Proof
  Induct >- simp[] >>
  Cases_on `h` >> Cases_on `r` >> rename1 `(inst,next,halting)::steps` >>
  rpt gen_tac >> strip_tac >>
  `(!op. MEM op (FILTER is_var_operand inst.inst_operands) <=> class_of op = SOME n) /\
   class_of (Var (HD inst.inst_outputs)) = NONE /\
   (!op. class_of op = SOME n ==> ~MEM (operand_to_string op) next)` by
    (qpat_assum `!i inst next halting. i < LENGTH (_::_) /\ _ ==> _`
       (qspecl_then [`0`, `inst`, `next`, `halting`] mp_tac) >>
     simp[NoAsms] >> metis_tac[]) >>
  qpat_x_assum `phi_origin_schedule_ready _ _ _ _ _` mp_tac >>
  simp[phi_origin_schedule_ready_def] >> strip_tac >>
  rename1 `phi_origin_stage inst next halting p q cells mid` >>
  `phi_origin_count n mid = 0` by
    (irule phi_origin_tagged_stage_extinction >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `phi_origin_tagged class_of mid` by
    (irule phi_origin_tagged_stage >> goal_assum (drule_at Any) >> simp[]) >>
  `!k. phi_origin_count k mid <= 1` by
    (gen_tac >> irule phi_origin_stage_unique >> goal_assum (drule_at Any) >> simp[]) >>
  `!i. i < LENGTH steps ==> phi_origin_count (SUC n+i) cells_end = 0` by
    (rpt strip_tac >> first_x_assum irule >> conj_tac >- simp[] >>
     qexistsl_tac [`mid`, `class_of`, `p`, `q`] >>
     simp[] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i inst next halting. i < LENGTH (_::_) /\ _ ==> _`
       (qspec_then `SUC i'` mp_tac) >>
     simp[arithmeticTheory.ADD_CLAUSES]) >>
  Cases
  >- (simp[] >> drule phi_origin_schedule_count_le >>
      disch_then (qspec_then `n` mp_tac) >> simp[]) >>
  simp[arithmeticTheory.ADD_CLAUSES] >> rpt strip_tac >>
  qpat_x_assum `!i. i < LENGTH steps ==> _` drule >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem phi_origin_tagged_schedule_projection:
  !steps n class_of cells p q cells_end.
    phi_origin_schedule_ready steps p q cells cells_end /\
    phi_origin_tagged class_of cells /\
    (!k. phi_origin_count k cells <= 1) /\
    (!i inst next halting. i < LENGTH steps /\ EL i steps = (inst,next,halting) ==>
      (!op. MEM op (FILTER is_var_operand inst.inst_operands) <=>
            class_of op = SOME (n+i)) /\
      class_of (Var (HD inst.inst_outputs)) = NONE /\
      (!op. class_of op = SOME (n+i) ==> ~MEM (operand_to_string op) next)) /\
    EVERY (\c. !k a b. c = PhiOriginal k a b ==>
      ?i. i < LENGTH steps /\ k = n+i) cells ==>
    MAP (phi_cell_value T) cells_end = MAP (phi_cell_value F) cells_end
Proof
  rpt gen_tac >> strip_tac >>
  `!i. i < LENGTH steps ==> phi_origin_count (n+i) cells_end = 0` by
    (rpt strip_tac >> irule phi_origin_tagged_schedule_extinction >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`cells`, `class_of`, `p`, `q`] >> metis_tac[]) >>
  `!k. phi_origin_count k cells_end = 0` by
    (gen_tac >> Cases_on `?i. i < LENGTH steps /\ k = n+i`
     >- metis_tac[] >>
     `phi_origin_count k cells = 0` by
       (simp[phi_origin_count_zero] >>
        gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
     drule phi_origin_schedule_count_le >> disch_then (qspec_then `k` mp_tac) >>
     simp[]) >>
  irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >> Cases_on `x`
  >- (qpat_x_assum `!k. phi_origin_count k cells_end = 0`
        (qspec_then `n'` mp_tac) >>
      simp[phi_origin_count_zero, listTheory.EVERY_MEM] >> metis_tac[]) >>
  simp[phi_cell_value_def]
QED
