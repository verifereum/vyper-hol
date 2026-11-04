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

Theorem stack_poke_bottom_extension:
  !d x prefix core. d < LENGTH core ==>
    stack_poke d x (prefix ++ core) = prefix ++ stack_poke d x core
Proof
  rpt strip_tac >>
  `LENGTH (prefix ++ core) - 1 - d = LENGTH prefix + (LENGTH core - 1 - d)` by
    (simp[] >> decide_tac) >>
  simp[stack_poke_def, LUPDATE_APPEND2]
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
