Theory fnLineageInvActualReplay
Ancestors fnPlanLineageInventory fnPlanLineageReplay fnPlanLineageSetup planWf
  reorderSim fnPlanLineagePhiTemporal
  fnLineageInvCleanupCoherence stackPlanGen
  stackPlanOps stackPlanTypes stackModel list rich_list

(* Silent spill release is independent of the entire physical stack, not
   merely of its live projection.  All allocator effects are retained. *)
Theorem release_dead_spills_stack_update:
  !nl ps stk.
    release_dead_spills nl (ps with ps_stack := stk) =
    (release_dead_spills nl ps) with ps_stack := stk
Proof
  simp[release_dead_spills_def,
       fnPlanLineageSetupTheory.release_fold_stack_update]
QED

Theorem optimistic_swap_plan_bottom_frame:
  !dfg inst nl term ps prefix ops qs.
    EVERY (\op. ~is_var_operand op) prefix /\
    optimistic_swap_plan dfg inst nl term ps = (ops,qs) ==>
    optimistic_swap_plan dfg inst nl term
      (ps with ps_stack := prefix ++ ps.ps_stack) =
    (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `~MEM (Var (LAST nl)) prefix` by
    (gvs[EVERY_MEM] >> metis_tac[is_var_operand_def]) >>
  simp[optimistic_swap_plan_def, stack_get_depth_bottom_excluded] >>
  Cases_on `term` >- gvs[optimistic_swap_plan_def] >>
  Cases_on `inst.inst_outputs = []` >- gvs[optimistic_swap_plan_def] >>
  Cases_on `nl = []` >- gvs[optimistic_swap_plan_def] >>
  Cases_on `operand_equiv dfg (Var (LAST inst.inst_outputs)) (Var (LAST nl))`
  >- gvs[optimistic_swap_plan_def] >>
  Cases_on `stack_get_depth (Var (LAST nl)) ps.ps_stack`
  >- gvs[optimistic_swap_plan_def] >>
  `x < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  gvs[optimistic_swap_plan_def] >>
  drule_all do_swap_bottom_frame >> simp[]
QED

Theorem restore_spilled_plan_bottom_frame:
  !targets ps prefix ops qs.
    restore_spilled_plan targets ps = (ops,qs) ==>
    restore_spilled_plan targets
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  Induct >- (simp[restore_spilled_plan_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `do_restore h ps` >>
  rename1 `do_restore h ps = (step_ops,ps_mid)` >>
  drule do_restore_bottom_frame >>
  disch_then (qspec_then `prefix` assume_tac) >>
  Cases_on `restore_spilled_plan targets ps_mid` >>
  gvs[restore_spilled_plan_def] >>
  first_x_assum drule >> simp[]
QED

Theorem generate_emit_ops_stack_update:
  !inst tc ps stk.
    generate_emit_ops inst tc (ps with ps_stack := stk) =
    (FST (generate_emit_ops inst tc ps),
     (SND (generate_emit_ops inst tc ps)) with ps_stack := stk)
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_opcode = INITIAL_FMP` >- simp[generate_emit_ops_def] >>
  Cases_on `inst.inst_opcode = BUMP` >- simp[generate_emit_ops_def] >>
  simp[generate_emit_ops_def] >>
  Cases_on `venom_to_evm_name inst.inst_opcode` >> simp[] >>
  Cases_on `inst.inst_opcode = JNZ`
  >- (simp[] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  Cases_on `inst.inst_opcode = JMP`
  >- (simp[] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  Cases_on `inst.inst_opcode = DJMP` >- simp[] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[] >> Cases_on `HD inst.inst_operands` >>
      simp[fresh_label_def]) >>
  Cases_on `inst.inst_opcode = RET` >- simp[] >>
  Cases_on `inst.inst_opcode = ASSERT` >- simp[] >>
  Cases_on `inst.inst_opcode = ASSERT_UNREACHABLE`
  >- simp[fresh_label_def] >>
  Cases_on `inst.inst_opcode = LOG` >- simp[] >>
  Cases_on `inst.inst_opcode = ISTORE` >> simp[]
QED

Theorem popmany_plan_bottom_frame:
  !requests ps prefix ops qs.
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set prefix) (set requests) /\
    popmany_plan requests ps = (ops,qs) ==>
    popmany_plan requests (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`requests`, `ps`, `ps`, `[]`, `prefix`, `ps.ps_stack`,
              `ps.ps_alloc`] mp_tac popmany_plan_prefix_replay >>
  simp[] >> strip_tac >>
  gvs[plan_state_component_equality]
QED

Theorem distinct_available_pending_inventory:
  !targets ps.
    ALL_DISTINCT targets /\
    EVERY (\op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) targets ==>
    pending_inventory_wf targets ps
Proof
  rpt gen_tac >> strip_tac >> simp[pending_inventory_wf_def] >>
  gen_tac >>
  drule all_distinct_elem_count_le_one >>
  disch_then (qspec_then `op` assume_tac) >>
  Cases_on `MEM op targets`
  >- (gvs[EVERY_MEM] >> first_x_assum drule >> strip_tac >>
      gvs[] >>
      `LIST_ELEM_COUNT op ps.ps_stack > 0` by
        metis_tac[LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  `LIST_ELEM_COUNT op targets = 0` by
    (spose_not_then assume_tac >>
     `LIST_ELEM_COUNT op targets > 0` by decide_tac >>
     metis_tac[LIST_ELEM_COUNT_MEM]) >>
  simp[]
QED

Theorem generate_jmp_plan_bottom_frame:
  !lv dfg cfg fn inst nl halting term lbl ps ops qs m.
    inst.inst_opcode = JMP /\ compute_operands inst = [] /\
    inst.inst_outputs = [] /\
    (!targets. join_target_ops lv fn lbl inst = SOME targets ==>
      ALL_DISTINCT targets /\ EVERY is_var_operand targets /\
      EVERY (\op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) targets) /\
    generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl ps = (ops,qs) ==>
    generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl
      (ps with ps_stack := REPLICATE m dead_stack_marker ++ ps.ps_stack) =
      (ops,qs with ps_stack := REPLICATE m dead_stack_marker ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `join_target_ops lv fn lbl inst`
  >- (gvs[generate_regular_inst_plan_def, emit_input_plan_def,
          reorder_plan_def, generate_emit_ops_def, fresh_label_def,
          asmIRTheory.venom_to_evm_name_def,
          venomEffectsTheory.is_commutative_def, stack_pop_def,
          release_dead_spills_stack_update] >>
      rpt (BasicProvers.TOP_CASE_TAC >> gvs[release_dead_spills_stack_update,
          fnPlanPrefixTheory.release_dead_spills_stack,
          TAKE_APPEND, TAKE_LENGTH_TOO_LONG])) >>
  rename1 `join_target_ops lv fn lbl inst = SOME targets` >>
  `ALL_DISTINCT targets /\ EVERY is_var_operand targets /\
   EVERY (\op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) targets` by
    metis_tac[] >>
  `pending_inventory_wf targets ps` by
    (irule distinct_available_pending_inventory >> simp[]) >>
  Cases_on `restore_spilled_plan targets ps` >>
  rename1 `restore_spilled_plan targets ps = (restore_ops,rs)` >>
  `LENGTH targets <= LENGTH rs.ps_stack` by
    metis_tac[restore_spilled_plan_length_floor] >>
  `EVERY (\op. ~MEM op (REPLICATE m dead_stack_marker)) targets` by
    (gvs[EVERY_MEM, MEM_REPLICATE, dead_stack_marker_def] >>
     metis_tac[is_var_operand_def]) >>
  drule restore_spilled_plan_bottom_frame >>
  disch_then (qspec_then `REPLICATE m dead_stack_marker` assume_tac) >>
  Cases_on `reorder_plan dfg targets rs` >>
  rename1 `reorder_plan dfg targets rs = (swap_ops,ts)` >>
  drule_all reorder_plan_bottom_frame >> strip_tac >>
  gvs[generate_regular_inst_plan_def, emit_input_plan_def,
      reorder_plan_def, generate_emit_ops_def, fresh_label_def,
      asmIRTheory.venom_to_evm_name_def,
      venomEffectsTheory.is_commutative_def, stack_pop_def,
      release_dead_spills_stack_update] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[release_dead_spills_stack_update,
          fnPlanPrefixTheory.release_dead_spills_stack,
          TAKE_APPEND, TAKE_LENGTH_TOO_LONG])
QED

Theorem generate_regular_plan_bottom_frame:
  !base lv dfg cfg fn inst nl halting term lbl ps ops qs m.
    residual_budget_wf base [] ps /\ inst.inst_opcode <> JMP /\
    LENGTH (compute_operands inst) <= 16 /\
    EVERY (\x. x <> dead_stack_marker) (compute_operands inst) /\
    (!v. MEM (Var v) (compute_operands inst) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    ALL_DISTINCT inst.inst_outputs /\
    EVERY (\v. ~MEM (Var v) (compute_operands inst) /\
      ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled) inst.inst_outputs /\
    generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl ps = (ops,qs) ==>
    generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl
      (ps with ps_stack := REPLICATE m dead_stack_marker ++ ps.ps_stack) =
      (ops,qs with ps_stack := REPLICATE m dead_stack_marker ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `operands = compute_operands inst` >>
  qabbrev_tac `prefix = REPLICATE m dead_stack_marker` >>
  `EVERY (\op. ~is_var_operand op) prefix` by
    simp[Abbr `prefix`, dead_stack_marker_def, is_var_operand_def] >>
  `EVERY (\op. ~MEM op prefix) operands` by
    (gvs[Abbr `prefix`, EVERY_MEM, MEM_REPLICATE] >> metis_tac[]) >>
  Cases_on `emit_input_plan inst.inst_opcode operands nl ps` >>
  rename1 `emit_input_plan _ _ _ _ = (iops,ps1)` >>
  drule_all emit_input_plan_bottom_frame >> strip_tac >>
  `LENGTH operands <= LENGTH ps1.ps_stack` by
    (irule fnPlanLineageReorderTheory.available_input_plan_length >>
     goal_assum (drule_at Any) >>
     Cases >> gvs[is_var_operand_def]) >>
  suspend "candidates"
QED

Resume generate_regular_plan_bottom_frame[candidates]:
  qabbrev_tac `swapped = TAKE (LENGTH operands - 2) operands ++
    [EL (LENGTH operands - 1) operands; EL (LENGTH operands - 2) operands]` >>
  qabbrev_tac `choice = if is_commutative inst.inst_opcode /\ 2 <= LENGTH operands then
    if reorder_cost (FST (reorder_plan dfg operands ps1)) <
       reorder_cost (FST (reorder_plan dfg swapped ps1))
    then reorder_plan dfg operands ps1 else reorder_plan dfg swapped ps1
    else reorder_plan dfg operands ps1` >>
  namedCases_on `choice` ["rops ps4"] >>
  `?selected. PERM operands selected /\
      reorder_plan dfg selected ps1 = (rops,ps4)` by
    (Cases_on `is_commutative inst.inst_opcode /\ 2 <= LENGTH operands`
     >- (Cases_on `reorder_cost (FST (reorder_plan dfg operands ps1)) <
                   reorder_cost (FST (reorder_plan dfg swapped ps1))`
         >- (qexists_tac `operands` >> gvs[markerTheory.Abbrev_def]) >>
         qexists_tac `swapped` >> gvs[markerTheory.Abbrev_def] >>
         irule genericInputReadyTheory.last_two_reorder_perm >> simp[]) >>
     qexists_tac `operands` >> gvs[markerTheory.Abbrev_def]) >>
  `reorder_plan dfg operands (ps1 with ps_stack := prefix ++ ps1.ps_stack) =
    (FST (reorder_plan dfg operands ps1),
     (SND (reorder_plan dfg operands ps1)) with ps_stack :=
       prefix ++ (SND (reorder_plan dfg operands ps1)).ps_stack)` by
    (Cases_on `reorder_plan dfg operands ps1` >>
     irule reorder_plan_bottom_frame >> simp[]) >>
  `2 <= LENGTH operands ==>
   reorder_plan dfg swapped (ps1 with ps_stack := prefix ++ ps1.ps_stack) =
    (FST (reorder_plan dfg swapped ps1),
     (SND (reorder_plan dfg swapped ps1)) with ps_stack :=
       prefix ++ (SND (reorder_plan dfg swapped ps1)).ps_stack)` by
    (strip_tac >> `PERM operands swapped` by
      (simp[Abbr `swapped`] >>
       irule genericInputReadyTheory.last_two_reorder_perm >> simp[]) >>
     `LENGTH swapped = LENGTH operands /\ EVERY (\op. ~MEM op prefix) swapped` by
       metis_tac[sortingTheory.PERM_LENGTH, sortingTheory.PERM_MEM_EQ, EVERY_MEM] >>
     Cases_on `reorder_plan dfg swapped ps1` >>
     irule reorder_plan_bottom_frame >> simp[]) >>
  suspend "resources"
QED

Resume generate_regular_plan_bottom_frame[resources]:
  rename1 `residual_budget_wf spillbase [] ps` >>
  qabbrev_tac `consumed = ps4 with ps_stack := stack_pop (LENGTH operands) ps4.ps_stack` >>
  qabbrev_tac `pushed = FOLDL (\p v. p with ps_stack := stack_push (Var v) p.ps_stack)
    consumed inst.inst_outputs` >>
  `residual_budget_wf spillbase [] pushed` by
    (`ps.ps_stack = REPLICATE 0 dead_stack_marker ++ ps.ps_stack` by simp[] >>
     `residual_budget_wf spillbase [] (ps with ps_stack := ps.ps_stack)` by simp[] >>
     `consumed = ps4 with ps_stack := stack_pop (LENGTH operands) ps4.ps_stack` by
       simp[Abbr `consumed`] >>
     drule_all emit_reorder_pop_marker_core_fresh >>
     qpat_x_assum `ps.ps_stack = REPLICATE 0 dead_stack_marker ++ ps.ps_stack` kall_tac >>
     strip_tac >>
     `pushed = FOLDL (\p v. p with ps_stack := stack_push (Var v) p.ps_stack)
       consumed inst.inst_outputs` by simp[Abbr `pushed`] >>
     drule_all output_push_marker_core >> strip_tac >>
     `pushed with ps_stack := rest ++ MAP Var inst.inst_outputs = pushed` by
       (qpat_x_assum `pushed.ps_stack = _` mp_tac >>
        simp_tac (srw_ss()) [plan_state_component_equality]) >>
     metis_tac[]) >>
  `LENGTH operands <= LENGTH ps4.ps_stack` by
    (`ps.ps_stack = REPLICATE 0 dead_stack_marker ++ ps.ps_stack` by simp[] >>
     `residual_budget_wf spillbase [] (ps with ps_stack := ps.ps_stack)` by simp[] >>
     `consumed = ps4 with ps_stack := stack_pop (LENGTH operands) ps4.ps_stack` by
       simp[Abbr `consumed`] >>
     drule_all emit_reorder_pop_marker_execution >>
     qpat_x_assum `ps.ps_stack = REPLICATE 0 dead_stack_marker ++ ps.ps_stack` kall_tac >>
     simp_tac (srw_ss()) [] >> strip_tac >> gvs[] >>
     metis_tac[sortingTheory.PERM_LENGTH]) >>
  suspend "tail"
QED

Resume generate_regular_plan_bottom_frame[tail]:
  qabbrev_tac `topic = case inst.inst_opcode of LOG =>
    (case HD inst.inst_operands of Lit v => w2n v | _ => 0) | _ => 0` >>
  Cases_on `generate_emit_ops inst topic pushed` >>
  rename1 `generate_emit_ops inst topic pushed = (eops,ps7)` >>
  `ALL_DISTINCT ps7.ps_stack` by
    (drule residual_budget_wf_empty_inventory >> strip_tac >>
     drule fnPlanLineageReorderTheory.generate_emit_ops_slots >> simp[]) >>
  `generate_emit_ops inst topic (pushed with ps_stack := prefix ++ pushed.ps_stack) =
    (eops,ps7 with ps_stack := prefix ++ ps7.ps_stack)` by
    (drule fnPlanLineageReorderTheory.generate_emit_ops_slots >>
     simp[generate_emit_ops_stack_update]) >>
  Cases_on `popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs)) ps7` >>
  rename1 `popmany_plan _ ps7 = (pops,ps8)` >>
  `DISJOINT (set prefix) (set (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs)))` by
    (gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION, MEM_MAP, EVERY_MEM] >>
     metis_tac[is_var_operand_def]) >>
  drule_all popmany_plan_bottom_frame >> strip_tac >>
  `!s. optimistic_swap_plan dfg inst nl term
       (s with ps_stack := prefix ++ s.ps_stack) =
       (FST (optimistic_swap_plan dfg inst nl term s),
        (SND (optimistic_swap_plan dfg inst nl term s)) with ps_stack :=
          prefix ++ (SND (optimistic_swap_plan dfg inst nl term s)).ps_stack)` by
    (gen_tac >> Cases_on `optimistic_swap_plan dfg inst nl term s` >>
     irule optimistic_swap_plan_bottom_frame >> simp[]) >>
  `FOLDL (\p v. p with ps_stack := stack_push (Var v) p.ps_stack)
     (ps4 with ps_stack := stack_pop (LENGTH operands) (prefix ++ ps4.ps_stack))
     inst.inst_outputs = pushed with ps_stack := prefix ++ pushed.ps_stack` by
    simp[Abbr `pushed`, Abbr `consumed`, parameter_push_fold,
         fnPlanLineageInventoryTheory.stack_pop_bottom_extension, APPEND_ASSOC] >>
  suspend "reconstruction"
QED

Resume generate_regular_plan_bottom_frame[reconstruction]:
  Cases_on `reorder_plan dfg operands ps1` >>
  Cases_on `reorder_plan dfg swapped ps1` >>
  Cases_on `is_commutative inst.inst_opcode /\ 2 <= LENGTH operands` >>
  Cases_on `reorder_cost (FST (reorder_plan dfg operands ps1)) <
            reorder_cost (FST (reorder_plan dfg swapped ps1))` >>
  qpat_x_assum `Abbrev ((rops,ps4) = _)`
    (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  gvs[Abbr `swapped`] >>
  qpat_x_assum `Abbrev (topic = _)`
    (fn th => fs[generate_regular_inst_plan_def,
      GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  gvs[Abbr `operands`, Abbr `prefix`, Abbr `consumed`, Abbr `pushed`] >>
  Cases_on `inst.inst_outputs = []` >>
  gvs[release_dead_spills_stack_update,
      fnPlanPrefixTheory.release_dead_spills_stack] >>
  Cases_on `~halting \/ LENGTH inst.inst_outputs > 1` >> gvs[] >>
  Cases_on `FILTER (\v. MEM v nl) inst.inst_outputs = []` >>
  gvs[release_dead_spills_stack_update,
      fnPlanPrefixTheory.release_dead_spills_stack] >>
  Cases_on `optimistic_swap_plan dfg inst nl term ps8` >>
  Cases_on `optimistic_swap_plan dfg inst nl term ps7` >>
  gvs[release_dead_spills_stack_update,
      fnPlanPrefixTheory.release_dead_spills_stack]
QED

Finalise generate_regular_plan_bottom_frame

Theorem stack_get_phi_depth_bottom_dead:
 !inst stk m.
 stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
   (REPLICATE m dead_stack_marker ++ stk) =
 stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) stk
Proof
 rpt gen_tac >>
 simp[stack_get_phi_depth_def, REVERSE_APPEND, stack_find_append_excluded,
   EVERY_MEM, MEM_FILTER, dead_stack_marker_def, is_var_operand_def]
QED

Theorem popmany_singleton_bottom_dead_frame:
 !ret ps m ops qs.
 ret <> dead_stack_marker /\ popmany_plan [ret] ps = (ops,qs) ==>
 popmany_plan [ret] (ps with ps_stack := REPLICATE m dead_stack_marker ++ ps.ps_stack) =
 (ops,qs with ps_stack := REPLICATE m dead_stack_marker ++ qs.ps_stack)
Proof
 rpt gen_tac >> strip_tac >>
 qmatch_goalsub_abbrev_tac `popmany_plan [ret] ext` >>
 `stack_get_depth ret ext.ps_stack = stack_get_depth ret ps.ps_stack` by
   simp[Abbr `ext`, stack_get_depth_bottom_dead] >>
 `ext.ps_alloc = ps.ps_alloc` by simp[Abbr `ext`] >>
 drule_all popmany_singleton_observation_frame >> strip_tac >>
 Cases_on `stack_get_depth ret ps.ps_stack`
 >- (gvs[popmany_plan_def, popmany_individual_def, sortingTheory.QSORT_DEF,
          sortingTheory.PARTITION_DEF, sortingTheory.PART_DEF, Abbr `ext`]) >>
 `x < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_props] >>
 mp_tac (Q.SPECL [`ret`, `ps`, `x`] popmany_singleton_stack_projection) >>
 mp_tac (Q.SPECL [`ret`, `ext`, `x`] popmany_singleton_stack_projection) >>
 mp_tac (Q.SPECL [`ret`, `ps`] popmany_singleton_state_frame) >>
 mp_tac (Q.SPECL [`ret`, `ext`] popmany_singleton_state_frame) >>
 simp[] >> rpt strip_tac >>
 ` (SND (popmany_plan [ret] ext)).ps_stack =
   REPLICATE m dead_stack_marker ++ qs.ps_stack` by
   (gvs[Abbr `ext`, stack_swap_bottom_extension, stack_pop_bottom_extension]) >>
 Cases_on `popmany_plan [ret] ext` >>
 gvs[Abbr `ext`, plan_state_component_equality]
QED

Theorem generate_phi_plan_bottom_frame:
 !inst nl halt ps ops qs m.
 generate_phi_plan inst nl halt ps = (ops,qs) ==>
 generate_phi_plan inst nl halt
   (ps with ps_stack := REPLICATE m dead_stack_marker ++ ps.ps_stack) =
 (ops,qs with ps_stack := REPLICATE m dead_stack_marker ++ qs.ps_stack)
Proof
 rpt gen_tac >> strip_tac >>
 Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
 >- gvs[generate_phi_plan_def, stack_get_phi_depth_bottom_dead] >>
 `x < LENGTH ps.ps_stack` by
   (qpat_x_assum `stack_get_phi_depth _ _ = SOME _` mp_tac >>
    simp[stack_get_phi_depth_def] >> metis_tac[planWfTheory.stack_find_bound, LENGTH_REVERSE]) >>
 `stack_peek x (REPLICATE m dead_stack_marker ++ ps.ps_stack) = stack_peek x ps.ps_stack` by
   simp[stack_peek_def, EL_APPEND2] >>
 qpat_x_assum `generate_phi_plan _ _ _ _ = _` mp_tac >>
 simp[generate_phi_plan_def, stack_get_phi_depth_bottom_dead] >>
 Cases_on `MEM (operand_to_string (stack_peek x ps.ps_stack)) nl`
 >- suspend "dup" >>
 simp[stack_poke_bottom_extension] >>
 Cases_on `~halt /\ ~MEM (HD inst.inst_outputs) nl`
 >- suspend "rename_pop" >> simp[] >> strip_tac >> gvs[]
QED

Resume generate_phi_plan_bottom_frame[dup]:
 Cases_on `do_dup x ps` >>
 drule_all do_dup_bottom_frame >>
 disch_then (qspec_then `REPLICATE m dead_stack_marker` assume_tac) >>
 simp[] >>
 `0 < LENGTH r.ps_stack` by
   (mp_tac (Q.SPECL [`x`, `ps`] doSwapSimTheory.do_dup_stack_exact) >> simp[] >>
    simp[stack_dup_def]) >>
 simp[stack_poke_bottom_extension] >>
 Cases_on `~halt /\ ~MEM (HD inst.inst_outputs) nl`
 >- suspend "dup_pop" >> simp[] >> strip_tac >> gvs[]
QED

Resume generate_phi_plan_bottom_frame[rename_pop]:
 Cases_on `popmany_plan [Var (HD inst.inst_outputs)]
   (ps with ps_stack := stack_poke x (Var (HD inst.inst_outputs)) ps.ps_stack)` >>
 drule_at (Pat `popmany_plan _ _ = _`) popmany_singleton_bottom_dead_frame >>
 disch_then (qspec_then `m` mp_tac) >>
 simp[dead_stack_marker_def] >> strip_tac >> simp[] >> strip_tac >> gvs[]
QED

Resume generate_phi_plan_bottom_frame[dup_pop]:
 Cases_on `popmany_plan [Var (HD inst.inst_outputs)]
   (r with ps_stack := stack_poke 0 (Var (HD inst.inst_outputs)) r.ps_stack)` >>
 drule_at (Pat `popmany_plan _ _ = _`) popmany_singleton_bottom_dead_frame >>
 disch_then (qspec_then `m` mp_tac) >>
 simp[dead_stack_marker_def] >> strip_tac >> simp[] >> strip_tac >> gvs[]
QED

Finalise generate_phi_plan_bottom_frame

Theorem generate_phi_plan_released_bottom_frame:
 !inst nl halt ps ops qs m.
 generate_phi_plan inst nl halt ps = (ops,qs) ==>
 (FST (generate_phi_plan inst nl halt
     (ps with ps_stack := REPLICATE m dead_stack_marker ++ ps.ps_stack)),
  release_dead_spills nl (SND (generate_phi_plan inst nl halt
     (ps with ps_stack := REPLICATE m dead_stack_marker ++ ps.ps_stack)))) =
 (ops,(release_dead_spills nl qs) with ps_stack :=
   REPLICATE m dead_stack_marker ++ (release_dead_spills nl qs).ps_stack)
Proof
 rpt gen_tac >> strip_tac >> drule generate_phi_plan_bottom_frame >>
 disch_then (qspec_then `m` assume_tac) >>
 simp[release_dead_spills_stack_update, fnPlanPrefixTheory.release_dead_spills_stack]
QED

(* Instruction execution does not inspect the block-cleanup bookkeeping. *)
Theorem do_dup_cleanup_frame:
  !d ps ch promised.
    do_dup d (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (do_dup d ps), SND (do_dup d ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  rpt gen_tac >> simp[do_dup_def] >>
  Cases_on `d <= 15` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[plan_state_component_equality]
QED

Theorem do_swap_cleanup_frame:
  !d ps ch promised.
    do_swap d (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (do_swap d ps), SND (do_swap d ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  rpt gen_tac >> simp[do_swap_def] >>
  Cases_on `d = 0` >> simp[] >> Cases_on `d <= 16` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[plan_state_component_equality]
QED

Theorem do_restore_cleanup_frame:
  !op ps ch promised.
    do_restore op (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (do_restore op ps), SND (do_restore op ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  rpt gen_tac >> simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[plan_state_component_equality]
QED

Theorem do_spill_at_cleanup_frame:
  !d ps ch promised.
    do_spill_at d (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (do_spill_at d ps), SND (do_spill_at d ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  rpt gen_tac >> simp[do_spill_at_def, do_spill_tos_def] >>
  Cases_on `d = 0` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> simp[plan_state_component_equality]
QED

Theorem reduce_depth_plan_cleanup_frame:
  !fuel targets op f len ps ch promised.
    reduce_depth_plan fuel targets op f len
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (reduce_depth_plan fuel targets op f len ps),
     SND (reduce_depth_plan fuel targets op f len ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  Induct >> rpt gen_tac >> simp[reduce_depth_plan_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[do_spill_at_cleanup_frame]) >>
  rpt (pairarg_tac >> gvs[]) >> simp[]
QED

Theorem restore_spilled_plan_cleanup_frame:
  !targets ps ch promised.
    restore_spilled_plan targets
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (restore_spilled_plan targets ps),
     SND (restore_spilled_plan targets ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  Induct >> rpt gen_tac >> simp[restore_spilled_plan_def, do_restore_cleanup_frame] >>
  rpt (pairarg_tac >> gvs[]) >> simp[]
QED

Theorem reorder_one_cleanup_frame:
  !dfg targets idx op ps ch promised.
    reorder_one dfg targets idx op
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (reorder_one dfg targets idx op ps),
     SND (reorder_one dfg targets idx op ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  rpt gen_tac >>
  Cases_on `do_restore op ps` >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - 1 - idx) (LENGTH targets) ps.ps_stack` >>
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  gvs[reorder_one_def, do_restore_cleanup_frame] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  rename1 `stack_get_unfixed_depth op (LENGTH targets - (idx + 1)) (LENGTH targets) st.ps_stack = SOME dist` >>
  Cases_on `dist > 16` >> simp[reduce_depth_plan_cleanup_frame] >>
  TRY (Cases_on `reduce_depth_plan (LENGTH st.ps_stack) targets op
         (LENGTH targets - (idx + 1)) (LENGTH targets) st` >> gvs[]) >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  rename1 `stack_get_unfixed_depth op (LENGTH targets - (idx + 1)) (LENGTH targets) rs.ps_stack = SOME final` >>
  Cases_on `final = LENGTH targets - 1 - idx` >> simp[] >>
  Cases_on `LENGTH targets - 1 - idx < LENGTH rs.ps_stack` >> simp[] >>
  TRY (Cases_on `operand_equiv dfg op (stack_peek (LENGTH targets - 1 - idx) rs.ps_stack)` >>
       simp[plan_state_component_equality]) >>
  Cases_on `do_swap final rs` >> simp[do_swap_cleanup_frame] >>
  rpt (pairarg_tac >> gvs[]) >> simp[]
QED

Theorem reorder_fold_cleanup_frame[local]:
  !xs ops ps dfg targets ch promised.
    FOLDL (\(ops,ps) (idx,op).
      (ops ++ FST (reorder_one dfg targets idx op ps), SND (reorder_one dfg targets idx op ps)))
      (ops,ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) xs =
    (\r. (FST r,SND r with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>))
      (FOLDL (\(ops,ps) (idx,op).
        (ops ++ FST (reorder_one dfg targets idx op ps), SND (reorder_one dfg targets idx op ps))) (ops,ps) xs)
Proof
  Induct >> rpt gen_tac >> simp[] >> PairCases_on `h` >>
  simp[reorder_one_cleanup_frame] >>
  Cases_on `reorder_one dfg targets h0 h1 ps` >> gvs[]
QED

Theorem reorder_plan_cleanup_frame:
  !dfg targets ps ch promised.
    reorder_plan dfg targets
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (reorder_plan dfg targets ps), SND (reorder_plan dfg targets ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  rpt gen_tac >>
  simp[reorder_plan_def, pairTheory.UNCURRY] >>
  irule (SRULE [LET_THM] reorder_fold_cleanup_frame)
QED

Theorem popmany_fold_cleanup_frame[local]:
  !xs ops ps ch promised.
    FOLDL (\(ops,ps) v.
      case stack_get_depth v ps.ps_stack of NONE => (ops,ps)
      | SOME d =>
        (\r. (ops ++ FST r ++ [SOPop 1],
          SND r with ps_stack := stack_pop 1 (SND r).ps_stack))
          (if d = 0 then ([],ps) else do_swap d ps))
      (ops,ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) xs =
    (\r. (FST r,SND r with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>))
      (FOLDL (\(ops,ps) v.
        case stack_get_depth v ps.ps_stack of NONE => (ops,ps)
        | SOME d =>
          (\r. (ops ++ FST r ++ [SOPop 1],
            SND r with ps_stack := stack_pop 1 (SND r).ps_stack))
            (if d = 0 then ([],ps) else do_swap d ps)) (ops,ps) xs)
Proof
  Induct >> rpt gen_tac >> simp[] >>
  Cases_on `stack_get_depth h ps.ps_stack` >> gvs[LET_THM] >>
  Cases_on `x = 0`
  >- (gvs[] >> first_x_assum (qspecl_then
        [`ops ++ [SOPop 1]`, `ps with ps_stack := stack_pop 1 ps.ps_stack`, `ch`, `promised`] mp_tac) >> simp[]) >>
  gvs[do_swap_cleanup_frame] >>
  Cases_on `do_swap x ps` >> gvs[] >>
  first_x_assum (qspecl_then
    [`ops ++ q ++ [SOPop 1]`, `r with ps_stack := stack_pop 1 r.ps_stack`, `ch`, `promised`] mp_tac) >> simp[]
QED

Theorem popmany_individual_cleanup_frame:
  !targets ps ch promised.
    popmany_individual targets
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (popmany_individual targets ps), SND (popmany_individual targets ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  rpt gen_tac >> simp[popmany_individual_def, pairTheory.UNCURRY] >>
  irule (SRULE [LET_THM] popmany_fold_cleanup_frame)
QED

Theorem popmany_plan_cleanup_frame:
  !targets ps ch promised.
    popmany_plan targets
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (popmany_plan targets ps), SND (popmany_plan targets ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  Cases >> rpt gen_tac >> simp[popmany_plan_def] >>
  Cases_on `EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) (h::t))` >>
  gvs[popmany_individual_cleanup_frame] >>
  Cases_on `is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v ps.ps_stack) (h::t)))` >>
  gvs[popmany_individual_cleanup_frame, do_swap_cleanup_frame] >>
  Cases_on `do_swap (SUC (LENGTH t)) ps` >> gvs[plan_state_component_equality] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Theorem emit_one_input_cleanup_frame:
  !opc nl op ps ch promised.
    emit_one_input opc nl op
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (emit_one_input opc nl op ps), SND (emit_one_input opc nl op ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  rpt gen_tac >> Cases_on `do_restore op ps` >>
  simp[emit_one_input_def, do_restore_cleanup_frame] >>
  Cases_on `is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)` >> simp[] >>
  Cases_on `op` >> simp[] >>
  TRY (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  TRY (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  simp[do_dup_cleanup_frame] >>
  rpt (pairarg_tac >> gvs[]) >> simp[plan_state_component_equality]
QED

Theorem emit_input_plan_cleanup_frame:
  !targets opc nl ps ch promised.
    emit_input_plan opc targets nl
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (emit_input_plan opc targets nl ps), SND (emit_input_plan opc targets nl ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  Induct >> rpt gen_tac >> simp[emit_input_plan_def, emit_one_input_cleanup_frame] >>
  Cases_on `emit_one_input opc (operand_vars targets ++ nl) h ps` >> simp[] >>
  Cases_on `emit_input_plan opc targets nl r` >> simp[]
QED

Theorem generate_emit_ops_cleanup_frame:
  !inst tc ps ch promised.
    generate_emit_ops inst tc
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (generate_emit_ops inst tc ps), SND (generate_emit_ops inst tc ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_opcode = INITIAL_FMP` >- simp[generate_emit_ops_def] >>
  Cases_on `inst.inst_opcode = BUMP` >- simp[generate_emit_ops_def] >>
  simp[generate_emit_ops_def] >>
  Cases_on `venom_to_evm_name inst.inst_opcode` >> simp[] >>
  Cases_on `inst.inst_opcode = JNZ`
  >- (simp[] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  Cases_on `inst.inst_opcode = JMP`
  >- (simp[] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  Cases_on `inst.inst_opcode = DJMP` >- simp[] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[] >> Cases_on `HD inst.inst_operands` >>
      simp[fresh_label_def, plan_state_component_equality]) >>
  Cases_on `inst.inst_opcode = RET` >- simp[] >>
  Cases_on `inst.inst_opcode = ASSERT` >- simp[] >>
  Cases_on `inst.inst_opcode = ASSERT_UNREACHABLE`
  >- simp[fresh_label_def, plan_state_component_equality] >>
  Cases_on `inst.inst_opcode = LOG` >- simp[] >>
  Cases_on `inst.inst_opcode = ISTORE` >> simp[]
QED

Theorem optimistic_swap_plan_cleanup_frame:
  !dfg inst nl term ps ch promised.
    optimistic_swap_plan dfg inst nl term
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (optimistic_swap_plan dfg inst nl term ps), SND (optimistic_swap_plan dfg inst nl term ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  rpt gen_tac >> simp[optimistic_swap_plan_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[do_swap_cleanup_frame])
QED

Theorem generate_phi_plan_cleanup_frame:
  !inst nl halt ps ch promised.
    generate_phi_plan inst nl halt
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (generate_phi_plan inst nl halt ps), SND (generate_phi_plan inst nl halt ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  rpt gen_tac >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack` >>
  simp[generate_phi_plan_def] >>
  Cases_on `MEM (operand_to_string (stack_peek x ps.ps_stack)) nl` >> simp[do_dup_cleanup_frame] >>
  Cases_on `do_dup x ps` >> simp[] >>
  Cases_on `~halt /\ ~MEM (HD inst.inst_outputs) nl` >> simp[popmany_plan_cleanup_frame] >>
  rpt (pairarg_tac >> gvs[])
  >- (qspecl_then [`[Var (HD inst.inst_outputs)]`,
        `r with ps_stack := stack_poke 0 (Var (HD inst.inst_outputs)) r.ps_stack`,
        `ch`, `promised`] mp_tac popmany_plan_cleanup_frame >> simp[]) >>
  qspecl_then [`[Var (HD inst.inst_outputs)]`,
    `ps with ps_stack := stack_poke x (Var (HD inst.inst_outputs)) ps.ps_stack`,
    `ch`, `promised`] mp_tac popmany_plan_cleanup_frame >> simp[]
QED

Theorem generate_offset_plan_cleanup_frame:
  !inst ps ch promised.
    generate_offset_plan inst
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (generate_offset_plan inst ps), SND (generate_offset_plan inst ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  rpt gen_tac >> simp[generate_offset_plan_def] >>
  Cases_on `EL 1 inst.inst_operands` >> simp[plan_state_component_equality]
QED

Theorem release_fold_cleanup_frame[local]:
  !xs ps ch promised.
    FOLDL (\ps (op,off). ps with <|ps_spilled := ps.ps_spilled \\ op;
      ps_alloc := free_spill_slot off ps.ps_alloc|>)
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) xs =
    (FOLDL (\ps (op,off). ps with <|ps_spilled := ps.ps_spilled \\ op;
      ps_alloc := free_spill_slot off ps.ps_alloc|>) ps xs) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>
Proof
  Induct >> rpt gen_tac >> simp[] >> PairCases_on `h` >> simp[] >>
  first_x_assum (qspecl_then [`ps with <|ps_spilled := ps.ps_spilled \\ h0;
    ps_alloc := free_spill_slot h1 ps.ps_alloc|>`, `ch`, `promised`] mp_tac) >> simp[]
QED

Theorem release_dead_spills_cleanup_frame:
  !nl ps ch promised.
    release_dead_spills nl
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (release_dead_spills nl ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>
Proof
  simp[release_dead_spills_def, release_fold_cleanup_frame]
QED

Theorem push_outputs_cleanup_frame[local]:
  !outs ps ch promised.
    FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) outs =
    (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack) ps outs) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>
Proof
  Induct >> rpt gen_tac >> simp[] >>
  first_x_assum (qspecl_then [`ps with ps_stack := stack_push (Var h) ps.ps_stack`,
    `ch`, `promised`] mp_tac) >> simp[]
QED



Theorem generate_regular_inst_plan_cleanup_frame:
  !lv dfg cfg fn inst nl halt term lbl ps ch promised.
    generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    (FST (generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl ps),
     SND (generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl ps) with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  rpt gen_tac >>
  simp[generate_regular_inst_plan_def, emit_input_plan_cleanup_frame] >>
  Cases_on `emit_input_plan inst.inst_opcode (compute_operands inst) nl ps` >> simp[] >>
  Cases_on `inst.inst_opcode = JMP` >> gvs[] >>
  TRY (Cases_on `join_target_ops lv fn lbl inst` >> gvs[]) >>
  TRY (rename1 `join_target_ops lv fn lbl inst = SOME targets` >>
    Cases_on `restore_spilled_plan targets r` >>
    simp[restore_spilled_plan_cleanup_frame] >>
    rename1 `restore_spilled_plan targets r = (ro,rs)` >>
    Cases_on `reorder_plan dfg targets rs` >> simp[reorder_plan_cleanup_frame]) >>
  simp[reorder_plan_cleanup_frame] >>
  qmatch_goalsub_rename_tac `reorder_plan dfg (compute_operands inst) stage` >>
  Cases_on `is_commutative inst.inst_opcode /\ LENGTH (compute_operands inst) >= 2` >> gvs[] >>
  Cases_on `reorder_plan dfg (compute_operands inst) stage` >> simp[] >>
  TRY (qmatch_goalsub_abbrev_tac `reorder_plan dfg swapped stage` >>
    Cases_on `reorder_plan dfg swapped stage` >> gvs[Abbr `swapped`]) >>
  TRY (qmatch_goalsub_rename_tac `reorder_cost oa < reorder_cost ob` >>
    Cases_on `reorder_cost oa < reorder_cost ob` >> simp[]) >>
  qmatch_goalsub_rename_tac `stack_pop (LENGTH (compute_operands inst)) chosen.ps_stack` >>
  qspecl_then [`inst.inst_outputs`,
    `chosen with ps_stack := stack_pop (LENGTH (compute_operands inst)) chosen.ps_stack`,
    `ch`, `promised`] (assume_tac o SRULE []) push_outputs_cleanup_frame >>
  Cases_on `inst.inst_outputs = []` >>
  simp[generate_emit_ops_cleanup_frame] >>
  qmatch_goalsub_abbrev_tac `generate_emit_ops inst tc _` >>
  qabbrev_tac `pushed = FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
    (chosen with ps_stack := stack_pop (LENGTH (compute_operands inst)) chosen.ps_stack) inst.inst_outputs` >>
  qspecl_then [`inst`, `tc`, `pushed`, `ch`, `promised`]
    (assume_tac o SRULE []) generate_emit_ops_cleanup_frame >>
  Cases_on `generate_emit_ops inst tc pushed` >>
  gvs[Abbr `tc`, Abbr `pushed`, release_dead_spills_cleanup_frame] >>
  Cases_on `~halt \/ LENGTH inst.inst_outputs > 1` >>
  simp[popmany_plan_cleanup_frame] >>
  TRY (qmatch_goalsub_abbrev_tac `popmany_plan dead after_emit` >>
    Cases_on `popmany_plan dead after_emit` >> gvs[Abbr `dead`]) >>
  Cases_on `FILTER (\out. MEM out nl) inst.inst_outputs = []` >>
  simp[optimistic_swap_plan_cleanup_frame, release_dead_spills_cleanup_frame] >>
  qmatch_goalsub_rename_tac `optimistic_swap_plan dfg inst nl term final_input` >>
  Cases_on `optimistic_swap_plan dfg inst nl term final_input` >>
  simp[release_dead_spills_cleanup_frame]
QED

Theorem generate_inst_plan_cleanup_frame:
  !lv dfg cfg fn inst nl halt term lbl ps ch promised.
    generate_inst_plan lv dfg cfg fn inst nl halt term lbl
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    OPTION_MAP (\(ops,s). (ops,s with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>))
      (generate_inst_plan lv dfg cfg fn inst nl halt term lbl ps)
Proof
  rpt gen_tac >>
  Cases_on `is_pre_codegen_opcode inst.inst_opcode` >- simp[generate_inst_plan_def] >>
  Cases_on `inst.inst_opcode = INVOKE /\ ~invoke_operands_wf inst`
  >- simp[generate_inst_plan_def] >>
  Cases_on `inst.inst_opcode = PHI`
  >- (simp[generate_inst_plan_def, generate_phi_plan_cleanup_frame] >>
      Cases_on `generate_phi_plan inst nl halt ps` >> simp[]) >>
  Cases_on `inst.inst_opcode = OFFSET`
  >- (simp[generate_inst_plan_def, generate_offset_plan_cleanup_frame] >>
      Cases_on `generate_offset_plan inst ps` >> simp[]) >>
  Cases_on `is_param_opcode inst.inst_opcode` >- simp[generate_inst_plan_def] >>
  Cases_on `inst.inst_opcode = NOP` >- simp[generate_inst_plan_def] >>
  simp[generate_inst_plan_def, generate_regular_inst_plan_cleanup_frame] >>
  Cases_on `generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl ps` >>
  simp[join_reached_def] >>
  Cases_on `join_target_ops lv fn lbl inst` >> simp[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem generate_block_insts_plan_cleanup_frame:
  !insts lv dfg cfg fn lbl halt np bl i ps ch promised.
    generate_block_insts_plan lv dfg cfg fn lbl halt np bl i insts
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    OPTION_MAP (\(ops,s). (ops,s with
      <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>))
      (generate_block_insts_plan lv dfg cfg fn lbl halt np bl i insts ps)
Proof
  Induct >> rpt gen_tac >>
  simp[generate_block_insts_plan_def, generate_inst_plan_cleanup_frame] >>
  qmatch_goalsub_abbrev_tac `generate_inst_plan lv dfg cfg fn h nl halt term lbl ps` >>
  Cases_on `generate_inst_plan lv dfg cfg fn h nl halt term lbl ps` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  first_x_assum (fn ih => rewrite_tac[ih]) >>
  Cases_on `generate_block_insts_plan lv dfg cfg fn lbl halt np bl (i+1) insts x1` >>
  simp[] >> PairCases_on `x` >> simp[]
QED
