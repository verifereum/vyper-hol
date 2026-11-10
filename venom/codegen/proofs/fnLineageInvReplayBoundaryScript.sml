Theory fnLineageInvReplayBoundary
Ancestors
  fnLineageInvActualReplay fnPlanLineageInventory reorderSim stackPlanGen
  stackPlanTypes stackPlanOps stackModel planWf foldlSim arithmetic list rich_list pred_set
  fnPlanLineageReorder fnPlanLineageSetup genericInputReady

Theorem available_inst_bottom_frame:
 !spill_base lv dfg cfg fn inst nl halt term lbl ps ops qs n core m.
 lineage_core n core ps /\
 residual_budget_wf spill_base [] (ps with ps_stack := core) /\
 inst.inst_opcode <> JMP /\ inst.inst_opcode <> PHI /\
 inst.inst_opcode <> OFFSET /\ inst.inst_opcode <> NOP /\
 ~is_param_opcode inst.inst_opcode /\
 LENGTH (compute_operands inst) <= 16 /\
 EVERY (\x. x <> dead_stack_marker) (compute_operands inst) /\
 (!v. MEM (Var v) (compute_operands inst) ==>
   MEM (Var v) core \/ Var v IN FDOM ps.ps_spilled) /\
 ALL_DISTINCT inst.inst_outputs /\
 EVERY (\v. ~MEM (Var v) (compute_operands inst) /\
   ~MEM (Var v) core /\ Var v NOTIN FDOM ps.ps_spilled) inst.inst_outputs /\
 generate_inst_plan lv dfg cfg fn inst nl halt term lbl ps = SOME (ops,qs)
 ==>
 generate_inst_plan lv dfg cfg fn inst nl halt term lbl
   (ps with ps_stack := REPLICATE m dead_stack_marker ++ ps.ps_stack) =
 SOME (ops,qs with ps_stack := REPLICATE m dead_stack_marker ++ qs.ps_stack)
Proof
 rpt gen_tac >> strip_tac >>
 `ps.ps_stack = REPLICATE n dead_stack_marker ++ core` by
   gvs[lineage_core_def] >>
 qabbrev_tac `canon = ps with ps_stack := core` >>
 Cases_on `generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl canon` >>
 rename1 `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ canon = (cops,cqs)` >>
 `!r. generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl
   (canon with ps_stack := REPLICATE r dead_stack_marker ++ canon.ps_stack) =
   (cops,cqs with ps_stack := REPLICATE r dead_stack_marker ++ cqs.ps_stack)` by
   (gen_tac >> irule generate_regular_plan_bottom_frame >>
    simp[Abbr `canon`] >> metis_tac[]) >>
 `canon with ps_stack := REPLICATE n dead_stack_marker ++ canon.ps_stack = ps` by
   (simp[Abbr `canon`, plan_state_component_equality]) >>
 first_assum (qspec_then `n` assume_tac) >>
 first_assum (qspec_then `m+n` assume_tac) >>
 qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
 simp[generate_inst_plan_def, AllCaseEqs()] >> strip_tac >>
 gvs[Abbr `canon`, GSYM REPLICATE_APPEND, APPEND_ASSOC]
QED

(* Count spill resources only when the remaining input/live footprint can
   restore them.  Unrequested surplus spills must not bound stack slots. *)
Theorem emit_one_input_stack_upper_acc[local]:
  !done rest opc nl h ps.
    (!x. LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled /\
          MEM x (MAP Var (operand_vars (h::rest) ++ nl)) then 1 else 0) <=
      LIST_ELEM_COUNT x done +
      (if MEM x (MAP Var (operand_vars (h::rest) ++ nl)) then 1 else 0)) ==>
    !x. LIST_ELEM_COUNT x (SND (emit_one_input opc (operand_vars rest ++ nl) h ps)).ps_stack +
      (if x IN FDOM (SND (emit_one_input opc (operand_vars rest ++ nl) h ps)).ps_spilled /\
          MEM x (MAP Var (operand_vars rest ++ nl)) then 1 else 0) <=
      LIST_ELEM_COUNT x (done ++ [h]) +
      (if MEM x (MAP Var (operand_vars rest ++ nl)) then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  first_x_assum (qspec_then `x` assume_tac) >>
  qspecl_then [`opc`, `operand_vars rest ++ nl`, `h`, `ps`, `x`]
    assume_tac emit_one_input_inventory_upper >>
  Cases_on `emit_one_input opc (operand_vars rest ++ nl) h ps` >>
  rename1 `emit_one_input _ _ _ _ = (step_ops,mid)` >>
  drule genBlockSimTheory.bump_emit_one_input_spilled_shape >> strip_tac >>
  Cases_on `x IN FDOM ps.ps_spilled` >>
  Cases_on `h` >> Cases_on `x` >>
  gvs[venomInstTheory.operand_vars_def, dfgDefsTheory.operand_vars_def,
      venomInstTheory.operand_var_def, dfgDefsTheory.operand_var_def,
      is_var_operand_def, elem_count_append, MAP_APPEND,
      LIST_ELEM_COUNT_DEF, MEM_MAP, finite_mapTheory.FDOM_DOMSUB] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (qpat_x_assum `emit_one_input _ _ (Lit _) _ = _` mp_tac >>
       simp[emit_one_input_def, is_var_operand_def] >> strip_tac >>
       gvs[stackModelTheory.stack_push_def, SNOC_APPEND, FILTER_APPEND, elem_count_append, LIST_ELEM_COUNT_DEF] >>
       NO_TAC) >>
  TRY (qpat_x_assum `emit_one_input _ _ (Label _) _ = _` mp_tac >>
       simp[emit_one_input_def, is_var_operand_def] >>
       Cases_on `opc = INVOKE` >> strip_tac >>
       gvs[stackModelTheory.stack_push_def, SNOC_APPEND, FILTER_APPEND, elem_count_append, LIST_ELEM_COUNT_DEF] >>
       NO_TAC) >>
  decide_tac
QED

Theorem emit_input_plan_stack_upper_acc[local]:
  !rest done opc nl ps iops qs.
    (!x. LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled /\
          MEM x (MAP Var (operand_vars rest ++ nl)) then 1 else 0) <=
      LIST_ELEM_COUNT x done +
      (if MEM x (MAP Var (operand_vars rest ++ nl)) then 1 else 0)) /\
    emit_input_plan opc rest nl ps = (iops,qs) ==>
    !x. LIST_ELEM_COUNT x qs.ps_stack +
      (if x IN FDOM qs.ps_spilled /\ MEM x (MAP Var nl) then 1 else 0) <=
      LIST_ELEM_COUNT x (done ++ rest) + (if MEM x (MAP Var nl) then 1 else 0)
Proof
  Induct_on `rest`
  >- simp[venomInstTheory.operand_vars_def, dfgDefsTheory.operand_vars_def] >>
  rpt gen_tac >> strip_tac >>
  drule emit_one_input_stack_upper_acc >>
  disch_then (qspec_then `opc` assume_tac) >>
  Cases_on `emit_one_input opc (operand_vars rest ++ nl) h ps` >>
  rename1 `emit_one_input _ _ _ _ = (step_ops,mid)` >>
  Cases_on `emit_input_plan opc rest nl mid` >>
  gvs[emit_input_plan_cons] >>
  first_x_assum drule >> disch_then drule >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem emit_input_plan_stack_live_upper:
  !opc operands nl ps iops qs.
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    set ps.ps_stack SUBSET set (MAP Var (operand_vars operands ++ nl)) /\
    emit_input_plan opc operands nl ps = (iops,qs) ==>
    !x. LIST_ELEM_COUNT x qs.ps_stack <=
      LIST_ELEM_COUNT x operands + (if MEM x (MAP Var nl) then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  `!x. LIST_ELEM_COUNT x ps.ps_stack +
    (if x IN FDOM ps.ps_spilled /\
        MEM x (MAP Var (operand_vars operands ++ nl)) then 1 else 0) <=
    LIST_ELEM_COUNT x [] +
    (if MEM x (MAP Var (operand_vars operands ++ nl)) then 1 else 0)` by
    (gen_tac >>
     drule all_distinct_elem_count_le_one >>
     disch_then (qspec_then `x` assume_tac) >>
     Cases_on `x IN FDOM ps.ps_spilled`
     >- (`~MEM x ps.ps_stack` by (gvs[DISJOINT_ALT] >> metis_tac[]) >>
         gvs[GSYM LIST_ELEM_COUNT_MEM, LIST_ELEM_COUNT_THM]) >>
     Cases_on `MEM x (MAP Var (operand_vars operands ++ nl))` >- simp[] >>
     `~MEM x ps.ps_stack` by (gvs[SUBSET_DEF] >> metis_tac[]) >>
     gvs[GSYM LIST_ELEM_COUNT_MEM, LIST_ELEM_COUNT_THM]) >>
  drule_all emit_input_plan_stack_upper_acc >> simp[] >> strip_tac >>
  gen_tac >> first_x_assum (qspec_then `x` mp_tac) >>
  Cases_on `x IN FDOM qs.ps_spilled /\ MEM x (MAP Var nl)` >> simp[]
QED

Theorem reduce_depth_plan_stack_count_mono:
  !fuel tops op f n ps ops qs.
    reduce_depth_plan fuel tops op f n ps = (ops,qs) ==>
    !x. LIST_ELEM_COUNT x qs.ps_stack <= LIST_ELEM_COUNT x ps.ps_stack
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `f + 1 < n` >> gvs[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> gvs[] >>
  rename1 `stack_get_unfixed_depth op f n ps.ps_stack = SOME dist` >>
  Cases_on `dist <= 16` >> gvs[] >>
  Cases_on `select_spill_candidate ps.ps_stack tops dist n` >> gvs[] >>
  rename1 `select_spill_candidate ps.ps_stack tops dist n = SOME cand` >>
  Cases_on `do_spill_at cand ps` >> gvs[] >>
  rename1 `do_spill_at cand ps = (spill_ops,mid)` >>
  Cases_on `reduce_depth_plan fuel tops op f n mid` >> gvs[] >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stackModelTheory.stack_get_unfixed_depth_bound >> simp[]) >>
  `cand <= 16 /\ cand < LENGTH ps.ps_stack` by
    metis_tac[select_spill_candidate_bound] >>
  gen_tac >> drule_all do_spill_at_stack_count >>
  disch_then (qspec_then `x` assume_tac) >>
  first_x_assum (drule_then (qspec_then `x` assume_tac)) >> decide_tac
QED

Theorem reorder_one_materialised_stack_count_mono:
  !dfg pending idx op ps ops qs d.
    idx < LENGTH pending /\ LENGTH pending <= LENGTH ps.ps_stack /\
    LENGTH pending <= 16 /\ MEM op pending /\
    stack_get_unfixed_depth op (LENGTH pending - 1 - idx)
      (LENGTH pending) ps.ps_stack = SOME d /\
    reorder_one dfg pending idx op ps = (ops,qs) ==>
    !x. LIST_ELEM_COUNT x qs.ps_stack <= LIST_ELEM_COUNT x ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH pending - 1 - idx = LENGTH pending - (idx + 1)` by decide_tac >>
  gvs[] >>
  `d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = op` by
    metis_tac[stackModelTheory.stack_get_unfixed_depth_props] >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  Cases_on `d > 16` >> simp[]
  >- (pairarg_tac >> simp[] >>
      rename1 `reduce_depth_plan _ _ _ _ _ ps = (reduce_ops,mid)` >>
      `LENGTH pending <= LENGTH mid.ps_stack` by
        (drule reduce_depth_plan_length_floor >> simp[] >> decide_tac) >>
      `?dist. stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
        (LENGTH pending) mid.ps_stack = SOME dist` by
        (qspecl_then [`LENGTH ps.ps_stack`, `pending`, `op`,
          `LENGTH pending - (idx + 1)`, `LENGTH pending`, `ps`, `d`]
          mp_tac (REWRITE_RULE [LET_THM] reduce_depth_plan_dist_ge) >>
         simp[] >> metis_tac[]) >>
      `dist < LENGTH mid.ps_stack /\ stack_peek dist mid.ps_stack = op` by
        metis_tac[stackModelTheory.stack_get_unfixed_depth_props] >>
      `LENGTH pending - (idx + 1) < LENGTH mid.ps_stack` by decide_tac >>
      qpat_x_assum `(case stack_get_unfixed_depth _ _ _ _ of _ => _) = _`
        mp_tac >> asm_rewrite_tac[] >>
      CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >> strip_tac >> gvs[] >>
      strip_tac >> gen_tac >>
      qspecl_then [`dfg`, `stack_peek d ps.ps_stack`, `dist`, `LENGTH pending - (idx + 1)`, `mid`, `x`]
        mp_tac reorder_place_phase_multiplicity >> simp[] >>
      drule reduce_depth_plan_stack_count_mono >>
      disch_then (qspec_then `x` assume_tac) >>
      Cases_on `dist = LENGTH pending - (idx + 1)` >> gvs[] >>
      Cases_on `operand_equiv dfg (stack_peek d ps.ps_stack)
        (stack_peek (LENGTH pending - (idx + 1)) mid.ps_stack)` >> gvs[] >>
      CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >> simp[]) >>
  strip_tac >> gen_tac >>
  qspecl_then [`dfg`, `op`, `d`, `LENGTH pending - (idx + 1)`, `ps`, `x`]
    mp_tac reorder_place_phase_multiplicity >> simp[] >> decide_tac
QED

Theorem plan_steps_reorder_materialised_stack_count_mono[local]:
  !items k dfg pending ps ops qs.
    k + LENGTH items = LENGTH pending /\
    (!j. j < LENGTH items ==>
      EL j items = (k + j, EL (k + j) pending)) /\
    LENGTH pending <= 16 /\ LENGTH pending <= LENGTH ps.ps_stack /\
    (!x. MEM x pending ==>
      LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x ps.ps_stack) /\
    (!i. i < k ==>
      stack_peek (LENGTH pending - 1 - i) ps.ps_stack = EL i pending) /\
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps)
      items ps = (ops,qs) ==>
    !x. LIST_ELEM_COUNT x qs.ps_stack <= LIST_ELEM_COUNT x ps.ps_stack
Proof
  Induct
  >- simp[plan_steps_def] >>
  rpt gen_tac >> strip_tac >>
  `h = (k, EL k pending)` by
    (qpat_x_assum `!j. j < LENGTH (h::items) ==> _`
      (qspec_then `0` mp_tac) >> simp[]) >>
  `k < LENGTH pending` by (fs[] >> decide_tac) >>
  drule plan_steps_cons_result >> strip_tac >>
  qpat_x_assum `h = _` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV pairLib.GEN_BETA_CONV)) >>
  rename1 `reorder_one dfg pending k (EL k pending) ps = (step_ops,mid)` >>
  `LENGTH pending <= LENGTH mid.ps_stack` by
    metis_tac[reorder_one_materialised_length_floor] >>
  `!i. i < SUC k ==>
    stack_peek (LENGTH pending - 1 - i) mid.ps_stack = EL i pending` by
    metis_tac[reorder_one_advances_fixed_window] >>
  `!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x ps.ps_stack` by
    (gen_tac >> Cases_on `MEM x pending`
     >- simp[] >>
     `LIST_ELEM_COUNT x pending = 0` by
       (qpat_x_assum `~MEM x pending` mp_tac >>
        rpt (pop_assum kall_tac) >> simp[GSYM LIST_ELEM_COUNT_MEM]) >> simp[]) >>
  `?d. stack_get_unfixed_depth (EL k pending)
    (LENGTH pending - 1 - k) (LENGTH pending) ps.ps_stack = SOME d` by
    metis_tac[materialised_pending_next_on_stack_window] >>
  `MEM (EL k pending) pending` by simp[EL_MEM] >>
  `!x. MEM x pending ==>
    LIST_ELEM_COUNT x mid.ps_stack = LIST_ELEM_COUNT x ps.ps_stack` by
    metis_tac[reorder_one_materialised_counts_unconditional] >>
  `!x. LIST_ELEM_COUNT x mid.ps_stack <= LIST_ELEM_COUNT x ps.ps_stack` by
    metis_tac[reorder_one_materialised_stack_count_mono] >>
  qpat_x_assum `!k dfg pending ps ops qs. _` (qspec_then `SUC k` mp_tac) >>
  disch_then (qspecl_then [`dfg`, `pending`, `mid`, `rest_ops`, `qs`] mp_tac) >>
  (impl_tac
  >- (simp[] >> conj_tac
      >- (fs[] >> decide_tac) >>
      gen_tac >> strip_tac >>
      qpat_x_assum `!j. j < LENGTH (_::items) ==> _`
        (qspec_then `SUC j` mp_tac) >> simp[ADD_CLAUSES, ADD_COMM])) >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem reorder_plan_materialised_stack_count_mono:
  !dfg pending ps ops qs.
    LENGTH pending <= 16 /\ LENGTH pending <= LENGTH ps.ps_stack /\
    (!x. MEM x pending ==>
      LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x ps.ps_stack) /\
    reorder_plan dfg pending ps = (ops,qs) ==>
    !x. LIST_ELEM_COUNT x qs.ps_stack <= LIST_ELEM_COUNT x ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`MAPi (\i op. (i,op)) pending`, `0`]
    mp_tac plan_steps_reorder_materialised_stack_count_mono >>
  disch_then (qspecl_then [`dfg`, `pending`, `ps`, `ops`, `qs`] mp_tac) >>
  simp[GSYM reorder_plan_eq_plan_steps, indexedListsTheory.LENGTH_MAPi,
    indexedListsTheory.EL_MAPi]
QED

Theorem emit_reorder_plan_core_stack_live_upper:
  !ps base operands selected opc nl dfg iops ps1 rops ps2.
    residual_budget_wf base [] ps /\ LENGTH operands <= 16 /\
    set ps.ps_stack SUBSET set (MAP Var (operand_vars operands ++ nl)) /\
    (!v. MEM (Var v) operands ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    PERM operands selected /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) ==>
    set (stack_pop (LENGTH selected) ps2.ps_stack) SUBSET set (MAP Var nl)
Proof
  rpt gen_tac >> strip_tac >> rename1 `residual_budget_wf spillbase [] ps` >>
  drule residual_budget_wf_empty_inventory >> strip_tac >>
  drule_all emit_input_plan_stack_live_upper >> strip_tac >>
  `!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (Cases >> gvs[is_var_operand_def]) >>
  drule_all emit_input_plan_materialised >> strip_tac >>
  drule_all available_input_plan_length >> strip_tac >>
  drule_all emit_input_plan_residual_budget_wf >> simp[] >> strip_tac >>
  drule perm_operand_counts >> strip_tac >>
  drule sortingTheory.PERM_LENGTH >> strip_tac >>
  `residual_budget_wf spillbase selected ps1` by
    metis_tac[residual_budget_wf_perm] >>
  `!x. MEM x selected ==>
    LIST_ELEM_COUNT x selected <= LIST_ELEM_COUNT x ps1.ps_stack` by metis_tac[] >>
  `LENGTH selected <= LENGTH ps1.ps_stack /\ LENGTH selected <= 16` by simp[] >>
  drule_all reorder_plan_materialised_stack_count_mono >> strip_tac >>
  drule_all emit_reorder_plan_core_suffix >> strip_tac >>
  simp[SUBSET_DEF] >> gen_tac >> strip_tac >>
  `LIST_ELEM_COUNT x ps2.ps_stack <=
    LIST_ELEM_COUNT x selected + (if MEM x (MAP Var nl) then 1 else 0)` by
    metis_tac[LESS_EQ_TRANS] >>
  qpat_x_assum `LIST_ELEM_COUNT x ps2.ps_stack <= _` mp_tac >>
  qpat_x_assum `ps2.ps_stack = _` (fn th => once_rewrite_tac[th]) >>
  simp[elem_count_append, stack_pop_def, TAKE_APPEND, TAKE_TAKE] >>
  gvs[stack_pop_def, GSYM LIST_ELEM_COUNT_MEM] >> decide_tac
QED

Theorem emit_reorder_pop_marker_core_stack_live_upper:
  !ps m core base operands selected opc nl dfg iops ps1 rops ps2 qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    set core SUBSET set (MAP Var (operand_vars operands ++ nl)) /\
    EVERY (\x. x <> dead_stack_marker) operands /\ LENGTH operands <= 16 /\
    (!v. MEM (Var v) operands ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    PERM operands selected /\
    emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps2) /\
    qs = ps2 with ps_stack := stack_pop (LENGTH operands) ps2.ps_stack ==>
    ?rest. qs.ps_stack = REPLICATE m dead_stack_marker ++ rest /\
      residual_budget_wf base [] (qs with ps_stack := rest) /\
      set rest SUBSET set (MAP Var nl)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emit_reorder_pop_marker_execution >> strip_tac >>
  `!v. MEM (Var v) operands ==>
    MEM (Var v) (ps with ps_stack := core).ps_stack \/
      Var v IN FDOM (ps with ps_stack := core).ps_spilled` by
    (gvs[MEM_REPLICATE, dead_stack_marker_def] >> metis_tac[]) >>
  `set (ps with ps_stack := core).ps_stack SUBSET
    set (MAP Var (operand_vars operands ++ nl))` by gvs[] >>
  drule_all emit_reorder_plan_core_stack_live_upper >> strip_tac >>
  `set [] SUBSET set nl` by simp[] >>
  `!v. MEM (Var v) operands \/ MEM v [] ==>
    MEM (Var v) (ps with ps_stack := core).ps_stack \/
      Var v IN FDOM (ps with ps_stack := core).ps_spilled` by simp[] >>
  drule_all emit_reorder_plan_core_protected_consumption >> strip_tac >>
  qpat_x_assum `qs = ps2 with ps_stack := _` kall_tac >>
  qexists_tac `stack_pop (LENGTH selected) cs2.ps_stack` >> gvs[]
QED

Theorem native_regular_stack_live_inventory:
  !lv dfg cfg fn inst nl term lbl ps m core base ops qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\
    EVERY (\x. x <> dead_stack_marker) (compute_operands inst) /\
    (!v. MEM (Var v) (compute_operands inst) \/
      (MEM v nl /\ ~MEM v inst.inst_outputs) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    generate_regular_inst_plan lv dfg cfg fn inst nl F term lbl ps = (ops,qs) /\
    set core SUBSET set (MAP Var (operand_vars (compute_operands inst) ++ nl)) /\
    ALL_DISTINCT inst.inst_outputs /\
    EVERY (\v. ~MEM (Var v) (compute_operands inst) /\ ~MEM (Var v) core /\
      Var v NOTIN FDOM ps.ps_spilled) inst.inst_outputs ==>
    lineage_inventory (set (MAP Var nl)) qs /\
    ?rest. lineage_core m rest qs /\
      residual_budget_wf base [] (qs with ps_stack := rest)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_regular_stages >>
  impl_tac >- simp[] >> strip_tac >>
  `!v. MEM (Var v) (compute_operands inst) ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
  qabbrev_tac `consumed = ps4 with ps_stack :=
    stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack` >>
  `consumed = ps4 with ps_stack :=
    stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack` by simp[Abbr `consumed`] >>
  drule_all emit_reorder_pop_marker_core_stack_live_upper >> strip_tac >>
  `EVERY (\v. ~MEM (Var v) rest /\ Var v NOTIN FDOM consumed.ps_spilled)
    inst.inst_outputs` by
    (drule_all emit_reorder_pop_marker_core_fresh >> strip_tac >>
     metis_tac[APPEND_11]) >>
  qabbrev_tac `emitted = FOLDL (\p v. p with ps_stack := stack_push (Var v) p.ps_stack)
    consumed inst.inst_outputs` >>
  `emitted = FOLDL (\p v. p with ps_stack := stack_push (Var v) p.ps_stack)
    consumed inst.inst_outputs` by simp[Abbr `emitted`] >>
  drule_all output_push_marker_core >> strip_tac >>
  `generate_emit_ops inst topic emitted = (eops,ps7)` by simp[Abbr `emitted`, Abbr `consumed`] >>
  drule_all generate_emit_ops_core_resource >> strip_tac >>
  suspend "tail"
QED

Resume native_regular_stack_live_inventory[tail]:
  `!v. MEM v nl ==>
    MEM (Var v) (stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack ++ MAP Var inst.inst_outputs) \/
    Var v IN FDOM ps4.ps_spilled` by
    (mp_tac (Q.SPECL [`ps`, `compute_operands inst`, `selected`,
       `inst.inst_opcode`, `nl`, `inst.inst_outputs`, `dfg`, `iops`, `ps1`,
       `rops`, `ps4`] emit_reorder_output_live_coverage) >>
     ntac 2 (impl_tac >- first_assum ACCEPT_TAC) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  drule generate_emit_ops_slots >> strip_tac >>
  `ps7.ps_stack = REPLICATE m dead_stack_marker ++ (rest ++ MAP Var inst.inst_outputs)` by metis_tac[] >>
  `stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack =
    REPLICATE m dead_stack_marker ++ rest` by
    (qpat_x_assum `consumed.ps_stack = _` mp_tac >> simp[Abbr `consumed`]) >>
  `ps7.ps_spilled = ps4.ps_spilled` by simp[Abbr `consumed`] >>
  `set (MAP Var nl) SUBSET set (rest ++ MAP Var inst.inst_outputs) UNION FDOM ps7.ps_spilled` by
    (simp[SUBSET_DEF, MEM_MAP] >> rpt strip_tac >> rename1 `MEM v nl` >>
     qpat_x_assum `!v. MEM v nl ==> MEM (Var v) (_ ++ _) \/ _`
       (qspec_then `v` mp_tac) >>
     simp[MEM_REPLICATE, dead_stack_marker_def, MEM_MAP] >> metis_tac[]) >>
  qabbrev_tac `deleted = MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs)` >>
  `set (rest ++ MAP Var inst.inst_outputs) DIFF set deleted SUBSET set (MAP Var nl)` by
    (simp[Abbr `deleted`, SUBSET_DEF, MEM_MAP, MEM_FILTER] >>
     rpt strip_tac >>
     qpat_x_assum `set rest SUBSET _` mp_tac >>
     simp[SUBSET_DEF, MEM_MAP] >> metis_tac[]) >>
  `deleted = if inst.inst_outputs <> [] /\ (~F \/ LENGTH inst.inst_outputs > 1)
    then MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs) else []` by
    (Cases_on `inst.inst_outputs` >> simp[Abbr `deleted`]) >>
  `ps8 = if inst.inst_outputs <> [] /\ (~F \/ LENGTH inst.inst_outputs > 1)
    then SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs)) ps7)
    else ps7` by
    (qpat_x_assum `ps8 = _` mp_tac >> simp[Abbr `deleted`]) >>
  drule_all regular_post_emit_tail_live_inventory >> simp[]
QED

Finalise native_regular_stack_live_inventory
