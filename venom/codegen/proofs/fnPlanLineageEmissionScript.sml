Theory fnPlanLineageEmission
Ancestors
  stackPlanGen fnPlanLineagePrefix list

Definition emission_anchor_def:
  emission_anchor op =
    case op of
      SOSwap _ => F | SODup _ => F | SOPop _ => F |
      SOSpill _ => F | SORestore _ => F | SOPoke _ _ => F |
      _ => T
End

Definition emission_projection_def:
  emission_projection ops = FILTER emission_anchor ops
End

Theorem emission_projection_append[simp]:
  !xs ys. emission_projection (xs ++ ys) =
    emission_projection xs ++ emission_projection ys
Proof
  simp[emission_projection_def, rich_listTheory.FILTER_APPEND]
QED

(* Actual emission depends on the label counter, not the physical resources.
   This does not synchronize source instruction boundaries in flattened code. *)
Theorem generate_emit_ops_label_counter_congruence:
  !inst topics p q.
    p.ps_label_counter = q.ps_label_counter ==>
    FST (generate_emit_ops inst topics p) = FST (generate_emit_ops inst topics q) /\
    (SND (generate_emit_ops inst topics p)).ps_label_counter =
      (SND (generate_emit_ops inst topics q)).ps_label_counter
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INITIAL_FMP`
  >- simp[generate_emit_ops_def] >>
  Cases_on `inst.inst_opcode = BUMP`
  >- simp[generate_emit_ops_def] >>
  Cases_on `venom_to_evm_name inst.inst_opcode`
  >- (simp[generate_emit_ops_def, stackPlanTypesTheory.fresh_label_def] >>
      rpt IF_CASES_TAC >> gvs[] >>
      rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  simp[generate_emit_ops_def]
QED

Theorem do_spill_tos_emission:
  !ps. emission_projection (FST (do_spill_tos ps)) = [] /\
    (SND (do_spill_tos ps)).ps_label_counter = ps.ps_label_counter
Proof
  gen_tac >> Cases_on `alloc_spill_slot ps.ps_alloc` >>
  simp[stackPlanOpsTheory.do_spill_tos_def,
       emission_projection_def, emission_anchor_def]
QED

Theorem do_restore_emission:
  !op ps. emission_projection (FST (do_restore op ps)) = [] /\
    (SND (do_restore op ps)).ps_label_counter = ps.ps_label_counter
Proof
  rpt gen_tac >> simp[stackPlanOpsTheory.do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[emission_projection_def, emission_anchor_def]
QED

Theorem do_spill_at_emission:
  !dist ps. emission_projection (FST (do_spill_at dist ps)) = [] /\
    (SND (do_spill_at dist ps)).ps_label_counter = ps.ps_label_counter
Proof
  rpt gen_tac >> simp[stackPlanOpsTheory.do_spill_at_def] >>
  Cases_on `dist = 0` >> simp[do_spill_tos_emission] >>
  Cases_on `do_spill_tos (ps with ps_stack := stack_swap dist ps.ps_stack)` >>
  qspec_then `ps with ps_stack := stack_swap dist ps.ps_stack` mp_tac
    do_spill_tos_emission >>
  gvs[emission_projection_def, emission_anchor_def]
QED

Theorem spill_fold_emission[local]:
  !items ops offs al.
    emission_projection
      (FST (FOLDL (\(ops,offs,al) item.
        let (off,al') = alloc_spill_slot al in
        (ops ++ [SOSpill off], SNOC off offs, al'))
        (ops,offs,al) items)) = emission_projection ops
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `alloc_spill_slot al` >>
  first_x_assum (qspecl_then [`ops ++ [SOSpill q]`, `SNOC q offs`, `r`] mp_tac) >>
  simp[emission_projection_def, emission_anchor_def,
       rich_listTheory.FILTER_APPEND]
QED

Theorem emission_projection_map_restore[simp]:
  !xs f. emission_projection (MAP (\x. SORestore (f x)) xs) = []
Proof
  Induct >> gvs[emission_projection_def, emission_anchor_def]
QED

Theorem do_swap_emission:
  !dist ps. emission_projection (FST (do_swap dist ps)) = [] /\
    (SND (do_swap dist ps)).ps_label_counter = ps.ps_label_counter
Proof
  rpt gen_tac >> simp[stackPlanOpsTheory.do_swap_def] >>
  rpt IF_CASES_TAC >> simp[] >>
  TRY (simp[emission_projection_def, emission_anchor_def] >> NO_TAC) >>
  pairarg_tac >> gvs[] >>
  qspec_then `top_n (dist + 1) ps.ps_stack` mp_tac spill_fold_emission >>
  disch_then (qspecl_then [`[]`, `[]`, `ps.ps_alloc`] mp_tac) >>
  gvs[emission_projection_def, emission_anchor_def,
       rich_listTheory.FILTER_APPEND, SNOC_APPEND]
QED

Theorem emission_projection_flat[simp]:
  !xss. emission_projection (FLAT xss) =
    FLAT (MAP emission_projection xss)
Proof
  Induct >- simp[emission_projection_def] >>
  simp[emission_projection_append]
QED

Theorem do_dup_emission:
  !dist ps. emission_projection (FST (do_dup dist ps)) = [] /\
    (SND (do_dup dist ps)).ps_label_counter = ps.ps_label_counter
Proof
  rpt gen_tac >> simp[stackPlanOpsTheory.do_dup_def] >>
  IF_CASES_TAC
  >- simp[emission_projection_def, emission_anchor_def] >>
  pairarg_tac >> gvs[] >>
  qspec_then `REVERSE (top_n (dist - 15) ps.ps_stack)` mp_tac
    spill_fold_emission >>
  disch_then (qspecl_then [`[]`, `[]`, `ps.ps_alloc`] mp_tac) >>
  gvs[SNOC_APPEND] >> strip_tac >>
  IF_CASES_TAC >>
  gvs[emission_projection_def, emission_anchor_def,
      rich_listTheory.FILTER_APPEND, rich_listTheory.FILTER_FLAT, MAP_MAP_o, combinTheory.o_DEF,
      FLAT_EQ_NIL, EVERY_MAP]
QED

Theorem restore_spilled_plan_emission:
  !xs ps. emission_projection (FST (restore_spilled_plan xs ps)) = [] /\
    (SND (restore_spilled_plan xs ps)).ps_label_counter = ps.ps_label_counter
Proof
  Induct >- simp[stackPlanOpsTheory.restore_spilled_plan_def,
                 emission_projection_def] >>
  rpt gen_tac >> simp[stackPlanOpsTheory.restore_spilled_plan_def] >>
  pairarg_tac >> gvs[] >>
  Cases_on `restore_spilled_plan xs ps1` >> gvs[] >>
  qspecl_then [`h`, `ps`] mp_tac do_restore_emission >>
  first_x_assum (qspec_then `ps1` mp_tac) >>
  gvs[emission_projection_append]
QED

Theorem reduce_depth_plan_emission:
  !fuel targets op f n ps.
    emission_projection (FST (reduce_depth_plan fuel targets op f n ps)) = [] /\
    (SND (reduce_depth_plan fuel targets op f n ps)).ps_label_counter =
      ps.ps_label_counter
Proof
  Induct >- simp[stackPlanOpsTheory.reduce_depth_plan_def, emission_projection_def] >>
  rpt gen_tac >> simp[stackPlanOpsTheory.reduce_depth_plan_def] >>
  IF_CASES_TAC >- simp[emission_projection_def] >>
  BasicProvers.TOP_CASE_TAC >- simp[emission_projection_def] >>
  IF_CASES_TAC >- simp[emission_projection_def] >>
  BasicProvers.TOP_CASE_TAC >- simp[emission_projection_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `do_spill_at cand ps = (ops1, ps1)` >>
  Cases_on `reduce_depth_plan fuel targets op f n ps1` >> gvs[] >>
  qspecl_then [`cand`, `ps`] mp_tac do_spill_at_emission >>
  first_x_assum (qspecl_then [`targets`, `op`, `f`, `n`, `ps1`] mp_tac) >>
  gvs[emission_projection_append]
QED

Theorem reorder_one_emission:
  !dfg targets idx op ps.
    emission_projection (FST (reorder_one dfg targets idx op ps)) = [] /\
    (SND (reorder_one dfg targets idx op ps)).ps_label_counter =
      ps.ps_label_counter
Proof
  rpt gen_tac >> simp[stackPlanOpsTheory.reorder_one_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `restore_ops ++ _` >>
  `emission_projection restore_ops = [] /\
   ps1.ps_label_counter = ps.ps_label_counter` by
    (qpat_x_assum `_ = (restore_ops, ps1)` mp_tac >>
     rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >>
     strip_tac >> qspecl_then [`op`, `ps`] mp_tac do_restore_emission >>
     gvs[emission_projection_def]) >>
  BasicProvers.TOP_CASE_TAC >- gvs[] >>
  pairarg_tac >> gvs[] >>
  `emission_projection reduce_ops = [] /\
   ps2.ps_label_counter = ps1.ps_label_counter` by
    (qpat_x_assum `_ = (reduce_ops, ps2)` mp_tac >>
     IF_CASES_TAC >> gvs[emission_projection_def] >>
     strip_tac >>
     qspecl_then [`LENGTH ps1.ps_stack`, `targets`, `op`,
                  `LENGTH targets - 1 - idx`, `LENGTH targets`, `ps1`]
       mp_tac reduce_depth_plan_emission >> gvs[emission_projection_def]) >>
  BasicProvers.TOP_CASE_TAC >- gvs[] >>
  rpt IF_CASES_TAC >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `do_swap d1 ps2 = (swap1_ops, ps3)` >>
  rename1 `do_swap d2 ps3 = (swap2_ops, ps4)` >>
  qspecl_then [`d1`, `ps2`] mp_tac do_swap_emission >>
  qspecl_then [`d2`, `ps3`] mp_tac do_swap_emission >>
  gvs[]
QED

Theorem reorder_fold_emission[local]:
  !xs dfg targets ops ps.
    emission_projection (FST (FOLDL (\(ops,ps) (idx,op).
      let (step_ops,ps') = reorder_one dfg targets idx op ps in
      (ops ++ step_ops,ps')) (ops,ps) xs)) = emission_projection ops /\
    (SND (FOLDL (\(ops,ps) (idx,op).
      let (step_ops,ps') = reorder_one dfg targets idx op ps in
      (ops ++ step_ops,ps')) (ops,ps) xs)).ps_label_counter = ps.ps_label_counter
Proof
  Induct >- simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >>
  pairarg_tac >> gvs[] >>
  qspecl_then [`dfg`, `targets`, `h0`, `h1`, `ps`] mp_tac reorder_one_emission >>
  first_x_assum (qspecl_then [`dfg`, `targets`, `ops ++ step_ops`, `ps'`] mp_tac) >>
  gvs[]
QED

Theorem reorder_plan_emission:
  !dfg targets ps.
    emission_projection (FST (reorder_plan dfg targets ps)) = [] /\
    (SND (reorder_plan dfg targets ps)).ps_label_counter = ps.ps_label_counter
Proof
  rpt gen_tac >>
  qspec_then `MAPi (\i op. (i,op)) targets` mp_tac reorder_fold_emission >>
  disch_then (qspecl_then [`dfg`, `targets`, `[]`, `ps`] mp_tac) >>
  simp[stackPlanOpsTheory.reorder_plan_def, emission_projection_def]
QED

Theorem popmany_fold_emission[local]:
  !xs ops ps.
    emission_projection (FST (FOLDL (\(ops,ps) v.
      case stack_get_depth v ps.ps_stack of NONE => (ops,ps)
      | SOME dist =>
        let (swap_ops,ps') = if dist = 0 then ([],ps) else do_swap dist ps in
        (ops ++ swap_ops ++ [SOPop 1],
         ps' with ps_stack := stack_pop 1 ps'.ps_stack)) (ops,ps) xs)) =
      emission_projection ops /\
    (SND (FOLDL (\(ops,ps) v.
      case stack_get_depth v ps.ps_stack of NONE => (ops,ps)
      | SOME dist =>
        let (swap_ops,ps') = if dist = 0 then ([],ps) else do_swap dist ps in
        (ops ++ swap_ops ++ [SOPop 1],
         ps' with ps_stack := stack_pop 1 ps'.ps_stack)) (ops,ps) xs)).ps_label_counter =
      ps.ps_label_counter
Proof
  Induct >- simp[] >> rpt gen_tac >> simp[] >>
  BasicProvers.TOP_CASE_TAC >- gvs[] >>
  pairarg_tac >> gvs[] >>
  `emission_projection swap_ops = [] /\
   ps'.ps_label_counter = ps.ps_label_counter` by
    (qpat_x_assum `_ = (swap_ops,ps')` mp_tac >>
     IF_CASES_TAC >> gvs[emission_projection_def] >>
     strip_tac >> qspecl_then [`x`, `ps`] mp_tac do_swap_emission >>
     gvs[emission_projection_def]) >>
  first_x_assum (qspecl_then
    [`ops ++ swap_ops ++ [SOPop 1]`,
     `ps' with ps_stack := stack_pop 1 ps'.ps_stack`] mp_tac) >>
  gvs[emission_projection_def, emission_anchor_def, rich_listTheory.FILTER_APPEND]
QED

Theorem popmany_individual_emission:
  !xs ps. emission_projection (FST (popmany_individual xs ps)) = [] /\
    (SND (popmany_individual xs ps)).ps_label_counter = ps.ps_label_counter
Proof
  rpt gen_tac >>
  simp[stackPlanOpsTheory.popmany_individual_def] >>
  qmatch_goalsub_abbrev_tac `FOLDL f ([],ps) sorted` >>
  qspec_then `sorted` mp_tac popmany_fold_emission >>
  disch_then (qspecl_then [`[]`, `ps`] mp_tac) >>
  simp[Abbr `f`, emission_projection_def]
QED

Theorem popmany_plan_emission:
  !xs ps. emission_projection (FST (popmany_plan xs ps)) = [] /\
    (SND (popmany_plan xs ps)).ps_label_counter = ps.ps_label_counter
Proof
  Cases >- simp[stackPlanOpsTheory.popmany_plan_def, emission_projection_def] >>
  rpt gen_tac >> simp[stackPlanOpsTheory.popmany_plan_def] >>
  IF_CASES_TAC >- (IF_CASES_TAC
    >- (pairarg_tac >> gvs[] >>
        qspecl_then [`LENGTH (h::t)`, `ps`] mp_tac do_swap_emission >>
        gvs[emission_projection_def, emission_anchor_def, rich_listTheory.FILTER_APPEND]) >>
    simp[popmany_individual_emission]) >>
  simp[popmany_individual_emission]
QED

Definition input_emission_def:
  input_emission opc op =
    case op of
      Var _ => []
    | Lit v => [SOPush (Lit v)]
    | Label l => if opc = INVOKE then [] else [SOPushLabel l]
End

Theorem emit_one_input_emission:
  !opc live op ps.
    emission_projection (FST (emit_one_input opc live op ps)) =
      input_emission opc op /\
    (SND (emit_one_input opc live op ps)).ps_label_counter = ps.ps_label_counter
Proof
  rpt gen_tac >> simp[emit_one_input_def] >>
  pairarg_tac >> gvs[] >>
  `emission_projection restore_ops = [] /\
   ps1.ps_label_counter = ps.ps_label_counter` by
    (qpat_x_assum `_ = (restore_ops,ps1)` mp_tac >>
     IF_CASES_TAC >> gvs[emission_projection_def] >> strip_tac >>
     qspecl_then [`op`, `ps`] mp_tac do_restore_emission >>
     gvs[emission_projection_def]) >>
  Cases_on `op` >> simp[input_emission_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[emission_projection_def, emission_anchor_def,
            rich_listTheory.FILTER_APPEND] >> NO_TAC) >>
  BasicProvers.TOP_CASE_TAC >- gvs[] >>
  pairarg_tac >> gvs[] >>
  qspecl_then [`x`, `ps1`] mp_tac do_dup_emission >> gvs[]
QED

Theorem emit_input_plan_emission:
  !xs opc live ps.
    emission_projection (FST (emit_input_plan opc xs live ps)) =
      FLAT (MAP (input_emission opc) xs) /\
    (SND (emit_input_plan opc xs live ps)).ps_label_counter = ps.ps_label_counter
Proof
  Induct >- simp[emit_input_plan_def, emission_projection_def] >>
  rpt gen_tac >> simp[emit_input_plan_def] >>
  pairarg_tac >> gvs[] >>
  Cases_on `emit_input_plan opc xs live ps1` >> gvs[] >>
  qspecl_then [`opc`, `operand_vars xs ++ live`, `h`, `ps`]
    mp_tac emit_one_input_emission >>
  first_x_assum (qspecl_then [`opc`, `live`, `ps1`] mp_tac) >>
  gvs[]
QED

Theorem optimistic_swap_plan_emission:
  !dfg inst live term ps.
    emission_projection (FST (optimistic_swap_plan dfg inst live term ps)) = [] /\
    (SND (optimistic_swap_plan dfg inst live term ps)).ps_label_counter =
      ps.ps_label_counter
Proof
  rpt gen_tac >> simp[optimistic_swap_plan_def] >>
  rpt IF_CASES_TAC >> simp[emission_projection_def] >>
  BasicProvers.TOP_CASE_TAC >- simp[] >>
  qspecl_then [`x`, `ps`] mp_tac do_swap_emission >>
  simp[emission_projection_def]
QED

Theorem generate_phi_plan_emission:
  !inst live halt ps.
    emission_projection (FST (generate_phi_plan inst live halt ps)) = [] /\
    (SND (generate_phi_plan inst live halt ps)).ps_label_counter = ps.ps_label_counter
Proof
  rpt gen_tac >> simp[generate_phi_plan_def] >>
  BasicProvers.TOP_CASE_TAC >- simp[emission_projection_def] >>
  pairarg_tac >> gvs[] >>
  `emission_projection ops = [] /\
   ps'.ps_label_counter = ps.ps_label_counter` by
    (qpat_x_assum `_ = (ops,ps')` mp_tac >>
     IF_CASES_TAC
     >- (Cases_on `do_dup x ps` >> gvs[] >> strip_tac >>
         qspecl_then [`x`, `ps`] mp_tac do_dup_emission >>
         gvs[emission_projection_def, emission_anchor_def, rich_listTheory.FILTER_APPEND]) >>
     strip_tac >> gvs[emission_projection_def, emission_anchor_def]) >>
  IF_CASES_TAC >- (pairarg_tac >> gvs[] >>
    qspecl_then [`[Var (HD inst.inst_outputs)]`, `ps'`] mp_tac popmany_plan_emission >>
    gvs[]) >> gvs[]
QED

Theorem generate_offset_plan_emission:
  !inst ps.
    FST (generate_offset_plan inst ps) = FST (generate_offset_plan inst q) /\
    (SND (generate_offset_plan inst ps)).ps_label_counter = ps.ps_label_counter
Proof
  rpt gen_tac >> simp[generate_offset_plan_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Theorem clean_stack_plan_emission:
  !liveness cfg fn bb ps.
    emission_projection (FST (clean_stack_plan liveness cfg fn bb ps)) = [] /\
    (SND (clean_stack_plan liveness cfg fn bb ps)).ps_label_counter = ps.ps_label_counter
Proof
  rpt gen_tac >> simp[clean_stack_plan_def] >>
  Cases_on `cfg_preds_of cfg bb.bb_label` >- simp[emission_projection_def] >>
  Cases_on `t` >> simp[emission_projection_def] >>
  IF_CASES_TAC >- simp[] >>
  BasicProvers.TOP_CASE_TAC >- simp[] >>
  rpt IF_CASES_TAC >> simp[] >>
  TRY (pairarg_tac >> gvs[] >>
    rename1 `popmany_plan xs ps = (ops,ps')` >>
    qspecl_then [`xs`, `ps`] mp_tac popmany_plan_emission >>
    gvs[emission_projection_def] >> NO_TAC) >>
  qmatch_goalsub_abbrev_tac `popmany_plan xs ps` >>
  qspecl_then [`xs`, `ps`] mp_tac popmany_plan_emission >>
  simp[emission_projection_def]
QED

Theorem foldl_observation_preserved:
  !xs step observe init.
    (!s x. observe (step s x) = observe s) ==>
    observe (FOLDL step init xs) = observe init
Proof
  Induct >> simp[]
QED

Theorem release_dead_spills_label_counter[simp]:
  !live ps. (release_dead_spills live ps).ps_label_counter = ps.ps_label_counter
Proof
  rpt gen_tac >> simp[stackPlanOpsTheory.release_dead_spills_def] >>
  irule foldl_observation_preserved >>
  simp[pairTheory.FORALL_PROD]
QED

Theorem push_outputs_label_counter[simp]:
  !outs ps.
    (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
      ps outs).ps_label_counter = ps.ps_label_counter
Proof
  rpt gen_tac >> irule foldl_observation_preserved >> simp[]
QED

Theorem prepare_params_plan_emission:
  !live fn ps.
    emission_projection (FST (prepare_params_plan live fn ps)) = [] /\
    (SND (prepare_params_plan live fn ps)).ps_label_counter = ps.ps_label_counter
Proof
  rpt gen_tac >> simp[prepare_params_plan_def] >>
  IF_CASES_TAC >- simp[emission_projection_def] >>
  pairarg_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `popmany_plan xs start = (pop_ops,ps'')` >>
  qspecl_then [`xs`, `start`] mp_tac popmany_plan_emission >>
  gvs[] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  rename1 `optimistic_swap_plan dfg_empty inst nl nt ps'' = (swap_ops,ps''')` >>
  qspecl_then [`dfg_empty`, `inst`, `nl`, `nt`, `ps''`]
    mp_tac optimistic_swap_plan_emission >>
  gvs[] >> strip_tac >>
  gvs[emission_projection_def, rich_listTheory.FILTER_APPEND] >>
  simp[Abbr `start`] >>
  irule foldl_observation_preserved >> simp[]
QED

Theorem generate_regular_inst_plan_emission:
  !liveness dfg cfg fn inst live halt term lbl ps.
    emission_projection (FST (generate_regular_inst_plan liveness dfg cfg fn
      inst live halt term lbl ps)) =
      FLAT (MAP (input_emission inst.inst_opcode) (compute_operands inst)) ++
      emission_projection (FST (generate_emit_ops inst
        (case inst.inst_opcode of LOG =>
          (case HD inst.inst_operands of Lit v => w2n v | _ => 0)
        | _ => 0) ps)) /\
    (SND (generate_regular_inst_plan liveness dfg cfg fn
      inst live halt term lbl ps)).ps_label_counter =
      (SND (generate_emit_ops inst
        (case inst.inst_opcode of LOG =>
          (case HD inst.inst_operands of Lit v => w2n v | _ => 0)
        | _ => 0) ps)).ps_label_counter
Proof
  rpt gen_tac >> simp[generate_regular_inst_plan_def] >>
  qmatch_goalsub_abbrev_tac `generate_emit_ops inst topics` >>
  pairarg_tac >> gvs[] >>
  qspecl_then [`compute_operands inst`, `inst.inst_opcode`, `live`, `ps`]
    mp_tac emit_input_plan_emission >> gvs[] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  `emission_projection join_ops = [] /\
   ps2.ps_label_counter = ps1.ps_label_counter` by
    (qpat_x_assum `_ = (join_ops,ps2)` mp_tac >>
     IF_CASES_TAC >- (
       BasicProvers.TOP_CASE_TAC >- (strip_tac >> gvs[emission_projection_def]) >>
       pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
       qspecl_then [`x`, `ps1`] mp_tac restore_spilled_plan_emission >>
       qspecl_then [`dfg`, `x`, `ps1'`] mp_tac reorder_plan_emission >> gvs[]) >>
     strip_tac >> gvs[emission_projection_def]) >>
  pairarg_tac >> gvs[] >>
  `emission_projection reorder_ops = [] /\
   ps4.ps_label_counter = ps2.ps_label_counter` by
    (qpat_x_assum `_ = (reorder_ops,ps4)` mp_tac >>
     IF_CASES_TAC >- (
       pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
       qspecl_then [`dfg`, `compute_operands inst`, `ps2`]
         mp_tac reorder_plan_emission >> gvs[] >> strip_tac >>
       qmatch_asmsub_abbrev_tac `reorder_plan dfg swapped ps2 = _` >>
       qspecl_then [`dfg`, `swapped`, `ps2`] mp_tac reorder_plan_emission >>
       gvs[] >> strip_tac >> IF_CASES_TAC >> strip_tac >> gvs[]) >>
     strip_tac >> qspecl_then [`dfg`, `compute_operands inst`, `ps2`]
       mp_tac reorder_plan_emission >> gvs[]) >>
  pairarg_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `generate_emit_ops inst topics emit_start = _` >>
  `emit_start.ps_label_counter = ps.ps_label_counter` by
    simp[Abbr `emit_start`] >>
  drule generate_emit_ops_label_counter_congruence >>
  disch_then (qspecl_then [`inst`, `topics`] mp_tac) >>
  gvs[] >> strip_tac >>
  IF_CASES_TAC >- simp[] >>
  pairarg_tac >> gvs[] >>
  `emission_projection pop_ops = [] /\
   ps8.ps_label_counter = ps7.ps_label_counter` by
    (qpat_x_assum `_ = (pop_ops,ps8)` mp_tac >>
     IF_CASES_TAC >- (
       strip_tac >>
       qmatch_asmsub_abbrev_tac `popmany_plan dead ps7 = _` >>
       qspecl_then [`dead`, `ps7`] mp_tac popmany_plan_emission >> gvs[]) >>
     strip_tac >> gvs[emission_projection_def]) >>
  pairarg_tac >> gvs[] >>
  `emission_projection opt_ops = [] /\
   ps9.ps_label_counter = ps8.ps_label_counter` by
    (qpat_x_assum `_ = (opt_ops,ps9)` mp_tac >>
     IF_CASES_TAC >- (strip_tac >> gvs[emission_projection_def]) >>
     strip_tac >> qspecl_then [`dfg`, `inst`, `live`, `term`, `ps8`]
       mp_tac optimistic_swap_plan_emission >> gvs[]) >>
  simp[]
QED

Theorem generate_regular_inst_plan_emission_congruence:
  !liveness dfg cfg fn inst live halt term lbl p q.
    p.ps_label_counter = q.ps_label_counter ==>
    emission_projection (FST (generate_regular_inst_plan liveness dfg cfg fn
      inst live halt term lbl p)) =
    emission_projection (FST (generate_regular_inst_plan liveness dfg cfg fn
      inst live halt term lbl q)) /\
    (SND (generate_regular_inst_plan liveness dfg cfg fn
      inst live halt term lbl p)).ps_label_counter =
    (SND (generate_regular_inst_plan liveness dfg cfg fn
      inst live halt term lbl q)).ps_label_counter
Proof
  rpt strip_tac >> simp[generate_regular_inst_plan_emission] >>
  drule generate_emit_ops_label_counter_congruence >>
  disch_then (qspec_then `inst` mp_tac) >>
  qmatch_goalsub_abbrev_tac `generate_emit_ops inst topics` >>
  disch_then (qspec_then `topics` strip_assume_tac) >> simp[]
QED

Theorem generate_inst_plan_emission_congruence:
  !liveness dfg cfg fn inst live halt term lbl p q ops p' ops' q'.
    p.ps_label_counter = q.ps_label_counter /\
    generate_inst_plan liveness dfg cfg fn inst live halt term lbl p = SOME (ops,p') /\
    generate_inst_plan liveness dfg cfg fn inst live halt term lbl q = SOME (ops',q') ==>
    emission_projection ops = emission_projection ops' /\
    p'.ps_label_counter = q'.ps_label_counter
Proof
  rpt gen_tac >> simp[generate_inst_plan_def] >>
  rpt IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
  TRY (simp[emission_projection_def] >> NO_TAC) >>
  TRY (rename1 `generate_phi_plan inst live halt p = _` >>
    qspecl_then [`inst`, `live`, `halt`, `p`] mp_tac generate_phi_plan_emission >>
    qspecl_then [`inst`, `live`, `halt`, `q`] mp_tac generate_phi_plan_emission >>
    gvs[] >> NO_TAC) >>
  TRY (rename1 `generate_offset_plan inst p = _` >>
    gvs[generate_offset_plan_def, AllCaseEqs()] >> NO_TAC) >>
  drule generate_regular_inst_plan_emission_congruence >>
  gvs[quantHeuristicsTheory.PAIR_EQ_EXPAND]
QED

Theorem generate_block_insts_plan_emission_congruence:
  !xs i lv dfg cfg fn lbl halt np bl p q ops p' ops' q'.
    p.ps_label_counter = q.ps_label_counter /\
    generate_block_insts_plan lv dfg cfg fn lbl halt np bl i xs p = SOME (ops,p') /\
    generate_block_insts_plan lv dfg cfg fn lbl halt np bl i xs q = SOME (ops',q') ==>
    emission_projection ops = emission_projection ops' /\
    p'.ps_label_counter = q'.ps_label_counter
Proof
  Induct >> simp[generate_block_insts_plan_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  drule_all generate_inst_plan_emission_congruence >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

(* The prefix keeps the unprocessed original tail for liveness and terminator
   lookahead; it is not planning a truncated source block. *)
Theorem generate_block_insts_prefix_emission_congruence:
  !k xs i lv dfg cfg fn lbl halt np bl p q ops p' ops' q'.
    p.ps_label_counter = q.ps_label_counter /\
    generate_block_insts_prefix lv dfg cfg fn lbl halt np bl i k xs p = SOME (ops,p') /\
    generate_block_insts_prefix lv dfg cfg fn lbl halt np bl i k xs q = SOME (ops',q') ==>
    emission_projection ops = emission_projection ops' /\
    p'.ps_label_counter = q'.ps_label_counter
Proof
  Induct >- simp[generate_block_insts_prefix_def, emission_projection_def] >>
  Cases_on `xs` >- simp[generate_block_insts_prefix_def] >>
  simp[generate_block_insts_prefix_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  drule_all generate_inst_plan_emission_congruence >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem generate_block_plan_emission_congruence:
  !lv dfg cfg fn bb p q ops p' ops' q'.
    p.ps_label_counter = q.ps_label_counter /\
    generate_block_plan lv dfg cfg fn bb p = SOME (ops,p') /\
    generate_block_plan lv dfg cfg fn bb q = SOME (ops',q') ==>
    emission_projection ops = emission_projection ops' /\
    p'.ps_label_counter = q'.ps_label_counter
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `if bb = HD fn.fn_blocks then prepare_params_plan lv fn p else ([],p)` >>
  rename1 `_ = (param_ops,ps1)` >>
  Cases_on `if bb = HD fn.fn_blocks then prepare_params_plan lv fn q else ([],q)` >>
  rename1 `_ = (param_ops',qs1)` >>
  `emission_projection param_ops = [] /\ ps1.ps_label_counter = p.ps_label_counter` by
    (qpat_x_assum `_ = (param_ops,ps1)` mp_tac >>
     IF_CASES_TAC >- (strip_tac >>
       qspecl_then [`lv`, `fn`, `p`] mp_tac prepare_params_plan_emission >> gvs[]) >>
     strip_tac >> gvs[emission_projection_def]) >>
  `emission_projection param_ops' = [] /\ qs1.ps_label_counter = q.ps_label_counter` by
    (qpat_x_assum `_ = (param_ops',qs1)` mp_tac >>
     IF_CASES_TAC >- (strip_tac >>
       qspecl_then [`lv`, `fn`, `q`] mp_tac prepare_params_plan_emission >> gvs[]) >>
     strip_tac >> gvs[emission_projection_def]) >>
  Cases_on `if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
    then clean_stack_plan lv cfg fn bb ps1 else ([],ps1)` >>
  rename1 `_ = (clean_ops,ps2)` >>
  Cases_on `if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
    then clean_stack_plan lv cfg fn bb qs1 else ([],qs1)` >>
  rename1 `_ = (clean_ops',qs2)` >>
  `emission_projection clean_ops = [] /\ ps2.ps_label_counter = ps1.ps_label_counter` by
    (qpat_x_assum `_ = (clean_ops,ps2)` mp_tac >>
     IF_CASES_TAC >- (strip_tac >>
       qspecl_then [`lv`, `cfg`, `fn`, `bb`, `ps1`] mp_tac clean_stack_plan_emission >> gvs[]) >>
     strip_tac >> gvs[emission_projection_def]) >>
  `emission_projection clean_ops' = [] /\ qs2.ps_label_counter = qs1.ps_label_counter` by
    (qpat_x_assum `_ = (clean_ops',qs2)` mp_tac >>
     IF_CASES_TAC >- (strip_tac >>
       qspecl_then [`lv`, `cfg`, `fn`, `bb`, `qs1`] mp_tac clean_stack_plan_emission >> gvs[]) >>
     strip_tac >> gvs[emission_projection_def]) >>
  fs[generate_block_plan_def] >>
  qpat_x_assum `_ = (param_ops,ps1)` kall_tac >>
  qpat_x_assum `_ = (param_ops',qs1)` kall_tac >>
  qpat_x_assum `_ = (clean_ops,ps2)` kall_tac >>
  qpat_x_assum `_ = (clean_ops',qs2)` kall_tac >>
  gvs[AllCaseEqs()] >>
  `ps2.ps_label_counter = qs2.ps_label_counter` by simp[] >>
  drule_all generate_block_insts_plan_emission_congruence >>
  gvs[emission_projection_def, emission_anchor_def, rich_listTheory.FILTER_APPEND]
QED

(* These templates classify anchors, not physical execution. ASSIGN can still
   have literal/label input anchors; its variable renaming and PHI's SOPoke are
   silent in this projection. BUMP retains ADD but erases its auxiliary DUP.
   INITIAL_FMP retains its dedicated constructor. INVOKE has four anchors and
   advances the generated-label counter: it is not a single producer opcode.
   Neither equal projections nor equal flattened code reconstruct source cuts,
   alias identities, underflow freedom, or initialized spill memory. *)
Theorem generate_emit_ops_assign_emission:
  !inst topics ps.
    inst.inst_opcode = ASSIGN ==>
    generate_emit_ops inst topics ps = ([],ps)
Proof
  simp[generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def]
QED

Theorem generate_emit_ops_bump_emission:
  !inst topics ps.
    inst.inst_opcode = BUMP ==>
    emission_projection (FST (generate_emit_ops inst topics ps)) = [SOEmit "ADD"] /\
    SND (generate_emit_ops inst topics ps) = ps
Proof
  simp[generate_emit_ops_def, bump_emit_ops_def,
    emission_projection_def, emission_anchor_def]
QED

Theorem generate_emit_ops_initial_fmp_emission:
  !inst topics ps.
    inst.inst_opcode = INITIAL_FMP ==>
    generate_emit_ops inst topics ps = ([SOInitialFmp],ps)
Proof
  simp[generate_emit_ops_def]
QED

Theorem generate_emit_ops_invoke_emission:
  !inst topics ps l ret.
    inst.inst_opcode = INVOKE /\ HD inst.inst_operands = Label l /\
    ret = "return_label_" ++ num_to_dec_string (ps.ps_label_counter + 1) ==>
    emission_projection (FST (generate_emit_ops inst topics ps)) =
      [SOPushLabel ret; SOPushLabel l; SOEmit "JUMP"; SOLabel ret] /\
    (SND (generate_emit_ops inst topics ps)).ps_label_counter = ps.ps_label_counter + 1
Proof
  simp[generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def,
    stackPlanTypesTheory.fresh_label_def, emission_projection_def, emission_anchor_def]
QED
