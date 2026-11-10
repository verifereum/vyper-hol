Theory fnPlanLineageEmission
Ancestors
  stackPlanGen list

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
