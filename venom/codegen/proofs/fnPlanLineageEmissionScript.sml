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
