Theory fnLineageInvReachable
Ancestors fnPlanPrefix stackPlanGen stackPlanTypes list rich_list

(* A necessary condition on a successful join result, not a preservation
   premise that may be assumed for reachable inputs. *)
Theorem marked_join_reached_targets_distinct:
  !base lv fn lbl inst ps targets.
    generated_plan_state_wf_marked base ps /\
    join_target_ops lv fn lbl inst = SOME targets /\
    join_reached lv fn lbl inst ps /\
    EVERY is_var_operand targets ==>
    ALL_DISTINCT targets
Proof
  rpt gen_tac >> strip_tac >>
  `FILTER (\op. op <> dead_stack_marker) targets = targets` by
    (simp[FILTER_EQ_ID, EVERY_MEM] >> rpt strip_tac >>
     gvs[EVERY_MEM] >> first_x_assum drule >>
     simp[is_var_operand_def, dead_stack_marker_def]) >>
  gvs[join_reached_def, generated_plan_state_wf_marked_def] >>
  qpat_x_assum `_ ++ targets = ps.ps_stack` mp_tac >>
  disch_then (mp_tac o AP_TERM ``FILTER (\op. op <> dead_stack_marker)``) >>
  simp[FILTER_APPEND] >> metis_tac[ALL_DISTINCT_APPEND]
QED
