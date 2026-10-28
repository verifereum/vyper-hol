(* Context generation observes only the operations and two final state fields.
   Keep the remaining planner state opaque at this symbolic boundary. *)
Theory stackPlanObservations
Ancestors stackPlanGen

val successor_equations = List.filter (fn theorem =>
    same_const (fst(strip_comb(lhs(concl theorem)))) ``generate_succs_plan``)
  (map SPEC_ALL (CONJUNCTS (SPEC_ALL generate_fn_plan_aux_def)))

Theorem generate_succs_plan_append:
  !prefix visited ps.
    generate_succs_plan liveness dfg cfg func saved_stack saved_spilled
      (prefix ++ suffix) visited ps =
    case generate_succs_plan liveness dfg cfg func saved_stack saved_spilled
           prefix visited ps of
      NONE => NONE
    | SOME (prefix_ops,visited1,ps1) =>
        case generate_succs_plan liveness dfg cfg func saved_stack saved_spilled
               suffix visited1 ps1 of
          NONE => NONE
        | SOME (suffix_ops,visited2,ps2) =>
            SOME (prefix_ops ++ suffix_ops,visited2,ps2)
Proof
  Induct >> simp successor_equations >> rpt gen_tac >>
  BasicProvers.every_case_tac >> simp[listTheory.APPEND_ASSOC]
QED

Theorem generate_succs_plan_two[compute]:
  generate_succs_plan liveness dfg cfg func saved_stack saved_spilled
    (first::second::rest) visited ps =
  case generate_succs_plan liveness dfg cfg func saved_stack saved_spilled
         [first] visited ps of
    NONE => NONE
  | SOME (first_ops,visited1,ps1) =>
      case generate_succs_plan liveness dfg cfg func saved_stack saved_spilled
             (second::rest) visited1 ps1 of
        NONE => NONE
      | SOME (rest_ops,visited2,ps2) =>
          SOME (first_ops ++ rest_ops,visited2,ps2)
Proof
  mp_tac (Q.SPECL [`[first]`,`visited`,`ps`]
    (Q.INST [`suffix` |-> `second::rest`] generate_succs_plan_append)) >> simp[]
QED

Definition observe_fn_plan_def:
  observe_fn_plan gen func spill_base labels =
    OPTION_MAP (\(ops,ps).
      (ops,ps.ps_alloc.sa_next_offset,ps.ps_label_counter))
      (gen func spill_base labels)
End

Theorem generate_context_regions_observed[compute]:
  generate_context_regions gen (func::funcs) acc =
    case observe_fn_plan gen func acc.cpa_next_spill_base acc.cpa_label_counter of
      NONE => NONE
    | SOME (ops,spill_end,labels) =>
        let spill_base = acc.cpa_next_spill_base;
            region = <|sr_fn_name := func.fn_name;
                       sr_spill_base := spill_base;
                       sr_spill_end := spill_end;
                       sr_plan := ops|>
        in
          if spill_plan_in_region spill_base spill_end ops then
            generate_context_regions gen funcs
              (acc with <|
                cpa_regions := SNOC region acc.cpa_regions;
                cpa_label_counter := labels;
                cpa_next_spill_base := spill_end;
                cpa_peak_spill_end :=
                  if spill_base < spill_end then
                    MAX acc.cpa_peak_spill_end spill_end
                  else acc.cpa_peak_spill_end|>)
          else NONE
Proof
  Cases_on `gen func acc.cpa_next_spill_base acc.cpa_label_counter` >>
  simp[observe_fn_plan_def,generate_context_regions_def] >>
  rename1 `gen func _ _ = SOME result` >>
  Cases_on `result` >> simp[]
QED
