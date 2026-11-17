(* The instruction planner does not inspect its polymorphic cfg argument. *)
Theory stackPlanCfgIrrelevance
Ancestors
  stackPlanGen

Theorem generate_inst_plan_cfg_unit:
  !lv dfg (cfg:'a) fn inst nl halting term label ps.
    generate_inst_plan lv dfg cfg fn inst nl halting term label ps =
    generate_inst_plan lv dfg () fn inst nl halting term label ps
Proof
  simp[generate_inst_plan_def, generate_regular_inst_plan_def]
QED
