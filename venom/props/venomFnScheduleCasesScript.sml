(* TOP-LEVEL: exact constructor equation for the original guarded schedule.
   Keeps compilation-unit and instruction payloads schematic during composition. *)
Theory venomFnScheduleCases
Ancestors
  venomFnScheduleRunner venomPassDispatcher venomPassSchedule venomInst
  singleUseExpansionDefs

Theorem sue_expand_function_supply_result:
  dfg_build_function func = dfg /\
  sue_expand_blocks_supply dfg supply func.fn_blocks = (blocks,next_supply) ==>
  sue_expand_function_supply supply func =
    (func with fn_blocks := blocks,next_supply)
Proof
  simp[sue_expand_function_supply_def]
QED

Theorem execute_configured_fn_pass_sue_result:
  sue_expand_function_supply supply func = (next_func,next_supply) ==>
  execute_configured_fn_pass rpolicy (CFP_Simple VP_SingleUseExpansion)
    unit supply func =
  SOME <| fpo_function := next_func; fpo_label_map := [];
          fpo_supply := next_supply |>
Proof
  simp[execute_configured_fn_pass_sue]
QED

Theorem run_configured_fn_pass_fold_cons_result:
  unit_with_current_fn unit func = SOME observed /\
  runner rpolicy pass observed supply func = SOME out ==>
  out.fpo_function.fn_name = func.fn_name /\
  fn_pass_effects_hold (fn_pass_tag pass) func out /\
  introduces_no_invoke_edges func out.fpo_function /\
  ir_supply_extends supply out.fpo_supply /\
  ir_supply_covers_fn out.fpo_supply out.fpo_function /\
  ir_supply_covers_unit out.fpo_supply observed ==>
  run_configured_fn_pass_fold runner rpolicy (pass::passes)
    unit supply func labels =
  run_configured_fn_pass_fold runner rpolicy passes unit
    out.fpo_supply out.fpo_function (labels ++ out.fpo_label_map)
Proof
  strip_tac >> simp[Once run_configured_fn_pass_fold_def]
QED
