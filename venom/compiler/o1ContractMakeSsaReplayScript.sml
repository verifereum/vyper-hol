(*
 * The O1 dispatcher's MakeSSA step is make_ssa_current_fn run from a
 * supply that covers the function and whose used instruction ids are
 * below its next one (ir_supply_inst_ok), as the per-function MakeSSA
 * lemmas assume.  The dispatcher's supply covers the observed unit but
 * need not have the second property, so the step is replayed from one
 * that has both and gives the same function.
 *)
Theory o1ContractMakeSsaReplay
Ancestors
  o1PassContract makeSsaCurrentDefs venomPassSchedule irSupply
  makeSsaCurrentUsedInstIds venomFnScheduleRunner venomFnScheduleRunnerProps

Theorem make_ssa_pass_step_replay:
  fn_pass_step rpolicy (CFP_Simple VP_MakeSSA) observed s fn out ==>
  ?t t'. ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
    make_ssa_current_fn t fn = (out.fpo_function,t')
Proof
  simp[fn_pass_step_def] >> strip_tac >>
  drule venomFnScheduleRunnerPropsTheory.lookup_unique_function_member >>
  strip_tac >>
  `ir_supply_covers_fn s fn` by
    (gvs[ir_supply_covers_unit_def, ir_supply_covers_fn_def, list_subset_def,
       unit_ir_inst_ids_def, unit_ir_vars_def, unit_ir_labels_def,
       listTheory.EVERY_MEM, listTheory.MEM_FLAT, listTheory.MEM_MAP,
       PULL_EXISTS] >> metis_tac[]) >>
  Cases_on `make_ssa_current_fn s fn` >> gvs[] >>
  drule makeSsaCurrentUsedInstIdsTheory.make_ssa_current_fn_used_inst_ids >>
  disch_then (qspec_then `fn_ir_inst_ids fn` strip_assume_tac) >>
  qexists_tac `s with irs_used_inst_ids := fn_ir_inst_ids fn` >>
  gvs[ir_supply_covers_fn_def, list_subset_def, ir_supply_inst_ok_def,
      listTheory.EVERY_MEM]
QED
