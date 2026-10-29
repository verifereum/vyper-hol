(* TOP-LEVEL: assignment, handler and blueprint-check supply preservation.
 *)
Theory vyperSourceCompoundSupply
Ancestors
  list pair option vyperMisc vyperSourceSupplyDefs vyperSourcePrimitiveSupply
  vyperInterpreter vyperCreate vyperState
Libs
  vyperSupplyProofLib

val source_facts = List.concat (map (CONJUNCTS o SPEC_ALL)
  [source_supply_reads, source_supply_field_updates, source_supply_locals,
   source_supply_locks, source_supply_action_return, source_supply_action_raise,
   source_supply_action_write_storage, source_supply_action_set_storage_backend,
   source_supply_action_set_global]);

val source_net = vyperSupplyProofLib.fact_net source_facts
  [source_supply_action_bind_simple, source_supply_action_ignore_bind,
   source_supply_action_cond];

Theorem source_supply_action_write_place:
  source_supply_action (write_place cx p v)
Proof
  Cases_on `p` >>
  simp_tac bool_ss [Once write_place_def, FORALL_PROD, LET_THM] >>
  rpt (vyperSupplyProofLib.step source_net)
QED

val place_net = vyperSupplyProofLib.fact_net
  (SPEC_ALL source_supply_action_write_place :: source_facts)
  [source_supply_action_bind_simple, source_supply_action_ignore_bind,
   source_supply_action_cond];

Theorem source_supply_assignment:
  (!cx p v. source_supply_action (write_place cx p v)) /\
  (!cx p v. source_supply_action (append_place cx p v)) /\
  (!cx p. source_supply_action (pop_place cx p))
Proof
  conj_tac >- metis_tac[source_supply_action_write_place] >>
  rpt conj_tac >> rpt gen_tac >> Cases_on `p` >>
  simp_tac bool_ss [Once append_place_def,
                   Once pop_place_def, FORALL_PROD, LET_THM] >>
  rpt strip_tac >> rpt (vyperSupplyProofLib.step place_net)
QED

Theorem source_supply_handlers:
  source_supply_action (handle_loop_exception error) /\
  source_supply_action (handle_function error)
Proof
  Cases_on `error` >> simp[handle_loop_exception_def, handle_function_def,
    source_supply_action_return, source_supply_action_raise]
QED

Theorem source_supply_switch:
  source_supply_action first /\ source_supply_action second ==>
  source_supply_action (switch_BoolV cx tv first second)
Proof
  strip_tac >> simp_tac bool_ss [switch_BoolV_def] >>
  rpt (vyperSupplyProofLib.step source_net)
QED

Theorem source_supply_create_soft_failure:
  source_supply_action (create_soft_failure revert_on_failure message)
Proof
  Cases_on `revert_on_failure` >> simp[create_soft_failure_def,
    source_supply_action_return, source_supply_action_raise]
QED

Theorem source_supply_check_create_blueprint:
  source_supply_action (check_create_blueprint has_salt values)
Proof
  simp_tac bool_ss [check_create_blueprint_def, LET_THM] >>
  rpt (vyperSupplyProofLib.step source_net)
QED

val () = List.app (fn (n, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th)))
     andalso null (Thm.hyp th)
  then () else raise Fail ("Unexpected proof oracle: " ^ n))
  (DB.thms "vyperSourceCompoundSupply");
