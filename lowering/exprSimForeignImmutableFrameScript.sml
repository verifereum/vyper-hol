Theory exprSimForeignImmutableFrame
Ancestors
  exprSimHyps vyperTypeInitialState vyperImmutableMetadataFrame
  supportedStmts vyperState vyperInterpreter vyperMisc alist

(* Updating one module's immutable cells preserves every other module's map,
   including at addresses other than the active contract. *)
Theorem set_immutable_other_module:
  !cx src name tv v s res t md addr.
    set_immutable cx src name tv v s = (res,t) /\ md <> src ==>
    (case ALOOKUP t.immutables addr of
       NONE => FEMPTY | SOME imms => get_source_immutables md imms) =
    (case ALOOKUP s.immutables addr of
       NONE => FEMPTY | SOME imms => get_source_immutables md imms)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[set_immutable_def, get_address_immutables_def,
      set_address_immutables_def, bind_def, lift_option_type_def,
      return_def, raise_def, option_CASE_rator, AllCaseEqs()] >>
  Cases_on `addr = cx.txn.target` >>
  gvs[alistTheory.ALOOKUP_ADELKEY,
      get_source_immutables_set_other] >>
  Cases_on `ALOOKUP s.immutables addr` >> gvs[]
QED

Theorem write_place_other_module:
  !cx src name path v s res t md addr.
    write_place cx (ImmutablePlace src name path) v s = (res,t) /\
    md <> src ==>
    (case ALOOKUP t.immutables addr of
       NONE => FEMPTY | SOME imms => get_source_immutables md imms) =
    (case ALOOKUP s.immutables addr of
       NONE => FEMPTY | SOME imms => get_source_immutables md imms)
Proof
  rpt gen_tac >>
  simp[write_place_def, bind_def, ignore_bind_def, lift_option_type_def,
       lift_sum_def, option_CASE_rator, sum_CASE_rator,
       return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac vyperStatePreservationTheory.get_immutables_state >> gvs[] >>
  Cases_on `ALOOKUP s.immutables addr` >> gvs[] >>
  drule_all set_immutable_other_module >>
  disch_then (qspec_then `addr` mp_tac) >>
  Cases_on `ALOOKUP t.immutables addr` >> gvs[]
QED
