(* Accepted source calls supply the passing runtime entry checks. *)
Theory entryAcceptedCheckFacts
Ancestors
  entryChecksProps vyperLoweringCorrect compileVyper compileEnv
  vyperInterpreter vyperState e2eDefs words

Theorem send_call_value_accepts_payable_or_zero[local]:
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE) s =
      (INL (),t) ==>
  mut = Payable \/ tx.value = 0
Proof
  Cases_on `tx.value = 0` >> simp[] >> Cases_on `mut = Payable` >> simp[] >>
  simp[send_call_value_def, initial_evaluation_context_def, check_def,
       assert_def, ignore_bind_def, bind_def, return_def, raise_def]
QED

Theorem source_selected_entry_checks_pass:
  source_typing_ok tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE) es =
      (INL (),es') /\
  set_external_package_target target
    (package_external_fn tops ut nkm
      (mut,F,rr,tx.function_name,args,([] : expr list),ret,fbody)) =
    (lbl,ce,pa,mc,pay,nr,key,tr,view,fbody,rt) ==>
  (pay \/ vs.vs_call_ctx.cc_callvalue = 0w) /\
  mc <= LENGTH vs.vs_call_ctx.cc_calldata /\
  LENGTH vs.vs_call_ctx.cc_calldata < dimword (:256)
Proof
  strip_tac >>
  drule send_call_value_accepts_payable_or_zero >> strip_tac >> (
  `pay = (mut = Payable)` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[package_external_fn_def, set_external_package_target_def] >>
     metis_tac[]) >>
  conj_tac
  >- gvs[initial_venom_state_rel_def, venom_env_rel_def, call_ctx_rel_def] >>
  reverse conj_tac
  >- (irule initial_venom_state_calldata_length >> goal_assum (drule_at Any) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `set_external_package_target target pkg = _` >>
  PairCases_on `pkg` >> gvs[set_external_package_target_def, markerTheory.Abbrev_def] >>
  qpat_x_assum `_ = package_external_fn _ _ _ _` (assume_tac o SYM) >>
  drule_all valid_vyper_call_min_calldata_size >> simp[])
QED
