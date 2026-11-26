(* Source frame at the reached nonmutating positional/keyword suffix. *)
Theory bodyExtNoncopyReachedFrameMods
Ancestors
  bodyExtNoncopySourceMods bodySavedTargetSourceMods bodyInvSplit
  bodyCallSupport vyperTypeContract vyperInterpreter vyperMachineFrame
  vyperCallOutcomeFrame vyperStorageBackend vyperState exprLowering option list

Theorem ext_noncopy_reached_suffix_frame_mods:
  contract_inv mods exps ctx cenv cx /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  IS_SOME (check_contract F cx.layouts cx.txn.target mods) /\
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  ~exprs_can_mutate cenv ys /\
  EVERY (source_body_call_supported cx) (int_calls_exprs ys) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_exprs ys) /\
  eval_exprs cx ys (src with gas_obs := obs) = (INL vs,dst) ==>
  dst.scopes = src.scopes /\ dst.immutables = src.immutables /\
  (!tr. get_storage cx dst tr = get_storage cx src tr) /\
  (!tr slot tv v. read_storage_slot cx tr slot tv src = (INL v,src) ==>
    read_storage_slot cx tr slot tv dst = (INL v,dst))
Proof
  simp[IS_SOME_EXISTS, PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  `dst.scopes = src.scopes /\ dst.immutables = src.immutables /\
    (!tr. get_storage cx dst tr = get_storage cx src tr)` by
    (irule ext_noncopy_suffix_frame_mods >>
     map_every qexists_tac [`cenv`, `exps`, `mods`, `obs`, `vs`, `ys`] >>
     simp[] >>
     reverse conj_tac >- fs[EVERY_MEM] >>
     map_every qx_gen_tac [`ty`, `key`, `actuals`, `fallback`] >>
     PairCases_on `key` >> strip_tac >>
     drule_all_then MATCH_ACCEPT_TAC saved_checked_call_frame) >>
  simp[read_storage_slot_eq, AllCaseEqs()]
QED
