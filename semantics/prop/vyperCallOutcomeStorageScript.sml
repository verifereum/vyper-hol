(* Storage/suffix boundary for TASK032/033. Runtime accounts guards bound only
 * balances and code: adopted payload storage comes solely from PLAN T6.2. *)
Theory vyperCallOutcomeStorage
Ancestors
  list pair option sum vyperState vyperCallOutcome vyperCallOutcomeProps vyperCallOutcomeBranches
  vyperCallOutcomeFrame vyperEvalOutcomeSuffix vyperTypeStoragePreservation
  vyperStorageBackend vyperStorageReadSoundness vyperStorageLayoutSafety
  vyperAST vyperInterpreter vyperTypeCallOutcome vyperABI vyperTypeSystem extCallOracle
Libs monadsyntax

(* ===== Suffix transport, including guard failures ===== *)
Theorem oracle_storage_ok_suffix:
  oracle_storage_ok cx st /\ outcome_suffix st.outcomes st'.outcomes ==>
  oracle_storage_ok cx st'
Proof
  simp[oracle_storage_ok_payload] >> rpt strip_tac >>
  drule_all outcome_suffix_EVERY >> simp[]
QED

(* Original TASK031 proof: unconditional equality is refuted by
   activated_ExtCall_consumes_counterexample. Retained for provenance.
Proof
  rpt conj_tac >> rpt strip_tac >> imp_res_tac eval_outcomes_preserved_mutual >>
  metis_tac[oracle_storage_ok_outcomes]
QED
*)
Theorem eval_oracle_storage_preserved_mutual:
  (!cx s st res st'. oracle_storage_ok cx st /\ eval_stmt cx s st = (res,st') ==> oracle_storage_ok cx st') /\
  (!cx ss st res st'. oracle_storage_ok cx st /\ eval_stmts cx ss st = (res,st') ==> oracle_storage_ok cx st') /\
  (!cx it st res st'. oracle_storage_ok cx st /\ eval_iterator cx it st = (res,st') ==> oracle_storage_ok cx st') /\
  (!cx tyv id body vs st res st'. oracle_storage_ok cx st /\ eval_for cx tyv id body vs st = (res,st') ==> oracle_storage_ok cx st') /\
  (!cx e st res st'. oracle_storage_ok cx st /\ eval_expr cx e st = (res,st') ==> oracle_storage_ok cx st') /\
  (!cx es st res st'. oracle_storage_ok cx st /\ eval_exprs cx es st = (res,st') ==> oracle_storage_ok cx st') /\
  (!cx bt st res st'. oracle_storage_ok cx st /\ eval_base_place cx bt st = (res,st') ==> oracle_storage_ok cx st') /\
  (!cx tgt st res st'. oracle_storage_ok cx st /\ eval_target_place cx tgt st = (res,st') ==> oracle_storage_ok cx st') /\
  (!cx g v st res st'. oracle_storage_ok cx st /\ assign_tuple_targets cx g v st = (res,st') ==> oracle_storage_ok cx st') /\
  (!cx gs vs st res st'. oracle_storage_ok cx st /\ assign_tuple_target_list cx gs vs st = (res,st') ==> oracle_storage_ok cx st')
Proof
  rpt conj_tac >> rpt strip_tac >> imp_res_tac eval_outcome_suffix_mutual >>
  drule_all oracle_storage_ok_suffix >> simp[]
QED

Theorem take_call_outcome_outcome_suffix:
  take_call_outcome target calldata value_opt st = (res,st') ==>
  outcome_suffix st.outcomes st'.outcomes
Proof
  rpt strip_tac >> Cases_on `st.outcomes`
  >- (gvs[take_call_outcome_NONE] >> simp[]) >>
  drule_all take_call_outcome_suffix >> strip_tac >>
  simp[outcome_suffix_def] >> qexists_tac `prefix` >> simp[]
QED

Theorem take_call_outcome_storage_suffix:
  contract_storage_well_formed cx st /\ oracle_storage_ok cx st /\
  take_call_outcome target calldata value_opt st = (res,st') ==>
  contract_storage_well_formed cx st' /\ oracle_storage_ok cx st' /\
  outcome_suffix st.outcomes st'.outcomes
Proof
  rpt strip_tac >> drule take_call_outcome_frame >>
  simp[evaluation_state_component_equality] >> strip_tac >>
  imp_res_tac take_call_outcome_outcome_suffix >>
  imp_res_tac oracle_storage_ok_suffix >> simp[] >>
  irule contract_storage_well_formed_backends_frame >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Recorded success uses T6.2; computed success uses the request snapshots.
   Neither argument asserts that the runtime balance/code guard checks storage. *)
Theorem take_outcome_success_storage_payload:
  contract_storage_well_formed cx st /\ oracle_storage_ok cx st /\
  st.outcomes = SOME os /\
  take_outcome (call_outcome_request target calldata value_opt st) os = (co,rest) /\
  co.co_success ==>
  contract_storage_well_formed cx
    (st with <|accounts := co.co_accounts; tStorage := co.co_tStorage|>)
Proof
  rpt strip_tac >>
  Cases_on `computed_precompile (call_outcome_request target calldata value_opt st)`
  >- (drule computed_precompile_state >> disch_then (qspec_then `os` mp_tac) >>
      simp[] >> strip_tac >>
      irule contract_storage_well_formed_backends_frame >>
      qexists_tac `st` >> gvs[call_outcome_request_def]) >>
  Cases_on `os` >> gvs[take_outcome_def] >> fs[oracle_storage_ok_def]
QED

(* Atomic take plus raw adoption, tied to the real request snapshot. *)
Theorem take_adopt_call_outcome_storage_suffix:
  contract_storage_well_formed cx st /\ oracle_storage_ok cx st /\
  take_call_outcome target calldata value_opt st = (INL (rq,co),st1) /\
  adopt_call_outcome rq co st1 = (INL (),st2) ==>
  contract_storage_well_formed cx st2 /\ oracle_storage_ok cx st2 /\
  outcome_suffix st.outcomes st2.outcomes
Proof
  rpt strip_tac >> drule_all take_call_outcome_storage_suffix >> strip_tac >>
  drule take_call_outcome_success >> strip_tac >>
  `co.co_success ==> contract_storage_well_formed cx
     (st with <|accounts := co.co_accounts; tStorage := co.co_tStorage|>)` by
    (strip_tac >> gvs[] >> drule_all take_outcome_success_storage_payload >> simp[]) >>
  Cases_on `rq.cr_static` >> Cases_on `co.co_success` >>
  gvs[adopt_call_outcome_equation, call_outcome_request_def] >>
  FIRST [
    irule contract_storage_well_formed_backends_frame >>
    qexists_tac `st with <|accounts := co.co_accounts; tStorage := co.co_tStorage|>` >>
    simp[] >> NO_TAC,
    irule oracle_storage_ok_suffix >> qexists_tac `st` >> simp[]]
QED

(* No-adoption needs no payload assumption: even arbitrary bad storage/code
   is ignored for static/failed outcomes. take still consumes atomically. *)
Theorem take_adopt_call_outcome_no_adoption_storage:
  contract_storage_well_formed cx st /\
  take_call_outcome target calldata value_opt st = (INL (rq,co),st1) /\
  (rq.cr_static \/ ~co.co_success) /\
  adopt_call_outcome rq co st1 = (INL (),st2) ==>
  contract_storage_well_formed cx st2 /\ outcome_suffix st.outcomes st2.outcomes
Proof
  rpt gen_tac >> strip_tac >>
  drule take_call_outcome_outcome_suffix >> strip_tac >>
  drule take_call_outcome_success >> strip_tac >>
  `rq.cr_kind = MessageCall` by gvs[call_outcome_request_def] >>
  `adopt_call_outcome rq co st1 = (INL (),st1)` by
    (irule adopt_call_outcome_static_failed >> simp[]) >>
  gvs[] >> drule take_call_outcome_frame >> strip_tac >>
  irule contract_storage_well_formed_backends_frame >>
  qexists_tac `st` >> gvs[evaluation_state_component_equality]
QED

(* Source runtime typing comes from the inherited real take guard; storage
   comes from T6.2/computed snapshots; layout/context fields are unchanged. *)
Theorem take_adopt_call_outcome_runtime_storage_suffix:
  runtime_storage_consistent env cx st /\ oracle_storage_ok cx st /\
  take_call_outcome target calldata value_opt st = (INL (rq,co),st1) /\
  adopt_call_outcome rq co st1 = (INL (),st2) ==>
  runtime_storage_consistent env cx st2 /\ oracle_storage_ok cx st2 /\
  outcome_suffix st.outcomes st2.outcomes
Proof
  rpt gen_tac >> strip_tac >>
  `contract_storage_well_formed cx st /\ runtime_consistent env cx st` by
    fs[runtime_storage_consistent_def] >>
  drule_all take_adopt_call_outcome_storage_suffix >> strip_tac >>
  drule_all take_adopt_call_outcome_runtime_consistent >>
  fs[runtime_storage_consistent_def]
QED

(* Creation adopts the payload even on failure (the creator nonce survives). *)
Theorem take_create_outcome_outcome_suffix:
  take_create_outcome kind value code st = (res,st') ==>
  outcome_suffix st.outcomes st'.outcomes
Proof
  rpt strip_tac >> Cases_on `st.outcomes`
  >- (gvs[take_create_outcome_NONE] >> simp[]) >>
  drule_all take_create_outcome_suffix >> strip_tac >>
  simp[outcome_suffix_def] >> qexists_tac `prefix` >> simp[]
QED

Theorem take_create_outcome_storage_suffix:
  contract_storage_well_formed cx st /\ oracle_storage_ok cx st /\
  take_create_outcome kind value code st = (res,st') ==>
  contract_storage_well_formed cx st' /\ oracle_storage_ok cx st' /\
  outcome_suffix st.outcomes st'.outcomes
Proof
  rpt strip_tac >> drule take_create_outcome_frame >>
  simp[evaluation_state_component_equality] >> strip_tac >>
  imp_res_tac take_create_outcome_outcome_suffix >>
  imp_res_tac oracle_storage_ok_suffix >> simp[] >>
  irule contract_storage_well_formed_backends_frame >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem take_create_outcome_storage_payload:
  contract_storage_well_formed cx st /\ oracle_storage_ok cx st /\
  take_create_outcome kind value code st = (INL (rq,co),st1) ==>
  contract_storage_well_formed cx
    (st with <|accounts := co.co_accounts; tStorage := co.co_tStorage|>)
Proof
  rpt strip_tac >> drule take_create_outcome_success >> strip_tac >>
  Cases_on `os` >>
  gvs[take_outcome_def, oracle_storage_ok_def] >>
  gvs[create_outcome_request_def, failed_outcome_def] >>
  irule contract_storage_well_formed_backends_frame >>
  qexists_tac `st` >> simp[]
QED

Theorem take_adopt_create_outcome_storage_suffix:
  kind <> MessageCall /\
  contract_storage_well_formed cx st /\ oracle_storage_ok cx st /\
  take_create_outcome kind value code st = (INL (rq,co),st1) /\
  adopt_call_outcome rq co st1 = (INL (),st2) ==>
  contract_storage_well_formed cx st2 /\ oracle_storage_ok cx st2 /\
  outcome_suffix st.outcomes st2.outcomes
Proof
  rpt strip_tac >> drule_all take_create_outcome_storage_suffix >> strip_tac >>
  drule_all take_create_outcome_storage_payload >> strip_tac >>
  drule take_create_outcome_success >> strip_tac >>
  gvs[adopt_create_outcome_equation] >>
  FIRST [
    irule contract_storage_well_formed_backends_frame >>
    qexists_tac `st with <|accounts := co.co_accounts; tStorage := co.co_tStorage|>` >>
    simp[] >> NO_TAC,
    irule oracle_storage_ok_suffix >> qexists_tac `st` >> simp[]]
QED

(* ===== Real consuming continuations ===== *)
Theorem checked_call_outcome_storage_suffix:
  runtime_storage_consistent env cx st /\ oracle_storage_ok cx st /\
  (!bs s r t. runtime_storage_consistent env cx s /\ oracle_storage_ok cx s /\
    k bs s = (r,t) ==>
    contract_storage_well_formed cx t /\ oracle_storage_ok cx t /\
    outcome_suffix s.outcomes t.outcomes) /\
  (do
    (rq,co) <- take_call_outcome target calldata value_opt;
    check co.co_success msg;
    adopt_call_outcome rq co;
    k co.co_returnData
  od) st = (res,st') ==>
  contract_storage_well_formed cx st' /\ oracle_storage_ok cx st' /\
  outcome_suffix st.outcomes st'.outcomes
Proof
  rpt gen_tac >> simp[checked_call_outcome_cases] >> strip_tac >> gvs[] >>
  `contract_storage_well_formed cx st` by fs[runtime_storage_consistent_def]
  >- (drule_all take_call_outcome_storage_suffix >>
      fs[runtime_storage_consistent_def])
  >- (drule_all take_call_outcome_storage_suffix >>
      fs[runtime_storage_consistent_def]) >>
  drule_all take_adopt_call_outcome_storage_suffix >> strip_tac >>
  `runtime_consistent env cx st` by fs[runtime_storage_consistent_def] >>
  drule_all take_adopt_call_outcome_runtime_consistent >> strip_tac >>
  `runtime_storage_consistent env cx st2` by fs[runtime_storage_consistent_def] >>
  qpat_x_assum `!bs s r t. _` drule_all >> strip_tac >> simp[] >>
  drule_all outcome_suffix_trans >> simp[]
QED

Theorem ExtCall_outcome_storage_suffix:
  runtime_storage_consistent env cx st /\ oracle_storage_ok cx st /\
  (!bs s r t. runtime_storage_consistent env cx s /\ oracle_storage_ok cx s /\
    k bs s = (r,t) ==>
    contract_storage_well_formed cx t /\ oracle_storage_ok cx t /\
    outcome_suffix s.outcomes t.outcomes) /\
  (do
    accounts <- get_accounts;
    (if ret_type = NoneT then
      check (~NULL (lookup_account target accounts).code) "ExtCall target has no code"
     else return ());
    (rq,co) <- take_call_outcome target calldata value_opt;
    check co.co_success "ExtCall reverted";
    adopt_call_outcome rq co;
    k co.co_returnData
  od) st = (res,st') ==>
  contract_storage_well_formed cx st' /\ oracle_storage_ok cx st' /\
  outcome_suffix st.outcomes st'.outcomes
Proof
  REWRITE_TAC[ExtCall_outcome_checked_tail] >>
  Cases_on `ret_type = NoneT /\ NULL (lookup_account target st.accounts).code` >>
  simp[] >> rpt gen_tac >> strip_tac
  >- gvs[runtime_storage_consistent_def] >>
  drule_all checked_call_outcome_storage_suffix >> simp[]
QED

Theorem Send_outcome_storage_suffix:
  runtime_storage_consistent env cx st /\ oracle_storage_ok cx st /\
  (do
    (rq,co) <- take_call_outcome target [] (SOME amount);
    check co.co_success "send failed";
    adopt_call_outcome rq co;
    return (Value NoneV)
  od) st = (res,st') ==>
  contract_storage_well_formed cx st' /\ oracle_storage_ok cx st' /\
  outcome_suffix st.outcomes st'.outcomes
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (checked_call_outcome_storage_suffix |>
    INST_TYPE [alpha |-> ``:eval_result``] |>
    Q.INST [`k` |-> `\bs. return (Value NoneV)`, `msg` |-> `"send failed"`,
            `calldata` |-> `[]`, `value_opt` |-> `SOME amount`]) >>
  simp[return_def, runtime_storage_consistent_def]
QED

(* This is the actual default/decode tail, not a duplicate evaluator. The
   default IH carries exactly the suffix invariant needed after a take. *)
Theorem ExtCall_outcome_return_storage_suffix:
  runtime_storage_consistent env cx st /\ oracle_storage_ok cx st /\
  (IS_SOME drv ==> !s r t.
    runtime_storage_consistent env cx s /\ oracle_storage_ok cx s /\
    eval_expr cx (THE drv) s = (r,t) ==>
    contract_storage_well_formed cx t /\ oracle_storage_ok cx t /\
    outcome_suffix s.outcomes t.outcomes) /\
  (do
    accounts <- get_accounts;
    (if ret_type = NoneT then
      check (~NULL (lookup_account target accounts).code) "ExtCall target has no code"
     else return ());
    (rq,co) <- take_call_outcome target calldata value_opt;
    check co.co_success "ExtCall reverted";
    adopt_call_outcome rq co;
    if co.co_returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
    else do
      v <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type co.co_returnData);
      return (Value v)
    od
  od) st = (res,st') ==>
  contract_storage_well_formed cx st' /\ oracle_storage_ok cx st' /\
  outcome_suffix st.outcomes st'.outcomes
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (ExtCall_outcome_storage_suffix |>
    INST_TYPE [alpha |-> ``:eval_result``] |>
    Q.INST [`k` |-> `\bs. if bs = [] /\ IS_SOME drv then eval_expr cx (THE drv)
      else do v <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type bs);
              return (Value v) od`]) >>
  impl_tac >- (
    simp[] >> rpt gen_tac >> strip_tac >>
    Cases_on `bs = [] /\ IS_SOME drv` >> gvs[]
    >- (first_x_assum drule_all >> simp[]) >>
    Cases_on `evaluate_abi_decode_return (get_tenv cx) ret_type bs` >>
    gvs[lift_sum_runtime_def, bind_def, return_def, raise_def,
        runtime_storage_consistent_def]) >> simp[]
QED

(* The generated IH is required only at the actual successful adoption,
   not at arbitrary states, and only when dispatch selects the default. *)
Theorem ExtCall_outcome_return_storage_preserved:
  runtime_storage_consistent env cx st /\ oracle_storage_ok cx st /\
  (!rq co st1 st2 r t.
    take_call_outcome target calldata value_opt st = (INL (rq,co),st1) /\
    co.co_success /\ adopt_call_outcome rq co st1 = (INL (),st2) /\
    co.co_returnData = [] /\ IS_SOME drv /\
    eval_expr cx (THE drv) st2 = (r,t) ==>
    contract_storage_well_formed cx t) /\
  (do
    accounts <- get_accounts;
    (if ret_type = NoneT then
      check (~NULL (lookup_account target accounts).code) "ExtCall target has no code"
     else return ());
    (rq,co) <- take_call_outcome target calldata value_opt;
    check co.co_success "ExtCall reverted";
    adopt_call_outcome rq co;
    if co.co_returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
    else do
      v <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type co.co_returnData);
      return (Value v)
    od
  od) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt gen_tac >> strip_tac >>
  `contract_storage_well_formed cx st` by fs[runtime_storage_consistent_def] >>
  Cases_on `take_call_outcome target calldata value_opt st` >>
  rename1 `take_call_outcome target calldata value_opt st = (answer,mid)` >>
  drule (ExtCall_outcome_continue |> INST_TYPE [alpha |-> ``:eval_result``]) >>
  disch_then (qspecl_then [`ret_type`,
    `\bs. if bs = [] /\ IS_SOME drv then eval_expr cx (THE drv)
     else do v <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type bs);
             return (Value v) od`] mp_tac) >> strip_tac >> gvs[] >>
  Cases_on `ret_type = NoneT /\ NULL (lookup_account target st.accounts).code`
  >- gvs[] >>
  gvs[] >> Cases_on `answer`
  >- (rename1 `INL ro` >> Cases_on `ro` >>
      rename1 `take_call_outcome target calldata value_opt st = (INL (rq,co),mid)` >>
      Cases_on `co.co_success`
      >- (Cases_on `adopt_call_outcome rq co mid` >>
          rename1 `adopt_call_outcome rq co mid = (ar,st2)` >>
          `ar = INL ()` by gvs[adopt_call_outcome_equation] >> gvs[] >>
          drule_all take_adopt_call_outcome_storage_suffix >> strip_tac >>
          Cases_on `co.co_returnData = [] /\ IS_SOME drv` >> gvs[]
          >- (qpat_x_assum `(res,st') = _` (assume_tac o SYM) >>
              first_x_assum drule_all >> simp[]) >>
          Cases_on `evaluate_abi_decode_return (get_tenv cx) ret_type co.co_returnData` >>
          gvs[lift_sum_runtime_def, bind_def, return_def, raise_def]) >>
      gvs[] >> drule_all take_call_outcome_storage_suffix >> simp[]) >>
  gvs[] >> drule_all take_call_outcome_storage_suffix >> simp[]
QED

(* These oracle storage interfaces and their prerequisites must be kernel closed. *)
val () = List.app (fn thy => List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles andalso null axioms
     then () else raise Fail ("Incomplete storage boundary: " ^ thy ^ "." ^ name)
  end) (DB.thms thy)) ["vyperTypeStoragePreservation", "vyperCallOutcomeStorage"];
