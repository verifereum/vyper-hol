Theory lowerDloadOracleAdoption
Ancestors
  lowerDloadOracleSelection lowerDloadSharedState extCallOracle ptrDiscipline

(* Neither histories nor snapshot records have to agree.  Masks are left
   unchanged here; mask resets belong to the instruction-level consumer. *)
Theorem ld_take_adopt_shared_state:
  ld_shared_state tn un s t /\
  rq.cr_kind = rt.cr_kind /\ rq.cr_value = rt.cr_value /\
  rq.cr_target = rt.cr_target /\ rq.cr_data = rt.cr_data /\
  rq.cr_static = rt.cr_static /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient /\
  rt.cr_accounts = t.vs_accounts /\ rt.cr_tStorage = t.vs_transient ==>
  ld_shared_state tn un
    (s with <|
      vs_accounts := FST (adopt_outcome rq (FST (take_outcome rq s.vs_outcomes))
        (s.vs_accounts,s.vs_transient,s.vs_logs));
      vs_transient := FST (SND (adopt_outcome rq (FST (take_outcome rq s.vs_outcomes))
        (s.vs_accounts,s.vs_transient,s.vs_logs)));
      vs_outcomes := SND (take_outcome rq s.vs_outcomes);
      vs_returndata := (FST (take_outcome rq s.vs_outcomes)).co_returnData |>)
    (t with <|
      vs_accounts := FST (adopt_outcome rt (FST (take_outcome rt t.vs_outcomes))
        (t.vs_accounts,t.vs_transient,t.vs_logs));
      vs_transient := FST (SND (adopt_outcome rt (FST (take_outcome rt t.vs_outcomes))
        (t.vs_accounts,t.vs_transient,t.vs_logs)));
      vs_outcomes := SND (take_outcome rt t.vs_outcomes);
      vs_returndata := (FST (take_outcome rt t.vs_outcomes)).co_returnData |>)
Proof
  strip_tac >>
  drule_all ld_computed_precompile_cong >> strip_tac >>
  drule ld_shared_state_environment >> strip_tac >>
  Cases_on `t.vs_outcomes`
  >- (gvs[take_outcome_def, failed_outcome_def, adopt_outcome_def,
          ld_shared_state_def] >> IF_CASES_TAC >> gvs[]) >>
  Cases_on `computed_precompile rt`
  >- (gvs[take_outcome_def] >>
      Cases_on `precompile_result rt.cr_target rt.cr_data`
      >- gvs[failed_outcome_def, adopt_outcome_def, ld_shared_state_def] >>
      rename1 `_ = SOME v` >> Cases_on `v`
      >- gvs[failed_outcome_def, adopt_outcome_def, ld_shared_state_def] >>
      Cases_on `h.co_success` >>
      gvs[failed_outcome_def, adopt_outcome_def, ld_shared_state_def]) >>
  gvs[take_outcome_def, adopt_outcome_def] >>
  IF_CASES_TAC >>
  gvs[ld_shared_state_def, storage_agree_except_def, word_agree_except_def]
QED

Theorem ld_exact_noncurrent:
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient ==>
  (!a. a <> s.vs_call_ctx.cc_address ==>
    (s.vs_accounts a).storage = (t.vs_accounts a).storage) /\
  (!a. a <> s.vs_call_ctx.cc_address ==>
    s.vs_transient a = t.vs_transient a)
Proof
  simp[]
QED

Theorem ld_take_adopt_noncurrent:
  ld_shared_state tn un s t /\
  (!a. a <> s.vs_call_ctx.cc_address ==>
    (s.vs_accounts a).storage = (t.vs_accounts a).storage) /\
  (!a. a <> s.vs_call_ctx.cc_address ==>
    s.vs_transient a = t.vs_transient a) /\
  rq.cr_kind = rt.cr_kind /\ rq.cr_value = rt.cr_value /\
  rq.cr_target = rt.cr_target /\ rq.cr_data = rt.cr_data /\
  rq.cr_static = rt.cr_static /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient /\
  rt.cr_accounts = t.vs_accounts /\ rt.cr_tStorage = t.vs_transient /\
  s' = s with <|
    vs_accounts := FST (adopt_outcome rq (FST (take_outcome rq s.vs_outcomes))
      (s.vs_accounts,s.vs_transient,s.vs_logs));
    vs_transient := FST (SND (adopt_outcome rq (FST (take_outcome rq s.vs_outcomes))
      (s.vs_accounts,s.vs_transient,s.vs_logs)));
    vs_outcomes := SND (take_outcome rq s.vs_outcomes);
    vs_returndata := (FST (take_outcome rq s.vs_outcomes)).co_returnData |> /\
  t' = t with <|
    vs_accounts := FST (adopt_outcome rt (FST (take_outcome rt t.vs_outcomes))
      (t.vs_accounts,t.vs_transient,t.vs_logs));
    vs_transient := FST (SND (adopt_outcome rt (FST (take_outcome rt t.vs_outcomes))
      (t.vs_accounts,t.vs_transient,t.vs_logs)));
    vs_outcomes := SND (take_outcome rt t.vs_outcomes);
    vs_returndata := (FST (take_outcome rt t.vs_outcomes)).co_returnData |> ==>
  (!a. a <> s'.vs_call_ctx.cc_address ==>
    (s'.vs_accounts a).storage = (t'.vs_accounts a).storage) /\
  (!a. a <> s'.vs_call_ctx.cc_address ==>
    s'.vs_transient a = t'.vs_transient a)
Proof
  strip_tac >>
  drule_all ld_computed_precompile_cong >> strip_tac >>
  drule ld_shared_state_environment >> strip_tac >>
  Cases_on `t.vs_outcomes`
  >- (gvs[take_outcome_def, failed_outcome_def, adopt_outcome_def] >>
      IF_CASES_TAC >> gvs[]) >>
  Cases_on `computed_precompile rt`
  >- (gvs[take_outcome_def] >>
      Cases_on `precompile_result rt.cr_target rt.cr_data`
      >- gvs[failed_outcome_def, adopt_outcome_def] >>
      rename1 `_ = SOME v` >> Cases_on `v`
      >- gvs[failed_outcome_def, adopt_outcome_def] >>
      Cases_on `h.co_success` >> gvs[failed_outcome_def, adopt_outcome_def]) >>
  gvs[take_outcome_def, adopt_outcome_def] >> IF_CASES_TAC >> gvs[]
QED

Theorem ld_storage_sensitive_exact:
  ld_shared_state tn un s t /\ taint_ok fn tn inst s /\
  (inst.inst_opcode = DELEGATECALL \/ inst.inst_opcode = CREATE \/
   inst.inst_opcode = CREATE2) ==>
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
  un.t_stor = {} /\ un.t_trans = {}
Proof
  strip_tac >> irule ld_shared_state_empty_exact >>
  gvs[taint_ok_def] >> metis_tac[]
QED

(* External storage producer checkpoint (source locations refer to the
   immutable producer files, not claims of a full instruction simulation).

   CALL -- venomExecSemantics:480-487, venomCallOracleDefs:11-44:
     MessageCall request, static iff current static or explicit static flag.
     extCallOracle:130-138 adopts maps iff nonstatic and successful.
     ptrDiscipline:402-420 clears masks only for CALL, nonstatic input,
     changed requests, consumed outcome, successful head.  Computed precompile
     leaves requests unchanged (record_request:124-126); empty outcomes cannot
     change outcomes; failed/static branches do not reset.  Thus no retained-map
     branch resets.  Common adopted maps justify a reset even if input masks
     are nonempty.  No source clean-mask premise is available or needed here.

   STATICCALL -- venomExecSemantics:1085-1095: same exec_ext_call with T.
     No map adoption (cr_static=T), no mask reset (opcode is not CALL).
     Companion transport uses retained input maps; arbitrary input masks.

   DELEGATECALL -- venomExecSemantics:493-506, extract_venom_result:437-471:
     Concrete EVM execution, NOT the outcome oracle. Success uses rollback
     accounts/tStorage, failure retains input maps. No mask reset. taint_ok:
     582-584 supplies empty source storage/transient masks; the checked
     ld_storage_sensitive_exact derives exact input maps and empty target
     masks. Full concrete-EVM congruence remains external-closure work.

   CREATE/CREATE2 -- venomExecSemantics:509-518,1107-1127;
     venomCallOracleDefs:76-119: CreateCall/Create2Call request, cr_static=F.
     adopt_outcome adopts supplied maps even on unsuccessful outcomes for
     these non-MessageCall kinds; empty list returns failed_outcome with input
     maps. No mask reset (not CALL). taint_ok:582-584 provides empty source
     masks, hence exact inputs by ld_storage_sensitive_exact. Even retained-map
     branches therefore have exact storage. Oversized initcode abort keeps
     input maps and is not an OK successor.

   All five producers keep vs_call_ctx, hence cc_address: oracle consumers
   update only listed fields, extract_venom_result likewise, and update_var
   only changes vs_vars. ld_take_adopt_noncurrent proves the bounded oracle
   companion interface for both retained and common-map branches. It does
   not establish request equality, memory relocation, or delegate execution.
*)
