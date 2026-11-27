(* Preserve a borrowed slot read across the actual runtime suffix. *)
Theory bodyAbiEncodeRuntimeSuffixReadMods
Ancestors
  bodyLogReachedSlotMods bodySavedTargetSourceMods bodySavedTargetWalkMods
  bodyCallSupport bodyInvSplit targetPurePostTransport
  vyperStorageBackend vyperState vyperInterpreter exprLowering

Theorem abi_encode_runtime_suffix_read_mods:
  contract_inv mods exps ctx cenv cx /\ ~cx.in_deploy /\
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  EVERY (source_body_call_supported cx) (int_calls_exprs xs) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_exprs xs) /\
  ~exprs_can_mutate cenv xs /\
  eval_exprs cx xs (mid with gas_obs := obs) = (INL vs,ee with gas_obs := []) /\
  read_storage_slot cx tr w tv mid = (INL v,mid) ==>
  read_storage_slot cx tr w tv ee = (INL v,ee)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!ty key actuals fallback.
      (source_body_call_supported cx key /\
       MEM key (linked_live_functions mods exps)) /\
      ~call_can_mutate cenv (IntCall key) /\
      state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
        (eval_exprs cx actuals) ==>
      state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
        (eval_expr cx (Call ty (IntCall key) actuals fallback))` by
    (rpt gen_tac >> strip_tac >> PairCases_on `key` >>
     metis_tac[saved_runtime_call_frame]) >>
  `read_storage_slot cx tr w tv (ee with gas_obs := []) =
      (INL v,ee with gas_obs := [])` by
    (match_mp_tac
       (Q.INST [`cx` |-> `cx`, `mods` |-> `mods`, `exps` |-> `exps`,
                `cenv` |-> `cenv`, `ys` |-> `xs`, `mid` |-> `mid`,
                `obs` |-> `obs`, `vs` |-> `vs`,
                `ee` |-> `ee with gas_obs := []`,
                `tr` |-> `tr`, `w` |-> `w`, `tv` |-> `tv`, `v` |-> `v`]
         log_reached_slot_read_mods) >>
     rpt conj_tac >> metis_tac[]) >>
  `read_storage_slot cx tr w tv (ee with gas_obs := []) =
      (INL v,ee with gas_obs := []) ==>
   read_storage_slot cx tr w tv ee = (INL v,ee)` by
    (strip_tac >> Cases_on `tr` >>
     gvs[read_storage_slot_def, get_storage_backend_eq, bind_def,
         get_storage_def, lift_option_def, return_def, raise_def] >>
     rpt CASE_TAC >> gvs[return_def, raise_def]) >>
  metis_tac[]
QED
