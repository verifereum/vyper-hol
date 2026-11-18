(* Source observations from compiled outcomes at one selected source trace. *)
Theory guardSourceAlignment
Ancestors
  guardSourceExternal guardStorageTransport loweringStateRelDefs
  e2eDefs vyperInterpreter vyperStorageFootprint list

Theorem aligned_trace_storage_observations:
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx (initial_state am []) (FST H) /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  call_external_trace (SOME os) gs am tx = (res,am',rqs,obs) /\
  EVERY (\r. MEM r (FST H)) (storage_trace_regions obs) /\
  EVERY (\l. MEM l (SND H)) (storage_trace_locks obs) /\
  storage_roots_fit obs /\
  (!pre rq co sfx.
    obs = pre ++ StorageOutcome rq co :: sfx /\
    valid_horizon cx (initial_state am []) H pre ==>
    (co.co_accounts = rq.cr_accounts /\ co.co_tStorage = rq.cr_tStorage) \/
    ?rq'. MEM (rq',co) trace /\ request_agree H cx.txn.target rq rq') /\
  (!rq co.
    MEM (rq,co) trace /\
    storage_well_formed_on cx
      (empty_state with <|accounts := rq.cr_accounts;
                         tStorage := rq.cr_tStorage|>) (FST H) ==>
    storage_well_formed_on cx
      (empty_state with <|accounts := co.co_accounts;
                         tStorage := co.co_tStorage|>) (FST H)) ==>
  storage_observations_ok cx H obs
Proof
  strip_tac >>
  qpat_x_assum `cx = _` (fn cxeq =>
  mp_tac (PURE_REWRITE_RULE [GSYM cxeq]
    (SPEC_ALL call_external_trace_storage_finite_prefix |> Q.INST
    [`tops` |-> `tops`, `am` |-> `am`, `tx` |-> `tx`,
     `os` |-> `os`, `gs` |-> `gs`, `res` |-> `res`,
     `am'` |-> `am'`, `rqs` |-> `rqs`, `obs` |-> `obs`,
     `cx` |-> `cx`, `H` |-> `H`]))) >>
  impl_tac >- (
  asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!pre rq co sfx. _`
    (qspecl_then [`pre`, `rq`, `co`, `sfx`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- gvs[] >>
  rename1 `MEM (crq,co) trace` >>
  qpat_x_assum `!rq co. _` irule >>
  goal_assum $ drule_at Any >>
  `storage_well_formed_on cx
      (empty_state with <|accounts := rq.cr_accounts;
                         tStorage := rq.cr_tStorage|>) (FST H) <=>
   storage_well_formed_on cx
      (empty_state with <|accounts := crq.cr_accounts;
                         tStorage := crq.cr_tStorage|>) (FST H)` by
    (irule guard_storage_well_formed_transport >> simp[] >>
     qexists_tac `H` >> fs[request_agree_def, EVERY_MEM]) >>
  metis_tac[]) >> simp[]
QED

Theorem valid_horizon_call_storage_ok:
  valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) H (source_storage_trace am tx os gobs) ==>
  call_storage_ok am tx os gobs
Proof
  simp[call_storage_ok_def, storage_trace_horizon_def, valid_horizon_def,
       storage_observations_ok_def] >> strip_tac >>
  rename1 `storage_roots_fit obs` >>
  `!st. storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE) st (FST H) ==>
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE) st
      (storage_trace_regions obs)` by
    (simp[storage_well_formed_on_def] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `storage_trace_backends_well_formed
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (storage_trace_regions obs) obs` by
    (simp[storage_trace_backends_well_formed_def] >>
     irule EVERY_MONOTONIC >>
     qexists_tac `\ob. case ob of StorageBackend acc ts =>
       storage_well_formed_on
         (initial_evaluation_context am.sources am.layouts tx NONE)
         (empty_state with <|accounts := acc; tStorage := ts|>) (FST H)
       | _ => T` >>
     conj_tac >- (Cases >> simp[]) >>
     fs[storage_trace_backends_well_formed_def]) >>
  fs[regions_consistent_def, storage_locks_separated_def, EVERY_MEM] >>
  metis_tac[]
QED
