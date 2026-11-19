Theory guardTerminalBackend
Ancestors
  guardStorageTransport e2eDefs vyperInterpreter vyperStorageFootprint
  vyperStorageBackend loweringStateRelDefs frameOutcome vfmProg vfmState
  vyperState vyperContext list arithmetic

Theorem guard_nested_frame_outcome:
  2 <= LENGTH e.contexts /\ frame_outcome e r e' exc out lgs ==>
  ISL r /\ LENGTH e'.contexts + 1 = LENGTH e.contexts /\
  (exc <> NONE ==> e'.rollback = SND (HD e.contexts))
Proof
  rpt strip_tac >> fs[frame_outcome_def] >>
  rename1 `e.contexts = (ctxt,rb)::rest` >>
  Cases_on `rest` >> gvs[] >>
  `pre.contexts <> []` by simp[] >>
  drule_all vfmRunCallTheory.handle_exception_inl_pops >> simp[]
QED

Theorem guard_processed_backend_well_formed[local]:
  cx.txn.target = tx.target /\ regions_consistent (FST H) /\
  EVERY (\region. MEM region (FST H)) (FST h) /\
  storage_well_formed_on cx (initial_state am' []) (FST H) /\
  accounts_agree h cx.txn.target am'.accounts
    (process_deletions e'.rollback.toDelete e'.rollback.accounts) /\
  transient_agree h cx.txn.target am'.tStorage e'.rollback.tStorage /\
  ~MEM tx.target e'.rollback.toDelete ==>
  storage_well_formed_on cx
    (empty_state with <|accounts := e'.rollback.accounts;
                       tStorage := e'.rollback.tStorage|>) (FST H)
Proof
  rpt strip_tac >> fs[] >>
  `storage_well_formed_on cx
    (empty_state with <|accounts := process_deletions e'.rollback.toDelete
                           e'.rollback.accounts;
                       tStorage := e'.rollback.tStorage|>) (FST H)` by
    (mp_tac (guard_storage_well_formed_transport |> Q.INST
      [`H` |-> `H`, `h` |-> `h`, `cx` |-> `cx`,
       `st` |-> `initial_state am' []`,
       `st'` |-> `empty_state with
         <|accounts := process_deletions e'.rollback.toDelete e'.rollback.accounts;
           tStorage := e'.rollback.tStorage|>`]) >>
     fs[initial_state_def] >> metis_tac[]) >>
  `process_deletions e'.rollback.toDelete e'.rollback.accounts tx.target =
    e'.rollback.accounts tx.target` by
    (mp_tac (lookup_account_process_deletions_other |> Q.INST
      [`addr` |-> `tx.target`, `toDelete` |-> `e'.rollback.toDelete`,
       `acc` |-> `e'.rollback.accounts`]) >> simp[lookup_account_def]) >>
  `!b. get_storage cx
    (empty_state with <|accounts := e'.rollback.accounts;
                       tStorage := e'.rollback.tStorage|>) b =
    get_storage cx
    (empty_state with <|accounts := process_deletions e'.rollback.toDelete
                           e'.rollback.accounts;
                       tStorage := e'.rollback.tStorage|>) b` by
    (gen_tac >> Cases_on `b` >> simp[get_storage_def] >>
     qpat_assum `process_deletions _ _ _ = _`
       (mp_tac o AP_TERM ``\a:account_state. a.storage``) >> simp[]) >>
  fs[storage_well_formed_on_def]
QED

Theorem guard_terminal_backend_well_formed:
  2 <= LENGTH e.contexts /\
  cx.txn.target = tx.target /\ regions_consistent (FST H) /\
  call_external_trace (SOME (MAP SND (call_trace e))) gs am tx =
    (res,am',rqs,obs) /\
  call_result_rel_at gs tops am tx e r e' /\
  ~source_exempt tops (res,am',rqs) /\
  EVERY (\region. MEM region (FST H)) (storage_trace_regions obs) /\
  storage_well_formed_on cx (initial_state am' []) (FST H) /\
  storage_well_formed_on cx
    (empty_state with <|accounts := (SND (HD e.contexts)).accounts;
                       tStorage := (SND (HD e.contexts)).tStorage|>) (FST H) /\
  ~MEM tx.target e'.rollback.toDelete ==>
  storage_well_formed_on cx
    (empty_state with <|accounts := e'.rollback.accounts;
                       tStorage := e'.rollback.tStorage|>) (FST H)
Proof
  rpt strip_tac >>
  qabbrev_tac `h = storage_trace_horizon obs` >>
  `EVERY (\region. MEM region (FST H)) (FST h)` by
    simp[Abbr `h`, storage_trace_horizon_def] >>
  `!exc out lgs. frame_outcome e r e' (SOME exc) out lgs ==>
    storage_well_formed_on cx
      (empty_state with <|accounts := e'.rollback.accounts;
                         tStorage := e'.rollback.tStorage|>) (FST H)` by
    (rpt strip_tac >> drule_all guard_nested_frame_outcome >> simp[]) >>
  `accounts_agree h cx.txn.target am'.accounts
      (process_deletions e'.rollback.toDelete e'.rollback.accounts) /\
    transient_agree h cx.txn.target am'.tStorage e'.rollback.tStorage ==>
    storage_well_formed_on cx
      (empty_state with <|accounts := e'.rollback.accounts;
                         tStorage := e'.rollback.tStorage|>) (FST H)` by
    (strip_tac >> drule_all guard_processed_backend_well_formed >> simp[]) >>
  `call_external (SOME (MAP SND (call_trace e))) gs am tx = (res,am',rqs)` by
    metis_tac[call_external_trace_result] >>
  qpat_x_assum `call_result_rel_at _ _ _ _ _ _ _` mp_tac >>
  simp[call_result_rel_at_def, source_storage_trace_def, Abbr `h`] >>
  Cases_on `res`
  >- (simp[effects_agree_def] >> rpt strip_tac >>
      qpat_x_assum `accounts_agree _ _ _ (process_deletions _ _) /\ _ ==> _` irule >>
      fs[] >> metis_tac[]) >>
  rename1 `INR exc` >> Cases_on `exc = HaltException`
  >- (gvs[effects_agree_def] >> rpt strip_tac >>
      qpat_x_assum `accounts_agree _ _ _ (process_deletions _ _) /\ _ ==> _` irule >>
      fs[] >> metis_tac[]) >>
  Cases_on `exc` >> simp[exception_outcome_rel_def] >> rpt strip_tac >>
  gvs[source_exempt_def] >>
  qpat_x_assum `!exc out lgs. frame_outcome _ _ _ (SOME exc) out lgs ==> _`
    (fn th => drule_all th) >> simp[]
QED
