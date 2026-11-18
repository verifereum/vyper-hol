(* Closed-world storage invariants for a reentered frame. *)
Theory e2eOutcomesGuard
Ancestors
  e2eRequestCutDefs e2eDefs vfmAccountFrame vyperStorageFootprint
  vyperInterpreter vyperState vyperStorageBackend vfmState vfmContext
  callTraceFrameProvenance callTraceFrame callTrace guardReentryCode
  guardPushProjections immutableSectionRel vfmExecution vfmExecutionProp
  arithmetic list

Triviality guard_closed_world_inherit:
  vyper_closed_world fin policy tops runtime_bc am tx H es /\
  run_call_reaches es e /\ LENGTH es.contexts <= LENGTH e.contexts /\
  am_e.sources = am.sources /\ am_e.layouts = am.layouts /\
  tx_e.target = tx.target /\
  world_rel am_e tx_e e /\
  storage_well_formed_on
    (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE)
    (empty_state with <|accounts := e.rollback.accounts;
                       tStorage := e.rollback.tStorage|>) (FST H) /\
  horizon_covers H am_e tx_e (MAP SND (call_trace e)) /\
  ~account_empty (lookup_account tx_e.target e.originalAccounts) /\
  (!gobs. ~source_exempt tops
    (call_external (SOME (MAP SND (call_trace e))) gobs am_e tx_e)) ==>
  vyper_closed_world fin policy tops runtime_bc am_e tx_e H e
Proof
  strip_tac >>
  `!a. (accounts_after_transfer tx_e am_e.accounts a).storage =
       (am_e.accounts a).storage` by
    (gen_tac >> rw[accounts_after_transfer_def, lookup_account_def,
                  update_account_def, combinTheory.APPLY_UPDATE_THM] >>
     rpt IF_CASES_TAC >> simp[]) >>
  `storage_well_formed_on
    (initial_evaluation_context am_e.sources am_e.layouts tx_e NONE)
    (initial_state am_e []) (FST H)` by
    (qpat_x_assum `world_rel _ _ _`
       (strip_assume_tac o REWRITE_RULE [world_rel_def]) >>
     qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
     simp[storage_well_formed_on_def, boolTheory.FORALL_BOOL,
          get_storage_def, vyperInterpreterTheory.initial_state_def]) >>
  fs[vyper_closed_world_def] >> rpt strip_tac >>
  rename1 `step s = (INL u, child)` >>
  `run_call_reaches es s` by
    (irule run_call_reaches_trans >> qexists_tac `e` >> simp[]) >>
  qpat_x_assum `!s child. run_call_reaches es s /\ _ ==> _`
    (qspecl_then [`s`, `child`] mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> simp[]
QED

val guard_frame_storage_pair =
  ``\cx (regions : (bool # bytes32 # type_value) list) p.
  ~NULL (FST p).code /\
  storage_well_formed_on cx
    (empty_state with <|accounts := K (FST p); tStorage := K (SND p)|>)
    regions``;

Triviality guard_trace_storage_from_reentries:
  call_state_rel tops runtime_bc am tx es /\ runtime_bc <> [] /\
  MEM (rq,co) (call_trace es) /\
  storage_well_formed_on
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (empty_state with <|accounts := rq.cr_accounts;
                       tStorage := rq.cr_tStorage|>) (regions : (bool # bytes32 # type_value) list) /\
  (!s u e r e'.
    run_call_reaches es s /\ LENGTH es.contexts <= LENGTH s.contexts /\
    wf_state s /\ wf_state e /\ step s = (INL u,e) /\
    LENGTH s.contexts < LENGTH e.contexts /\
    (FST (HD e.contexts)).msgParams.callee = tx.target /\
    ~(FST (HD e.contexts)).msgParams.static /\
    run_call e = SOME (r,e') /\
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (empty_state with <|accounts := e.rollback.accounts;
                         tStorage := e.rollback.tStorage|>) regions /\
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (empty_state with <|accounts := (SND (HD e.contexts)).accounts;
                         tStorage := (SND (HD e.contexts)).tStorage|>) regions ==>
    ISL r /\ LENGTH e'.contexts + 1 = LENGTH e.contexts /\
    storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (empty_state with <|accounts := e'.rollback.accounts;
                         tStorage := e'.rollback.tStorage|>) regions) ==>
  storage_well_formed_on
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (empty_state with <|accounts := co.co_accounts;
                       tStorage := co.co_tStorage|>) regions
Proof
  strip_tac >>
  `wf_state es /\
   (FST (HD es.contexts)).msgParams.callee = tx.target` by
    fs[call_state_rel_def, evm_state_ok_def, frame_tx_rel_def] >>
  `~NULL (lookup_account tx.target es.rollback.accounts).code` by
    (fs[call_state_rel_def, installed_code_rel_def, NULL_EQ] >>
     metis_tac[APPEND_eq_NIL]) >>
  `0 < LENGTH es.contexts` by
    (Cases_on `es.contexts` >> gvs[wf_state_def]) >>
  `~NULL (lookup_account tx.target rq.cr_accounts).code` by
    (drule_all call_trace_entry_provenance >> strip_tac >> gvs[] >>
     irule guard_reaches_code_nonempty >> qexists_tac `es` >> simp[]) >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  `^guard_frame_storage_pair cx regions
    (lookup_account tx.target rq.cr_accounts, rq.cr_tStorage tx.target)` by
    (BETA_TAC >> fs[storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def,
      lookup_account_def, Abbr `cx`, initial_evaluation_context_def]) >>
  `^guard_frame_storage_pair cx regions
    (lookup_account tx.target co.co_accounts, co.co_tStorage tx.target)`
    suffices_by
      (BETA_TAC >> fs[storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def,
        lookup_account_def, Abbr `cx`, initial_evaluation_context_def]) >>
  BETA_TAC >> RULE_ASSUM_TAC BETA_RULE >>
  irule (BETA_RULE (Q.INST
    [`P` |-> `^guard_frame_storage_pair cx regions`, `a` |-> `tx.target`,
     `es` |-> `es`, `rq` |-> `rq`, `oc` |-> `co`]
    call_trace_account_transient_frame)) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      fs[storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def]) >>
  conj_tac
  >- (rpt gen_tac >> simp[foreign_account_change_def] >> strip_tac >>
      fs[account_already_created_def, storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def]) >>
  qexistsl_tac [`es`, `rq`] >> asm_rewrite_tac[] >>
  reverse conj_tac >- gvs[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?s. _`
    (qx_choose_then `s` (qx_choose_then `u` (map_every assume_tac o CONJUNCTS))) >>
  `2 <= LENGTH e.contexts` by decide_tac >>
  Cases_on `(FST (HD e.contexts)).msgParams.static`
  >- (mp_tac (Q.INST
        [`obs` |-> `\p. ^guard_frame_storage_pair cx regions
          (lookup_account tx.target (FST p), SND p tx.target)`,
         `e` |-> `e`, `e'` |-> `e'`, `r` |-> `r`]
        (INST_TYPE [alpha |-> ``:bool``] run_call_static_observation)) >>
      simp[] >> impl_tac
      >- (drule_all step_push_static_output_not_code >> fs[]) >>
      simp[]) >>
  qpat_x_assum `!s u e r e'. _`
    (qspecl_then [`s`, `u`, `e`, `r`, `e'`] mp_tac) >>
  impl_tac >-
    fs[storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def,
       lookup_account_def, Abbr `cx`, initial_evaluation_context_def] >>
  strip_tac >>
  `run_call_reaches es e` by
    (irule run_call_reaches_step >> qexistsl_tac [`s`, `u`] >> simp[]) >>
  `LENGTH es.contexts <= LENGTH e.contexts` by decide_tac >>
  `run_call_reaches e e'` by
    (drule run_call_finite_trace >> strip_tac >>
     mp_tac (Q.SPEC `n` (Q.INST [`es` |-> `e`] run_call_trace_reaches)) >>
     simp[] >> metis_tac[]) >>
  `run_call_reaches es e'` by
    (irule run_call_reaches_trans >> qexists_tac `e` >> simp[]) >>
  `LENGTH es.contexts <= LENGTH e'.contexts` by decide_tac >>
  `~NULL (lookup_account tx.target e'.rollback.accounts).code` by
    (drule_all guard_reaches_code_nonempty >> simp[]) >>
  fs[storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def,
     lookup_account_def, Abbr `cx`, initial_evaluation_context_def]
QED
