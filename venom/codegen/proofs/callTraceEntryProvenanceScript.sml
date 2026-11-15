Theory callTraceEntryProvenance
Ancestors
  callTrace frameObsStep vfmAccountFrame vfmDecreasesGas

Definition entry_origin_def[local]:
  entry_origin es rq oc <=>
  ?s t u. run_call_reaches es s /\ wf_state s /\
    LENGTH s.contexts = LENGTH es.contexts /\
    observable_call (FST (HD s.contexts)) /\
    rq.cr_accounts = s.rollback.accounts /\
    rq.cr_tStorage = s.rollback.tStorage /\
    oc.co_accounts = t.rollback.accounts /\
    oc.co_tStorage = t.rollback.tStorage /\
    ((step s = (INL u,t) /\ LENGTH t.contexts = LENGTH s.contexts) \/
     (?c. step s = (INL u,c) /\
          LENGTH c.contexts = SUC (LENGTH s.contexts) /\
          run_call c = SOME (INL (),t)))
End

Definition pending_origin_def[local]:
  pending_origin es x rq n m <=>
  LENGTH es.contexts < LENGTH x.contexts /\
  ?s c u. run_call_reaches es s /\ wf_state s /\
    LENGTH s.contexts = LENGTH es.contexts /\
    observable_call (FST (HD s.contexts)) /\
    rq = request_of s /\ n = LENGTH (FST (HD s.contexts)).logs /\
    m = LENGTH s.rollback.toDelete /\
    step s = (INL u,c) /\ LENGTH c.contexts = SUC (LENGTH es.contexts) /\
    run_call c = SOME (run_call_tr (SUC (LENGTH es.contexts)) (step x))
End

Definition observer_origin_def[local]:
  observer_origin es x obs <=>
    (!rq oc. MEM (rq,oc) obs.entries ==> entry_origin es rq oc) /\
    (!rq n m. obs.pending = SOME (rq,n,m) ==> pending_origin es x rq n m)
End

Theorem observe_origin[local]:
  wf_state es /\ run_call_reaches es x /\
  LENGTH es.contexts <= LENGTH x.contexts /\ step x = (r,y) /\
  observer_origin es x obs ==>
  (!rq oc. MEM (rq,oc) (observe (LENGTH es.contexts) x (r,y) obs).entries ==>
            entry_origin es rq oc) /\
  (ISL r /\ LENGTH es.contexts <= LENGTH y.contexts ==>
    observer_origin es y (observe (LENGTH es.contexts) x (r,y) obs))
Proof
  strip_tac >>
  `wf_state x` by metis_tac[run_call_reaches_wf_state] >>
  Cases_on `r` >> simp[observe_def, observer_origin_def] >>
  gvs[observer_origin_def] >>
  Cases_on `LENGTH x.contexts = LENGTH es.contexts` >> simp[]
  >- (`obs.pending = NONE` by
        (Cases_on `obs.pending` >> simp[] >> rename1 `SOME p` >>
         PairCases_on `p` >>
         gvs[pending_origin_def]) >>
      Cases_on `next_opcode (FST (HD x.contexts)) = SOME Gas /\
                   LENGTH y.contexts = LENGTH es.contexts` >> simp[] >>
      Cases_on `observable_call (FST (HD x.contexts))` >> simp[]
      >- (Cases_on `LENGTH y.contexts = LENGTH es.contexts` >> simp[]
          >- ( `entry_origin es (request_of x)
                  (outcome_of (request_of x).cr_kind y
                    (LENGTH (FST (HD x.contexts)).logs)
                    (LENGTH x.rollback.toDelete))` by
                 (simp[entry_origin_def] >> qexistsl [`x`,`y`] >>
                  Cases_on `next_opcode (FST (HD x.contexts)) = SOME Create \/
                    next_opcode (FST (HD x.contexts)) = SOME Create2` >>
                  simp[request_of_def, outcome_of_def]) >>
               metis_tac[]) >>
          Cases_on `LENGTH y.contexts = LENGTH es.contexts + 1` >> simp[] >>
          rpt strip_tac >> simp[pending_origin_def] >>
          qexistsl [`x`,`y`] >> simp[run_call_eq_tr, arithmeticTheory.ADD1]) >>
      metis_tac[]) >>
  Cases_on `LENGTH es.contexts < LENGTH x.contexts /\
              LENGTH y.contexts = LENGTH es.contexts` >> simp[]
  >- (Cases_on `obs.pending` >> simp[] >> rename1 `SOME p` >>
      PairCases_on `p` >> gvs[] >>
      gvs[pending_origin_def] >>
      `run_call c = SOME (INL (),y)` by
        (qpat_x_assum `run_call c = _` mp_tac >>
         simp[Once run_call_tr_def]) >>
      `entry_origin es (request_of s) (outcome_of (request_of s).cr_kind y
           (LENGTH (FST (HD s.contexts)).logs) (LENGTH s.rollback.toDelete))` by
        (simp[entry_origin_def] >> qexistsl [`s`,`y`] >>
         Cases_on `next_opcode (FST (HD s.contexts)) = SOME Create \/
                   next_opcode (FST (HD s.contexts)) = SOME Create2` >>
         simp[request_of_def, outcome_of_def] >> metis_tac[]) >>
      metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `!rq n m. _` (qspecl_then [`rq`,`n`,`m`] mp_tac) >>
  simp[] >> simp[pending_origin_def] >> strip_tac >>
  `LENGTH es.contexts < LENGTH y.contexts` by decide_tac >>
  simp[] >> qexistsl [`s`,`c`] >> simp[] >>
  qpat_x_assum `run_call c = _` mp_tac >>
  simp[Once run_call_tr_def] >> simp[Once run_call_tr_def]
QED

Theorem frame_obs_tr_origin[local]:
  !d obs x r y. !es.
  d = LENGTH es.contexts /\ wf_state es /\ run_call_reaches es x /\
  d <= LENGTH x.contexts /\ step x = (r,y) /\ observer_origin es x obs ==>
  !rq oc. MEM (rq,oc) (frame_obs_tr d obs x (r,y)).entries ==>
          entry_origin es rq oc
Proof
  recInduct frame_obs_tr_ind >> rpt gen_tac >> strip_tac >>
  gen_tac >> strip_tac >> gvs[] >>
  drule_all observe_origin >> strip_tac >>
  once_rewrite_tac[frame_obs_tr_def] >> simp[] >>
  IF_CASES_TAC >- metis_tac[] >>
  Cases_on `r` >> gvs[] >>
  qpat_x_assum `!es'. _` (qspec_then `es` mp_tac) >>
  impl_tac >- metis_tac[run_call_reaches_step] >> simp[]
QED

Theorem call_trace_entry_origin:
  wf_state es /\ MEM (rq,oc) (call_trace es) ==>
  ?s t u. run_call_reaches es s /\ wf_state s /\
    LENGTH s.contexts = LENGTH es.contexts /\
    observable_call (FST (HD s.contexts)) /\
    rq.cr_accounts = s.rollback.accounts /\
    rq.cr_tStorage = s.rollback.tStorage /\
    oc.co_accounts = t.rollback.accounts /\
    oc.co_tStorage = t.rollback.tStorage /\
    ((step s = (INL u,t) /\ LENGTH t.contexts = LENGTH s.contexts) \/
     (?c. step s = (INL u,c) /\
          LENGTH c.contexts = SUC (LENGTH s.contexts) /\
          run_call c = SOME (INL (),t)))
Proof
  simp[GSYM entry_origin_def] >> strip_tac >>
  irule frame_obs_tr_origin >> conj_tac >- simp[] >>
  qexistsl [`LENGTH es.contexts`,
    `<|entries := []; readings := []; pending := NONE|>`,
    `FST (step es)`, `es`, `SND (step es)`] >>
  gvs[call_trace_def, frame_obs_def, observer_origin_def]
QED
