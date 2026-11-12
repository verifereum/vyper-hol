Theory callTraceChildFrame
Ancestors
  callTrace vfmAccountFrame vfmExecution vfmExecutionProp vfmState

Theorem observable_child_account_transient_frame:
  (!acc acc' ts. P (acc, ts) /\ foreign_account_change acc acc' ==>
                 P (acc', ts)) /\
  (!e r e'.
     (FST (HD e.contexts)).msgParams.callee = a /\
     wf_state e /\
     P (lookup_account a e.rollback.accounts, e.rollback.tStorage a) /\
     (2 <= LENGTH e.contexts ==>
        P (lookup_account a (SND (HD e.contexts)).accounts,
           (SND (HD e.contexts)).tStorage a)) /\
     (?s u. run_call_reaches es s /\
            LENGTH es.contexts <= LENGTH s.contexts /\
            wf_state s /\
            P (lookup_account a s.rollback.accounts, s.rollback.tStorage a) /\
            step s = (INL u, e) /\
            LENGTH s.contexts < LENGTH e.contexts /\
            ((FST (HD s.contexts)).msgParams.callee <> a /\
             ~(FST (HD e.contexts)).msgParams.static \/
             LENGTH s.contexts = LENGTH es.contexts /\
             observable_call (FST (HD s.contexts)))) /\
     run_call e = SOME (r, e') ==>
     P (lookup_account a e'.rollback.accounts, e'.rollback.tStorage a)) /\
  run_call_reaches es s /\
  LENGTH s.contexts = LENGTH es.contexts /\
  wf_state s /\
  observable_call (FST (HD s.contexts)) /\
  P (lookup_account a s.rollback.accounts, s.rollback.tStorage a) /\
  step s = (INL u,c) /\ LENGTH s.contexts < LENGTH c.contexts /\
  wf_state c /\
  P (lookup_account a c.rollback.accounts, c.rollback.tStorage a) /\
  (2 <= LENGTH c.contexts ==>
     P (lookup_account a (SND (HD c.contexts)).accounts,
        (SND (HD c.contexts)).tStorage a)) /\
  run_call c = SOME (r,t) ==>
  P (lookup_account a t.rollback.accounts,t.rollback.tStorage a)
Proof
  strip_tac
  >> irule run_call_account_transient_frame
  >> conj_tac >- gvs[]
  >> qexistsl [`c`,`r`]
  >> conj_tac >- first_assum ACCEPT_TAC
  >> reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)
  >> rpt gen_tac >> strip_tac
  >- (qpat_x_assum `!e r e'. _` irule
      >> qexistsl [`e`,`r'`]
      >> gvs[]
      >> qexists_tac `s`
      >> simp[])
  >> `run_call_reaches es c` by
       (irule run_call_reaches_step
        >> qexistsl [`s`,`u`] >> simp[])
  >> `LENGTH es.contexts <= LENGTH c.contexts` by decide_tac
  >> `run_call_reaches es s'` by
       (irule run_call_reaches_trans
        >> qexists_tac `c` >> simp[])
  >> qpat_x_assum `!e r e'. _` irule
  >> qexistsl [`e`,`r'`]
  >> simp[]
  >> qexists_tac `s'`
  >> Cases_on `u'`
  >> simp[] >> decide_tac
QED
