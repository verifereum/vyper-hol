(* Root-frame metadata is retained even for a singleton initial stack. *)
Theory callTraceRootMetadata
Ancestors
  asmFrameCallStep vfmAccountFrame vfmExecutionProp vfmRunCall vfmWfState

Theorem run_call_reaches_root_msgParams:
  wf_state es /\ run_call_reaches es s /\
  LENGTH s.contexts = LENGTH es.contexts ==>
  (FST (HD s.contexts)).msgParams = (FST (HD es.contexts)).msgParams
Proof
  strip_tac >>
  `es.contexts <> []` by gvs[wf_state_def] >>
  `wf_state s /\
   (LENGTH es.contexts <= LENGTH s.contexts ==>
    ?active. active <> [] /\ s.contexts = active ++ TL es.contexts /\
      (FST (LAST active)).msgParams = (FST (HD es.contexts)).msgParams)` by
    (mp_tac (Q.INST [`Q` |-> `\x. wf_state x /\
       (LENGTH es.contexts <= LENGTH x.contexts ==>
        ?active. active <> [] /\ x.contexts = active ++ TL es.contexts /\
          (FST (LAST active)).msgParams = (FST (HD es.contexts)).msgParams)`]
       run_call_reaches_inv) >>
     simp[] >> impl_tac >- (conj_tac
     >- (qexists_tac `[HD es.contexts]` >> Cases_on `es.contexts` >> gvs[]) >>
     rpt gen_tac >> strip_tac >> conj_tac
     >- (drule step_preserves_wf_state >> simp[]) >>
     strip_tac >>
     `LENGTH (TL es.contexts) < LENGTH s'.contexts` by
       (Cases_on `es.contexts` >> gvs[]) >>
     qpat_x_assum `_ ==> ?active. _` mp_tac >> simp[] >> strip_tac >>
     drule_all asm_call_bottom_message_step >> strip_tac >>
     qexists_tac `active'` >> simp[]) >> simp[]) >>
  gvs[] >>
  `LENGTH active = 1` by
    (Cases_on `es.contexts` >> gvs[]) >>
  Cases_on `active` >> gvs[] >> Cases_on `t` >> gvs[]
QED
