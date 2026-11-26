(* Stopped full cuts provide the starting state for a request prefix. *)
Theory s1PrefixRawCreateStop
Ancestors
  s1PrefixCompose s1PrefixOfVV s1PrefixProps s1PrefixDefs
  gasOutcomeFullCompose fragGasOriginPtr vyperStorageFootprint
  vyperStorageTrace vyperCallOutcomeFrame vyperState sum pair

Triviality tag_return_state:
  SND (bind src (\x. return (tag x)) st) = SND (src st)
Proof
  Cases_on `src st` >> rename1 `src st = (res,ee)` >>
  Cases_on `res` >> simp[vyperStateTheory.bind_def,vyperStateTheory.return_def]
QED

Theorem raw_create_prefix_bind_stop:
  (!x. untag (tag x) = x) /\
  storage_trace_frame src /\ requests_outcomes_frame src /\
  (!x. storage_trace_frame (next x)) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 src (es,s,G,tn) /\
  (!H res ee gt r. R H res ee gt r ==> ISR res) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind src (\x. return (tag x))) (es,s,G,tn)
    (\H res ee J tj z. !w. res = INL w ==>
      gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
        (next (untag w)) (ee,z,J,tj)) R ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (bind src next) (es,s,G,tn)
Proof
  strip_tac >>
  `bind (bind src (\x. return (tag x))) (\w. next (untag w)) = bind src next` by
    simp[bind_assoc,bind_return,ETA_AX] >>
  pop_assum (once_rewrite_tac o single o GSYM) >>
  irule gas_prefix_full_bind >>
  `gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
     (bind src (\x. return (tag x))) (es,s,G,tn) <=>
   gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 src (es,s,G,tn)` by
    (irule gas_prefix_full_state_cong >> simp[tag_return_state]) >>
  `requests_outcomes_frame (bind src (\x. return (tag x)))` by
    (irule requests_outcomes_frame_bind_all >>
     simp[] >> simp[requests_outcomes_frame_def,state_rel_frame_def,return_def]) >>
  simp[storage_trace_frame_bind_all,storage_trace_frame_return] >>
  qexistsl_tac [`\H res ee J tj z. !w. res = INL w ==>
      gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
        (next (untag w)) (ee,z,J,tj)`, `R`, `tops`] >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  fs[storage_trace_domain_def]
QED

Theorem raw_create_prefix_return_stop:
  ~t.vs_halted /\ storage_trace_domain cx st0 mid.storage_trace /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (next (untag w)) (mid,t,J,tj) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (return w) (mid,t,J,tj)
    (\H res ee J tj z. !v. res = INL v ==>
      gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
        (next (untag v)) (ee,z,J,tj)) R
Proof
  strip_tac >> irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`J`,`mid`,`INL w`,`t`,`tj`] >>
  simp[return_def,gas_origin_ptr_path_rules] >>
  qpat_x_assum `gas_prefix_full _ _ _ _ _` mp_tac >>
  simp[gas_prefix_full_def]
QED
