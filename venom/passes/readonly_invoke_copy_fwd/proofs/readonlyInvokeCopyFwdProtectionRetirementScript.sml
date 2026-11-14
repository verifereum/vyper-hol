(* Retiring cross certificates does not retire live pointer translations.
   Map restriction is separately guarded by ordinary agreement. *)
Theory readonlyInvokeCopyFwdProtectionRetirement
Ancestors
  readonlyInvokeCopyFwdRel internalReturnCopyFwdSim
  o1LowerDloadRelocationKernel taintAgree finite_map pred_set list

Theorem ricf_site_triples_drestrict_subset:
  ricf_site_triples (DRESTRICT sites keep) SUBSET ricf_site_triples sites
Proof
  simp[ricf_site_triples_def, SUBSET_DEF, FLOOKUP_DRESTRICT] >>
  metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem ricf_sites_ok_drestrict:
  ricf_sites_ok sites ==> ricf_sites_ok (DRESTRICT sites keep)
Proof
  simp[ricf_sites_ok_def, FLOOKUP_DRESTRICT] >> rpt strip_tac >>
  Cases_on `(db,sz) IN keep` >> gvs[] >> metis_tac[]
QED

Theorem ricf_value_agree_drestrict:
  ricf_value_agree sites p m x y /\
  (!id. p = SOME id /\ id IN FDOM sites /\ id NOTIN keep ==>
        word_agree_except m x y) ==>
  ricf_value_agree (DRESTRICT sites keep) p m x y
Proof
  Cases_on `p` >> simp[ricf_value_agree_def, ld_value_agree_def] >>
  rename1 `SOME id` >> Cases_on `id IN FDOM sites` >>
  Cases_on `id IN keep` >> simp[FDOM_DRESTRICT, FLOOKUP_DRESTRICT]
QED

Theorem ricf_params_agree_drestrict:
  ricf_params_agree sites PG xs ys /\
  (!j id. j < LENGTH xs /\ EL j PG = SOME id /\
          id IN FDOM sites /\ id NOTIN keep ==>
          word_agree_except {} (EL j xs) (EL j ys)) ==>
  ricf_params_agree (DRESTRICT sites keep) PG xs ys
Proof
  simp[ricf_params_agree_def] >> rpt strip_tac >>
  irule ricf_value_agree_drestrict >> metis_tac[]
QED

Theorem ricf_frame_agree_drestrict:
  ricf_frame_agree D X sites PG G tn s t /\
  (!v id. v IN FDOM s.vs_vars /\ FLOOKUP G v = SOME id /\
          id IN FDOM sites /\ id NOTIN keep ==>
          word_agree_except (op_taint tn (Var v))
            (s.vs_vars ' v) (t.vs_vars ' v)) /\
  (!j id. j < LENGTH s.vs_params /\ EL j PG = SOME id /\
          id IN FDOM sites /\ id NOTIN keep ==>
          word_agree_except {} (EL j s.vs_params) (EL j t.vs_params)) ==>
  ricf_frame_agree D X (DRESTRICT sites keep) PG G tn s t
Proof
  simp[ricf_frame_agree_def] >> rpt strip_tac
  >- metis_tac[ricf_value_agree_drestrict]
  >- metis_tac[ricf_params_agree_drestrict]
  >- metis_tac[ricf_sites_ok_drestrict]
  >> metis_tac[ircf_cross_subset, ricf_site_triples_drestrict_subset]
QED

Theorem ricf_live_local_agree_drestrict:
  ricf_live_local_agree sites PG G tv s t /\
  (!v id. v IN FDOM s.vs_vars /\ FLOOKUP G v = SOME id /\
          id IN FDOM sites /\ id NOTIN keep ==>
          word_agree_except (case FLOOKUP tv v of NONE => {} | SOME m => m)
            (s.vs_vars ' v) (t.vs_vars ' v)) /\
  (!j id. j < LENGTH s.vs_params /\ EL j PG = SOME id /\
          id IN FDOM sites /\ id NOTIN keep ==>
          word_agree_except {} (EL j s.vs_params) (EL j t.vs_params)) ==>
  ricf_live_local_agree (DRESTRICT sites keep) PG G tv s t
Proof
  simp[ricf_live_local_agree_def] >> rpt strip_tac
  >- metis_tac[ricf_value_agree_drestrict]
  >- metis_tac[ricf_params_agree_drestrict]
  >> metis_tac[ricf_sites_ok_drestrict]
QED

(* Neither sites nor maps changes in this rule. *)
Theorem ricf_cert_core_retire_current:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  next SUBSET cur ==>
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 next curs s t
Proof
  simp[ricf_cert_core_def] >> metis_tac[ircf_cross_subset]
QED

(* Pointwise lifting: use ricf_live_local_agree_drestrict to discharge the
   local premise. The shared state is unchanged, and surviving crosses are
   inherited from the old map, never re-established by a readonly claim. *)
Theorem ricf_live_stack_agree_drestrict:
  ricf_live_stack_agree D ids tn maps stk targets s t /\
  LENGTH maps' = LENGTH stk /\
  (!j. j < LENGTH stk ==>
    EL j maps' = DRESTRICT (EL j maps) (keep j) /\
    ricf_live_local_agree (EL j maps')
      (ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params)
      (EL j stk).cf_prov (EL j stk).cf_tvar
      (EL j stk).cf_state (EL j targets)) ==>
  ricf_live_stack_agree D ids tn maps' stk targets s t
Proof
  simp[ricf_live_stack_agree_def, ricf_live_frame_decompose] >>
  rpt strip_tac >>
  metis_tac[ircf_cross_subset, ricf_site_triples_drestrict_subset]
QED

(* Suspended owner-current certificates may shrink independently as well.
   The separate live-stack translation map index is not an argument here. *)
Theorem ricf_cert_crosses_subset:
  ricf_cert_crosses tn curs stk s t /\ LENGTH curs' = LENGTH curs /\
  (!j. j < LENGTH curs ==> EL j curs' SUBSET EL j curs) ==>
  ricf_cert_crosses tn curs' stk s t
Proof
  simp[ricf_cert_crosses_def, EVERY_EL] >>
  metis_tac[ircf_cross_subset]
QED
