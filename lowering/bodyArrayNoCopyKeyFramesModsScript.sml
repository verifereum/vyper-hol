(* Compose the linked base and key frames at their reached cuts, before
   running any selection instructions. *)
Theory bodyArrayNoCopyKeyFramesMods
Ancestors
  bodyArrayNoCopyCutsMods bodyFullPostsMods exprSimWordArgs wordArgsPtr
  exprSimProps loweringPosts vyperEvalExprPreservesScopesDom vyperStorageFootprint

Theorem array_nocopy_key_prefix_frames_mods:
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty obj idx et bd st0
      (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
      (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
      (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) ==>
  wb_frame cenv es fin sa s0 it /\
  (~expr_has_effect (Subscript ann obj idx) ==> pure_frame cenv func es sa s0 it) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
       stmt_state_rel H ctx func cenv cx fin it /\ immutable_frame_mods func cenv cx fin it /\
       storage_well_formed_on cx fin (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx fin Gi tni it)
Proof
  rewrite_tac[array_nocopy_cut_mods_def] >> strip_tac >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
       stmt_state_rel H ctx func cenv cx fin it /\ immutable_frame_mods func cenv cx fin it /\
       storage_well_formed_on cx fin (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx fin Gi tni it` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ idx mid _ _ _ fin _ _ it /\ _`
       (drule_then strip_assume_tac) >>
     fs[expr_post_mods_def,expr_post_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qabbrev_tac `H = storage_trace_horizon fin.storage_trace` >>
  qpat_assum `!h. _ ==> valid_horizon _ _ h mid.storage_trace /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. _ ==> stmt_state_rel h _ _ _ _ es s0 /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. _ ==> vv_post_mods h _ _ _ _ obj es _ _ _ mid _ _ s /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. _ ==> expr_post_mods h _ _ _ _ idx mid _ _ _ fin _ _ it /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `wb_frame cenv es mid sa s0 s /\
   (~expr_has_effect obj ==> pure_frame cenv func es sa s0 s)` by
    (qpat_assum `vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `expr_post_mods H _ _ _ _ idx mid _ _ _ fin _ _ it`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_then assume_tac expr_post_frame >>
  `wb_frame cenv es fin sa s0 it` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >> simp[] >> conj_tac
     >- (qexistsl [`mid`,`sm`,`s`] >> simp[]) >>
     qexistsl [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
  simp[] >> conj_tac
  >- (strip_tac >> drule_all_then assume_tac expr_post_pure_frame >>
      irule pure_frame_trans >> simp[] >> qexistsl [`mid`,`sm`,`s`] >>
      fs[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans) >> simp[] >> conj_tac
  >- (qexistsl [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
  qexistsl [`G1`,`mid`,`mid`,`s`,`sm`,`tn1`] >> simp[]
QED
