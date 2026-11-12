(* History transport through compiler-only suffixes, with fixed producers. *)
Theory exprExtRequestHistoryCompose
Ancestors
  exprExtRequestStrongCapture exprExtRequestHistory exprExtRequestSourceProbe
  exprExtRequestReadProbe loweringPosts exprSimProps compileEnv freshWrites

Theorem extrequest_history_frame_trans:
  extrequest_history_frame cenv cx ec sc tc ee sm t /\
  stmt_state_rel ctx func cenv cx ec tc /\
  extrequest_history_frame cenv cx ee sm t ef sn u ==>
  extrequest_history_frame cenv cx ec sc tc ef sn u
Proof
  strip_tac >>
  `!n b sz. local_region cenv ec.scopes tc n b sz <=>
             local_region cenv ee.scopes t n b sz` by
    (rpt gen_tac >> drule_all extrequest_history_local_regions >> simp[]) >>
  rewrite_tac[extrequest_history_frame_def] >> rpt conj_tac
  >- (gvs[extrequest_history_frame_def] >>
      metis_tac[extrequest_read_frame_trans])
  >- gvs[extrequest_history_frame_def]
  >- gvs[extrequest_history_frame_def]
  >- gvs[extrequest_history_frame_def]
  >- gvs[extrequest_history_frame_def]
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (gvs[extrequest_history_frame_def] >> metis_tac[not_fresh_at_mono]) >>
      gvs[extrequest_history_frame_def] >> metis_tac[])
  >- (gvs[extrequest_history_frame_def] >> metis_tac[])
  >- (rpt strip_tac >>
      `local_region cenv ee.scopes t n b sz` by metis_tac[] >>
      gvs[extrequest_history_frame_def] >> metis_tac[])
  >- suspend "allocations"
  >> (rpt strip_tac >>
      `ALOOKUP ec.immutables cx.txn.target = ALOOKUP ee.immutables cx.txn.target` by
        gvs[extrequest_history_frame_def, extrequest_read_frame_def] >>
      gvs[extrequest_history_frame_def] >> metis_tac[])
QED

Resume extrequest_history_frame_trans[allocations]:
  rpt strip_tac >>
  `FLOOKUP t.vs_allocas aid = SOME (b,sz)` by
    (gvs[extrequest_history_frame_def] >> metis_tac[]) >>
  `aid < sm.cs_next_id` by gvs[extrequest_history_frame_def] >>
  `!n lb lsz. local_region cenv ee.scopes t n lb lsz ==>
      regions_disjoint b sz lb lsz` by metis_tac[] >>
  `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz tc.vs_memory` by
    (gvs[extrequest_history_frame_def] >>
     qpat_x_assum `!aid b sz. FLOOKUP tc.vs_allocas aid = SOME (b,sz) /\ _ ==> _`
       (drule_all_then mp_tac) >> simp[]) >>
  `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz t.vs_memory` by
    (fs[extrequest_history_frame_def] >>
     qpat_x_assum `!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ _ ==> _`
       (qspecl_then [`aid`, `b`, `sz`] mp_tac) >>
     impl_tac >- metis_tac[] >>
     simp[]) >> simp[]
QED

Finalise extrequest_history_frame_trans

Theorem extrequest_strong_capture_history:
  extrequest_strong_capture ctx func cenv cx e r vv ee sm t /\
  extrequest_history_frame cenv cx ee sm t ef sn u ==>
  extrequest_strong_capture ctx func cenv cx e r vv ef sn u
Proof
  simp[extrequest_strong_capture_def] >> strip_tac >>
  qexistsl_tac [`es`, `sa`, `sc`, `s0`, `ec`, `tc`] >> simp[] >>
  irule extrequest_history_frame_trans >>
  qpat_assum `extrequest_history_frame _ _ _ _ _ ee sm t` (irule_at Any) >>
  gvs[vv_post_def] >> metis_tac[]
QED

Theorem extrequest_strong_captures_history:
  !es rs vvs.
    extrequest_strong_captures ctx func cenv cx es rs vvs ee sm t /\
    extrequest_history_frame cenv cx ee sm t ef sn u ==>
    extrequest_strong_captures ctx func cenv cx es rs vvs ef sn u
Proof
  Induct >> Cases_on `rs` >> Cases_on `vvs` >>
  simp[extrequest_strong_captures_def] >> rpt strip_tac
  >- (drule_all extrequest_strong_capture_history >> simp[]) >>
  qpat_x_assum `!rs vvs. _`
    (drule_all_then mp_tac o SRULE [extrequest_strong_captures_def]) >> simp[]
QED
