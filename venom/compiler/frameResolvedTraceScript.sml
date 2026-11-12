Theory frameResolvedTrace
Ancestors venomWfProps ctxLookupAgreeHelpers frameResolvedOrigins frameActivationLifetime frameActivationCache
  frameJointTrace frameOriginCache
  frameOriginUpdates ptrDiscipline ptrDisciplineEmptyTaint frameJointTransition venomExecSemantics
  venomState venomInst venomMemProps frameAllocationOwnership frameOriginHistory
  frameOriginReachable frameHistoryDefinitions contextCodegenRel
  removeUnusedSsaProofs finite_map list pred_set

(* The local table is a view of the real cache, not an independently
   updated ghost cache.  In particular zero-size sites are retained. *)
Definition resolved_cache_def:
  resolved_cache (birth:num) (cache:(num,num # num) fmap) =
    FUN_FMAP (\aid. ((birth,aid), cache ' aid)) (FDOM cache)
End

Theorem resolved_cache_lookup:
  FLOOKUP (resolved_cache birth cache) aid =
    OPTION_MAP (\site. ((birth,aid),site)) (FLOOKUP cache aid)
Proof
  simp[resolved_cache_def, FLOOKUP_FUN_FMAP, FLOOKUP_DEF, FUN_FMAP_DEF] >>
  IF_CASES_TAC >> simp[]
QED

Theorem resolved_cache_local:
  resolve_tag (resolved_cache birth cache) rp (OriginLocal aid) site =
    if FLOOKUP cache aid = SOME site then SOME ((birth,aid),site) else NONE
Proof
  simp[resolve_tag_def, resolved_cache_lookup] >>
  Cases_on `FLOOKUP cache aid` >> simp[] >>
  Cases_on `x = site` >> simp[]
QED

(* A suffix describes the owning frame and its ancestors only.  Saved
   callers therefore cannot acquire tokens belonging to a popped callee. *)
Definition resolved_live_def:
  resolved_live (ids:num list) (frames:(ir_function # (num,num # num) fmap) list)
    entry <=>
    ?k. k < LENGTH ids /\ k < LENGTH frames /\
      EL k ids = FST (FST entry) /\
      FLOOKUP (SND (EL k frames)) (SND (FST entry)) = SOME (SND entry)
End

(* dyn is the bottom of the dynamic (DALLOCA) region.  A pointer that
   resolves to no entry, a dynamic actual included, has its site above it. *)
Definition resolved_frame_ok_def:
  resolved_frame_ok dyn birth cache PG G om rp rv ids frames <=>
    LIST_REL (\r p. case r of
                     SOME e => p = SOME (SND e)
                   | NONE => !site. p = SOME site ==> dyn <= FST site) rp PG /\
    resolution (resolved_cache birth cache) rp om rv /\
    origin_erase om = G /\
    (!v tag site. FLOOKUP om v = SOME (tag,site) /\ FLOOKUP rv v = NONE ==>
       dyn <= FST site) /\
    (!entry. MEM (SOME entry) rp ==> resolved_live ids frames entry) /\
    (!v entry. FLOOKUP rv v = SOME entry ==> resolved_live ids frames entry)
End

Definition resolved_stack_ok_def:
  (resolved_stack_ok [] [] [] [] [] <=> T) /\
  (resolved_stack_ok (birth::ids) (f::fs) (om::oms) (ann::anns) frames <=>
     frames = (f.cf_fn,f.cf_state.vs_allocas)::
       MAP (\g. (g.cf_fn,g.cf_state.vs_allocas)) fs /\
     resolved_frame_ok (w2n f.cf_state.vs_initial_fmp) birth
       f.cf_state.vs_allocas f.cf_params f.cf_prov om
       (FST ann) (SND ann) (birth::ids) frames /\
     resolved_stack_ok ids fs oms anns (TL frames)) /\
  (resolved_stack_ok [] (f::fs) oms anns frames <=> F) /\
  (resolved_stack_ok (birth::ids) [] oms anns frames <=> F) /\
  (resolved_stack_ok (birth::ids) (f::fs) [] anns frames <=> F) /\
  (resolved_stack_ok (birth::ids) (f::fs) (om::oms) [] frames <=> F) /\
  (resolved_stack_ok [] [] (om::oms) anns frames <=> F) /\
  (resolved_stack_ok [] [] [] (ann::anns) frames <=> F) /\
  (resolved_stack_ok [] [] [] [] (frame::frames) <=> F)
End

Definition resolved_config_ok_def:
  resolved_config_ok q ids anns <=>
    case q of JointConfig stk PG G tn fn inst s oms om hs h =>
      ?birth births ann saved.
        ids = birth::births /\ anns = ann::saved /\
        resolved_frame_ok (w2n s.vs_initial_fmp) birth s.vs_allocas PG G om
          (FST ann) (SND ann) ids ((fn,s.vs_allocas)::MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk) /\
        resolved_stack_ok births stk oms saved
          (MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk)
End

(* Every pointer of every frame resolves, as in a run without DALLOCA. *)
Definition resolved_complete_def:
  resolved_complete q anns <=>
    case q of JointConfig stk PG G tn fn inst s oms om hs h =>
      ?ann saved. anns = ann::saved /\
        MAP (OPTION_MAP SND) (FST ann) = PG /\ SND o_f SND ann = G /\
        LIST_REL (\f a. MAP (OPTION_MAP SND) (FST a) = f.cf_params /\
                        SND o_f SND a = f.cf_prov) stk saved
End

(* A frame is suspended in the state it was reachable in, so a property
   every reachable state has holds of every saved frame too. *)
Theorem frame_reachable_saved_below_fmp:
  !vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==>
    (!stk PG G tn fn inst s. frame_reachable vs0 ctx stk PG G tn fn inst s ==>
       allocas_below_fmp s) ==>
    EVERY (\f. allocas_below_fmp f.cf_state) stk
Proof
  ho_match_mp_tac frame_reachable_strongind >> rw[] >> metis_tac[]
QED

Theorem frame_reachable_initial_fmp:
  !vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==>
    s.vs_initial_fmp = vs0.vs_initial_fmp /\
    EVERY (\f. f.cf_state.vs_initial_fmp = vs0.vs_initial_fmp) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rw[] >>
  imp_res_tac enters_block_initial_fmp >> imp_res_tac step_inst_initial_fmp >>
  imp_res_tac setup_callee_initial_fmp >> imp_res_tac bind_outputs_initial_fmp >>
  gvs[]
QED

(* With DALLOCA, every cache of a reachable frame and its callers lies below
   the dynamic region. *)
Theorem frame_reachable_caches_below:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\ ptr_discipline lo ctx vs0 /\
  ctx_has_dalloca ctx ==>
  !k aid b sz.
    k < LENGTH ((fn,s.vs_allocas)::MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk) /\
    FLOOKUP (SND (EL k ((fn,s.vs_allocas)::
      MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk))) aid = SOME (b,sz) ==>
    b + sz <= w2n s.vs_initial_fmp
Proof
  strip_tac >>
  `!stk PG G tn fn inst s. frame_reachable vs0 ctx stk PG G tn fn inst s ==>
     allocas_below_fmp s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `allocas_below_fmp s` by metis_tac[] >>
  drule_all frame_reachable_saved_below_fmp >> strip_tac >>
  drule frame_reachable_initial_fmp >> strip_tac >>
  qpat_x_assum `!stk PG G tn fn inst s. _` kall_tac >>
  rpt gen_tac >> Cases_on `k` >> simp[]
  >- (fs[allocas_below_fmp_def] >> metis_tac[]) >>
  strip_tac >>
  `allocas_below_fmp (EL n stk).cf_state /\
   (EL n stk).cf_state.vs_initial_fmp = vs0.vs_initial_fmp` by fs[EVERY_EL] >>
  fs[allocas_below_fmp_def] >>
  `FLOOKUP (EL n stk).cf_state.vs_allocas aid = SOME (b,sz)` by gvs[EL_MAP] >>
  metis_tac[]
QED

Theorem resolved_frame_empty:
  resolved_frame_ok dyn birth cache [] FEMPTY FEMPTY [] FEMPTY ids frames
Proof
  simp[resolved_frame_ok_def, resolution_empty, origin_erase_def]
QED

Theorem resolved_config_initial:
  joint_initial vs0 C q ==> resolved_config_ok q [0] [([],FEMPTY)]
Proof
  simp[Once joint_initial_cases] >> rpt strip_tac >>
  simp[resolved_config_ok_def, resolved_stack_ok_def, resolved_frame_empty]
QED

Theorem resolved_complete_initial:
  joint_initial vs0 C q ==> resolved_complete q [([],FEMPTY)]
Proof
  simp[Once joint_initial_cases] >> rpt strip_tac >> simp[resolved_complete_def]
QED

Theorem resolved_frame_erasure:
  resolved_frame_ok dyn birth cache PG G om rp rv ids frames ==>
  LIST_REL (\r p. case r of
                   SOME e => p = SOME (SND e)
                 | NONE => !site. p = SOME site ==> dyn <= FST site) rp PG /\
  (!v e. FLOOKUP rv v = SOME e ==> FLOOKUP G v = SOME (SND e)) /\
  (!v site. FLOOKUP G v = SOME site /\ FLOOKUP rv v = NONE ==> dyn <= FST site) /\
  origin_erase om = G
Proof
  simp[resolved_frame_ok_def] >> strip_tac >> gvs[] >>
  simp[origin_erase_lookup, PULL_EXISTS, pairTheory.FORALL_PROD] >> rpt strip_tac
  >- (drule_all resolution_erasure >> rw[origin_erase_lookup] >> metis_tac[]) >>
  qpat_x_assum `!v tag site. _` drule_all >> simp[]
QED

Theorem resolved_frame_complete:
  resolved_frame_ok dyn birth cache PG G om rp rv ids frames ==>
  ((MAP (OPTION_MAP SND) rp = PG /\ SND o_f rv = G) <=>
   !d. resolved_frame_ok d birth cache PG G om rp rv ids frames)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> gen_tac >>
      qpat_x_assum `MAP _ rp = PG` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `SND o_f rv = G` (SUBST_ALL_TAC o SYM) >>
      fs[resolved_frame_ok_def] >> rpt conj_tac
      >- (simp[LIST_REL_MAP2] >> irule EVERY2_refl >> Cases >> simp[]) >>
      rpt strip_tac >>
      `FLOOKUP (origin_erase om) v = FLOOKUP (SND o_f rv) v` by fs[] >>
      gvs[origin_erase_lookup, FLOOKUP_o_f] >> res_tac >> fs[]) >>
  strip_tac >>
  `!d. LIST_REL (\r p. case r of
                         SOME e => p = SOME (SND e)
                       | NONE => !site. p = SOME site ==> d <= FST site) rp PG /\
       !v site. FLOOKUP G v = SOME site /\ FLOOKUP rv v = NONE ==> d <= FST site` by
    (gen_tac >> qpat_x_assum `!d. _`
       (qspec_then `d` (strip_assume_tac o MATCH_MP resolved_frame_erasure)) >>
     metis_tac[]) >>
  `LENGTH PG = LENGTH rp /\
   !k e. k < LENGTH rp /\ EL k rp = SOME e ==> EL k PG = SOME (SND e)` by
    (qpat_x_assum `!d. LIST_REL _ _ _ /\ _` (qspec_then `0` mp_tac) >>
     simp[LIST_REL_EL_EQN] >> rpt strip_tac >> gvs[] >>
     qpat_x_assum `!n. n < _ ==> _` (qspec_then `k` mp_tac) >> simp[]) >>
  `!v e. FLOOKUP rv v = SOME e ==> FLOOKUP G v = SOME (SND e)` by
    metis_tac[resolved_frame_erasure] >>
  conj_tac
  >- (simp[LIST_EQ_REWRITE] >> rpt strip_tac >>
      `EL x (MAP (OPTION_MAP SND) rp) = OPTION_MAP SND (EL x rp)` by
        (irule EL_MAP >> fs[]) >>
      fs[] >> Cases_on `EL x rp` >> Cases_on `EL x PG` >> fs[] >>
      res_tac >> fs[] >>
      qpat_x_assum `!d. LIST_REL _ _ _ /\ _`
        (qspec_then `SUC (FST x')` strip_assume_tac) >>
      qpat_x_assum `LIST_REL _ rp PG`
        (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
      first_x_assum (qspec_then `x` mp_tac) >> fs[]) >>
  simp[fmap_eq_flookup, FLOOKUP_o_f] >> gen_tac >>
  Cases_on `FLOOKUP rv x` >> simp[]
  >- (Cases_on `FLOOKUP G x` >> simp[] >>
      qpat_x_assum `!d. LIST_REL _ _ _ /\ _`
        (qspec_then `SUC (FST x')` strip_assume_tac) >>
      res_tac >> fs[]) >>
  res_tac >> fs[]
QED

Theorem resolved_frame_parameters:
  resolved_frame_ok dyn birth cache PG G om rp rv ids frames ==>
  LENGTH PG = LENGTH rp /\
  !k e. k < LENGTH rp /\ EL k rp = SOME e ==> EL k PG = SOME (SND e)
Proof
  simp[resolved_frame_ok_def, LIST_REL_EL_EQN] >> rpt strip_tac >>
  qpat_x_assum `!n. n < _ ==> _` (qspec_then `k` mp_tac) >> gvs[]
QED

Theorem resolved_config_current:
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) (ann::anns) ==>
  resolved_frame_ok (w2n s.vs_initial_fmp) birth s.vs_allocas PG G om
    (FST ann) (SND ann) (birth::ids) ((fn,s.vs_allocas)::MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk)
Proof
  simp[resolved_config_ok_def]
QED

Theorem resolved_live_head:
  FLOOKUP cache aid = SOME site ==>
  resolved_live (birth::ids) ((fn,cache)::frames) ((birth,aid),site)
Proof
  simp[resolved_live_def] >> strip_tac >> qexists_tac `0` >> simp[]
QED

Theorem resolved_live_weaken:
  resolved_live ids frames entry ==>
  resolved_live (birth::ids) (frame::frames) entry
Proof
  simp[resolved_live_def] >> rpt strip_tac >>
  qexists_tac `SUC k` >> simp[]
QED

Theorem resolved_live_cache_transport:
  resolved_live (birth::ids) ((fn,cache)::frames) entry /\
  (!aid site. FLOOKUP cache aid = SOME site ==> FLOOKUP cache' aid = SOME site) ==>
  resolved_live (birth::ids) ((fn,cache')::frames) entry
Proof
  simp[resolved_live_def] >> rpt strip_tac >>
  qexists_tac `k` >> Cases_on `k` >> gvs[]
QED

Theorem resolved_frame_restrict:
  resolved_frame_ok dyn birth cache PG G om rp rv ids frames ==>
  resolved_frame_ok dyn birth cache PG (DRESTRICT G keys) (DRESTRICT om keys)
    rp (DRESTRICT rv keys) ids frames
Proof
  simp[resolved_frame_ok_def] >> rpt strip_tac
  >- metis_tac[resolution_restrict]
  >- simp[origin_erase_restrict]
  >> fs[FLOOKUP_DRESTRICT, AllCaseEqs()] >> metis_tac[]
QED

Theorem resolved_stack_lengths:
  !ids stk oms anns frames. resolved_stack_ok ids stk oms anns frames ==>
  LENGTH ids = LENGTH stk /\ LENGTH oms = LENGTH stk /\ LENGTH anns = LENGTH stk
Proof
  Induct >> Cases_on `stk` >> Cases_on `oms` >> Cases_on `anns` >>
  simp[resolved_stack_ok_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem resolved_config_lengths:
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h) ids anns ==>
  LENGTH ids = SUC (LENGTH stk) /\ LENGTH anns = SUC (LENGTH stk) /\
  LENGTH oms = LENGTH stk
Proof
  simp[resolved_config_ok_def] >> rpt strip_tac >>
  drule resolved_stack_lengths >> simp[]
QED

Theorem resolved_config_return:
  joint_transition C q (SOME (OriginResume fuel fn inst s ret send post)) q' /\
  resolved_config_ok q ids anns ==>
  ?anns'. resolved_config_ok q' (TL ids) anns'
Proof
  rewrite_tac[joint_transition_return] >> rpt strip_tac >> gvs[] >>
  gvs[resolved_config_ok_def] >>
  Cases_on `births` >> Cases_on `saved` >> gvs[resolved_stack_ok_def] >>
  rename1 `resolved_frame_ok _ caller_birth _ _ _ _ (FST caller_ann) _ _ _` >>
  `post.vs_allocas = f.cf_state.vs_allocas` by
    (drule return_bind_cache >> simp[]) >>
  `post.vs_initial_fmp = f.cf_state.vs_initial_fmp` by
    (drule bind_outputs_initial_fmp >> simp[]) >>
  qexistsl_tac [`(FST caller_ann,
    DRESTRICT (SND caller_ann) (COMPL (set f.cf_inst.inst_outputs)))`, `t'`] >>
  simp[] >> metis_tac[resolved_frame_restrict]
QED

Theorem resolved_arguments_live:
  (!v entry. FLOOKUP rv v = SOME entry ==> resolved_live ids frames entry) /\
  MEM (SOME entry) (MAP (resolved_op rv) ops) ==>
  resolved_live ids frames entry
Proof
  simp[MEM_MAP] >> rpt strip_tac >> Cases_on `y` >>
  gvs[resolved_op_def] >> metis_tac[]
QED

Theorem resolved_frame_callee:
  resolved_frame_ok dyn birth cache PG G om rp rv ids frames ==>
  resolved_frame_ok dyn fresh callee_cache (MAP (op_prov G) ops) FEMPTY FEMPTY
    (MAP (resolved_op rv) ops) FEMPTY (fresh::ids) ((callee,callee_cache)::frames)
Proof
  strip_tac >> drule resolved_frame_erasure >> strip_tac >>
  fs[resolved_frame_ok_def, resolution_empty, origin_erase_def] >>
  rpt strip_tac
  >- (simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
      Cases_on `EL n ops` >> simp[resolved_op_def, op_prov_def] >>
      Cases_on `FLOOKUP rv s` >> simp[] >> metis_tac[]) >>
  irule resolved_live_weaken >> metis_tac[resolved_arguments_live]
QED

Theorem resolved_config_call:
  joint_transition C q NONE q' /\ resolved_config_ok q ids anns ==>
  ?anns'. resolved_config_ok q' (fresh::ids) anns'
Proof
  Cases_on `q` >> strip_tac >>
  rename1 `joint_transition C (JointConfig stk PG G tn caller callinst s oms om hs h) NONE q'` >>
  gvs[joint_transition_call_iff] >>
  gvs[resolved_config_ok_def] >>
  qexistsl_tac [`(MAP (resolved_op (SND ann)) ops,FEMPTY)`, `ann::saved`] >>
  simp[resolved_stack_ok_def] >>
  `s1.vs_initial_fmp = s.vs_initial_fmp` by
    metis_tac[enters_block_initial_fmp, setup_callee_initial_fmp] >>
  simp[] >> metis_tac[resolved_frame_callee]
QED

Theorem resolve_cache_transport:
  (!aid site. FLOOKUP cache aid = SOME site ==> FLOOKUP cache' aid = SOME site) /\
  resolve_tag (resolved_cache birth cache) rp tag site = SOME entry ==>
  resolve_tag (resolved_cache birth cache') rp tag site = SOME entry
Proof
  Cases_on `tag` >> simp[resolve_tag_def, resolved_cache_lookup] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem resolution_cache_transport:
  resolution (resolved_cache birth cache) rp om rv /\
  (!aid site. FLOOKUP cache aid = SOME site ==> FLOOKUP cache' aid = SOME site) ==>
  resolution (resolved_cache birth cache') rp om rv
Proof
  simp[resolution_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >>
  Cases_on `FLOOKUP om v` >> simp[] >> PairCases_on `x` >> simp[] >>
  Cases_on `resolve_tag (resolved_cache birth cache) rp x0 (x1,x2)`
  >- (simp[] >> strip_tac >> gvs[unresolved_tag_def, resolve_tag_def]) >>
  drule_all resolve_cache_transport >> simp[]
QED

Theorem resolved_frame_cache_transport:
  resolved_frame_ok dyn birth cache PG G om rp rv (birth::ids) ((fn,cache)::frames) /\
  (!aid site. FLOOKUP cache aid = SOME site ==> FLOOKUP cache' aid = SOME site) ==>
  resolved_frame_ok dyn birth cache' PG G om rp rv (birth::ids) ((fn,cache')::frames)
Proof
  simp[resolved_frame_ok_def] >> metis_tac[resolution_cache_transport,
    resolved_live_cache_transport]
QED

Theorem origin_set_property:
  (!v entry. FLOOKUP rv v = SOME entry ==> P entry) /\
  (!entry. r = SOME entry ==> P entry) ==>
  !v entry. FLOOKUP (origin_set rv outs r) v = SOME entry ==> P entry
Proof
  Cases_on `outs` >> Cases_on `r` >>
  simp[origin_set_def, FLOOKUP_DRESTRICT, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> Cases_on `t` >>
  gvs[origin_set_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]
QED

Theorem resolved_phi_property:
  (!v entry. FLOOKUP rv v = SOME entry ==> P entry) /\
  resolved_phi prev rv inst = SOME entry ==> P entry
Proof
  Cases_on `prev` >> simp[resolved_phi_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `op` >> gvs[resolved_op_def] >> metis_tac[]
QED

Theorem resolved_phis_property:
  !insts. (!v entry. FLOOKUP rv v = SOME entry ==> P entry) ==>
  !v entry. FLOOKUP (resolved_phis prev rv insts) v = SOME entry ==> P entry
Proof
  Induct >- simp[resolved_phis_def] >> gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (simp[resolved_phis_def] >> ho_match_mp_tac origin_set_property >>
      conj_tac >- metis_tac[] >> metis_tac[resolved_phi_property]) >>
  simp[resolved_phis_def] >> metis_tac[]
QED

Definition resolved_entry_def:
  resolved_entry fn s rv =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      NONE => rv | SOME bb => resolved_phis s.vs_prev_bb rv bb.bb_instructions
End

Theorem origin_set_floor[local]:
  (!v tag site. FLOOKUP om v = SOME (tag,site:num # num) /\ FLOOKUP rv v = NONE ==>
     (dyn:num) <= FST site) /\
  (!tag site. p = SOME (tag,site) /\ r = NONE ==> dyn <= FST site) ==>
  !v tag site. FLOOKUP (origin_set om outs p) v = SOME (tag,site) /\
    FLOOKUP (origin_set rv outs r) v = NONE ==> dyn <= FST site
Proof
  strip_tac >> Cases_on `outs`
  >- (simp[origin_set_def, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  Cases_on `t`
  >- (Cases_on `p` >> Cases_on `r` >>
      simp[origin_set_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
      rw[] >> gvs[] >> metis_tac[]) >>
  Cases_on `p` >> Cases_on `r` >>
  simp[origin_set_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem origin_phi_floor[local]:
  (!v tag site. FLOOKUP om v = SOME (tag,site) /\ FLOOKUP rv v = NONE ==>
     dyn <= FST site) /\
  origin_phi prev om inst = SOME (tag,site) /\ resolved_phi prev rv inst = NONE ==>
  dyn <= FST site
Proof
  Cases_on `prev` >> simp[origin_phi_def, resolved_phi_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `op` >> gvs[origin_op_def, resolved_op_def] >> metis_tac[]
QED

Theorem origin_phis_floor[local]:
  !insts. (!v tag site. FLOOKUP om v = SOME (tag,site) /\ FLOOKUP rv v = NONE ==>
     dyn <= FST site) ==>
  !v tag site. FLOOKUP (origin_phis prev om insts) v = SOME (tag,site) /\
    FLOOKUP (resolved_phis prev rv insts) v = NONE ==> dyn <= FST site
Proof
  Induct >- simp[origin_phis_def, resolved_phis_def] >>
  gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[origin_phis_def, resolved_phis_def]
  >- (ho_match_mp_tac origin_set_floor >> conj_tac >- metis_tac[] >>
      metis_tac[origin_phi_floor]) >>
  metis_tac[]
QED

Theorem resolved_frame_entry:
  resolved_frame_ok dyn birth s.vs_allocas PG G om rp rv ids frames ==>
  resolved_frame_ok dyn birth s.vs_allocas PG (entry_prov fn s G)
    (origin_entry fn s om) rp (resolved_entry fn s rv) ids frames
Proof
  strip_tac >>
  `resolution (resolved_cache birth s.vs_allocas) rp
     (origin_entry fn s om) (resolved_entry fn s rv)` by
    (fs[resolved_frame_ok_def] >>
     simp[origin_entry_def, resolved_entry_def] >>
     Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
     simp[resolution_phis]) >>
  `origin_erase (origin_entry fn s om) = entry_prov fn s G` by
    fs[resolved_frame_ok_def, origin_entry_erase] >>
  `!v tag site. FLOOKUP (origin_entry fn s om) v = SOME (tag,site) /\
     FLOOKUP (resolved_entry fn s rv) v = NONE ==> dyn <= FST site` by
    (fs[resolved_frame_ok_def, origin_entry_def, resolved_entry_def] >>
     Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[]
     >- metis_tac[] >>
     metis_tac[origin_phis_floor]) >>
  `!v entry. FLOOKUP (resolved_entry fn s rv) v = SOME entry ==>
     resolved_live ids frames entry` by
    (fs[resolved_frame_ok_def, resolved_entry_def] >>
     Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[]
     >- metis_tac[] >>
     rpt strip_tac >> drule resolved_phis_property >>
     disch_then (qspecl_then [`s.vs_prev_bb`, `x.bb_instructions`, `v`, `entry`] mp_tac) >>
     simp[]) >>
  fs[resolved_frame_ok_def] >> metis_tac[]
QED

Theorem resolved_config_block:
  joint_transition C q (SOME (OriginBlock fuel post)) q' /\
  resolved_config_ok q ids anns ==>
  ?anns'. resolved_config_ok q' ids anns'
Proof
  Cases_on `q` >> strip_tac >>
  rename1 `joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h) _ q'` >>
  gvs[joint_transition_block_iff, resolved_config_ok_def] >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `post.vs_initial_fmp = s.vs_initial_fmp` by
    metis_tac[step_inst_non_invoke, step_inst_base_initial_fmp] >>
  `s1.vs_initial_fmp = s.vs_initial_fmp` by
    metis_tac[enters_block_initial_fmp] >>
  `post.vs_allocas = s.vs_allocas` by
    (gvs[step_inst_non_invoke] >> metis_tac[step_inst_base_preserves_allocas]) >>
  `s1.vs_allocas = s.vs_allocas` by metis_tac[enters_block_allocas] >>
  qexistsl_tac [`(FST ann, resolved_entry fn post (SND ann))`, `saved`] >>
  simp[] >> metis_tac[resolved_frame_entry]
QED

Theorem resolved_parameter_exists:
  MAP (OPTION_MAP SND) rp = PG /\ k < LENGTH PG /\ EL k PG = SOME site ==>
  ?entry. resolve_tag ct rp (OriginParameter k) site = SOME entry /\
    MEM (SOME entry) rp
Proof
  strip_tac >> gvs[EL_MAP] >>
  Cases_on `EL k rp` >> gvs[resolve_tag_def, EL_MAP] >>
  metis_tac[MEM_EL]
QED

Theorem resolved_parameter_unresolved:
  LIST_REL (\r p. case r of
                   SOME e => p = SOME (SND e)
                 | NONE => !site. p = SOME site ==> dyn <= FST site) rp PG /\
  k < LENGTH PG /\ EL k PG = SOME site /\
  resolve_tag ct rp (OriginParameter k) site = NONE ==>
  unresolved_tag rp (OriginParameter k) /\ dyn <= FST site
Proof
  rw[LIST_REL_EL_EQN] >> qpat_x_assum `!n. n < _ ==> _` (qspec_then `k` mp_tac) >>
  Cases_on `EL k rp` >> gvs[resolve_tag_def, unresolved_tag_def]
QED

Theorem resolved_tag_live:
  resolved_frame_ok dyn birth cache PG G om rp rv (birth::ids) ((fn,cache)::frames) /\
  resolve_tag (resolved_cache birth cache) rp tag site = SOME entry ==>
  resolved_live (birth::ids) ((fn,cache)::frames) entry
Proof
  simp[resolved_frame_ok_def] >> rpt strip_tac >>
  Cases_on `tag` >> fs[resolve_tag_def, resolved_cache_lookup, AllCaseEqs()] >>
  gvs[]
  >- metis_tac[resolved_live_head] >>
  metis_tac[MEM_EL]
QED

(* A new pointer resolves unless it is dynamic: a DALLOCA result, a dynamic
   actual, or derived from one; its site is then above dyn. *)
Theorem resolved_origin_out:
  resolved_frame_ok dyn birth s.vs_allocas PG G om rp rv ids frames /\
  (inst.inst_opcode = DALLOCA ==>
   !out b. inst.inst_outputs = [out] /\ lookup_var out s = SOME b ==>
     dyn <= w2n b) /\
  origin_out PG om inst s = SOME (tag,site) /\
  resolve_tag (resolved_cache birth s.vs_allocas) rp tag site = NONE ==>
  unresolved_tag rp tag /\ dyn <= FST site
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- gvs[origin_out_alloca, resolved_cache_local] >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- gvs[origin_out_dalloca, unresolved_tag_def] >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (gvs[origin_out_param] >> fs[resolved_frame_ok_def] >>
      metis_tac[resolved_parameter_unresolved]) >>
  drule_all origin_out_inherited >> strip_tac >>
  Cases_on `op` >> gvs[origin_op_def] >>
  fs[resolved_frame_ok_def] >> drule_all resolution_lookup >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Definition resolved_out_def:
  resolved_out birth cache rp p =
    case p of NONE => NONE | SOME (tag,site) =>
      resolve_tag (resolved_cache birth cache) rp tag site
End

Theorem resolved_frame_step:
  resolved_frame_ok dyn birth s.vs_allocas PG G om rp rv (birth::ids)
    ((fn,s.vs_allocas)::frames) /\
  (inst.inst_opcode = DALLOCA ==>
   !out b. inst.inst_outputs = [out] /\ lookup_var out s = SOME b ==>
     dyn <= w2n b) ==>
  resolved_frame_ok dyn birth s.vs_allocas PG (step_prov PG G inst s)
    (origin_step PG om inst s) rp
    (origin_set rv inst.inst_outputs
      (resolved_out birth s.vs_allocas rp (origin_out PG om inst s)))
    (birth::ids) ((fn,s.vs_allocas)::frames)
Proof
  strip_tac >>
  `resolution (resolved_cache birth s.vs_allocas) rp (origin_step PG om inst s)
    (origin_set rv inst.inst_outputs
      (resolved_out birth s.vs_allocas rp (origin_out PG om inst s)))` by
    (simp[origin_step_def] >> irule resolution_origin_set >>
     reverse conj_tac >- fs[resolved_frame_ok_def] >>
     Cases_on `origin_out PG om inst s` >> simp[resolved_out_def] >>
     PairCases_on `x` >> simp[] >> metis_tac[resolved_origin_out]) >>
  `origin_erase (origin_step PG om inst s) = step_prov PG G inst s` by
    fs[resolved_frame_ok_def, origin_step_erase] >>
  `!v tag site. FLOOKUP (origin_step PG om inst s) v = SOME (tag,site) /\
     FLOOKUP (origin_set rv inst.inst_outputs
       (resolved_out birth s.vs_allocas rp (origin_out PG om inst s))) v = NONE ==>
     dyn <= FST site` by
    (simp[origin_step_def] >> ho_match_mp_tac origin_set_floor >>
     conj_tac >- fs[resolved_frame_ok_def] >>
     simp[resolved_out_def] >> rpt strip_tac >> gvs[] >>
     drule_all resolved_origin_out >> simp[]) >>
  `!v entry. FLOOKUP (origin_set rv inst.inst_outputs
       (resolved_out birth s.vs_allocas rp (origin_out PG om inst s))) v =
       SOME entry ==> resolved_live (birth::ids) ((fn,s.vs_allocas)::frames) entry` by
    (ho_match_mp_tac origin_set_property >> conj_tac
     >- fs[resolved_frame_ok_def] >>
     simp[resolved_out_def] >>
     Cases_on `origin_out PG om inst s` >> simp[] >> PairCases_on `x` >>
     simp[] >> metis_tac[resolved_tag_live]) >>
  fs[resolved_frame_ok_def] >> metis_tac[]
QED

Theorem resolved_dalloca_output:
  inst.inst_opcode = DALLOCA /\ step_inst fuel ctx inst s = OK post /\
  inst.inst_outputs = [out] /\ lookup_var out post = SOME b ==> b = s.vs_fmp
Proof
  rpt strip_tac >> gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem resolved_config_ordinary:
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginOrdinary fuel post)) q' /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h) ids anns /\
  (inst.inst_opcode = DALLOCA ==> w2n s.vs_initial_fmp <= w2n s.vs_fmp) ==>
  ?anns'. resolved_config_ok q' ids anns'
Proof
  simp[joint_transition_ordinary] >> rpt strip_tac >> gvs[] >>
  gvs[resolved_config_ok_def] >>
  `post.vs_initial_fmp = s.vs_initial_fmp` by
    metis_tac[step_inst_non_invoke, step_inst_base_initial_fmp] >>
  `resolved_frame_ok (w2n s.vs_initial_fmp) birth post.vs_allocas PG G om
    (FST ann) (SND ann)
    (birth::births)
    ((fn,post.vs_allocas)::MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk)` by
    (irule resolved_frame_cache_transport >> goal_assum (drule_at Any) >>
     metis_tac[step_inst_cache_preserved]) >>
  qexistsl_tac [`(FST ann, origin_set (SND ann) inst.inst_outputs
    (resolved_out birth post.vs_allocas (FST ann) (origin_out PG om inst post)))`,
    `saved`] >>
  simp[] >> irule resolved_frame_step >> simp[] >> rpt strip_tac >>
  drule_all resolved_dalloca_output >> simp[]
QED

Theorem resolved_config_transition:
  joint_transition C q ev q' /\ resolved_config_ok q ids anns /\
  (case q of JointConfig stk PG G tn fn inst s oms om hs h =>
    inst.inst_opcode = DALLOCA ==> w2n s.vs_initial_fmp <= w2n s.vs_fmp) ==>
  ?anns'. resolved_config_ok q' (lifetime_step n ev ids) anns'
Proof
  rpt strip_tac >> drule joint_transition_label_cases >> strip_tac
  >- (gvs[lifetime_step_def] >> metis_tac[resolved_config_call])
  >- (Cases_on `q` >> gvs[lifetime_step_def] >>
      metis_tac[resolved_config_ordinary])
  >- (gvs[lifetime_step_def] >> metis_tac[resolved_config_block]) >>
  gvs[lifetime_step_def] >> metis_tac[resolved_config_return]
QED

(* A reachable DALLOCA is an instruction of the program. *)
Theorem joint_reachable_dalloca:
  joint_config_reachable vs0 C (JointConfig stk PG G tn fn inst s oms om hs h) /\
  inst.inst_opcode = DALLOCA ==> ctx_has_dalloca C
Proof
  strip_tac >> spose_not_then assume_tac >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `MEM fn C.ctx_functions` by metis_tac[frame_allocation_ownership] >>
  `active_inst fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_projection, frame_history_active]) >>
  qpat_x_assum `~ctx_has_dalloca C` mp_tac >>
  simp[ctx_has_dalloca_def, EXISTS_MEM] >>
  qexists_tac `fn` >> simp[] >>
  gvs[active_inst_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  metis_tac[MEM_EL]
QED

Theorem resolved_reachable_transition:
  joint_config_reachable vs0 C q /\ ptr_discipline lo C vs0 /\
  joint_transition C q ev q' /\ resolved_config_ok q ids anns ==>
  ?anns'. resolved_config_ok q' (lifetime_step n ev ids) anns'
Proof
  Cases_on `q` >> rpt strip_tac >>
  rename1 `joint_config_reachable vs0 C (JointConfig stk PG G tn fn inst s oms om hs h)` >>
  `inst.inst_opcode = DALLOCA ==> w2n s.vs_initial_fmp <= w2n s.vs_fmp` by
    (strip_tac >> drule_all joint_reachable_dalloca >> strip_tac >>
     `frame_reachable vs0 C stk PG G tn fn inst s` by
       (fs[joint_config_reachable_def] >>
        metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
     fs[ptr_discipline_def, allocas_below_fmp_def] >> metis_tac[]) >>
  irule resolved_config_transition >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any)
QED

Theorem resolved_chain_annotations:
  !es n ids anns q qs r.
  joint_chain C q es qs r /\ joint_config_reachable vs0 C q /\
  ptr_discipline lo C vs0 /\ resolved_config_ok q ids anns ==>
  ?ass. HD ass = anns /\ LENGTH ass = SUC (LENGTH es) /\
    !k. k <= LENGTH es ==>
      resolved_config_ok (EL k (q::qs))
        (EL k (lifetime_annotations n ids es)) (EL k ass)
Proof
  Induct >> Cases_on `qs` >> simp[joint_chain_def]
  >- (rpt strip_tac >> qexists_tac `[anns]` >> simp[lifetime_annotations_def]) >>
  rpt strip_tac >> rename1 `joint_transition C q ev next` >>
  `?anns1. resolved_config_ok next (lifetime_step n ev ids) anns1` by
    metis_tac[resolved_reachable_transition] >>
  `joint_config_reachable vs0 C next` by metis_tac[joint_transition_reachable] >>
  first_x_assum drule >>
  disch_then (qspecl_then [`SUC n`, `lifetime_step n ev ids`, `anns1`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `anns::ass` >> simp[] >>
  gen_tac >> Cases_on `k` >> simp[lifetime_annotations_def]
QED

Theorem joint_trace_resolved_annotations:
  joint_trace vs0 C q0 es qs q /\ ptr_discipline lo C vs0 ==>
  ?ass. HD ass = [([],FEMPTY)] /\ LENGTH ass = SUC (LENGTH es) /\
    !k. k <= LENGTH es ==>
      resolved_config_ok (EL k (q0::qs))
        (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
Proof
  simp[joint_trace_def] >> strip_tac >>
  `resolved_config_ok q0 [0] [([],FEMPTY)]` by metis_tac[resolved_config_initial] >>
  `joint_config_reachable vs0 C q0` by metis_tac[joint_initial_reachable] >>
  drule_all resolved_chain_annotations >>
  disch_then (qspec_then `0` mp_tac) >> simp[]
QED

Theorem resolved_live_activation_cache:
  resolved_live ids ((fn,s.vs_allocas)::
    MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk) ((birth,aid),site) /\
  LENGTH ids = SUC (LENGTH stk) ==>
  ?k owner. k < LENGTH ids /\ EL k ids = birth /\
    activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
      (LENGTH stk - k) owner aid site
Proof
  simp[resolved_live_def] >> rpt strip_tac >>
  Cases_on `k`
  >- (qexistsl_tac [`0`, `fn`] >> gvs[activation_cache_current]) >>
  gvs[EL_MAP] >>
  qexistsl_tac [`SUC n`, `(EL n stk).cf_fn`] >>
  simp[activation_cache_saved]
QED

Theorem resolved_current_lookup:
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\ FLOOKUP om v = SOME (tag,site) ==>
  FLOOKUP rv v = resolve_tag (resolved_cache birth s.vs_allocas) rp tag site /\
  !entry. FLOOKUP rv v = SOME entry ==> SND entry = site
Proof
  strip_tac >> drule resolved_config_current >> simp[] >>
  simp[resolved_frame_ok_def] >> rpt strip_tac >>
  drule_all resolution_lookup >> strip_tac >>
  metis_tac[resolve_tag_site]
QED

Theorem resolved_current_owner:
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\ FLOOKUP rv v = SOME ((token,aid),site) ==>
  ?k owner. k < LENGTH (birth::ids) /\ EL k (birth::ids) = token /\
    activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
      (LENGTH stk - k) owner aid site
Proof
  strip_tac >> drule resolved_config_lengths >> strip_tac >>
  drule resolved_config_current >> simp[resolved_frame_ok_def] >> rpt strip_tac >>
  `resolved_live (birth::ids)
    ((fn,s.vs_allocas)::MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk)
    ((token,aid),site)` by metis_tac[] >>
  drule_all resolved_live_activation_cache >> simp[]
QED

Theorem resolved_stack_frame:
  !ids stk oms anns frames k.
  resolved_stack_ok ids stk oms anns frames /\ k < LENGTH stk ==>
  resolved_frame_ok (w2n (EL k stk).cf_state.vs_initial_fmp) (EL k ids)
    (EL k stk).cf_state.vs_allocas
    (EL k stk).cf_params (EL k stk).cf_prov (EL k oms)
    (FST (EL k anns)) (SND (EL k anns)) (DROP k ids) (DROP k frames)
Proof
  Induct >> Cases_on `stk` >> Cases_on `oms` >> Cases_on `anns` >>
  simp[resolved_stack_ok_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `k` >> gvs[] >> metis_tac[]
QED

Theorem resolved_live_drop:
  !k ids frames entry. resolved_live (DROP k ids) (DROP k frames) entry ==>
  resolved_live ids frames entry
Proof
  Induct >- simp[] >> rpt gen_tac >>
  Cases_on `ids` >- simp[resolved_live_def] >>
  Cases_on `frames` >- simp[resolved_live_def] >>
  simp[] >> strip_tac >> irule resolved_live_weaken >>
  first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem resolved_config_saved:
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) (ann::anns) ==>
  resolved_stack_ok ids stk oms anns (MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk)
Proof
  simp[resolved_config_ok_def]
QED

Theorem resolved_saved_lookup:
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) (ann::anns) /\ k < LENGTH stk /\
  FLOOKUP (EL k oms) v = SOME (tag,site) ==>
  FLOOKUP (SND (EL k anns)) v = resolve_tag
      (resolved_cache (EL k ids) (EL k stk).cf_state.vs_allocas)
      (FST (EL k anns)) tag site /\
  !entry. FLOOKUP (SND (EL k anns)) v = SOME entry ==> SND entry = site
Proof
  strip_tac >> drule resolved_config_saved >> strip_tac >>
  drule_all resolved_stack_frame >> simp[resolved_frame_ok_def] >> rpt strip_tac >>
  drule_all resolution_lookup >> strip_tac >> metis_tac[resolve_tag_site]
QED

Theorem resolved_saved_owner:
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) (ann::anns) /\ k < LENGTH stk /\
  FLOOKUP (SND (EL k anns)) v = SOME ((token,aid),site) ==>
  ?j owner. j < LENGTH (birth::ids) /\ EL j (birth::ids) = token /\
    activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
      (LENGTH stk - j) owner aid site
Proof
  strip_tac >> drule resolved_config_lengths >> strip_tac >>
  drule resolved_config_saved >> strip_tac >>
  drule_all resolved_stack_frame >> simp[resolved_frame_ok_def] >> rpt strip_tac >>
  `resolved_live (DROP k ids)
    (DROP k (MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk)) ((token,aid),site)` by
    metis_tac[] >>
  drule resolved_live_drop >> strip_tac >>
  `resolved_live (birth::ids)
    ((fn,s.vs_allocas)::MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk)
    ((token,aid),site)` by metis_tac[resolved_live_weaken] >>
  drule_all resolved_live_activation_cache >> simp[]
QED

Theorem resolved_operand_owner:
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\ resolved_op rv op = SOME ((token,aid),site) ==>
  ?k owner. k < LENGTH (birth::ids) /\ EL k (birth::ids) = token /\
    activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
      (LENGTH stk - k) owner aid site
Proof
  Cases_on `op` >> simp[resolved_op_def] >>
  strip_tac >> drule_all resolved_current_owner >> simp[]
QED
