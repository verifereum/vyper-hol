Theory bodyIntCallStackHeadMods
Ancestors
  bodyIntCallStagePacketMods bodyFullIntCallArgs bodyFullPredsMods
  bodyForcedStorageFrameMods gasOutcomeFullBindPathMods gasOutcomeFullPostMods
  exprSimFullBundleProps bodyWriteSubscriptSourceMods bodyBranchCellFrameMods
  exprOperandVar exprSimWordArgs wordArgsPtr bodyFullIfExpReach
  vyperEvalExprPreservesScopesDom vyperEvalScopesProgress exprSimSliceCompose
  vyperTypeInvariants vyperTypeExprSoundness valueEncodingTyping
  stmtSimForRounds freshWrites loweringPosts bodyPtrDefs ptrDiscipline list
  loweringStateRelDefs loweringShapeDefs

(* The old prefix is transported through the forced expression's actual
   variable, allocation, and ghost frame. No operand is evaluated again. *)
Theorem stack_keep_prefix[local]:
  intcall_stage_ops_mods (lo,func) cenv cx sa (si,esi,s,G,tn) pin
    (ops,ws,vals,ptys,pflags) /\
  wb_frame cenv esi mid si s t /\ ghost_kept_at lo cenv esi si G tn s G1 tn1 /\
  si.cs_next_var <= cu.cs_next_var /\ si.cs_next_id <= cu.cs_next_id /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!n b k. local_region cenv esi.scopes s n b k <=>
           local_region cenv mid.scopes t n b k) /\ t.vs_labels = s.vs_labels /\
  (case pin of NONE => T | SOME (rb,b,k) =>
      FLOOKUP G rb = SOME (b,k) /\ op_taint tn (Var rb) = {} /\
      lookup_var rb s = SOME (n2w b) /\
      FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,k) /\
      sa.cs_next_id < si.cs_next_id /\ lo <= b /\ b+k <= s.vs_alloca_next /\
      not_fresh_at si rb /\
      (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
        b+k <= lb \/ lb+sz <= b)) ==>
  intcall_stage_ops_mods (lo,func) cenv cx sa (cu,mid,t,G1,tn1) pin
    (ops,ws,vals,ptys,pflags) /\
  (case pin of NONE => T | SOME (rb,b,k) =>
      FLOOKUP G1 rb = SOME (b,k) /\ op_taint tn1 (Var rb) = {} /\
      lookup_var rb t = SOME (n2w b) /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,k) /\
      sa.cs_next_id < cu.cs_next_id /\ lo <= b /\ b+k <= t.vs_alloca_next /\
      not_fresh_at cu rb /\
      (!n lb sz. local_region cenv mid.scopes t n lb sz ==>
        b+k <= lb \/ lb+sz <= b))
Proof
  pure_rewrite_tac [intcall_stage_ops_mods_def] >> strip_tac >>
  `!j. j < LENGTH ops ==> op_prov G1 (EL j ops) = op_prov G (EL j ops)` by
    (rpt strip_tac >> `MEM (EL j ops) ops` by simp[EL_MEM] >>
     Cases_on `EL j ops` >> gvs[op_prov_def,ghost_kept_at_def]) >>
  `!lbl. FLOOKUP t.vs_labels lbl = FLOOKUP s.vs_labels lbl` by simp[] >>
  drule_all_then mp_tac (SIMP_RULE bool_ss []
    (Q.INST [`clean_words` |-> `T`] intcall_args_prefix_frame)) >>
  simp[] >> strip_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac
  >- (qpat_assum `!j. j < LENGTH ops /\ ~EL j pflags ==> _`
        (drule_all_then strip_assume_tac) >>
      qexistsl_tac [`b`,`cap`,`aid`] >>
      `FLOOKUP t.vs_allocas aid = SOME (b,cap)` by fs[wb_frame_def] >>
      `aid < cu.cs_next_id` by decide_tac >> simp[] >> metis_tac[]) >>
  qpat_assum `!i j b k c l. _ ==> regions_disjoint b k c l` irule >>
  qexistsl_tac [`i`,`j`] >> simp[] >>
  `i < LENGTH ops` by decide_tac >>
  qpat_assum `!j. j < LENGTH ops ==> op_prov G1 _ = _`
    (fn th => simp[GSYM th])
QED

Theorem stack_locals_compose[local]:
  (!n b sz. local_region cenv es.scopes s n b sz ==>
             local_region cenv es1.scopes t n b sz) /\
  locals_kept cenv es es1 s t /\ locals_kept cenv es1 es2 t u ==>
  locals_kept cenv es es2 s u
Proof
  strip_tac >> fs[locals_kept_def] >> rpt conj_tac
  >- metis_tac[]
  >- metis_tac[scopes_progress_trans]
  >- (rpt strip_tac >>
      `?e e1. lookup_scopes n es.scopes = SOME e /\
              lookup_scopes n es1.scopes = SOME e1` by
        (gvs[local_region_def] >> metis_tac[optionTheory.option_CASES]) >>
      `e1 = e` by
        (qpat_x_assum `scopes_progress es.scopes _`
           (qspecl_then [`n`,`e`,`e1`] mp_tac o REWRITE_RULE [scopes_progress_def]) >>
         qpat_x_assum `scopes_progress es1.scopes _`
           (qspecl_then [`n`,`e1`,`e`] mp_tac o REWRITE_RULE [scopes_progress_def]) >>
         gvs[] >> rw[] >> gvs[]) >>
      gvs[] >> metis_tac[]) >>
  fs[popped_kept_def] >> rpt strip_tac >>
  qpat_x_assum `!n b sz entry' h. local_region _ es1.scopes _ _ _ _ /\ _ ==> _`
    irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `n` >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!n b sz entry' h. local_region _ es.scopes _ _ _ _ /\ _ ==> _`
        irule >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexists_tac `n` >> fs[])
  >- simp[] >> metis_tac[]
QED

Theorem stack_keep_frame[local]:
  wb_frame cenv es0 esi sa s0 s /\ wb_frame cenv esi mid si s t /\
  ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\ ghost_kept_at lo cenv esi si G tn s G1 tn1 /\
  sa.cs_next_id <= si.cs_next_id /\ sa.cs_next_var <= si.cs_next_var /\
  (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
             local_region cenv esi.scopes s n b sz) ==>
  wb_frame cenv es0 mid sa s0 t /\ ghost_kept_at lo cenv es0 sa G0 tn0 s0 G1 tn1
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at si x` by metis_tac[not_fresh_at_mono] >>
  conj_tac
  >- (fs[wb_frame_def] >> conj_tac
      >- (rpt strip_tac >> `aid < si.cs_next_id` by decide_tac >> metis_tac[]) >>
      irule stack_locals_compose >> qexistsl_tac [`esi`,`s`] >> simp[]) >>
  irule ghost_kept_at_trans >> qexistsl_tac [`G`,`esi`,`s`,`si`,`tn`] >>
  fs[wb_frame_def] >> metis_tac[]
QED
