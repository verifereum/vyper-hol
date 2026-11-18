(* The allocation extends the site map above every suspended frame. *)
Theory gasFocusFmpDallocaSaved
Ancestors
  gasFocusFmpCutSites fmpStageRel o1LowerDloadRelocationKernel
  o1PassContract o1SafeUpto lowerDloadPtrRawReachable unitTransformDefs
  venomState venomInst finite_map list pair words

Theorem saved_value_map_extend[local]:
  (!k v. FLOOKUP sm k = SOME v ==> FLOOKUP sm' k = SOME v) /\
  fmp_value_rel sm h m x y ==> fmp_value_rel sm' h m x y
Proof
  Cases_on `h` >- simp[fmp_value_rel_def, ld_value_agree_def] >>
  rename1 `SOME site` >> PairCases_on `site` >>
  simp[fmp_value_rel_def, ld_value_agree_def, FLOOKUP_fmp_ld_sites] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem saved_frame_above_extend[local]:
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tv s t /\
  (!k v. FLOOKUP sm k = SOME v ==>
     FLOOKUP (sm |+ ((b,z),(c,id))) k = SOME v) /\
  w2n s.vs_fmp <= b /\ lo <= c ==>
  fmp_frame_rel (sm |+ ((b,z),(c,id))) fmp0 raw0 eb elo lo
    T fn fn' PG G tv s t
Proof
  simp[fmp_frame_rel_def] >> strip_tac >> gvs[] >>
  qexistsl [`infos`,`ctx`,`runner`] >> simp[] >>
  rpt conj_tac
  >- (simp[fmp_env_rel_def] >> rpt strip_tac >>
      qpat_x_assum `fmp_env_rel _ _ _ _ _ _ _` mp_tac >>
      simp[fmp_env_rel_def] >> disch_then drule >> strip_tac >>
      qexists `y` >> simp[] >> strip_tac >>
      irule saved_value_map_extend >> qexists `sm` >> simp[])
  >- (gvs[fmp_params_rel_def] >> rpt strip_tac >>
      irule saved_value_map_extend >> qexists `sm` >> simp[])
  >- (rpt strip_tac >> gvs[FLOOKUP_UPDATE, AllCaseEqs()] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.NOT_LESS]) >>
  Cases_on `fmp_stage_root infos ctx fn` >> gvs[] >>
  rename1 `fmp_stage_root infos ctx fn = SOME root` >>
  PairCases_on `root` >> gvs[] >>
  conj_tac
  >- (gvs[fmp_frame_covers_def] >> rpt strip_tac >>
      gvs[FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]) >>
  IF_CASES_TAC >> gvs[] >> qexists `regions` >> simp[] >>
  gvs[fmp_ledger_link_def] >> rpt strip_tac >>
  gvs[FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]
QED

Theorem saved_stack_above_extend[local]:
  !stk ts.
    fmp_saved_rel C' sm fmp0 raw0 stk ts /\
    EVERY (\f. w2n f.cf_state.vs_fmp <= b) stk /\
    fmp_frame_lo fmp0 ts <= c /\
    (!k v. FLOOKUP sm k = SOME v ==>
       FLOOKUP (sm |+ ((b,z),(c,id))) k = SOME v) ==>
    fmp_saved_rel C' (sm |+ ((b,z),(c,id))) fmp0 raw0 stk ts
Proof
  Induct >> namedCases_on `ts` ["", "row rest"] >> simp[fmp_saved_rel_def] >>
  PairCases_on `row` >> simp[fmp_saved_rel_def] >> gen_tac >> strip_tac >>
  gvs[EVERY_DEF, fmp_frame_lo_def] >> conj_tac
  >- (irule saved_frame_above_extend >> simp[]) >>
  first_x_assum irule >> simp[] >>
  qpat_x_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[fmp_frame_rel_def] >> rpt strip_tac >> decide_tac
QED

Theorem focus_fmp_dalloca_saved_upto:
  o1_ctx_shape C /\ EVERY (o1_fn_row 3) C.ctx_functions /\
  raw0 = w2n vs.vs_fmp /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
               dalloca_no_wrap inst s) /\
  frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s /\
  inst.inst_opcode = DALLOCA /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts ==>
  fmp_saved_rel C'
    (if z = 0 then sm else sm |+ ((w2n s.vs_fmp,z),(lo,inst.inst_id)))
    fmp0 raw0 stk ts
Proof
  strip_tac >> Cases_on `z = 0` >> simp[]
  >- gvs[fmp_stage_rel_def] >>
  drule_all focus_fmp_frame_sites_upto >> strip_tac >>
  gvs[fmp_stage_rel_def] >> irule saved_stack_above_extend >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> Cases_on `k` >> Cases_on `v` >> strip_tac >>
      simp[FLOOKUP_UPDATE] >> IF_CASES_TAC >> gvs[] >>
      gvs[fmp_sites_ok_def] >>
      qpat_x_assum `!b z c id. FLOOKUP sm _ = _ ==> _` drule >>
      simp[] >> decide_tac) >>
  qpat_x_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[fmp_frame_rel_def] >> rpt strip_tac >> simp[]
QED
