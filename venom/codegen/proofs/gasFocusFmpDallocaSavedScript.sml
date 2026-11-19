(* The allocation extends the site map above every suspended frame. *)
Theory gasFocusFmpDallocaSaved
Ancestors fmpStageFmpStepsDallocaSaved[qualified]
  gasFocusFmpCutSites fmpStageRel o1LowerDloadRelocationKernel
  o1PassContract o1SafeUpto lowerDloadPtrRawReachable unitTransformDefs
  venomState venomInst finite_map list pair words

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
  gvs[fmp_stage_rel_def] >> irule fmpStageFmpStepsDallocaSavedTheory.fmp_dalloca_saved_extend >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> Cases_on `k` >> Cases_on `v` >> strip_tac >>
      simp[FLOOKUP_UPDATE] >> IF_CASES_TAC >> gvs[] >>
      gvs[fmp_sites_ok_def] >>
      qpat_x_assum `!b z c id. FLOOKUP sm _ = _ ==> _` drule >>
      simp[] >> decide_tac) >>
  qpat_x_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[fmp_frame_rel_def] >> rpt strip_tac >> simp[]
QED
