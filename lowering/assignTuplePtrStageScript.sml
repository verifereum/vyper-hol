(* Compiler-facing separation for the optional tuple snapshot. *)
Theory assignTuplePtrStage
Ancestors
  assignTuplePtrAlloc assignTuplePtrStageFrame allocationPtr localPtrsProps
  exprLoweringProps exprSimProps compileEnv venomState venomInst
  venomExecSemantics loweringHalt finite_map valueEncoding

Theorem alloca_step_live_local_separated_ptr:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\ n < dimword(:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  FLOOKUP s1.vs_allocas id = SOME (b,n) ==>
  !name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    w2n w + val_footprint entry.type entry.value <= b \/ b+n <= w2n w
Proof
  strip_tac >>
  `alloca_inv s /\ local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  rpt gen_tac >> strip_tac >>
  `w2n w + sz <= s.vs_alloca_next /\
   type_memory_size entry.type <= sz /\ val_wf entry.type entry.value` by
    (fs[local_ptrs_rel_def] >>
     qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >> gvs[]) >>
  `val_footprint entry.type entry.value <= sz` by
    metis_tac[val_footprint_le, arithmeticTheory.LESS_EQ_TRANS] >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[update_var_def, FLOOKUP_UPDATE] >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[update_var_def] >>
  `local_region cenv es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  drule_at (Pat `MEM _ (fn_insts _)`) local_ptrs_rel_alloca_disjoint >>
  simp[mk_inst_def] >> disch_then drule_all >>
  simp[regions_disjoint_def] >> decide_tac
QED
