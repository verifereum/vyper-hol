(* Old-register metadata boundary for shared reason encoder allocations. *)
Theory reasonAllocationFramePtr
Ancestors allocationPtr bodyPtrDefs loweringHalt ptrDiscipline ptrSafeRun
  compileEnv finite_map words

Theorem reason_alloca_old_metadata:
  !ctx func cenv cx es s id n out s1 PG G tn p.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    p <> out ==>
    FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1) p =
      FLOOKUP G p /\
    op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) (Var p) =
      op_taint tn (Var p)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
      simp[op_taint_def, FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >>
  disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `PG`, `G`, `tn`] strip_assume_tac) >>
  simp[op_taint_def, FLOOKUP_UPDATE]
QED
