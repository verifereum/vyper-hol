Theory s1PrefixAugAssignScalarTarget
Ancestors
  augAssignFullTargetRoutes s1PrefixFrame s1PrefixNames s1PrefixDefs
  vyperStorageTrace vyperInterpreter vyperPlaceFrames vyperState

Theorem augassign_scalar_target_prefix_entry:
  body_inv tops ctx cenv cx /\ FST nsid = NONE /\
  supported_scalar_target tops nsid ==>
  (?vis ity slot mut.
    supported_variable_decl tops nsid = SOME (vis,mut,ity,SOME slot) /\
    (mut = Storage \/ mut = Transient) /\
    supported_target_info tops bindings (TopLevelNameTarget nsid) =
      SOME (ValPT ity) /\
    ~immutable_root cx (TopLevelNameTarget nsid)) /\
  (!DF lo shadow_ctx func PG st0 es s0 G0 tn0.
    ~s0.vs_halted ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_target_place cx (TopLevelNameTarget nsid)) (es,s0,G0,tn0))
Proof
  strip_tac >> conj_tac
  >- (irule augassign_scalar_target_route >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  irule gas_prefix_full_no_outcome >> simp[evaluate_storage_trace_frame] >>
  Cases_on `nsid` >> rpt gen_tac >>
  simp[Once evaluate_def,bind_def] >> simp[Once evaluate_def] >>
  qmatch_goalsub_abbrev_tac `lookup_global cx src id st` >>
  Cases_on `lookup_global cx src id st` >>
  rename1 `lookup_global cx src id st = (found,st')` >>
  drule lookup_global_no_outcome >> Cases_on `found` >>
  simp[get_place_def,return_def,raise_def,Abbr `st`] >>
  rpt strip_tac >>
  imp_res_tac get_place_state >> gvs[]
QED
