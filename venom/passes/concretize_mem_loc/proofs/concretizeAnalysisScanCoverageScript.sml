Theory concretizeAnalysisScanCoverage
Ancestors venomWfProps
  concretizeAnalysisScan concretizeAnalysisOriginCoverage cfgAnalysisProps cfgWf
  removeUnusedSsaProofs venomExecProofs venomInstProps venomWf venomInst
  codegenReadyCompute list pred_set

Theorem bp_scan_insts_intro:
  !order. MEM lbl order /\
    FIND (\bb. bb.bb_label = lbl) fn.fn_blocks = SOME bb /\
    MEM i bb.bb_instructions ==> MEM i (bp_scan_insts fn order)
Proof
  Induct >> simp[bp_scan_insts_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `FIND (\bb. bb.bb_label = h) fn.fn_blocks` >> simp[] >> metis_tac[]
QED

Theorem bp_scan_production_complete:
  wf_function fn /\ all_reachable fn /\ MEM i (fn_insts fn) ==>
  MEM i (bp_scan_insts fn (cfg_analyze fn).cfg_dfs_pre)
Proof
  rpt strip_tac >>
  gvs[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  rename1 `MEM bb fn.fn_blocks` >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (`cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
       (gvs[GSYM fn_reachable_cfg_analyze, all_reachable_def]) >>
     drule cfg_analyze_reachable_sets >>
     simp[EXTENSION] >> metis_tac[]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  irule bp_scan_insts_intro >>
  gvs[lookup_block_def] >> metis_tac[]
QED

Theorem origin_frame_current_production_coverage:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY wf_function ctx.ctx_functions /\
  wf_function fn /\ all_reachable fn /\ ssa_form fn /\
  FLOOKUP om v = SOME (OriginLocal aid,site) ==>
  Allocation aid IN bp_bases
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) v
Proof
  rpt strip_tac >> irule origin_frame_current_base_coverage >>
  metis_tac[bp_scan_production_complete]
QED

Theorem origin_frame_saved_production_coverage:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY wf_function ctx.ctx_functions /\
  n < LENGTH stk /\ wf_function (EL n stk).cf_fn /\
  all_reachable (EL n stk).cf_fn /\ ssa_form (EL n stk).cf_fn /\
  FLOOKUP (EL n oms) v = SOME (OriginLocal aid,site) ==>
  Allocation aid IN bp_bases
    (bp_analyze_fuel (concretize_memloc_fuel (EL n stk).cf_fn)
      (cfg_analyze (EL n stk).cf_fn) (EL n stk).cf_fn) v
Proof
  rpt strip_tac >> irule origin_frame_saved_base_coverage >>
  metis_tac[bp_scan_production_complete]
QED
