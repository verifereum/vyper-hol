(*
 * The O1 source safety up to a gas cut (o1SafeUpto) through the pre-walk
 * and MakeSSA's first run: SimplifyCFG, DretDesugar (the identity), the
 * pruning of unreachable functions, and stage 0.  Each step's output
 * state before the cut corresponds to an input state before it with the
 * same gas readings, so the guarded facts move along the same
 * correspondences the whole-run ones do (o1ContractSimplifyCfg,
 * o1ContractMakeSsa*, o1PipelineCompose's pruning).
 *)
Theory o1PrewalkSafeUpto
Ancestors
  o1SafeUpto o1PipelineCompose o1ComposeSupport o1ContractTheorems
  o1DretDesugarContract o1ContractSimplifyCfg o1ContractSimplifyCfgSrcStatic
  o1ContractMakeSsa o1ContractMakeSsaPtr o1ContractMakeSsaTaint
  o1ContractMakeSsaSrc o1PassContract o1PassLift ptrDiscipline
  ptrDisciplineAgree ctxLookupAgree unitMemInv unitShapeDefs
  unitTransformDefs fcgPruning list

(* ===== Pruning ===== *)

Theorem o1_safe_upto_prune:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  o1_safe_upto D lo n unit.cu_context vs ==>
  o1_safe_upto D lo n (prune_unit_fcg_unreachable unit fcg).cu_context vs
Proof
  strip_tac >>
  `ctx_wf unit.cu_context /\ wf_invoke_targets unit.cu_context` by
    metis_tac[o1_ctx_shape_wf] >>
  drule_all prune_unit_ctx_agree >> strip_tac >>
  `fcg_is_reachable fcg entry` by metis_tac[fcg_analyze_entry_reachable] >>
  `!fn. MEM fn
          (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_functions ==>
        MEM fn unit.cu_context.ctx_functions` by
    simp[MEM_prune_unit_fcg_unreachable_functions] >>
  `mem_inv dload_headroom_ok unit.cu_context vs` by fs[o1_safe_upto_def] >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==>
              raw_mem_ok ctx fn inst s /\ dload_offset_ok ctx fn inst s)
     unit.cu_context vs` by
    (fs[o1_safe_upto_def, mem_inv_raw_reachable] >> metis_tac[]) >>
  `mem_inv dload_headroom_ok
     (prune_unit_fcg_unreachable unit fcg).cu_context vs` by
    (mp_tac (Q.INST [`M` |-> `dload_headroom_ok`] o1_prune_sim) >>
     impl_tac >- (fs[] >> metis_tac[dload_headroom_ok_prune]) >>
     strip_tac >> pop_assum irule >> simp[]) >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==>
              raw_mem_ok ctx fn inst s /\ dload_offset_ok ctx fn inst s)
     (prune_unit_fcg_unreachable unit fcg).cu_context vs` by
    (mp_tac (Q.INST [`M` |-> `\ctx fn inst s. gas_cut n vs s ==>
               raw_mem_ok ctx fn inst s /\ dload_offset_ok ctx fn inst s`]
               o1_prune_sim) >>
     impl_tac
     >- (fs[] >> metis_tac[raw_mem_ok_ctx_free, dload_offset_ok_ctx_free]) >>
     strip_tac >> pop_assum irule >> simp[]) >>
  `ptr_discipline_upto lo n
     (prune_unit_fcg_unreachable unit fcg).cu_context vs` by
    (irule ptr_discipline_upto_ctx_agree >>
     simp[prune_unit_fcg_unreachable_fields] >>
     qexistsl_tac [`fcg_is_reachable fcg`, `unit.cu_context`] >>
     gvs[o1_safe_upto_def, o1_ptr_safe_upto_def]) >>
  `taint_within_upto D n
     (prune_unit_fcg_unreachable unit fcg).cu_context vs` by
    (irule taint_within_upto_ctx_agree >>
     simp[prune_unit_fcg_unreachable_fields] >>
     qexistsl_tac [`fcg_is_reachable fcg`, `unit.cu_context`] >>
     gvs[o1_safe_upto_def, o1_ptr_safe_upto_def]) >>
  qpat_x_assum `fcg = _` kall_tac >>
  `fmp_free_ctx (prune_unit_fcg_unreachable unit fcg).cu_context` by
    (irule fmp_free_ctx_prune >> fs[o1_safe_upto_def, o1_ptr_safe_upto_def]) >>
  `~ctx_has_dalloca (prune_unit_fcg_unreachable unit fcg).cu_context` by
    (fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ctx_has_dalloca_def,
        EXISTS_MEM] >> metis_tac[]) >>
  fs[o1_safe_upto_def, o1_ptr_safe_upto_def, mem_inv_raw_reachable] >>
  fs[EVERY_MEM, fixed_region_reserved_def, prune_unit_fcg_unreachable_fields]
QED

(* ===== SimplifyCFG ===== *)

(* The guarded raw memory fact moves through a stage like the whole one:
   mem_corr keeps the gas readings. *)
Theorem raw_mem_ok_upto_closed[local]:
  mem_corr_closed_rf
    (\ctx fn inst s. gas_cut n vs s ==> raw_mem_ok ctx fn inst s)
Proof
  `mem_corr_closed_rf (\ctx fn inst s.
     (\r. LENGTH vs.vs_gas_readings < n + LENGTH r) s.vs_gas_readings ==>
     raw_mem_ok ctx fn inst s)` by
    (irule mem_corr_closed_rf_readings_guard >>
     simp[mem_corr_closed_rf_raw_mem_ok]) >>
  fs[gas_cut_def]
QED

Theorem simplify_cfg_stage_safe_upto:
  ctx_pass_stage rpolicy (CFP_Simple VP_SimplifyCFG) view C C' /\
  o1_ctx_shape C /\ EVERY simplify_cfg_fn_ok C.ctx_functions /\
  EVERY (\fn. EVERY (\inst. inst.inst_opcode <> PHI) (fn_insts fn))
    C.ctx_functions /\
  o1_run_state_ok vs /\ o1_safe_upto D lo n C vs ==>
  o1_safe_upto D lo n C' vs
Proof
  rewrite_tac[o1_safe_upto_def, o1_ptr_safe_upto_def] >> strip_tac >>
  `C'.ctx_functions = MAP simplify_cfg_fn C.ctx_functions` by
    metis_tac[simplify_cfg_stage_functions] >>
  `C'.ctx_global_reserved = C.ctx_global_reserved` by
    fs[ctx_pass_stage_def] >>
  `EVERY (\fn. fn.fn_eom = NONE) C'.ctx_functions /\
   ~ctx_has_dalloca C' /\ fmp_free_ctx C' /\
   (!lo. fixed_region_reserved lo C ==> fixed_region_reserved lo C')` by
    (irule simplify_cfg_ctx_static_rows >> simp[]) >>
  `!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
     dload_offset_ok C fn inst s` by metis_tac[] >>
  drule_all simplify_cfg_stage_src_frame_upto >> strip_tac >>
  drule_all simplify_cfg_stage_headroom >> strip_tac >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==> raw_mem_ok ctx fn inst s)
     C vs` by
    (fs[mem_inv_raw_reachable] >> metis_tac[]) >>
  assume_tac raw_mem_ok_upto_closed >>
  drule_all simplify_cfg_stage_mem_inv_rf >> strip_tac >>
  `ptr_discipline_upto lo n C' vs` by
    (qpat_x_assum `ptr_discipline_upto lo n C vs` mp_tac >>
     rewrite_tac[ptr_discipline_upto_def] >> strip_tac >>
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (qexists_tac `P` >> asm_rewrite_tac[] >>
         simp[EVERY_MAP, EVERY_MEM] >> gen_tac >> strip_tac >>
         irule simplify_cfg_fn_shape_ptr_ok >>
         fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
     first_assum ACCEPT_TAC) >>
  `fixed_region_reserved lo C'` by metis_tac[] >>
  `!fn inst s. raw_reachable vs C' fn inst s /\ gas_cut n vs s ==>
     raw_mem_ok C' fn inst s` by
    (qpat_x_assum `mem_inv (\ctx fn inst s. gas_cut n vs s ==>
                     raw_mem_ok ctx fn inst s) C' vs` mp_tac >>
     simp[mem_inv_raw_reachable]) >>
  simp[]
QED

(* ===== MakeSSA's first run ===== *)

Theorem make_ssa_stage_safe_upto:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY make_ssa_input_ok C.ctx_functions /\
  callee_first names C.ctx_functions /\
  o1_safe_upto D lo n C vs ==>
  o1_safe_upto D lo n C' vs
Proof
  rewrite_tac[o1_safe_upto_def, o1_ptr_safe_upto_def] >> strip_tac >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted` by
    fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `C'.ctx_global_reserved = C.ctx_global_reserved` by
    fs[ctx_pass_stage_def] >>
  `!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
     dload_offset_ok C fn inst s` by metis_tac[] >>
  drule_all make_ssa_stage_src_rows_upto >> strip_tac >>
  `ptr_discipline_upto lo n C' vs` by
    (irule make_ssa_stage_ptr_upto >> metis_tac[]) >>
  `taint_within_upto D n C' vs` by
    (irule make_ssa_stage_taint_upto >> metis_tac[]) >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==> raw_mem_ok ctx fn inst s)
     C vs` by
    (fs[mem_inv_raw_reachable] >> metis_tac[]) >>
  assume_tac raw_mem_ok_upto_closed >>
  drule_all make_ssa_stage_mem_inv >> strip_tac >>
  `fixed_region_reserved lo C'` by fs[fixed_region_reserved_def] >>
  `!fn inst s. raw_reachable vs C' fn inst s /\ gas_cut n vs s ==>
     raw_mem_ok C' fn inst s` by
    (qpat_x_assum `mem_inv (\ctx fn inst s. gas_cut n vs s ==>
                     raw_mem_ok ctx fn inst s) C' vs` mp_tac >>
     simp[mem_inv_raw_reachable]) >>
  simp[]
QED

(* ===== The walk's input ===== *)

(* The pre-walk (SimplifyCFG, then DretDesugar, the identity) and the
   pruning keep the guarded source safety. *)
Theorem o1_walk_input_safe_upto:
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit s =
    SOME (pre, t) /\
  o1_ctx_shape unit.cu_context /\ ALL_DISTINCT (unit_label_namespace unit) /\
  ir_supply_inst_ok s /\ o1_source_unit_ok unit /\ unit_defs_reach_uses unit /\
  pre.cu_context.ctx_entry = SOME entry /\
  o1_run_state_ok vs /\ o1_safe_upto D lo n unit.cu_context vs ==>
  o1_safe_upto D lo n
    (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs
Proof
  strip_tac >> drule o1_pre_walk_runs >>
  disch_then (qx_choosel_then [`mid`, `t0`] strip_assume_tac) >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_SimplifyCFG`,
                  `u` |-> `unit`, `u'` |-> `mid`, `s'` |-> `t0`]
            mapped_pass_stage) >>
  impl_tac >- simp[o1_contract_simplify_cfg_pre_walk] >> strip_tac >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_DretDesugar`,
                  `u` |-> `mid`, `s` |-> `t0`, `u'` |-> `pre`, `s'` |-> `t`]
            mapped_pass_stage) >>
  impl_tac
  >- simp[o1_contract_dret_desugar_pre_walk, unit_labels_wf_namespace] >>
  strip_tac >>
  `pre.cu_context = mid.cu_context` by
    metis_tac[dret_desugar_stage_identity] >>
  `EVERY (\fn. EVERY (\inst. inst.inst_opcode <> PHI) (fn_insts fn))
     unit.cu_context.ctx_functions` by
    (fs[o1_source_unit_ok_def, EVERY_MEM] >> rpt strip_tac >>
     res_tac >> gvs[raw_opcode_ok_def]) >>
  `EVERY simplify_cfg_fn_ok unit.cu_context.ctx_functions` by
    (fs[o1_ctx_shape_def, unit_defs_reach_uses_def, EVERY_MEM] >>
     rpt strip_tac >> irule simplify_cfg_fn_ok_no_phi >>
     simp[EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  `o1_safe_upto D lo n mid.cu_context vs` by
    (irule simplify_cfg_stage_safe_upto >> metis_tac[]) >>
  irule o1_safe_upto_prune >> gvs[]
QED
