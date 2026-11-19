(* Bounded same-filling safety through the actual pre-walk SimplifyCFG stage. *)
Theory o1SimplifyCfgStageUpto
Ancestors
  o1SimplifyCfgCutFrames o1SimplifyCfgCutTaint o1SimplifyCfgCutMemory
  o1SafeUpto o1ContractSimplifyCfg o1ContractSimplifyCfgSrcStatic
  o1ContractSimplifyCfgSrcFrame o1PassContract unitTransformDefs
  unitMemInv ptrDiscipline simplifyCfgStaticInterface simplifyCfgShapeCore
  simplifyCfgControl simplifyCfgDefs simplifyCfgStruct simplifyCfgProof
  simplifyCfgLabelProps
  simplifyCfgCorrectness simplifyCfgInvariant venomInst venomState list

Theorem simplify_cfg_stage_safe_upto:
  ctx_pass_stage rpolicy (CFP_Simple VP_SimplifyCFG) view C C' /\
  o1_ctx_shape C /\ EVERY simplify_cfg_fn_ok C.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) C.ctx_functions /\
  o1_initial_state_ok vs /\ o1_safe_upto D lo n C vs ==>
  o1_safe_upto D lo n C' vs
Proof
  strip_tac >>
  `C' = C with ctx_functions := MAP simplify_cfg_fn C.ctx_functions` by
    (drule simplify_cfg_stage_functions >> strip_tac >>
     fs[ctx_pass_stage_def, venom_context_component_equality]) >>
  `EVERY scfg_static C.ctx_functions` by
    (fs[o1_ctx_shape_def, EVERY_MEM, scfg_static_def] >>
     metis_tac[o1_fn_shape_def, fn_shape_ok_scfg_shape]) >>
  `scfg_context_trace C C'` by metis_tac[scfg_context_trace_simplify_cfg] >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted` by fs[o1_initial_state_ok_def] >>
  `ctx_has_dalloca C' ==> ctx_has_dalloca C` by
    metis_tac[scfg_simplify_cfg_no_dalloca] >>
  `mem_inv dload_headroom_ok C' vs /\
   (!fn inst s. raw_reachable vs C' fn inst s /\ gas_cut n vs s ==>
     raw_mem_ok C' fn inst s /\ dload_offset_ok C' fn inst s)` by
    (drule_all simplify_cfg_stage_cut_memory >> simp[]) >>
  `EVERY (\fn. fn.fn_eom = NONE) C'.ctx_functions /\
   fmp_free_ctx C' /\ fixed_region_reserved lo C' /\
   (?P. EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn))
          C'.ctx_functions)` by suspend "static" >>
  `taint_within_upto D n C' vs` by
    (irule scfg_context_trace_taint_within_upto >> simp[] >>
     qexists_tac `C` >> fs[o1_safe_upto_def, o1_ptr_safe_upto_def] >>
     metis_tac[]) >>
  `C'.ctx_global_reserved = C.ctx_global_reserved` by simp[] >>
  qpat_x_assum `C' = _` kall_tac >>
  `reserved_intervals_wf C.ctx_global_reserved /\
   ptr_discipline_upto lo n C vs` by
    fs[o1_safe_upto_def, o1_ptr_safe_upto_def] >>
  `lo <= vs.vs_alloca_next` by fs[ptr_discipline_upto_def] >>
  simp[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >>
  conj_tac >- (qexists_tac `P` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all scfg_context_trace_frame_rows_upto >> simp[]
QED

Resume simplify_cfg_stage_safe_upto[static]:
  fs[o1_safe_upto_def, o1_ptr_safe_upto_def] >>
  conj_tac >- (fs[EVERY_MAP, EVERY_MEM] >>
    metis_tac[simplify_cfg_fn_metadata, fn_static_layout_eq_def]) >>
  conj_tac >- suspend "fmp" >>
  conj_tac >- fs[fixed_region_reserved_def] >>
  fs[ptr_discipline_upto_def] >> qexists_tac `P` >>
  simp[EVERY_MAP, EVERY_MEM] >> rpt gen_tac >> strip_tac >>
  irule simplify_cfg_fn_shape_ptr_ok >>
  fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]
QED

Resume simplify_cfg_stage_safe_upto[fmp]:
  fs[fmp_free_ctx_def, EVERY_MAP, EVERY_MEM] >>
  rpt gen_tac >> strip_tac >> gvs[MEM_MAP] >> conj_tac
  >- metis_tac[simplify_cfg_fn_metadata, fn_fmp_convention_eq_def] >>
  simp[pre_fmp_ops_def, simplify_cfg_fn_def] >>
  irule simplify_cfg_fn_with_labels_opcodes >>
  fs[pre_fmp_ops_def, pre_fmp_opcode_def, EVERY_MEM] >> metis_tac[]
QED

Finalise simplify_cfg_stage_safe_upto
