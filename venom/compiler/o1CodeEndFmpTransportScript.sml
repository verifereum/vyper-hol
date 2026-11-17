Theory o1CodeEndFmpTransport
Ancestors
  o1ContractFmpLowering ctxSealAgree codegenSymRel o1PassContract
  o1ScheduleDecomp o1LabelFlowMiddleFmp o1ComposeSupport unitMemInv
  unitTransformDefs venomPassSchedule venomPassDispatcher o1DretDesugarContract
  venomInst ctxLookupAgreeHelpers contextCodegenRel pair list
  fmpStageCoverage fmpStageCoverInv fmpStageCoverMem fmpStageControl
  fmpStageOpBase fmpStageCoverBack fmpStageRel fmpCoverInvokeIndex
  concretizePtrCoverageStaticMemReachability lowerDloadPtrRawReachable
  ptrStaticDiscipline venomWf venomState finite_map pred_set
  o1LowerDloadRelocationKernel
  ptrDiscipline unitShapeDefs venomExecSemantics passSimulationDefs
  analysisSimDefs pointerConfinedDefs memLocDefs lowerDloadRevertSuffix
  o1ContractSimplifyCfgSrcFrame frameViewFacts o1ScheduleDecompHelpers
  lowerDloadReachability

Theorem fmp_codecopy_source_nonpointer[local]:
  ptr_use_static_ok P pv inst /\ inst.inst_opcode = CODECOPY /\
  inst.inst_operands = [dst; Var x; sz] ==> x NOTIN pv
Proof
  strip_tac >> disch_tac >>
  qpat_x_assum `ptr_use_static_ok _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_use_static_ok_def] >>
  disch_then (CONJUNCTS_THEN2 kall_tac (qspec_then `x` mp_tac)) >>
  simp[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def] >>
  Cases_on `dst = Var x` >> gvs[AllCaseEqs()]
QED

Theorem fmp_codecopy_source_equal[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; Var x; sz] ==>
  eval_operand (Var x) s = eval_operand (Var x) t
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `FDOM G SUBSET fn_pv P fn` by metis_tac[fmp_stage_prov_support] >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    (gvs[EVERY_MEM, fn_static_ptr_ok_def] >> metis_tac[]) >>
  `x NOTIN fn_pv P fn` by metis_tac[fmp_codecopy_source_nonpointer] >>
  `op_prov G (Var x) = NONE` by
    (gvs[op_prov_def, SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  `op_taint tn (Var x) = {}` by
    (gvs[taint_ok_def] >> metis_tac[MEM]) >>
  `~retpc_var fn x` by
    (irule ordinary_operand_not_retpc >> conj_tac
     >- fs[o1_fn_shape_def, fn_shape_ok_def] >>
     qexists_tac `inst` >> simp[]) >>
  `inst.inst_opcode <> PHI /\ MEM (Var x) inst.inst_operands /\
   (!v. Var x = Var v ==> ~retpc_var fn v)` by simp[] >>
  `?w. eval_operand (Var x) s = SOME w` by
    (drule_all fmp_stage_src_defined >>
     Cases_on `lookup_var x s` >> gvs[eval_operand_def]) >>
  drule_all fmp_stage_operand >>
  simp[fmp_value_rel_def] >> strip_tac >>
  metis_tac[ld_value_agree_clean]
QED

(* At a CODECOPY the coverage cursor is past every inserted instruction. *)
Theorem fmp_codecopy_point_inst[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom restored
    stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  active_inst fn' ti t /\ ti.inst_opcode = CODECOPY ==>
  ti = inst
Proof
  strip_tac >> Cases_on `restored` >>
  (drule_all fmp_cov_target_labels >> strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  drule_all fmp_cov_frame_pos >> strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by fs[o1_fn_shape_def, wf_function_def] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
    metis_tac[active_inst_block_lookup] >>
  `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
        get_instruction bt t.vs_inst_idx = SOME ti` by
    metis_tac[active_inst_block_lookup] >>
  qpat_x_assum `!bb. lookup_block _ _ = _ ==> _` drule >> strip_tac >>
  qpat_x_assum `get_instruction bb _ = _` mp_tac >>
  simp[get_instruction_def] >> strip_tac >> gvs[] >>
  Cases_on `((s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn) /\
             t.vs_inst_idx =
               fmp_stage_tidx (fmp_stage_plan infos ctx fn)
                 (fmp_stage_root infos ctx fn) s.vs_current_bb
                 bb.bb_instructions s.vs_inst_idx) \/
            MEM (EL s.vs_inst_idx bb.bb_instructions).inst_opcode
              [DALLOCA; RETPC_PARAM]`
  >- (mp_tac (Q.INST [`i` |-> `t.vs_inst_idx`, `idx` |-> `s.vs_inst_idx`,
                      `lbl` |-> `s.vs_current_bb`] fmp_stage_inserted_at) >>
      impl_tac
      >- (qspecl_then [`fmp_stage_plan infos ctx fn`,
                       `fmp_stage_root infos ctx fn`, `s.vs_current_bb`,
                       `bb.bb_instructions`, `s.vs_inst_idx`] assume_tac
            (Q.GENL [`plan`, `root`, `lbl`, `insts`, `idx`] fmp_cov_tidx_lt) >>
          rw[] >> gvs[]) >>
      gvs[get_instruction_def, fmp_inserted_op_def]) >>
  Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = INVOKE`
  >- (drule_all fmp_stage_invoke_inst >> gvs[get_instruction_def]) >>
  `pre_fmp_opcode (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` by
    fs[pre_fmp_ops_def, EVERY_MEM] >>
  mp_tac (Q.INST [`inst` |-> `EL s.vs_inst_idx bb.bb_instructions`,
                  `idx` |-> `s.vs_inst_idx`, `lbl` |-> `s.vs_current_bb`]
            fmp_stage_kept_inst) >>
  impl_tac >- gvs[] >>
  gvs[get_instruction_def])
QED

Theorem fmp_codecopy_coverage_reflect[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\ ctx_seal_eq C C' /\
  fmp_cov D C C' vs vs' fmp eom stk' fn' t /\ active_inst fn' ti t /\
  ti.inst_opcode = CODECOPY /\ ti.inst_operands = [dst; Var x; sz] /\
  code_end_var fn' x /\ eval_operand (Var x) t = SOME w ==>
  ?fn inst s. raw_reachable vs C fn inst s /\
    inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; Var x; sz] /\
    code_end_var fn x /\ eval_operand (Var x) s = SOME w /\
    s.vs_labels = t.vs_labels
Proof
  rw[fmp_cov_def]
  >- (Cases_on `t.vs_inst_idx = t1.vs_inst_idx`
      >- (`t1 = t` by
            (qpat_x_assum `!k. fmp_target_run _ _ _ _ _ _` (qspec_then `0` mp_tac) >>
             simp[] >> strip_tac >> drule fmp_target_run_zero >> simp[]) >>
          qpat_x_assum `t1 = t` SUBST_ALL_TAC >>
          `ti = inst` by metis_tac[fmp_codecopy_point_inst] >> gvs[] >>
          drule_all fmp_stage_frame_facts >> strip_tac >>
          `lookup_function fn.fn_name C.ctx_functions = SOME fn` by
            (fs[fmp_stage_ctx_def, o1_ctx_shape_def, ctx_wf_def,
                ctx_distinct_fn_names_def, ctx_fn_names_def] >>
             simp[lookup_function_member_iff]) >>
          drule_all ctx_seal_eq_lookup >> strip_tac >> gvs[] >>
          drule fn_seal_eq_fields >> strip_tac >>
          `code_end_var fn x` by metis_tac[code_end_var_same_blocks] >>
          `eval_operand (Var x) s = eval_operand (Var x) t` by
            metis_tac[fmp_codecopy_source_equal] >>
          `s.vs_labels = t.vs_labels` by
            gvs[fmp_stage_rel_def, fmp_frame_rel_def] >>
          `o1_ctx_shape C` by fs[fmp_stage_ctx_def] >>
          qexistsl_tac [`fn`, `inst`, `s`] >>
          metis_tac[ld_frame_reachable_raw]) >>
      drule_all fmp_cov_target_labels >> strip_tac >>
      `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
            get_instruction bt t.vs_inst_idx = SOME ti` by
        metis_tac[active_inst_block_lookup] >>
      qpat_x_assum `!i. _ <= i /\ _ ==> _` (qspec_then `t.vs_inst_idx` mp_tac) >>
      simp[] >> gvs[get_instruction_def, fmp_inserted_op_def]) >>
  `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
        get_instruction bt t.vs_inst_idx = SOME ti` by
    metis_tac[active_inst_block_lookup] >>
  gvs[] >> drule_all ld_revert_pair_suffix_opcode >> simp[]
QED

Theorem fmp_lowering_code_end_relocate:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_pre 3 C C' /\ dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs' /\
  EVERY no_raw_fmp_ops C.ctx_functions /\
  o1_inv D 3 C (vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |>) /\
  fmp_variant_room (SOME fmp) C' vs' /\
  code_end_offset_ok
    (raw_reachable (vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |>)) C ==>
  code_end_offset_ok (raw_reachable vs') C'
Proof
  strip_tac >>
  qabbrev_tac `vraw = vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |>` >>
  `?eom. max_live_eom C = SOME eom` by
    (fs[o1_inv_def, o1_static_inv_def] >> metis_tac[]) >>
  `fmp_stage_ctx rpolicy D C C' vraw vs' fmp eom` by
    fs[fmp_stage_ctx_def, o1_run_state_ok_def, Abbr `vraw`] >>
  `EVERY (\fn. fn.fn_fmp_signature = NONE /\ no_raw_fmp_ops fn)
     C.ctx_functions` by
    (fs[o1_inv_def, o1_static_inv_def, fmp_free_ctx_def, EVERY_MEM] >> metis_tac[]) >>
  `?names. callee_first names C.ctx_functions` by
    (fs[o1_inv_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  drule_all fmp_lowering_stage_sealed >> strip_tac >>
  `ctx_seal_eq C C'` by
    (fs[ctx_seal_eq_def, ctx_pass_stage_def] >>
     irule LIST_REL_mono >> first_x_assum (irule_at Any) >>
     simp[fn_seal_eq_def]) >>
  simp[code_end_offset_ok_def] >> rpt strip_tac >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  `active_inst fn inst vs` by metis_tac[scfg_frame_reachable_active] >>
  drule_all fmp_stage_coverage >> strip_tac >>
  drule_all fmp_codecopy_coverage_reflect >> strip_tac >>
  fs[code_end_offset_ok_def, Abbr `vraw`] >> metis_tac[]
QED

(* Sealing changes signatures only: the active instruction and its state
   are literally unchanged, including the evaluated code_end offset. *)
Theorem code_end_offset_ok_seal_eq[local]:
  ctx_seal_eq C C' ==>
  (code_end_offset_ok (raw_reachable s) C <=>
   code_end_offset_ok (raw_reachable s) C')
Proof
  strip_tac >> simp[code_end_offset_ok_def] >> eq_tac >>
  rpt strip_tac >>
  `ctx_seal_eq C' C` by metis_tac[ctx_seal_eq_sym] >>
  drule_all raw_reachable_seal_eq >> strip_tac >>
  drule fn_seal_eq_fields >> strip_tac >>
  `code_end_var fn' x` by metis_tac[code_end_var_same_blocks] >>
  metis_tac[]
QED

Theorem fmp_lowering_code_end_run_contract:
  o1_stage_contract rpolicy D (EL 3 o1_fn_passes)
    (o1_walk_view rpolicy 3) (o1_pre 3)
    (\C s. o1_inv D 3 C s /\ EVERY no_raw_fmp_ops C.ctx_functions /\
      code_end_offset_ok (raw_reachable s) C)
    (\C s. o1_inv D 4 C s /\ code_end_offset_ok (raw_reachable s) C)
Proof
  simp[o1_stage_contract_def] >> rpt gen_tac >> strip_tac >>
  `EL 3 o1_fn_passes = CFP_Simple VP_FmpLowering` by EVAL_TAC >>
  fs[o1_inv_def, o1_static_inv_def, fmp_free_ctx_def] >>
  rename1 `max_live_eom C = SOME eom` >>
  `EVERY (\fn. fn.fn_fmp_signature = NONE /\ no_raw_fmp_ops fn)
     C.ctx_functions` by fs[EVERY_MEM] >>
  drule_all fmp_lowering_stage_sealed >> strip_tac >>
  `ctx_seal_eq C C'` by
    (fs[ctx_seal_eq_def, ctx_pass_stage_def] >>
     irule LIST_REL_mono >> first_x_assum (irule_at Any) >>
     simp[fn_seal_eq_def]) >>
  `ctx_sim_fuel I D C C' s s` by
    (`ctx_sim_fuel I D C C s s` by
       (irule ctx_sim_refl >> rpt strip_tac >>
        imp_res_tac lookup_function_MEM >>
        imp_res_tac lookup_function_selected_name >>
        fs[o1_ctx_shape_def, EVERY_MEM] >>
        metis_tac[o1_fn_shape_def]) >>
     fs[ctx_sim_fuel_def] >> metis_tac[run_context_seal_eq]) >>
  `max_live_eom C' = max_live_eom C` by
    (irule ctx_pass_stage_max_live_eom >>
     qexistsl_tac [`CFP_Simple VP_FmpLowering`, `rpolicy`, `o1_walk_view rpolicy 3`] >>
     simp[fn_pass_tag_def, fn_pass_static_layout_effect_def]) >>
  `mem_inv (lowered_mem_fact eom) C' s` by
    (irule mem_inv_seal_eq >>
     qexistsl_tac [`C`, `static_mem_ok eom`] >> simp[] >>
     rpt strip_tac >> drule fn_seal_eq_fields >>
     fs[static_mem_ok_def, lowered_mem_fact_def, lowered_mem_ok_def,
        in_revert_forward_def, EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  `EVERY make_ssa_input_ok C'.ctx_functions` by
    (fs[o1_pre_def, EVERY_MEM, o1_fn_row_def] >> metis_tac[]) >>
  drule code_end_offset_ok_seal_eq >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[o1_lowered_inv_def, pass_fuel_def]
QED
