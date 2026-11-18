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
  fmpLowerDefs fmpStepOpaque fmpStepLayout fmpStepRewriteOrigin
  fmpStepReclaim fmpLowerProps fmpStageControlWalk fmpLowerIndexedProps irSupply
  fmpStepSupply fmpStepRetpcShape venomFnInstsProofs venomFnScheduleRunner
  fmpStageOpBaseActual venomExecProofs

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

Theorem fmp_lower_inst_protected[local]:
  fmp_lower_inst infos ctx runner s i = SOME (out,s') /\
  pre_fmp_opcode i.inst_opcode /\ MEM x s.irs_used_vars /\ x <> runner /\
  (MEM x i.inst_outputs ==> i = d) /\ d.inst_opcode = ADD /\
  (MEM (Var x) i.inst_operands ==> i.inst_opcode = CODECOPY) /\
  MEM j out /\ (MEM x j.inst_outputs \/ MEM (Var x) j.inst_operands) ==>
  j = i
Proof
  strip_tac
  >- (Cases_on `i.inst_opcode = DALLOCA`
      >- (gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def] >>
          imp_res_tac fresh_ir_var_contract >> gvs[] >> metis_tac[MEM]) >>
      Cases_on `i.inst_opcode = INVOKE`
      >- (gvs[fmp_lower_inst_def, AllCaseEqs(), MEM_APPEND] >>
          BasicProvers.EVERY_CASE_TAC >> fs[]) >>
      gvs[fmp_lower_inst_def, pre_fmp_opcode_def, AllCaseEqs()]) >>
  drule_all fmp_lower_inst_var_operand_origin >> strip_tac >> gvs[] >>
  gvs[fmp_lower_inst_def, AllCaseEqs()]
QED

Theorem fmp_lower_indexed_protected[local]:
  fmp_lower_indexed infos ctx runner lbl k s restores is = SOME (out,left,s') /\
  MEM x s.irs_used_vars /\ x <> runner /\ d.inst_opcode = ADD /\
  (!pt. ~MEM (pt,x) restores) /\
  (!i. MEM i is ==> pre_fmp_opcode i.inst_opcode /\
    (MEM x i.inst_outputs ==> i = d) /\
    (MEM (Var x) i.inst_operands ==> i.inst_opcode = CODECOPY)) ==>
  !j. MEM j out /\ (MEM x j.inst_outputs \/ MEM (Var x) j.inst_operands) ==> MEM j is
Proof
  map_every qid_spec_tac [`s'`, `left`, `out`, `restores`, `s`, `k`] >>
  Induct_on `is` >- simp[fmp_lower_indexed_def] >>
  simp[fmp_lower_indexed_cons] >> rpt gen_tac >> strip_tac >>
  drule fmp_control_emit_vars_mono >> strip_tac >>
  drule fmp_control_inst_vars_mono >> strip_tac >>
  `!pt. ~MEM (pt,x) later` by
    metis_tac[fmp_select_point_restores_once] >>
  `~MEM x bases` by metis_tac[fmp_select_point_restores_once] >>
  gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  Cases_on `MEM j prefix`
  >- (drule_all fmp_emit_restores_assign_origin >> strip_tac >>
      qpat_x_assum `j = mk_inst _ _ _ _` SUBST_ALL_TAC >>
      qpat_x_assum `MEM x (mk_inst _ _ _ _).inst_outputs \/ _` mp_tac >>
      PURE_REWRITE_TAC
        [mk_inst_def, instruction_accessors, instruction_accfupds, combinTheory.K_THM,
         MEM, operand_11, OR_CLAUSES] >>
      disch_then (DISJ_CASES_THEN SUBST_ALL_TAC) >> gvs[]) >>
  Cases_on `MEM j head`
  >- (`j = h` by (irule fmp_lower_inst_protected >> metis_tac[]) >> simp[]) >>
  `MEM j tail` by gvs[MEM_APPEND] >>
  `MEM x s1.irs_used_vars` by metis_tac[] >>
  qpat_x_assum `!k s rs out left s'. _`
    (qspecl_then [`SUC k`, `s1`, `later`, `tail`, `left`, `s'`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qspec_then `j` mp_tac) >> simp[]
QED

Theorem fmp_lower_blocks_protected[local]:
  fmp_lower_blocks infos ctx runner s restores bs = SOME (FmpBlocksResult out left s') /\
  MEM x s.irs_used_vars /\ x <> runner /\ d.inst_opcode = ADD /\
  (!pt. ~MEM (pt,x) restores) /\
  (!i. MEM i (fn_insts_blocks bs) ==> pre_fmp_opcode i.inst_opcode /\
    (MEM x i.inst_outputs ==> i = d) /\
    (MEM (Var x) i.inst_operands ==> i.inst_opcode = CODECOPY)) ==>
  !j. MEM j (fn_insts_blocks out) /\ (MEM x j.inst_outputs \/ MEM (Var x) j.inst_operands) ==>
      MEM j (fn_insts_blocks bs)
Proof
  map_every qid_spec_tac [`s'`, `left`, `out`, `restores`, `s`] >>
  Induct_on `bs` >- simp[fmp_lower_blocks_def, fn_insts_blocks_def] >>
  simp[fmp_lower_blocks_def, AllCaseEqs(), fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule (REWRITE_RULE [Once (GSYM AND_IMP_INTRO)] fmp_lower_indexed_protected) >>
  disch_then (qspecl_then [`x`, `d`] assume_tac) >>
  drule fmp_control_indexed_vars_mono >> strip_tac >>
  drule fmp_lower_indexed_leftover >> strip_tac >>
  qpat_x_assum `!s rs out left s'. _`
    (qspecl_then [`s2`, `later`, `tail`, `left`, `s'`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[fn_insts_blocks_def, MEM_APPEND] >> metis_tac[]
QED

Theorem fmp_lowered_protected_origin[local]:
  fmp_stage_lowered infos ctx runner f g /\
  pre_fmp_ops f /\ MEM d (fn_insts f) /\ MEM x d.inst_outputs /\ d.inst_opcode = ADD /\
  (!i. MEM i (fn_insts f) /\ MEM x i.inst_outputs ==> i = d) /\
  (!i. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands ==> i.inst_opcode = CODECOPY) /\
  MEM j (fn_insts g) /\ (MEM x j.inst_outputs \/ MEM (Var x) j.inst_operands) ==>
  MEM j (fn_insts f)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `fmp_stage_lowered _ _ _ _ _` mp_tac >>
  simp[fmp_stage_lowered_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule fmp_checked_seal_some >> strip_tac >> gvs[fmp_seal_def, fn_insts_def] >>
  Cases_on `root_layout` >> gvs[] >>
  `MEM x (fn_ir_vars f)` by
    (fs[fn_ir_vars_member, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `MEM x sp.irs_used_vars` by
    (fs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >> metis_tac[]) >>
  drule fresh_ir_var_contract >> strip_tac >>
  drule fmp_make_root_layout_used_vars >> strip_tac >>
  `x <> runner` by metis_tac[] >>
  `!point. ~MEM (point,x) (fmp_plan_to_alist f plan)` by
    (rpt strip_tac >>
     `FLOOKUP plan point = SOME x` by metis_tac[MEM_fmp_plan_to_alist] >>
     drule_all analyze_fmp_reclaims_output >> strip_tac >>
     fs[fn_insts_def] >>
     `inst = d` by metis_tac[] >> gvs[]) >>
  `!j. MEM j (fn_insts_blocks blocks) /\
       (MEM x j.inst_outputs \/ MEM (Var x) j.inst_operands) ==>
       MEM j (fn_insts_blocks f.fn_blocks)` by
    (drule (REWRITE_RULE [Once (GSYM AND_IMP_INTRO)] fmp_lower_blocks_protected) >>
     disch_then (qspecl_then [`x`, `d`] mp_tac) >>
     fs[pre_fmp_ops_def, fn_insts_def, EVERY_MEM] >> metis_tac[]) >>
  `?users oldpc suffix. split_fmp_entry f = SOME (FmpEntryLayout users oldpc suffix)` by
    (qpat_assum `fmp_make_root_layout _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  `!i. MEM i (OPTION_TO_LIST oldpc) ==>
       MEM i (fn_insts_blocks f.fn_blocks) /\ i.inst_opcode = RETPC_PARAM` by
    (drule split_fmp_entry_reconstruct >> strip_tac >>
     Cases_on `oldpc` >>
     fs[callLayoutDefsTheory.OPTION_TO_LIST_def, fn_insts_blocks_MEM] >>
     metis_tac[MEM, MEM_APPEND, split_fmp_entry_retpc_opcode]) >>
  `!i. MEM i (OPTION_TO_LIST oldpc) ==>
       ~MEM x i.inst_outputs /\ ~MEM (Var x) i.inst_operands` by
    (qx_gen_tac `old` >> strip_tac >>
     qpat_assum `!i. MEM i (OPTION_TO_LIST oldpc) ==> _` drule >> strip_tac >>
     conj_tac >> strip_tac
     >- (`old = d` by metis_tac[] >> gvs[]) >>
     `old.inst_opcode = CODECOPY` by metis_tac[] >> gvs[]) >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> fs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  qpat_x_assum `blocks = entry::rest` SUBST_ALL_TAC >>
  drule_all fmp_make_root_layout_opaque_shape >> strip_tac >>
  drule fmp_make_root_layout_runner_outputs >> strip_tac >>
  drule_all (SRULE [fn_insts_def] fmp_install_root_instruction_origin) >> strip_tac
  >- (fs[] >> metis_tac[]) >>
  (Cases_on `MEM (Var x) j.inst_operands`
   >- metis_tac[fmp_make_root_layout_operand_origin] >>
   metis_tac[MEM, fmp_optional_outputs_origin])
QED

Theorem fmp_code_end_adjacent[local]:
  fmp_stage_lowered infos ctx runner f g /\
  (fn_is_context_entry ctx f ==> entry_fn_no_params f) /\
  lookup_block lbl f.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ d::j::post /\
  d.inst_opcode = ADD /\ j.inst_opcode = CODECOPY ==>
  ?bg a b. lookup_block lbl g.fn_blocks = SOME bg /\
           bg.bb_instructions = a ++ d::j::b
Proof
  strip_tac >>
  qabbrev_tac `p = LENGTH pre` >>
  `SUC p < LENGTH bb.bb_instructions /\ p < LENGTH bb.bb_instructions /\
   EL p bb.bb_instructions = d /\ EL (SUC p) bb.bb_instructions = j` by
    (simp[Abbr `p`, EL_APPEND_EQN] >> decide_tac) >>
  `!k. k = p \/ k = SUC p ==>
    (EL k bb.bb_instructions).inst_opcode = ADD \/
    (EL k bb.bb_instructions).inst_opcode = CODECOPY` by
    (rpt strip_tac >> gvs[]) >>
  `!k. k = p \/ k = SUC p ==> (lbl,k) NOTIN FDOM (fmp_stage_plan infos ctx f)` by
    (rpt strip_tac >> drule_all fmp_stage_plan_point >> strip_tac >>
     drule fmp_reclaim_point_opcodes >> strip_tac >>
     qpat_assum `!k. k = p \/ k = SUC p ==> _` (qspec_then `k` mp_tac) >>
     impl_tac >- simp[] >> fs[]) >>
  `!rl rp. fmp_stage_root infos ctx f = SOME (rl,rp) /\ lbl = rl ==> rp <> SUC p` by
    (rpt strip_tac >>
     mp_tac (Q.INST [`idx` |-> `p`, `rp` |-> `SUC p`, `rl` |-> `lbl`,
                    `fn` |-> `f`, `fn'` |-> `g`]
       fmp_stage_root_crossing) >>
     impl_tac >- metis_tac[] >> fs[]) >>
  `fmp_stage_tidx (fmp_stage_plan infos ctx f) (fmp_stage_root infos ctx f)
      lbl bb.bb_instructions (SUC p) =
    SUC (fmp_stage_tidx (fmp_stage_plan infos ctx f) (fmp_stage_root infos ctx f)
      lbl bb.bb_instructions p)` by
    (irule fmp_stage_tidx_suc >> simp[] >> metis_tac[]) >>
  map_every (fn (i,idx) =>
    mp_tac (Q.INST [`inst` |-> i, `idx` |-> idx, `fn` |-> `f`,
                    `fn'` |-> `g`] fmp_stage_kept_inst) >>
    impl_tac >- gvs[pre_fmp_opcode_def] >> strip_tac)
      [(`d`, `p`), (`j`, `SUC p`)] >>
  gvs[] >>
  qabbrev_tac `k = fmp_stage_tidx (fmp_stage_plan infos ctx f)
      (fmp_stage_root infos ctx f) lbl (pre ++ [d;j] ++ post) p` >>
  qexistsl_tac [`TAKE k bb'.bb_instructions`, `DROP (SUC (SUC k)) bb'.bb_instructions`] >>
  qpat_x_assum `EL k bb'.bb_instructions = d` (SUBST1_TAC o SYM) >>
  qpat_x_assum `EL (SUC k) bb'.bb_instructions = j` (SUBST1_TAC o SYM) >>
  `k < LENGTH bb'.bb_instructions` by decide_tac >>
  `DROP k bb'.bb_instructions =
    EL k bb'.bb_instructions :: EL (SUC k) bb'.bb_instructions ::
      DROP (SUC (SUC k)) bb'.bb_instructions` by metis_tac[rich_listTheory.DROP_CONS_EL] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> metis_tac[TAKE_DROP]
QED

(* No inserted ADD seeds a code-end variable. A restore reads a DALLOCA
   output, which cannot have a code-end definition in the source SSA. *)
Theorem fmp_code_end_inst_origin[local]:
  fmp_stage_lowered infos ctx runner f g /\ pre_fmp_ops f /\ ssa_form f /\
  MEM j (fn_insts g) /\
  ((j.inst_opcode = ADD /\ ?op. j.inst_operands = [op; Label "code_end"]) \/
   (j.inst_opcode = ASSIGN /\ ?y. j.inst_operands = [Var y] /\ code_end_var f y)) ==>
  MEM j (fn_insts f)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `fmp_stage_lowered _ _ _ _ _` mp_tac >>
  simp[fmp_stage_lowered_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule fmp_checked_seal_some >> strip_tac >> gvs[fmp_seal_def, fn_insts_def] >>
  Cases_on `root_layout` >> gvs[] >>
  `?users oldpc suffix. split_fmp_entry f = SOME (FmpEntryLayout users oldpc suffix)` by
    (qpat_assum `fmp_make_root_layout _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> fs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  qpat_x_assum `blocks = entry::rest` SUBST_ALL_TAC >>
  drule_all fmp_make_root_layout_opaque_shape >> strip_tac >>
  `MEM j (fn_insts (f with fn_blocks := entry::rest))` by
    (drule_all (SRULE [fn_insts_def] fmp_install_root_instruction_origin) >>
     strip_tac >> fs[fn_insts_def] >>
     qpat_x_assum `!i. MEM i _ ==> i.inst_opcode = _ \/ _`
       (qspec_then `j` mp_tac) >>
     qpat_x_assum `!i. MEM i _ ==> i.inst_opcode = RETPC_PARAM`
       (qspec_then `j` mp_tac) >> simp[]) >>
  fs[fn_insts_def] >>
  qpat_x_assum `MEM j (fn_insts_blocks (entry::rest))` mp_tac >>
  pure_rewrite_tac[fn_insts_blocks_MEM] >>
  strip_tac >> drule_all fmp_lower_blocks_origin >> strip_tac >>
  TRY (rename1 `fmp_lower_inst _ _ _ _ src_inst = SOME _` >>
       `pre_fmp_opcode src_inst.inst_opcode` by
         (fs[pre_fmp_ops_def, fn_insts_def, fn_insts_blocks_MEM, EVERY_MEM] >>
          metis_tac[]) >>
       gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def, pre_fmp_opcode_def] >>
       metis_tac[]) >>
  gvs[mk_inst_def] >>
  rename1 `MEM (restore_point,restore_base) (fmp_plan_to_alist f plan)` >>
  `FLOOKUP plan restore_point = SOME restore_base` by metis_tac[MEM_fmp_plan_to_alist] >>
  drule_all analyze_fmp_reclaims_output >> strip_tac >>
  drule_all code_end_var_def_inst >> simp[]
QED

Theorem fmp_code_end_var_backward[local]:
  !g x. code_end_var g x ==> !infos ctx runner f.
    fmp_stage_lowered infos ctx runner f g /\ pre_fmp_ops f /\ ssa_form f ==>
    code_end_var f x
Proof
  Induct_on `code_end_var` >> rpt strip_tac
  >- (`MEM inst (fn_insts f)` by
        (irule fmp_code_end_inst_origin >> metis_tac[]) >>
      metis_tac[code_end_var_rules]) >>
  rename1 `inst.inst_operands = [Var y]` >>
  `code_end_var f y` by metis_tac[] >>
  `MEM inst (fn_insts f)` by
    (irule fmp_code_end_inst_origin >> metis_tac[]) >>
  metis_tac[code_end_var_rules]
QED

Theorem fmp_lowered_protected_lifetime[local]:
  fmp_stage_lowered infos ctx runner f g /\
  (fn_is_context_entry ctx f ==> entry_fn_no_params f) /\
  wf_function f /\ fn_inst_ids_distinct g /\ pre_fmp_ops f /\ ssa_form f /\
  (!x. code_end_var f x ==>
    ?d op. MEM d (fn_insts f) /\ d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
      (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
        MEM (Var x) j.inst_operands ==>
        j.inst_opcode = CODECOPY /\
        (?dst sz. j.inst_operands = [dst; Var x; sz] /\
          dst <> Var x /\ sz <> Var x) /\
        ?pre post. bb.bb_instructions = pre ++ d::j::post)) ==>
  !x. code_end_var g x ==>
    ?d op. MEM d (fn_insts g) /\ d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts g) /\ MEM x k.inst_outputs ==> k = d) /\
      (!bb j. MEM bb g.fn_blocks /\ MEM j bb.bb_instructions /\
        MEM (Var x) j.inst_operands ==>
        j.inst_opcode = CODECOPY /\
        (?dst sz. j.inst_operands = [dst; Var x; sz] /\
          dst <> Var x /\ sz <> Var x) /\
        ?pre post. bb.bb_instructions = pre ++ d::j::post)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `code_end_var f x` by
    (drule fmp_code_end_var_backward >>
     disch_then (qspecl_then [`infos`, `ctx`, `runner`, `f`] mp_tac) >> simp[]) >>
  qpat_x_assum `!x. code_end_var f x ==> _` drule >> strip_tac >>
  `!i. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = CODECOPY` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `!j. MEM j (fn_insts g) /\ (MEM x j.inst_outputs \/ MEM (Var x) j.inst_operands) ==>
    MEM j (fn_insts f)` by
    (gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     mp_tac (Q.INST [`f` |-> `f`, `g` |-> `g`, `d` |-> `d`,
       `x` |-> `x`, `j` |-> `j`, `infos` |-> `infos`, `ctx` |-> `ctx`,
       `runner` |-> `runner`] fmp_lowered_protected_origin) >> simp[]) >>
  qexistsl_tac [`d`, `op`] >> simp[] >> rpt conj_tac
  >- (qpat_assum `MEM d (fn_insts f)` (mp_tac o REWRITE_RULE [fn_insts_def, fn_insts_blocks_MEM]) >>
      strip_tac >> rename1 `MEM d b.bb_instructions` >>
      `lookup_block b.bb_label f.fn_blocks = SOME b` by
        (metis_tac[wf_lookup_block]) >>
      `?i. i < LENGTH b.bb_instructions /\ d = EL i b.bb_instructions` by
        metis_tac[MEM_EL] >>
      `pre_fmp_opcode d.inst_opcode /\ ~MEM d.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by
        simp[pre_fmp_opcode_def] >>
      drule_all fmp_stage_kept_inst >> strip_tac >>
      simp[fn_insts_def, fn_insts_blocks_MEM] >>
      metis_tac[EL_MEM, lookup_block_MEM]) >>
  rpt gen_tac >> strip_tac >>
  `MEM j (fn_insts g)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `MEM j (fn_insts f)` by metis_tac[] >>
  qpat_x_assum `MEM j (fn_insts f)`
    (qx_choose_then `src` strip_assume_tac o REWRITE_RULE [fn_insts_def, fn_insts_blocks_MEM]) >>
  `lookup_block src.bb_label f.fn_blocks = SOME src` by
    (metis_tac[wf_lookup_block]) >>
  qpat_assum `!bb j. _ ==> j.inst_opcode = CODECOPY /\ _`
    (qspecl_then [`src`, `j`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all fmp_code_end_adjacent >> strip_tac >>
  `MEM bg g.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM j bg.bb_instructions` by simp[] >>
  `bb = bg` by metis_tac[inst_in_unique_block] >>
  fs[APPEND] >> metis_tac[]
QED

Theorem fmp_stage_protected_lifetime_static:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\ o1_ctx_shape C' /\
  EVERY (\f. !x. code_end_var f x ==>
    ?d op. MEM d (fn_insts f) /\ d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
      (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
        MEM (Var x) j.inst_operands ==>
        j.inst_opcode = CODECOPY /\
        (?dst sz. j.inst_operands = [dst; Var x; sz] /\
          dst <> Var x /\ sz <> Var x) /\
        ?pre post. bb.bb_instructions = pre ++ d::j::post)) C.ctx_functions ==>
  EVERY (\f. !x. code_end_var f x ==>
    ?d op. MEM d (fn_insts f) /\ d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
      (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
        MEM (Var x) j.inst_operands ==>
        j.inst_opcode = CODECOPY /\
        (?dst sz. j.inst_operands = [dst; Var x; sz] /\
          dst <> Var x /\ sz <> Var x) /\
        ?pre post. bb.bb_instructions = pre ++ d::j::post)) C'.ctx_functions
Proof
  strip_tac >>
  `o1_ctx_shape C /\ o1_inv D 3 C vs /\
   ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering) (o1_walk_view rpolicy 3) C C'` by
    fs[fmp_stage_ctx_def] >>
  gs[EVERY_MEM] >> gen_tac >> strip_tac >>
  rename1 `MEM g C'.ctx_functions` >>
  `lookup_function g.fn_name C'.ctx_functions = SOME g` by
    (irule fmp_lookup_function_self >>
     fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  qpat_assum `ctx_pass_stage _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ctx_pass_stage_def]) >>
  drule_all LIST_REL_MEM_IMP_R >> strip_tac >>
  rename1 `MEM f C.ctx_functions` >>
  `f.fn_name = g.fn_name` by (fs[fn_pass_step_def] >> metis_tac[]) >>
  `o1_fn_shape C f /\ o1_fn_shape C' g` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `lookup_function f.fn_name C'.ctx_functions = SOME g` by simp[] >>
  drule_all fmp_stage_actual_witness >> strip_tac >>
  `ssa_form f` by fs[o1_inv_def, EVERY_MEM] >>
  `(fn_is_context_entry ctx0 f ==> entry_fn_no_params f) /\
   wf_function f /\ fn_inst_ids_distinct g` by fs[o1_fn_shape_def, wf_function_def] >>
  mp_tac (Q.INST [`f` |-> `f`, `g` |-> `g`, `ctx` |-> `ctx0`,
    `infos` |-> `infos0`, `runner` |-> `runner0`] fmp_lowered_protected_lifetime) >>
  simp[] >>
  qpat_assum `!f. MEM f C.ctx_functions ==> _` (qspec_then `f` mp_tac) >>
  simp[]
QED

Theorem fmp_codecopy_coverage_reflect[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
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
          drule_all fmp_stage_actual_witness >> strip_tac >>
          `code_end_var fn x` by
            (drule fmp_code_end_var_backward >>
             disch_then (qspecl_then [`infos0`, `ctx0`, `runner0`, `fn`] mp_tac) >> simp[]) >>
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

Theorem fmp_lowering_code_end_relocate_static:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_pre 3 C C' /\ dead_wf D /\ o1_ctx_shape C /\
  o1_initial_state_ok vs' /\ vs'.vs_fmp = vs'.vs_initial_fmp /\
  code_layout_valid vs' /\
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
    fs[fmp_stage_ctx_def, Abbr `vraw`] >>
  simp[code_end_offset_ok_def] >> rpt strip_tac >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  `active_inst fn inst vs` by metis_tac[scfg_frame_reachable_active] >>
  drule_all fmp_stage_coverage >> strip_tac >>
  drule_all fmp_codecopy_coverage_reflect >> strip_tac >>
  fs[code_end_offset_ok_def, Abbr `vraw`] >> metis_tac[]
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
  strip_tac >> irule fmp_lowering_code_end_relocate_static >>
  fs[o1_run_state_ok_def] >> metis_tac[]
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
