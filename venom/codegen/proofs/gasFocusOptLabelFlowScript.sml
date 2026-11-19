Theory gasFocusOptLabelFlow
Ancestors o1LabelFlowCompose[qualified]
  o1LabelFlowSource o1LabelFlowMiddle o1LabelFlowLateContracts
  fmpLowerDefs fmpStepBridge fmpStepLayout fmpStepOpaque fmpStepRewriteOrigin
  fmpStepRewriteSupply fmpLowerIndexedProps fmpStepRetpcShape
  o1ContractMakeSsaReplay o1LabelFlowMiddleSsaAssembly
  o1ScheduleDecomp o1PipelineCorrect o1ComposeSupport
  codegenSymRel o1PassContract list rich_list irSupply venomInst
  fmpLowerSequenceExec fmpLowerProps fmpStepTraversal fmpStepReclaim arithmetic
  venomExecSemantics
  dretDesugarProofs finite_map venomFnScheduleRunner
  o1LabelFlowCfgSplitPreservation o1LabelFlowMiddleConcretize o1LabelFlowMiddleFmp
  o1LabelFlowLowerDload concretizeMemLocDefs venomPassDispatcher
  o1ContractLowerDload lowerDloadDefs lowerDloadMakeSsaInput unitShapeDefs
  o1LabelFlowSourceBoundary o1LabelFlowSourceSsaStep o1LabelFlowSourcePreWalk
  o1LabelFlowStaticContracts o1FnScheduleDecompHelpers o1PipelineCompose
  o1PartialSchedule venomFnScheduleRunnerProps fcgPruning venomPassSchedule
  venomPipelineRunner

(* These opcodes pass through the instruction rewrite exactly. *)
Theorem fmp_label_flow_inst_keep[local]:
  fmp_lower_inst infos ctx runner s i = SOME (ys,t) /\
  MEM i.inst_opcode [ADD; CODECOPY; CODESIZE] ==>
  ys = [i]
Proof
  rpt strip_tac >> gvs[fmp_lower_inst_def, is_raw_fmp_opcode_def, AllCaseEqs()]
QED

Theorem fmp_label_flow_inst_origin[local]:
  fmp_lower_inst infos ctx runner s i = SOME (ys,t) /\ MEM j ys /\
  (MEM j.inst_opcode [CODECOPY; CODESIZE] \/
   (j.inst_opcode = ADD /\ ?op. j.inst_operands = [op; Label "code_end"])) ==>
  j = i
Proof
  Cases_on `i.inst_opcode = DALLOCA` >>
  simp[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem fmp_label_flow_inst_writer[local]:
  fmp_lower_inst infos ctx runner s i = SOME (ys,t) /\ MEM j ys /\
  MEM x s.irs_used_vars /\ x <> runner /\
  (MEM x i.inst_outputs ==> i.inst_opcode = ADD) /\ MEM x j.inst_outputs ==>
  j = i
Proof
  Cases_on `i.inst_opcode = DALLOCA`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, AllCaseEqs()] >>
      rpt (drule (cj 1 fresh_ir_var_contract) >> strip_tac >>
           dxrule (cj 2 fresh_ir_var_contract) >> strip_tac) >>
      gvs[mk_inst_def] >> metis_tac[MEM]) >>
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, AllCaseEqs(), MEM_APPEND] >>
  fs[] >> metis_tac[MEM]
QED

(* Restores are indexed by the original list: one may precede the ADD,
   but the reclaim-point classifier never selects the CODECOPY. *)
Theorem fmp_label_flow_indexed_pair[local]:
  fmp_lower_indexed infos ctx runner label k s restores (a ++ d::j::b) =
    SOME (out,leftover,t) /\ d.inst_opcode = ADD /\ j.inst_opcode = CODECOPY /\
  (!base. ~MEM ((label,SUC (k + LENGTH a)),base) restores) ==>
  ?pre post. out = pre ++ d::j::post
Proof
  strip_tac >> drule fmp_lower_indexed_append >> strip_tac >>
  qpat_x_assum `fmp_lower_indexed _ _ _ _ _ _ _ (d::j::b) = _`
    (strip_assume_tac o SRULE [Once fmp_lower_indexed_cons]) >>
  `head = [d]` by (irule fmp_label_flow_inst_keep >> simp[] >> metis_tac[]) >>
  `!base. ~MEM ((label,SUC (k + LENGTH a)),base) later` by
    (drule fmp_select_point_restores_once >> strip_tac >>
     qpat_assum `fmp_lower_indexed _ _ _ _ _ _ restores a = _`
       (mp_tac o MATCH_MP fmp_lower_indexed_leftover) >>
     metis_tac[]) >>
  qpat_x_assum `fmp_lower_indexed _ _ _ _ _ _ later (j::b) = _`
    (strip_assume_tac o SRULE [Once fmp_lower_indexed_cons]) >>
  `bases' = []` by
    (drule fmp_select_point_restores_absent >> gvs[]) >>
  `head' = [j]` by (irule fmp_label_flow_inst_keep >> metis_tac[MEM]) >>
  gvs[fmp_emit_restores_def] >>
  qexistsl [`c1 ++ prefix`,`tail'`] >> simp[APPEND_ASSOC]
QED

Theorem fmp_label_flow_blocks_indexed[local]:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover t) /\ ir_supply_inst_ok s ==>
  LIST_REL (\bb outbb. outbb.bb_label = bb.bb_label /\
    ?s0 rs restout s1. ir_supply_inst_ok s0 /\ dret_supply_extends s s0 /\
      (!q base. MEM (q,base) rs ==> MEM (q,base) restores) /\
      fmp_lower_indexed infos ctx runner bb.bb_label 0 s0 rs bb.bb_instructions =
        SOME (outbb.bb_instructions,restout,s1)) bbs out
Proof
  map_every qid_spec_tac [`s`, `restores`, `out`, `leftover`, `t`] >>
  Induct_on `bbs` >> simp[fmp_lower_blocks_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> conj_tac
  >- (qexistsl [`s`,`restores`,`later`,`s2`] >> simp[dret_supply_extends_refl]) >>
  drule_all fmp_lower_indexed_supply >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  irule LIST_REL_mono >> goal_assum $ drule_at Any >>
  rpt gen_tac >> disch_then (strip_assume_tac o BETA_RULE) >>
  simp[] >> qexistsl [`s0`,`rs`,`restout`,`s1`] >> simp[] >>
  conj_tac >- metis_tac[dret_supply_extends_trans] >>
  qpat_assum `fmp_lower_indexed _ _ _ _ _ s restores _ = _`
    (mp_tac o MATCH_MP fmp_lower_indexed_leftover) >> metis_tac[]
QED

Theorem fmp_label_flow_no_codecopy_restore[local]:
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  bb.bb_instructions = a ++ d::j::b /\ j.inst_opcode = CODECOPY ==>
  !base. ~MEM ((bb.bb_label,SUC (LENGTH a)),base) (fmp_plan_to_alist fn plan)
Proof
  rpt strip_tac >> gvs[MEM_fmp_plan_to_alist] >>
  drule_all analyze_fmp_reclaims_position >> simp[] >> strip_tac >> gvs[] >>
  drule fmp_reclaim_point_opcodes >>
  simp[EL_APPEND_EQN, DECIDE ``!n. SUC n - n = 1``]
QED

Theorem fmp_label_flow_indexed_origin[local]:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,t) /\ ir_supply_inst_ok s /\ MEM j out ==>
  (?i s0 ys s1. MEM i insts /\ dret_supply_extends s s0 /\
    fmp_lower_inst infos ctx runner s0 i = SOME (ys,s1) /\ MEM j ys) \/
  (?p base id. MEM (p,base) restores /\ j = mk_inst id ASSIGN [Var base] [runner])
Proof
  map_every qid_spec_tac [`k`,`s`,`restores`,`out`,`leftover`,`t`] >>
  Induct_on `insts` >- simp[fmp_lower_indexed_def] >>
  simp[fmp_lower_indexed_cons] >> rpt gen_tac >> strip_tac >> gvs[MEM_APPEND] >>
  drule fmp_select_point_restores_once >> strip_tac
  >- (drule_all fmp_emit_restores_assign_origin >> metis_tac[]) >>
  drule_all fmp_emit_restores_supply >> strip_tac
  >- metis_tac[] >>
  drule_all fmp_lower_inst_supply >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  metis_tac[dret_supply_extends_trans]
QED

Theorem fmp_label_flow_indexed_keep[local]:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,t) /\ MEM j insts /\ MEM j.inst_opcode [ADD; CODECOPY] ==>
  MEM j out
Proof
  strip_tac >> qpat_x_assum `MEM j insts` (strip_assume_tac o PURE_REWRITE_RULE [MEM_SPLIT]) >>
  qpat_x_assum `insts = _` SUBST_ALL_TAC >>
  drule fmp_lower_indexed_append >> strip_tac >>
  qpat_x_assum `fmp_lower_indexed _ _ _ _ _ _ _ (j::_) = _`
    (strip_assume_tac o SRULE [Once fmp_lower_indexed_cons]) >>
  `MEM j.inst_opcode [ADD; CODECOPY; CODESIZE]` by fs[] >>
  `head = [j]` by (drule_all fmp_label_flow_inst_keep >> simp[]) >>
  gvs[MEM_APPEND]
QED

Theorem fmp_label_flow_inst_use[local]:
  fmp_lower_inst infos ctx runner s i = SOME (ys,t) /\ MEM j ys /\
  MEM x s.irs_used_vars /\ x <> runner /\ MEM (Var x) j.inst_operands /\
  (MEM (Var x) i.inst_operands ==> i.inst_opcode = CODECOPY) ==>
  j = i /\ i.inst_opcode = CODECOPY
Proof
  strip_tac >> drule_all fmp_lower_inst_var_operand_origin >> strip_tac >> gvs[] >>
  `i.inst_opcode = CODECOPY` by metis_tac[] >>
  `ys = [i]` by (irule fmp_label_flow_inst_keep >> simp[] >> metis_tac[]) >> fs[]
QED

(* A parameter prefix cannot consume the ADD at the start of this pair. *)
Theorem fmp_label_flow_strip_prefix_pair[local]:
  EVERY P oldpre /\ ~P d /\ oldpre ++ suffix = a ++ d::j::b ==>
  ?pre. suffix = pre ++ d::j::b
Proof
  strip_tac >>
  `a ++ [d] ++ (j::b) = oldpre ++ suffix` by simp[] >>
  pop_assum (strip_assume_tac o PURE_REWRITE_RULE [APPEND_EQ_APPEND_MID])
  >- gvs[EVERY_APPEND] >> qexists `l` >> simp[]
QED

Theorem fmp_label_flow_root_pair[local]:
  EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM]) oldpre /\
  oldpre ++ suffix = a ++ d::j::b /\ d.inst_opcode = ADD ==>
  ?pre. newpre ++ suffix = pre ++ d::j::b
Proof
  strip_tac >>
  `~(\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM]) d` by simp[] >>
  drule_all fmp_label_flow_strip_prefix_pair >> strip_tac >>
  qexists `newpre ++ pre` >> simp[APPEND_ASSOC]
QED

(* Root installation is a single entry-block prefix replacement.  Keep the
   corresponding pre-installation block, including when it is not the entry. *)
Theorem fmp_label_flow_root_blocks[local]:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 = SOME (FmpRootLayout n root pc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root pc s2) blocks = SOME (out,s3) ==>
  LIST_REL (\bb bb'.
    (!j. MEM j bb'.bb_instructions ==>
      MEM j bb.bb_instructions \/ MEM j (OPTION_TO_LIST root) \/ MEM j (OPTION_TO_LIST pc)) /\
    (!j. MEM j bb.bb_instructions /\ MEM j.inst_opcode [ADD; CODECOPY] ==>
      MEM j bb'.bb_instructions) /\
    (!a d j b. bb.bb_instructions = a ++ d::j::b /\ d.inst_opcode = ADD ==>
      ?pre. bb'.bb_instructions = pre ++ d::j::b)) blocks out
Proof
  strip_tac >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> fs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  `EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM])
     (users ++ OPTION_TO_LIST oldpc)` by
    (drule split_fmp_entry_parameter_prefix >>
     Cases_on `oldpc` >> simp[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  qpat_x_assum `blocks = entry::rest` SUBST_ALL_TAC >>
  drule_all fmp_install_root_exact_prefix >>
  disch_then (qspecl_then [`s2`,`root`,`rest`,`fn`,`ctx`] assume_tac) >>
  gvs[LIST_REL_CONS1] >> reverse conj_tac
  >- (simp[LIST_REL_EL_EQN] >> metis_tac[]) >>
  Cases_on `fn_is_context_entry ctx fn` >> simp[] >>
  (conj_tac >- (simp[MEM_APPEND] >> metis_tac[]) >>
   conj_tac
   >- (simp[MEM_APPEND] >> rpt strip_tac >> simp[] >>
       qpat_assum `EVERY _ (case oldpc of NONE => [] | SOME i => [i])`
         (qspec_then `j` mp_tac o SRULE [EVERY_MEM]) >> fs[]) >>
   rpt gen_tac >> strip_tac >>
   irule (SRULE [] fmp_label_flow_root_pair) >> simp[] >>
   qexistsl [`a`,`users ++ OPTION_TO_LIST oldpc`] >>
   fs[EVERY_APPEND, APPEND_ASSOC])
QED

Theorem fmp_label_flow_reclaim_not_seed[local]:
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  (!i. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==> i.inst_opcode = ADD) ==>
  !p. ~MEM (p,x) (fmp_plan_to_alist fn plan)
Proof
  rpt strip_tac >> fs[MEM_fmp_plan_to_alist] >>
  drule_all analyze_fmp_reclaims_output >> strip_tac >> res_tac >> fs[]
QED

(* At each output block, retain the particular input occurrence that supplied
   the protected read, rather than merely recovering global membership. *)
Theorem fmp_label_flow_indexed_protected[local]:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,t) /\ ir_supply_inst_ok s /\ MEM x s.irs_used_vars /\
  x <> runner /\ (!p. ~MEM (p,x) restores) /\
  (!i. MEM i insts /\ MEM (Var x) i.inst_operands ==> i.inst_opcode = CODECOPY) /\
  (!i. MEM i insts /\ MEM x i.inst_outputs ==> i = d) /\ d.inst_opcode = ADD ==>
  (!j. MEM j out /\ MEM (Var x) j.inst_operands ==>
    MEM j insts /\ j.inst_opcode = CODECOPY) /\
  (!j. MEM j out /\ MEM x j.inst_outputs ==> j = d)
Proof
  strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all fmp_label_flow_indexed_origin >> strip_tac
      >- (`MEM x s0.irs_used_vars` by fs[dret_supply_extends_def, MEM_APPEND] >>
          drule fmp_label_flow_inst_use >> simp[] >> metis_tac[]) >>
      gvs[mk_inst_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> drule_all fmp_label_flow_indexed_origin >> strip_tac
  >- (`MEM x s0.irs_used_vars` by fs[dret_supply_extends_def, MEM_APPEND] >>
      drule fmp_label_flow_inst_writer >> simp[] >> metis_tac[]) >>
  gvs[mk_inst_def]
QED

Theorem fmp_label_flow_indexed_opcode_origin[local]:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,t) /\ ir_supply_inst_ok s /\ MEM j out /\
  (MEM j.inst_opcode [CODESIZE; CODECOPY] \/
   (j.inst_opcode = ADD /\ ?op. j.inst_operands = [op; Label "code_end"])) ==>
  MEM j insts
Proof
  strip_tac >>
  (drule_all fmp_label_flow_indexed_origin >> strip_tac
   >- (drule fmp_label_flow_inst_origin >> fs[] >> metis_tac[]) >>
   fs[mk_inst_def])
QED

Theorem fmp_label_flow_lowered_pair[local]:
  fmp_lower_indexed infos ctx runner bb.bb_label 0 s rs bb.bb_instructions =
    SOME (out,leftover,t) /\
  wf_function fn /\ MEM bb fn.fn_blocks /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  (!q base. MEM (q,base) rs ==> MEM (q,base) (fmp_plan_to_alist fn plan)) /\
  bb.bb_instructions = a ++ d::j::b /\ d.inst_opcode = ADD /\
  j.inst_opcode = CODECOPY ==>
  ?pre post. out = pre ++ d::j::post
Proof
  strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (fs[venomWfTheory.wf_function_def, fn_labels_def] >>
     irule venomExecPropsTheory.MEM_lookup_block >> simp[]) >>
  drule_all fmp_label_flow_no_codecopy_restore >> strip_tac >>
  `!base. ~MEM ((bb.bb_label,SUC (LENGTH a)),base) rs` by metis_tac[] >>
  qpat_assum `bb.bb_instructions = _` SUBST_ALL_TAC >>
  drule (SRULE [] (Q.INST [`k` |-> `0`] fmp_label_flow_indexed_pair)) >> simp[]
QED

Theorem fmp_label_flow_layout_protected[local]:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  fmp_make_root_layout ctx fn info runner s = SOME (FmpRootLayout n root pc t) /\
  MEM j (OPTION_TO_LIST root ++ OPTION_TO_LIST pc) ==>
  ~MEM j.inst_opcode [ADD; CODECOPY; CODESIZE] /\
  (!x. x <> runner /\
    (!i. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==> i.inst_opcode = ADD) /\
    (!i. MEM i (fn_insts fn) /\ MEM (Var x) i.inst_operands ==> i.inst_opcode = CODECOPY) ==>
    ~MEM x j.inst_outputs /\ ~MEM (Var x) j.inst_operands)
Proof
  strip_tac >> drule_all fmp_make_root_layout_opaque_shape >> strip_tac >>
  drule fmp_make_root_layout_runner_outputs >> strip_tac >>
  drule split_fmp_entry_reconstruct >> strip_tac >>
  `!i. MEM i (OPTION_TO_LIST oldpc) ==> MEM i (fn_insts fn) /\
    i.inst_opcode = RETPC_PARAM` by
    (Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def] >>
     drule split_fmp_entry_retpc_opcode >>
     simp[fn_insts_def, fn_insts_blocks_MEM, MEM_APPEND] >>
     strip_tac >> qexists `entry` >> simp[MEM_APPEND]) >>
  conj_tac >- (fs[MEM_APPEND] >> res_tac >> fs[]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (strip_tac >> fs[MEM_APPEND] >> res_tac >> gvs[] >>
      Cases_on `pc` >> Cases_on `oldpc` >> gvs[callLayoutDefsTheory.OPTION_TO_LIST_def] >>
      res_tac >> fs[]) >>
  strip_tac >>
  `MEM j (OPTION_TO_LIST oldpc)` by
    (drule_all (PURE_ONCE_REWRITE_RULE [GSYM MEM_APPEND]
       fmp_make_root_layout_operand_origin) >> simp[]) >>
  res_tac >> fs[]
QED

(* Compose the indexed rewrite with root installation at the same block index. *)
Theorem fmp_label_flow_rewrite_blocks[local]:
  split_fmp_entry fn = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  fmp_make_root_layout ctx fn info runner s0 = SOME (FmpRootLayout n root pc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist fn plan) fn.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx fn (FmpRootLayout n root pc s2) blocks = SOME (out,s3) /\
  wf_function fn /\ ir_supply_inst_ok s1 ==>
  LIST_REL (\bb bb'.
    (!j. MEM j bb'.bb_instructions /\
      (MEM j.inst_opcode [CODESIZE; CODECOPY] \/
       (j.inst_opcode = ADD /\ ?op. j.inst_operands = [op; Label "code_end"])) ==>
      MEM j bb.bb_instructions) /\
    (!d. MEM d bb.bb_instructions /\ d.inst_opcode = ADD ==> MEM d bb'.bb_instructions) /\
    (!x d. MEM x s1.irs_used_vars /\ x <> runner /\ d.inst_opcode = ADD /\
      (!i. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==> i = d) /\
      (!i. MEM i (fn_insts fn) /\ MEM (Var x) i.inst_operands ==> i.inst_opcode = CODECOPY) ==>
      (!j. MEM j bb'.bb_instructions /\ MEM x j.inst_outputs ==> j = d) /\
      (!j. MEM j bb'.bb_instructions /\ MEM (Var x) j.inst_operands ==>
        MEM j bb.bb_instructions /\ j.inst_opcode = CODECOPY)) /\
    (!a d j b. bb.bb_instructions = a ++ d::j::b /\
      d.inst_opcode = ADD /\ j.inst_opcode = CODECOPY ==>
      ?pre post. bb'.bb_instructions = pre ++ d::j::post)) fn.fn_blocks out
Proof
  strip_tac >> drule_all fmp_label_flow_blocks_indexed >> strip_tac >>
  drule_all fmp_label_flow_root_blocks >> strip_tac >>
  fs[LIST_REL_EL_EQN] >> qx_gen_tac `idx` >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH blocks ==> _` (qspec_then `idx` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH fn.fn_blocks ==> _` (qspec_then `idx` mp_tac) >>
  simp[] >> strip_tac >>
  qabbrev_tac `bb = EL idx fn.fn_blocks` >>
  `MEM bb fn.fn_blocks` by simp[Abbr `bb`, EL_MEM] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `MEM j (EL idx blocks).bb_instructions` by
        (res_tac >> fs[] >>
         `MEM j (OPTION_TO_LIST root ++ OPTION_TO_LIST pc)` by simp[MEM_APPEND] >>
         drule_all fmp_label_flow_layout_protected >> simp[]) >>
      drule fmp_label_flow_indexed_opcode_origin >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `MEM d (EL idx blocks).bb_instructions` by
        (drule fmp_label_flow_indexed_keep >> simp[]) >> res_tac >> fs[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `!i. MEM i bb.bb_instructions ==> MEM i (fn_insts fn)` by
        (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
      `!i. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==> i.inst_opcode = ADD` by metis_tac[] >>
      `!p. ~MEM (p,x) rs` by
        (drule_all fmp_label_flow_reclaim_not_seed >> metis_tac[]) >>
      `MEM x s0'.irs_used_vars` by fs[dret_supply_extends_def, MEM_APPEND] >>
      drule fmp_label_flow_indexed_protected >>
      disch_then (qspecl_then [`x`,`d`] mp_tac) >> simp[] >>
      strip_tac >>
      `!j. MEM j (OPTION_TO_LIST root ++ OPTION_TO_LIST pc) ==>
        ~MEM x j.inst_outputs /\ ~MEM (Var x) j.inst_operands` by
        (rpt strip_tac >> drule_all fmp_label_flow_layout_protected >> metis_tac[]) >>
      metis_tac[MEM_APPEND]) >>
  rpt gen_tac >> strip_tac >>
  `?pre post. (EL idx blocks).bb_instructions = pre ++ d::j::post` by
    (drule_all (SRULE [] fmp_label_flow_lowered_pair) >> simp[]) >>
  pop_assum (assume_tac o SRULE []) >> metis_tac[]
QED

Theorem fmp_label_flow_reflect[local]:
  !g x. code_end_var g x ==> !f.
    (!j. MEM j (fn_insts g) /\ j.inst_opcode = ADD /\
         (?op. j.inst_operands = [op; Label "code_end"]) ==> MEM j (fn_insts f)) /\
    (!j y. MEM j (fn_insts g) /\ MEM (Var y) j.inst_operands /\ code_end_var f y ==>
           j.inst_opcode = CODECOPY) ==>
    code_end_var f x
Proof
  ho_match_mp_tac code_end_var_ind >> rpt strip_tac
  >- metis_tac[code_end_var_seed] >>
  rename1 `inst.inst_operands = [Var src]` >>
  `code_end_var f src` by metis_tac[] >>
  `MEM (Var src) inst.inst_operands` by simp[] >>
  res_tac >> fs[]
QED

Theorem fmp_label_flow_rewrite[local]:
  split_fmp_entry f = SOME (FmpEntryLayout users oldpc suffix) /\
  analyze_fmp_reclaims infos ctx f = SOME plan /\
  fmp_make_root_layout ctx f info runner s0 = SOME (FmpRootLayout n root pc s1) /\
  fmp_lower_blocks infos ctx runner s1 (fmp_plan_to_alist f plan) f.fn_blocks =
    SOME (FmpBlocksResult blocks leftover s2) /\
  fmp_install_root ctx f (FmpRootLayout n root pc s2) blocks = SOME (out,s3) /\
  g.fn_blocks = out /\ wf_function f /\ ir_supply_inst_ok s1 /\
  (!x. code_end_var f x ==> MEM x s1.irs_used_vars /\ x <> runner) /\
  middle_code_end_lifetime f /\ label_flow_ok (C with ctx_functions := [f]) ==>
  middle_code_end_lifetime g /\ label_flow_ok (C with ctx_functions := [g])
Proof
  strip_tac >> drule_all fmp_label_flow_rewrite_blocks >> strip_tac >>
  `!j. MEM j (fn_insts g) /\
       (MEM j.inst_opcode [CODESIZE; CODECOPY] \/
        (j.inst_opcode = ADD /\ ?op. j.inst_operands = [op; Label "code_end"])) ==>
       MEM j (fn_insts f)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> rpt strip_tac >>
     drule_all LIST_REL_MEM_IMP_R >> disch_then (strip_assume_tac o BETA_RULE) >>
     metis_tac[MEM]) >>
  `!d. MEM d (fn_insts f) /\ d.inst_opcode = ADD ==> MEM d (fn_insts g)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> rpt strip_tac >>
     drule_all LIST_REL_MEM_IMP >> disch_then (strip_assume_tac o BETA_RULE) >>
     metis_tac[]) >>
  `!x. code_end_var f x ==>
      ?d op. MEM d (fn_insts g) /\ d.inst_opcode = ADD /\
        d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
        (!k. MEM k (fn_insts g) /\ MEM x k.inst_outputs ==> k = d) /\
        (!bb j. MEM bb g.fn_blocks /\ MEM j bb.bb_instructions /\ MEM (Var x) j.inst_operands ==>
          j.inst_opcode = CODECOPY /\
          (?dst sz. j.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x) /\
          ?pre post. bb.bb_instructions = pre ++ d::j::post)` by
    (rpt gen_tac >> strip_tac >> fs[middle_code_end_lifetime_def] >>
     qpat_x_assum `!v. code_end_var f v ==> ?d op. _` (qspec_then `x` mp_tac) >>
     simp[] >> strip_tac >> qexistsl [`d`,`op`] >> simp[] >>
     `!i. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands ==> i.inst_opcode = CODECOPY` by
       (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
     conj_tac
     >- (simp[fn_insts_def, fn_insts_blocks_MEM] >> rpt strip_tac >>
         drule_all LIST_REL_MEM_IMP_R >> disch_then (strip_assume_tac o BETA_RULE) >>
         first_x_assum (qspecl_then [`x`,`d`] mp_tac) >> simp[]) >>
     rpt gen_tac >> strip_tac >>
     drule_all LIST_REL_MEM_IMP_R >> disch_then (strip_assume_tac o BETA_RULE) >>
     qpat_x_assum `!v d. MEM v s1.irs_used_vars /\ _ ==> _`
       (qspecl_then [`x`,`d`] mp_tac) >> simp[] >> strip_tac >>
     rename1 `MEM srcbb f.fn_blocks` >>
     `MEM j srcbb.bb_instructions` by metis_tac[] >>
     qpat_x_assum `!b i. MEM b f.fn_blocks /\ MEM i b.bb_instructions /\ _ ==> _`
       (qspecl_then [`srcbb`,`j`] mp_tac) >> simp[] >> strip_tac >>
     qpat_x_assum `!a d j b. _ ==> ?pre. _` (qspecl_then [`pre`,`d`,`j`,`post`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `!j x. MEM j (fn_insts g) /\ MEM (Var x) j.inst_operands /\ code_end_var f x ==>
     j.inst_opcode = CODECOPY` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `!x. code_end_var g x <=> code_end_var f x` by
    (gen_tac >> eq_tac >> strip_tac
     >- (drule fmp_label_flow_reflect >> metis_tac[]) >>
     res_tac >> irule code_end_var_seed >> metis_tac[MEM]) >>
  conj_tac >- simp[middle_code_end_lifetime_def] >>
  qpat_x_assum `label_flow_ok _` (assume_tac o SRULE [label_flow_ok_def]) >>
  simp[label_flow_ok_def] >> qx_gen_tac `j` >> strip_tac >>
  rpt conj_tac
  >- (strip_tac >> `MEM j (fn_insts f)` by metis_tac[MEM] >>
      first_x_assum (qspec_then `j` mp_tac) >> simp[])
  >- (rpt strip_tac >> `j.inst_opcode = CODECOPY` by metis_tac[] >>
      `MEM j (fn_insts f)` by metis_tac[MEM] >>
      qpat_x_assum `!i. MEM i (fn_insts f) ==> i.inst_opcode <> CODESIZE /\ _`
        (qspec_then `j` mp_tac) >> simp[]) >>
  strip_tac >> `MEM j (fn_insts f)` by metis_tac[MEM] >>
  qpat_x_assum `!i. MEM i (fn_insts f) ==> i.inst_opcode <> CODESIZE /\ _`
    (qspec_then `j` mp_tac) >> simp[]
QED

Theorem fmp_label_flow_seal[local]:
  fmp_checked_seal ctx f info blocks = SOME g ==>
  g.fn_blocks = blocks
Proof
  strip_tac >> drule fmp_checked_seal_some >> simp[fmp_seal_def]
QED

Theorem fmp_label_flow_function[local]:
  fmp_lower_function ctx s f = SOME (g,t) /\
  wf_function f /\ ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  middle_code_end_lifetime f /\ label_flow_ok (C with ctx_functions := [f]) ==>
  middle_code_end_lifetime g /\ label_flow_ok (C with ctx_functions := [g])
Proof
  strip_tac >> gvs[fmp_lower_function_def, AllCaseEqs()] >>
  qpat_x_assum `fmp_lower_function_with_info _ _ _ _ = _`
    (strip_assume_tac o SRULE [fmp_lower_function_with_info_def, AllCaseEqs()]) >>
  gvs[]
  >- (drule fmp_label_flow_seal >> strip_tac >>
      `!x. code_end_var g x <=> code_end_var f x` by
        metis_tac[code_end_var_same_blocks] >>
      conj_tac >- fs[middle_code_end_lifetime_def, fn_insts_def] >>
      metis_tac[label_flow_ok_same_blocks]) >>
  Cases_on `root_layout` >> gvs[] >>
  drule fmp_label_flow_seal >> strip_tac >>
  drule fmp_make_root_layout_used_vars >> strip_tac >>
  `?users oldpc suffix. split_fmp_entry f = SOME (FmpEntryLayout users oldpc suffix)` by
    gvs[Once fmp_make_root_layout_def, AllCaseEqs()] >>
  `ir_supply_inst_ok s1` by metis_tac[fresh_ir_var_inst_ok] >>
  drule_all fmp_make_root_layout_inst_ok >> strip_tac >>
  `!x. code_end_var f x ==> MEM x s1.irs_used_vars /\ x <> runner` by
    (drule fresh_ir_var_contract >>
     fs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >>
     metis_tac[code_end_var_ir_var, MEM]) >>
  drule fmp_label_flow_rewrite >> disch_then irule >>
  fs[] >> goal_assum $ drule_at (Pat `fmp_make_root_layout _ _ _ _ _ = _`) >>
  goal_assum $ drule_at (Pat `fmp_lower_blocks _ _ _ _ _ _ = _`) >>
  goal_assum $ drule_at (Pat `fmp_install_root _ _ _ _ = _`) >> simp[]
QED

Theorem focus_label_flow_step_shape[local]:
  fn_pass_step rp pass observed s f out /\ o1_ctx_shape observed.cu_context ==>
  o1_fn_shape observed.cu_context f /\ ir_supply_covers_fn s f
Proof
  strip_tac >>
  `MEM f observed.cu_context.ctx_functions` by
    metis_tac[fn_pass_step_def, lookup_unique_function_member] >>
  conj_tac >- fs[o1_ctx_shape_def, EVERY_MEM] >>
  irule ir_supply_covers_unit_member >> fs[fn_pass_step_def] >> metis_tac[]
QED

Theorem focus_label_flow_fmp_step[local]:
  fn_pass_step rp (CFP_Simple VP_FmpLowering) observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  label_flow_ok (C with ctx_functions := [f]) /\ middle_code_end_lifetime f ==>
  label_flow_ok (C with ctx_functions := [out.fpo_function]) /\
  middle_code_end_lifetime out.fpo_function
Proof
  strip_tac >> drule_all focus_label_flow_step_shape >> strip_tac >>
  drule fmp_fn_pass_step_result >> strip_tac >>
  `wf_function f` by fs[o1_fn_shape_def] >>
  drule_all fmp_label_flow_function >> simp[]
QED

Theorem focus_label_flow_second_ssa[local]:
  fn_pass_step rp (CFP_Simple VP_MakeSSA) observed s f out /\
  o1_ctx_shape observed.cu_context /\ o1_fn_row 4 f /\
  label_flow_ok (C with ctx_functions := [f]) /\ middle_code_end_lifetime f ==>
  label_flow_ok (C with ctx_functions := [out.fpo_function])
Proof
  strip_tac >> drule_all focus_label_flow_step_shape >> strip_tac >>
  `wf_function f /\ fn_inst_wf f /\ make_ssa_input_ok f` by
    fs[o1_fn_shape_def, o1_fn_row_def, fn_shape_ok_def] >>
  drule make_ssa_pass_step_replay >> strip_tac >>
  irule make_ssa_current_fn_label_flow >> goal_assum $ drule_at Any >>
  fs[middle_code_end_lifetime_def]
QED

Theorem focus_label_flow_late_step[local]:
  ((k = 5 /\ pass = CFP_Simple VP_SimplifyCFG) \/
   (k = 6 /\ pass = CFP_Simple VP_SingleUseExpansion) \/
   (k = 7 /\ pass = CFP_Simple VP_DFT) \/
   (k = 8 /\ pass = CFP_Simple VP_CFGNormalization)) /\
  fn_pass_step rp pass observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  o1_fn_row k f /\ label_flow_ok (C with ctx_functions := [f]) ==>
  label_flow_ok (C with ctx_functions := [out.fpo_function])
Proof
  strip_tac >>
  `label_flow_ok (observed.cu_context with ctx_functions := [f])` by
    metis_tac[o1LabelFlowComposeTheory.label_flow_singleton_context] >>
  `label_flow_ok (observed.cu_context with ctx_functions := [out.fpo_function])` by
    metis_tac[o1_late_row_label_flow_ok] >>
  metis_tac[o1LabelFlowComposeTheory.label_flow_singleton_context]
QED

(* Carry only the label-flow facts needed at each row.  Running the enriched
   contracts on the actual schedule retains observed shape and valid supplies. *)
Theorem focus_label_flow_rows[local]:
  rows_step_contracts_from
    (\k f. o1_fn_row k f /\ label_flow_ok (C with ctx_functions := [f]) /\
      (k <= 1 ==> !i. MEM i (fn_insts f) ==>
        ~MEM (Label "code_end") i.inst_operands) /\
      (2 <= k /\ k <= 4 ==> middle_code_end_lifetime f))
    rp 0 o1_fn_passes
Proof
  mp_tac (MATCH_MP o1_step_contracts_from_rows o1_fn_passes_steps) >>
  rewrite_tac[o1_fn_passes_def, rows_step_contracts_from_def, rows_step_contract_def] >>
  strip_tac >> simp[] >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  `EVERY (\g. ?j. o1_fn_row j g) observed.cu_context.ctx_functions` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  fs[] >> first_x_assum drule_all >> strip_tac >> simp[]
  >- (`!i. MEM i (fn_insts fn) ==> i.inst_opcode <> CODESIZE /\
         (i.inst_opcode = CODECOPY ==> ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz])` by
        metis_tac[label_flow_ok_seed_free_function] >>
      drule_all first_make_ssa_step_seed_free_flow >>
      metis_tac[label_flow_ok_seed_free_function])
  >- metis_tac[o1LabelFlowMiddleTheory.middle_lower_dload_step]
  >- metis_tac[o1LabelFlowMiddleTheory.middle_concretize_step]
  >- metis_tac[focus_label_flow_fmp_step]
  >- metis_tac[focus_label_flow_second_ssa]
  >- (irule (SRULE [] (Q.INST [`k` |-> `5`] focus_label_flow_late_step)) >> metis_tac[])
  >- (irule (SRULE [] (Q.INST [`k` |-> `6`] focus_label_flow_late_step)) >> metis_tac[])
  >- (irule (SRULE [] (Q.INST [`k` |-> `7`] focus_label_flow_late_step)) >> metis_tac[]) >>
  irule (SRULE [] (Q.INST [`k` |-> `8`] focus_label_flow_late_step)) >> metis_tac[]
QED

Theorem focus_label_flow_walk[local]:
  run_named_fn_schedules execute_configured_fn_pass rp o1_fn_passes names u s =
    SOME (u',s') /\ o1_ctx_shape u.cu_context /\
  ALL_DISTINCT (unit_label_namespace u) /\ ALL_DISTINCT names /\
  (!n. MEM n names <=> MEM n (ctx_fn_names u.cu_context)) /\
  ir_supply_inst_ok s /\ EVERY (o1_fn_row 0) u.cu_context.ctx_functions /\
  (!f i. MEM f u.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands /\ i.inst_opcode <> CODESIZE /\
    (i.inst_opcode = CODECOPY ==>
      ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz])) ==>
  label_flow_ok u'.cu_context
Proof
  strip_tac >>
  assume_tac (Q.INST [`C` |-> `u.cu_context`, `rp` |-> `rp`] focus_label_flow_rows) >>
  drule_at (Pos (el 1)) run_named_fn_schedules_decomp >>
  disch_then (drule_at (Pat `run_named_fn_schedules _ _ _ _ _ _ = _`)) >>
  simp[] >> impl_tac
  >- (fs[EVERY_MEM] >> rpt strip_tac
      >- (irule (iffRL label_flow_ok_seed_free_function) >> metis_tac[])
      >> metis_tac[]) >>
  disch_then (qx_choose_then `chains` strip_assume_tac) >>
  `!i. i < LENGTH chains ==>
    label_flow_ok (u.cu_context with ctx_functions :=
      [EL (LENGTH o1_fn_passes) (FST (EL i chains))])` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     drule chain_facts_row >> disch_then (qspec_then `LENGTH o1_fn_passes` mp_tac) >>
     simp[]) >>
  gvs[stage_ctx_def, stage_fns_def, label_flow_ok_def, MEM_MAP] >>
  metis_tac[MEM_EL]
QED

Theorem focus_opt_label_flow:
  o1PipelineCorrect$o1_pipeline rp unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  label_flow_ok unit.cu_context /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "code_end") inst.inst_operands) ==>
  label_flow_ok out.po_unit.cu_context
Proof
  rewrite_tac[o1PipelineCorrectTheory.o1_pipeline_def] >>
  strip_tac >> drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)` by simp[init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  drule o1_pre_walk_seed_free_flow >> simp[] >> disch_tac >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  mp_tac (Q.INST [`unit` |-> `pre`, `fcg` |-> `fcg_analyze pre.cu_context`]
    o1_walk_callee_first) >> simp[] >> strip_tac >>
  drule unit_labels_wf_namespace >> strip_tac >>
  `o1_ctx_shape (prune_unit_fcg_unreachable pre
     (fcg_analyze pre.cu_context)).cu_context /\
   ALL_DISTINCT (unit_label_namespace
     (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)))` by
    metis_tac[o1_ctx_shape_prune] >>
  fs[run_callee_first_def] >>
  drule focus_label_flow_walk >> simp[o1_prune_every] >>
  metis_tac[MEM_prune_unit_fcg_unreachable_functions]
QED
