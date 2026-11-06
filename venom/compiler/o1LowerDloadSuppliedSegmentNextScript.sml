Theory o1LowerDloadSuppliedSegmentNext
Ancestors
  o1LowerDloadSuppliedSegmentResources o1LowerDloadSuppliedSegmentTransport
  o1LowerDloadSuppliedSegmentControl o1LowerDloadJointRelation
  o1LowerDloadOccurrence o1LowerDloadReadiness o1LowerDloadRawBridge
  o1LowerDloadOccurrenceHeadroom o1LowerDloadJointScalar
  o1LowerDloadScratchExtension
  o1LowerDloadEnvironment o1LowerDloadShared o1LowerDloadOpaque
  o1PassContract lowerDloadDefs ptrDiscipline contextCodegenRel
  venomExecSemantics venomExecProps venomWf venomInst venomState
  irSupply list finite_map words

Theorem ld_dloadbytes_successor_shape[local]:
  wf_function fn /\ fn_inst_wf fn /\ active_inst fn inst s /\
  inst.inst_opcode = DLOADBYTES /\ step_inst fuel C inst s = OK s1 ==>
  ?dst src sz p x z inst2.
    inst.inst_operands = [dst;src;sz] /\ inst.inst_outputs = [] /\
    eval_operand dst s = SOME p /\ eval_operand src s = SOME x /\
    eval_operand sz s = SOME z /\
    s1 = write_memory_with_expansion (w2n p)
      (TAKE (w2n z) (DROP (w2n x) s.vs_data_section ++ REPLICATE (w2n z) 0w)) s /\
    active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `inst_wf inst` by
    (fs[wf_function_def, fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `inst.inst_outputs = []` by gvs[inst_wf_def] >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `s1.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  drule_all ld_nonterminator_successor >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem ld_joint_dloadbytes_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  mem_inv dload_offset_ok C vs /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = DLOADBYTES /\ step_inst fuel C inst s = OK s1 ==>
  ?inst2 es t2 t3 fn' bb'.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    TAKE 2 (DROP t.vs_inst_idx bb'.bb_instructions) = es /\ LENGTH es = 2 /\
    t.vs_inst_idx + 2 <= LENGTH bb'.bb_instructions /\
    step_inst fuel C' (EL 0 es) t = OK t2 /\
    step_inst fuel C' (EL 1 es) t2 = OK t3 /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t3 with vs_inst_idx := t.vs_inst_idx+2)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by
    (drule ld_joint_source >> strip_tac >>
     drule occ_frame_reachable_annotation >> simp[]) >>
  `wf_function fn /\ fn_inst_wf fn` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]) >>
  drule_all ld_dloadbytes_successor_shape >> strip_tac >>
  drule_at (Pat `ld_joint_boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    ld_joint_segment_control >>
  disch_then drule >> disch_then drule >> simp[IgnAsm `s1 = _`] >> strip_tac >>
  `code_layout_valid t` by metis_tac[ld_joint_segment_layout] >>
  `w2n x + (LENGTH t.vs_code - LENGTH t.vs_data_section) < dimword(:256)` by
    (drule ld_joint_segment_offset >> disch_then irule >> simp[] >> metis_tac[]) >>
  Cases_on `fresh_ir_var v` >> rename1 `fresh_ir_var v = (bv,v1)` >>
  `~MEM bv v.irs_used_vars` by metis_tac[fresh_ir_var_contract] >>
  `~MEM bv (fn_ir_vars fn)` by metis_tac[] >>
  `dst <> Var bv /\ sz <> Var bv` by
    (conj_tac >> strip_tac >>
     `MEM (Var bv) inst.inst_operands` by simp[] >>
     metis_tac[ld_active_operand_ir_var]) >>
  drule_at (Pat `lower_dload_inst_supply _ _ = _`)
    (BETA_RULE (PURE_REWRITE_RULE [LET_THM] ld_joint_supply_dloadbytes_transport)) >>
  disch_then (drule_at (Pat `ld_joint_boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fresh_ir_var _ = _`)) >>
  simp[IgnAsm `s1 = _`] >>
  disch_then drule >> strip_tac >>
  qmatch_asmsub_abbrev_tac `step_inst fuel C' (HD es) t = OK t2` >>
  qmatch_asmsub_abbrev_tac `ld_env_agree sites fn _ _ s1 t3` >>
  `step_prov PG G inst s1 = G /\ occurrence_step a HP H inst s1 = H` by
    simp[step_prov_def, occurrence_step_def, set_prov_def, DRESTRICT_UNIV] >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    fs[ld_joint_boundary_def] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> ALLOCA` by simp[is_terminator_def] >>
  `occ_frame_reachable vs C stk PG G (step_taint inst s s1 tn) fn inst2
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H` by
    (drule_all occ_frame_reachable_next >> simp[occurrence_sites_step_def] >> gvs[]) >>
  `occurrence_annotation_ok n a U B HP H stk PG G
    (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     simp[occurrence_sites_step_def] >> gvs[]) >>
  qexistsl_tac [`inst2`,`t2`,`t3`] >>
  simp[IgnAsm `s1 = _`, arithmeticTheory.ADD_COMM] >>
  `TAKE 2 (DROP t.vs_inst_idx bb'.bb_instructions) = es` by metis_tac[] >>
  simp[IgnAsm `s1 = _`] >>
  qhdtm_assum `ld_joint_boundary`
    (strip_assume_tac o REWRITE_RULE [ld_joint_boundary_def]) >>
  simp[IgnAsm `s1 = _`, ld_joint_boundary_def] >>
  `fn'' = fn'` by metis_tac[optionTheory.SOME_11] >>
  `active_inst fn inst2 (s with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `active_inst fn inst2 _` mp_tac >>
     simp[write_memory_with_expansion_def, active_inst_def]) >>
  `ld_joint_control u fn fn' (s with vs_inst_idx := SUC s.vs_inst_idx)
    (t with vs_inst_idx := t.vs_inst_idx + 2)` by metis_tac[arithmeticTheory.ADD_COMM] >>
  conj_tac
  >- (qexists_tac `u'` >>
      qhdtm_assum `ld_joint_frame`
        (strip_assume_tac o REWRITE_RULE [ld_joint_frame_def]) >>
      `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
        fs[wf_function_def, fn_labels_def] >>
      qpat_x_assum `ld_joint_control u' _ _ _ _` mp_tac >>
      strip_tac >> drule_all ld_joint_control_segment >> strip_tac >>
      rename1 `lower_dload_inst_supply v2 inst = (es2,v2')` >>
      `LENGTH es2 = 2` by
        (qpat_x_assum `lower_dload_inst_supply v2 inst = _` mp_tac >>
         simp[lower_dload_inst_supply_def, AllCaseEqs()] >>
         rpt strip_tac >> gvs[]) >>
      `ld_joint_control u' fn fn'' (s with vs_inst_idx := SUC s.vs_inst_idx)
        (t with vs_inst_idx := t.vs_inst_idx + 2)` by metis_tac[] >>
      qpat_x_assum `ld_joint_boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
      qpat_x_assum `!next. _` kall_tac >>
      qpat_x_assum `!next. _` kall_tac >>
      simp[IgnAsm `s1 = _`, ld_joint_frame_def] >>
      conj_tac
      >- (qpat_x_assum `ld_env_agree sites fn (occurrence_step _ _ _ _ _) _ _ _` mp_tac >>
          simp[IgnAsm `s1 = _`, ld_env_agree_def, op_taint_def]) >>
      fs[IgnAsm `s1 = _`, ld_params_agree_def, ld_joint_local_fields_def,
         ld_joint_allocas_def] >>
      simp[Abbr `t3`, Abbr `t2`, write_memory_with_expansion_def,
          update_var_def, ld_params_agree_def, ld_joint_local_fields_def,
          ld_joint_allocas_def] >>
      qpat_x_assum `ld_joint_control u' _ _ (_ with vs_inst_idx := _) _` mp_tac >>
      simp[NoAsms, ld_joint_control_def, write_memory_with_expansion_def,
           update_var_def] >> strip_tac >> gvs[] >> metis_tac[]) >>
  gvs[Abbr `t3`, Abbr `t2`, write_memory_with_expansion_def,
      update_var_def, ld_shared_agree_def, step_taint_def,
      set_var_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
      DRESTRICT_UNIV]
QED

Theorem ld_dload_successor_shape[local]:
  wf_function fn /\ fn_inst_wf fn /\ active_inst fn inst s /\
  inst.inst_opcode = DLOAD /\ step_inst fuel C inst s = OK s1 ==>
  ?off out x inst2.
    inst.inst_operands = [off] /\ inst.inst_outputs = [out] /\
    eval_operand off s = SOME x /\
    s1 = update_var out (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n x) s.vs_data_section ++ REPLICATE 32 0w))) s /\
    active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `inst_wf inst` by
    (fs[wf_function_def, fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `?off out. inst.inst_operands = [off] /\ inst.inst_outputs = [out]` by
    gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `s1.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  drule_all ld_nonterminator_successor >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[exec_read1_def, bind_outputs_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_joint_dload_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  mem_inv dload_offset_ok C vs /\ mem_inv dload_headroom_ok C vs /\
  callee_first names C.ctx_functions /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = DLOAD /\ step_inst fuel C inst s = OK s1 ==>
  ?inst2 es t1 t2 t3 t4 fn' bb' X1.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    TAKE 4 (DROP t.vs_inst_idx bb'.bb_instructions) = es /\ LENGTH es = 4 /\
    t.vs_inst_idx + 4 <= LENGTH bb'.bb_instructions /\
    step_inst fuel C' (EL 0 es) t = OK t1 /\
    step_inst fuel C' (EL 1 es) t1 = OK t2 /\
    step_inst fuel C' (EL 2 es) t2 = OK t3 /\
    step_inst fuel C' (EL 3 es) t3 = OK t4 /\
    ((FLOOKUP X (a,inst.inst_id) = NONE /\
      X1 = X |+ ((a,inst.inst_id),((EL 0 es).inst_id,t.vs_alloca_next))) \/
     (IS_SOME (FLOOKUP X (a,inst.inst_id)) /\ X1 = X)) /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t4 with vs_inst_idx := t.vs_inst_idx+4)
      n a U B HP (occurrence_step a HP H inst s1) sites X1 ts
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by
    (drule ld_joint_source >> strip_tac >>
     drule occ_frame_reachable_annotation >> simp[]) >>
  `wf_function fn /\ fn_inst_wf fn` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]) >>
  drule_all ld_dload_successor_shape >> strip_tac >>
  qhdtm_assum `ld_joint_boundary`
    (strip_assume_tac o REWRITE_RULE [ld_joint_boundary_def]) >>
  qhdtm_assum `ld_joint_frame`
    (strip_assume_tac o REWRITE_RULE [ld_joint_frame_def]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  drule_all ld_joint_control_segment >> strip_tac >>
  `ld_joint_scratch u fn inst.inst_id (HD es).inst_id` by metis_tac[] >>
  `ir_supply_covers_fn u fn` by fs[ld_joint_control_def] >>
  `code_layout_valid t` by metis_tac[ld_joint_segment_layout] >>
  `w2n x + (LENGTH t.vs_code - LENGTH t.vs_data_section) < dimword(:256)` by
    (drule ld_joint_segment_offset >> disch_then irule >> simp[] >> metis_tac[]) >>
  Cases_on `fresh_ir_var v` >> rename1 `fresh_ir_var v = (av,v1)` >>
  Cases_on `fresh_ir_var v1` >> rename1 `fresh_ir_var v1 = (bv,v2)` >>
  `~MEM av v.irs_used_vars /\ ~MEM bv v1.irs_used_vars` by
    metis_tac[fresh_ir_var_contract] >>
  `~MEM av (fn_ir_vars fn) /\ ~MEM bv (fn_ir_vars fn)` by
    metis_tac[fresh_ir_var_preserves_old] >>
  `off <> Var av` by
    (strip_tac >> `MEM (Var av) inst.inst_operands` by simp[] >>
     metis_tac[ld_active_operand_ir_var]) >>
  Q.SUBGOAL_THEN `?b X1 ta.
    ((FLOOKUP X (a,inst.inst_id) = NONE /\
      X1 = X |+ ((a,inst.inst_id),((HD es).inst_id,t.vs_alloca_next))) \/
     (IS_SOME (FLOOKUP X (a,inst.inst_id)) /\ X1 = X)) /\
    ((FLOOKUP t.vs_allocas (HD es).inst_id = NONE /\ b = t.vs_alloca_next) \/
     FLOOKUP t.vs_allocas (HD es).inst_id = SOME (b,32)) /\
    b+32 < dimword(:256) /\
    ta = (if FLOOKUP t.vs_allocas (HD es).inst_id = NONE then
      t with <|vs_allocas := t.vs_allocas |+ ((HD es).inst_id,(b,32));
               vs_alloca_next := t.vs_alloca_next+32|> else t) /\
    ld_joint_geometry sites X1 lo (a::MAP (\f. f.of_owner) U) /\
    FLOOKUP X1 (a,inst.inst_id) = SOME ((HD es).inst_id,b) /\
    ld_joint_allocas sites X1 a fn ta /\
    (!d id c. FLOOKUP X1 (a,d) = SOME (id,c) ==> ld_joint_scratch u fn d id) /\
    ld_joint_saved C' sites X1 lo U stk ts /\
    ta.vs_alloca_next < dimword(:256) /\
    t.vs_alloca_next <= ta.vs_alloca_next /\
    (!did aid c. FLOOKUP X1 (a,did) = SOME (aid,c) ==>
      c+32 <= ta.vs_alloca_next) /\
    ta.vs_alloca_next = s.vs_alloca_next +
      32 * CARD {id | id IN FDOM X1 /\ MEM (FST id) (a::MAP (\f. f.of_owner) U)}`
    (qx_choose_then `b` (qx_choose_then `X1` (qx_choose_then `ta`
      (map_every assume_tac o CONJUNCTS))))
    >- 
    (Cases_on `FLOOKUP X (a,inst.inst_id)`
     >- (qabbrev_tac `ta = t with
           <|vs_allocas := t.vs_allocas |+ ((HD es).inst_id,(t.vs_alloca_next,32));
             vs_alloca_next := t.vs_alloca_next+32|>` >>
         `(a,inst.inst_id) NOTIN FDOM X` by fs[FLOOKUP_DEF] >>
         drule_at (Pat `ld_joint_boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
           (BETA_RULE (PURE_REWRITE_RULE [LET_THM] ld_joint_dload_fresh_metadata)) >>
         disch_then (drule_at (Pat `ld_joint_scratch _ _ _ _`)) >>
         disch_then (qspec_then `ta` mp_tac) >>
         simp[IgnAsm `s1 = _`, IgnAsm `t.vs_alloca_next = _`, Abbr `ta`] >>
         disch_then drule >> strip_tac >>
         `!did aid c.
           FLOOKUP (X |+ ((a,inst.inst_id),((HD es).inst_id,t.vs_alloca_next)))
             (a,did) = SOME (aid,c) ==> c+32 <= t.vs_alloca_next+32` by
           (qpat_x_assum `t.vs_alloca_next = _` kall_tac >>
            qpat_x_assum `t.vs_alloca_next + 32 = _` kall_tac >>
            rpt gen_tac >> simp[NoAsms, FLOOKUP_UPDATE] >>
            Cases_on `inst.inst_id = did` >- simp[] >>
            simp[] >> strip_tac >>
            `c+32 <= t.vs_alloca_next` by metis_tac[] >> decide_tac) >>
         qexists_tac `t.vs_alloca_next` >>
         qpat_x_assum `t.vs_alloca_next = _` kall_tac >>
         fs[IgnAsm `s1 = _`, FLOOKUP_UPDATE] >>
         qpat_assum `t.vs_alloca_next + 32 = _`
           (fn th => pure_rewrite_tac[GSYM th]) >>
         simp[NoAsms] >> metis_tac[]) >>
     PairCases_on `x'` >>
     `ld_joint_scratch u fn inst.inst_id x'0` by metis_tac[] >>
     `ALL_DISTINCT (fn_ir_inst_ids fn)` by
       (qpat_assum `wf_function fn`
          (mp_tac o REWRITE_RULE [wf_function_def, fn_inst_ids_distinct_def]) >>
        simp[fn_ir_inst_ids_def, lambdify block_ir_inst_ids_def]) >>
     `x'0 = (HD es).inst_id` by metis_tac[ld_joint_scratch_functional] >>
     `FLOOKUP t.vs_allocas (HD es).inst_id = SOME (x'1,32)` by
       metis_tac[ld_scratch_allocation_present] >>
     `x'1+32 < dimword(:256)` by
       (`x'1+32 <= t.vs_alloca_next` by metis_tac[] >> decide_tac) >>
     qexistsl_tac [`x'1`, `X`, `t`] >>
     simp[IgnAsm `s1 = _`, IgnAsm `t.vs_alloca_next = _`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `t.vs_alloca_next = _` mp_tac >>
     pure_rewrite_tac[listTheory.MEM] >> decide_tac) >>
  (drule (REWRITE_RULE [EL] (BETA_RULE (PURE_REWRITE_RULE [LET_THM] ld_joint_supply_dload_transport))) >>
   disch_then (drule_at (Pat `lower_dload_inst_supply _ _ = _`)) >>
   disch_then (drule_at (Pat `ld_joint_geometry sites X1 lo _`)) >>
   disch_then (drule_at (Pat `step_inst _ _ _ _ = OK s1`)) >>
   disch_then (drule_at (Pat `FLOOKUP X1 _ = SOME _`)) >>
   disch_then (drule_at (Pat `fresh_ir_var v = _`)) >>
   disch_then (drule_at (Pat `fresh_ir_var v1 = _`)) >>
   disch_then (drule_at (Pat `inst.inst_operands = _`)) >>
   disch_then (drule_at (Pat `inst.inst_outputs = _`)) >>
   disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
   (impl_tac >- simp[IgnAsm `s1 = _`, IgnAsm `ta = _`, IgnAsm `X1 = _`,
        IgnAsm `t.vs_alloca_next = _`, EL]) >>
   strip_tac >>
   qmatch_asmsub_abbrev_tac `step_inst fuel C' (HD es) t = OK t1` >>
   qmatch_asmsub_abbrev_tac `step_inst fuel C' (EL 1 es) t1 = OK t2` >>
   qmatch_asmsub_abbrev_tac `step_inst fuel C' (EL 2 es) t2 = OK t3` >>
   qmatch_asmsub_abbrev_tac `ld_env_agree sites fn _ _ s1 t4` >>
   `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
     inst.inst_opcode <> ALLOCA` by simp[is_terminator_def] >>
   `occ_frame_reachable vs C stk PG (step_prov PG G inst s1)
     (step_taint inst s s1 tn) fn inst2
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP
     (occurrence_step a HP H inst s1)` by
     (drule_all occ_frame_reachable_next >> simp[occurrence_sites_step_def] >> gvs[]) >>
   `occurrence_annotation_ok n a U B HP (occurrence_step a HP H inst s1)
     stk PG (step_prov PG G inst s1)
     (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
     (drule occurrence_annotation_next >>
      disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
      simp[occurrence_sites_step_def] >> gvs[]) >>
   qexistsl_tac [`inst2`,`es`,`t1`,`t2`,`t3`,`t4`,`fn'`,`bb'`,`X1`] >>
   `TAKE 4 (DROP t.vs_inst_idx bb'.bb_instructions) = es` by metis_tac[] >>
   simp[IgnAsm `s1 = _`, IgnAsm `ta = _`, IgnAsm `X1 = _`,
        IgnAsm `t.vs_alloca_next = _`, EL, ld_joint_boundary_def] >>
   conj_tac
   >- (qexists_tac `u` >>
       `active_inst fn inst2 (s with vs_inst_idx := SUC s.vs_inst_idx)` by
         (qpat_x_assum `active_inst fn inst2 _` mp_tac >>
          simp[update_var_def, active_inst_def]) >>
       `ld_joint_control u fn fn' (s with vs_inst_idx := SUC s.vs_inst_idx)
         (t with vs_inst_idx := t.vs_inst_idx+4)` by metis_tac[] >>
       simp[IgnAsm `s1 = _`, IgnAsm `ta = _`, IgnAsm `X1 = _`,
            IgnAsm `t.vs_alloca_next = _`, ld_joint_frame_def] >>
       conj_tac
       >- (qpat_x_assum `ld_env_agree sites fn (occurrence_step _ _ _ _ _) _ _ _` mp_tac >>
           simp[IgnAsm `s1 = _`, ld_env_agree_def, op_taint_def]) >>
       `t4.vs_allocas = ta.vs_allocas /\ t4.vs_alloca_next = ta.vs_alloca_next` by
         (qpat_assum `ta = _` (fn th => pure_rewrite_tac[th]) >>
          simp[IgnAsm `t.vs_alloca_next = _`, IgnAsm `ta.vs_alloca_next = _`,
               Abbr `t4`, Abbr `t3`, Abbr `t2`, Abbr `t1`,
               write_memory_with_expansion_def, update_var_def]) >>
       `s1.vs_alloca_next = s.vs_alloca_next` by simp[update_var_def] >>
       conj_tac
       >- (qpat_assum `ld_params_agree sites HP s t`
             (mp_tac o REWRITE_RULE [ld_params_agree_def]) >>
           qpat_assum `s1 = _` (fn th => pure_rewrite_tac[th]) >>
           Cases_on `FLOOKUP t.vs_allocas (HD es).inst_id = NONE` >>
           simp[IgnAsm `ta = _`, IgnAsm `X1 = _`,
                IgnAsm `t.vs_alloca_next = _`, IgnAsm `ta.vs_alloca_next = _`,
                ld_params_agree_def, Abbr `t4`, Abbr `t3`, Abbr `t2`, Abbr `t1`,
                update_var_def, write_memory_with_expansion_def]) >>
       conj_tac
       >- (qpat_assum `ld_joint_local_fields s t`
             (mp_tac o REWRITE_RULE [ld_joint_local_fields_def]) >>
           qpat_assum `s1 = _` (fn th => pure_rewrite_tac[th]) >>
           Cases_on `FLOOKUP t.vs_allocas (HD es).inst_id = NONE` >>
           simp[IgnAsm `ta = _`, IgnAsm `X1 = _`,
                IgnAsm `t.vs_alloca_next = _`, IgnAsm `ta.vs_alloca_next = _`,
                ld_joint_local_fields_def, Abbr `t4`, Abbr `t3`, Abbr `t2`, Abbr `t1`,
                update_var_def, write_memory_with_expansion_def]) >>
       conj_tac
       >- (qpat_x_assum `ld_joint_control u _ _ (_ with vs_inst_idx := _) _` mp_tac >>
           simp[NoAsms, ld_joint_control_def, Abbr `t4`, Abbr `t3`, Abbr `t2`, Abbr `t1`,
                update_var_def, write_memory_with_expansion_def] >>
           strip_tac >>
           Cases_on `FLOOKUP t.vs_allocas (HD es).inst_id = NONE` >>
           simp[IgnAsm `t.vs_alloca_next = _`, update_var_def] >> metis_tac[]) >>
       conj_tac
       >- (qpat_assum `ld_joint_allocas sites X1 a fn ta`
             (mp_tac o REWRITE_RULE [ld_joint_allocas_def]) >>
           simp[IgnAsm `ta = _`, IgnAsm `X1 = _`, ld_joint_allocas_def] >>
           metis_tac[]) >>

       conj_tac >- (qpat_assum `s1.vs_alloca_next = _`
           (fn th => pure_rewrite_tac[th]) >>
         qpat_assum `t4.vs_alloca_next = _`
           (fn th => pure_rewrite_tac[th]) >>
         metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
       conj_tac >- (qpat_assum `t4.vs_alloca_next = _`
         (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
       simp[IgnAsm `s1 = _`, IgnAsm `ta = _`, IgnAsm `X1 = _`,
            IgnAsm `t.vs_alloca_next = _`, IgnAsm `ta.vs_alloca_next = _`] >>
       qpat_assum `ta.vs_alloca_next = _` mp_tac >>
       pure_rewrite_tac[listTheory.MEM] >> decide_tac) >>
   Cases_on `FLOOKUP t.vs_allocas (HD es).inst_id = NONE` >>
   qpat_assum `ld_shared_agree D _ tn s t`
     (mp_tac o REWRITE_RULE [ld_shared_agree_def]) >>
   simp[IgnAsm `t.vs_alloca_next = _`, IgnAsm `ta.vs_alloca_next = _`,
       Abbr `t4`, Abbr `t3`, Abbr `t2`, Abbr `t1`,
       write_memory_with_expansion_def, update_var_def, ld_shared_agree_def,
       step_taint_def, set_var_taint_def, store_taint_def, imm_taint_def,
       adopt_reset_def, DRESTRICT_UNIV])
QED
