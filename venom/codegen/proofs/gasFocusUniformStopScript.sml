Theory gasFocusUniformStop
Ancestors gasFocusPlainFrameInitialStatic[qualified] quantHeuristics[qualified,ignore_grammar]
  gasFocusJointProgress gasFocusProductionPacketCursorStatic gasFocusPlainEntry
  codegenEntryFacts[qualified] codegenEntrySim fnEntryParams fnFramePrefixStack
  fnPlanPlaceDfsBlock stackPlanGen
  gasFocusPlainGasPreEdge gasFocusGasPreEdge codegenAsmProgOk
  asmFinalizerPrefix asmFinalizerPrefixFrame
  gasFocusFalseCodegenContext gasFocusOptLabelFlow gasFocusOptStaticAssembly
  o1ContractCfgNormCursors cfgNormSupplySim
  dftFinitePacket dftGasFromListTraceDefs dftGasInvCrossingProbe dftDefs
  o1ContractCfgNormJointCursors frameJointTrace frameJointTransition
  fnFramePrefixDriver fnFrameSymbolicPrefix codegenEntryRel
  fnFramePrefixEntry fnFrameBoundaryEntryParams fnFramePrefix fnBlockBodySteps frameRel
  o1PipelineCorrect o1SafeUpto o1PassContract o1PassLift unitMemInv
  venomPipelineRunner venomPassSchedule irSupply fcgDefs
  dftGasOracleDefs gasEvents contextRawReachable memSafeRun
  venomExecSemantics venomExecProofs venomWf venomInst venomState unitShapeDefs
  codegenSymRel asmDataEnv asmFrameRel asmOptimizer asmSem asmSymSem symbolResolve
  contextCodegenRel codegenRel lowerDloadDefs staticAbortDefs frameOutcome callTrace
  o1RequestContract unitTransformDefs ptrDiscipline passSimulationDefs
  vfmExecution codegen asmIR
  finite_map list rich_list words arithmetic
  dftGasNativePrefixReplay dftGasInvReachSlice dftRunRel dftPacketCommonOracle
  dftGasInvExtraction dftGasInvInversion dftGasInvFlexibleTrace dftGasInvFuel
  dftScheduleOrder dftWf sorting
  dftGasInvOracleFrame[qualified] dftGasFromListRestore[qualified]
  venomEffects[qualified] opcodeClass[qualified] oracleExecProps[qualified]

(* Split blocks introduce administrative instructions. The only original
   instructions whose syntax can change are PHIs and branches. *)
Theorem focus_cfg_norm_cursor_instruction[local]:
  !C rounds cursors. cfg_norm_cursors C rounds cursors ==>
    FST (FST (LAST cursors)) = FST (FST (HD cursors)) \/
    MEM (FST (FST (LAST cursors))).inst_opcode [PHI; ASSIGN; JMP; JNZ]
Proof
  ho_match_mp_tac cfg_norm_cursors_ind >>
  simp_tac bool_ss [HD,LAST_CONS,pairTheory.FST,NOT_CONS_NIL] >>
  conj_tac >> rpt gen_tac >> DISCH_THEN (CONJUNCTS_THEN assume_tac)
  >- (gvs[] >>
      qabbrev_tac `i = EL v.vs_inst_idx bb.bb_instructions` >>
      qabbrev_tac `u = EL v.vs_inst_idx
        (supply_block_image pred target split repls bb).bb_instructions` >>
      `u.inst_opcode = i.inst_opcode` by
        metis_tac[supply_block_image_index,Abbr`u`,Abbr`i`] >>
      Cases_on `MEM i.inst_opcode [PHI; JMP; JNZ]`
      >- (fs[] >> metis_tac[]) >>
      `label_positions_ok i` by
        (fs[EVERY_MEM,fn_insts_def] >>
         metis_tac[MEM_fn_insts_blocks,EL_MEM,Abbr`i`]) >>
      `u = i` by
        metis_tac[o1ContractCfgNormTheory.supply_block_image_index_unchanged,
                  Abbr`u`,Abbr`i`] >>
      metis_tac[])
  >> gvs[]
  >> `ir_supply_inst_ok s /\ ir_supply_covers_fn s fn` by fs[supply_norm_inv_def]
  >> drule_all supply_split_index_shape >> simp[] >> metis_tac[]
QED

(* A successful split block cannot hide a stopped step at its cursor. *)
Theorem focus_split_cursor_step[local]:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
  build_split_block_supply s pred target = (split,repls,s') /\
  v.vs_inst_idx < LENGTH split.bb_instructions /\
  inst = EL v.vs_inst_idx split.bb_instructions /\
  supply_state_agree fn a v /\ ~a.vs_halted /\
  exec_block fuel C split v = OK m ==>
  inst.inst_opcode <> INVOKE /\
  ?w. step_inst fuel C inst v = OK w /\ ~w.vs_halted
Proof
  strip_tac >>
  `~v.vs_halted` by metis_tac[supply_state_agree_halted] >>
  drule_all supply_split_index_shape >> disch_then assume_tac >>
  `inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[]) >>
  simp[] >>
  `?w. step_inst fuel C inst v = OK w` by
    (Cases_on `step_inst fuel C inst v` >> simp[] >>
     qpat_x_assum `exec_block fuel C split v = OK m`
       (mp_tac o ONCE_REWRITE_RULE [exec_block_def]) >>
     gvs[get_instruction_def]) >>
  qexists `w` >> conj_tac >- metis_tac[] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (drule_all supply_exec_block_step_residual >> gvs[]) >>
  drule_all supply_split_step_agree >> simp[]
QED

Theorem focus_cursor_body_result[local]:
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  MEM bb fn.fn_blocks /\ a.vs_inst_idx < LENGTH bb.bb_instructions /\
  phi_prefix_length bb.bb_instructions <= a.vs_inst_idx /\
  inst = EL a.vs_inst_idx bb.bb_instructions /\
  next = EL v.vs_inst_idx
    (supply_block_image pred target split repls bb).bb_instructions /\
  a.vs_current_bb = v.vs_current_bb /\ a.vs_inst_idx = v.vs_inst_idx /\
  supply_state_agree fn a v ==>
  next.inst_opcode = inst.inst_opcode /\
  lift_result (\u w. u.vs_halted = w.vs_halted) (\u w. T) (\u w. T)
    (step_inst fuel C inst a) (step_inst fuel C next v)
Proof
  strip_tac >>
  conj_tac >- metis_tac[supply_block_image_index] >>
  `MEM inst bb.bb_instructions` by metis_tac[EL_MEM] >>
  `wf_function fn /\ fn_inst_wf fn` by fs[supply_norm_inv_def] >>
  `inst_wf inst` by metis_tac[fn_inst_wf_def] >>
  `label_positions_ok inst` by
    (fs[EVERY_MEM,fn_insts_def] >> metis_tac[MEM_fn_insts_blocks]) >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `inst.inst_opcode <> PHI` by
    (fs[bb_well_formed_def] >> metis_tac[fnBlockBodyStepsTheory.phi_prefix_not_phi]) >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (drule_all supply_block_image_step_terminator >>
      disch_then (qspecl_then [`target`,`split`,`repls`,`pred`,`fuel`,`C`] mp_tac) >>
      Cases_on `step_inst fuel C inst a` >> Cases_on `step_inst fuel C next v` >>
      gvs[stateEquivTheory.lift_result_def] >> metis_tac[supply_state_agree_halted]) >>
  gvs[] >> drule_all supply_block_image_step_body >>
  disch_then (qspecl_then [`target`,`split`,`repls`,`pred`,`fuel`,`C`] mp_tac) >>
  qmatch_goalsub_rename_tac `lift_result _ _ _ res1 res2` >>
  Cases_on `res1` >> Cases_on `res2` >>
  gvs[stateEquivTheory.lift_result_def] >> metis_tac[supply_state_agree_halted]
QED

Theorem focus_cursor_native_result[local]:
  !C rounds cursors. cfg_norm_cursors C rounds cursors ==>
  !fuel. (FST (FST (HD cursors))).inst_opcode <> INVOKE ==>
    (FST (FST (LAST cursors))).inst_opcode <> INVOKE /\
    lift_result (\u v. u.vs_halted = v.vs_halted) (\u v. T) (\u v. T)
      (step_inst fuel C (FST (FST (HD cursors))) (SND (FST (HD cursors))))
      (step_inst fuel C (FST (FST (LAST cursors))) (SND (FST (LAST cursors))))
Proof
  ho_match_mp_tac cfg_norm_cursors_ind >>
  simp_tac bool_ss [HD,LAST_CONS,pairTheory.FST,pairTheory.SND,NOT_CONS_NIL,
    passSimulationProofsTheory.lift_result_refl_proof] >>
  conj_tac >> rpt gen_tac >> strip_tac >> gen_tac >> disch_tac
  >- (qabbrev_tac `inst = EL v.vs_inst_idx bb.bb_instructions` >>
      qabbrev_tac `next = EL v.vs_inst_idx (supply_block_image pred target split repls bb).bb_instructions` >>
      `next.inst_opcode = inst.inst_opcode /\
       lift_result (\u v. u.vs_halted = v.vs_halted) (\u v. T) (\u v. T)
         (step_inst fuel C inst a) (step_inst fuel C next v)` by
        (irule focus_cursor_body_result >> simp[] >>
         qexistsl [`bb`,`fn`,`pred`,`repls`,`s`,`split`,`target`] >>
         simp[Abbr `inst`,Abbr `next`]) >>
      first_x_assum (qspec_then `fuel` mp_tac) >> simp[] >> strip_tac >>
      irule (SIMP_RULE (srw_ss()) []
        (Q.SPECL [`\u v. u.vs_halted = v.vs_halted`, `\(u:venom_state) (v:venom_state). T`,
                  `\(u:venom_state) (v:venom_state). T`]
          passSimulationProofsTheory.lift_result_trans_proof)) >>
      goal_assum (drule_at Any) >> simp[]) >>
  qpat_assum `!n ctx. ?m. _` (qspecl_then [`fuel`,`C`] strip_assume_tac) >>
  `ir_supply_inst_ok s /\ ir_supply_covers_fn s fn` by fs[supply_norm_inv_def] >>
  qabbrev_tac `next = EL v.vs_inst_idx split.bb_instructions` >>
  `next.inst_opcode <> INVOKE /\
   ?w. step_inst fuel C next v = OK w /\ ~w.vs_halted` by
    (irule focus_split_cursor_step >> fs[Abbr `next`] >> metis_tac[]) >>
  `step_inst fuel C inst a = OK u` by
    fs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  qpat_assum `!f. next.inst_opcode <> INVOKE ==> _`
    (qspec_then `fuel` (strip_assume_tac o UNDISCH)) >>
  qabbrev_tac `r = step_inst fuel C (FST (FST (LAST (((next,v),pending)::cursors))))
    (SND (FST (LAST (((next,v),pending)::cursors))))` >>
  Cases_on `r` >> gvs[stateEquivTheory.lift_result_def]
QED

Theorem focus_current_instruction[local]:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ==>
  active_inst fn9 inst9 s9 /\ ~s9.vs_halted /\
  (inst9 = inst8 \/ MEM inst9.inst_opcode [PHI; ASSIGN; JMP; JNZ])
Proof
  PairCases_on `current` >>
  simp[cfg_norm_joint_cursors_def] >> strip_tac >>
  qpat_x_assum `EVERY _ schedules`
    (drule_then strip_assume_tac o REWRITE_RULE [EVERY_MEM]) >>
  drule_then strip_assume_tac cfg_norm_cursors_last >>
  drule focus_cfg_norm_cursor_instruction >>
  gvs[]
QED

Theorem focus_active_var_ready[local]:
  supply_norm_inv supply fn /\ supply_prefix_defined fn s /\
  active_inst fn inst s /\ inst.inst_opcode <> PHI /\
  MEM (Var x) inst.inst_operands ==>
  eval_operand (Var x) s <> NONE
Proof
  simp[eval_operand_def,lookup_var_def,FLOOKUP_DEF,active_inst_def] >>
  strip_tac >>
  `wf_function fn /\ def_dominates_uses fn` by
    fs[supply_norm_inv_def,wf_ssa_def] >>
  `MEM inst bb.bb_instructions` by metis_tac[EL_MEM] >>
  `def_available_at fn bb (SOME inst) x` by
    metis_tac[def_dominates_uses_def] >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  Cases_on `def_bb = bb`
  >- (gvs[] >>
      `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
        metis_tac[wf_function_def,venomFnInstsProofsTheory.fn_inst_ids_block_distinct] >>
      `j = s.vs_inst_idx` by
        (qpat_x_assum `ALL_DISTINCT _`
           (mp_tac o SIMP_RULE (srw_ss()) [EL_ALL_DISTINCT_EL_EQ,EL_MAP]) >>
         metis_tac[]) >>
      gvs[supply_prefix_defined_def] >> first_x_assum irule >>
      qexistsl [`bb`,`i`] >> simp[]) >>
  `def_bb.bb_label <> s.vs_current_bb` by metis_tac[same_label_same_block] >>
  fs[supply_prefix_defined_def,supply_entry_defined_def] >>
  metis_tac[venomWfPropsTheory.strict_dom_vars_defined_def]
QED

Theorem focus_joint_cursor_native_result[local]:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  inst8.inst_opcode <> INVOKE ==>
  inst9.inst_opcode <> INVOKE /\
  lift_result (\u v. u.vs_halted = v.vs_halted) (\u v. T) (\u v. T)
    (step_inst fuel C8 inst8 s8) (step_inst 0 C9 inst9 s9)
Proof
  PairCases_on `current` >> simp[cfg_norm_joint_cursors_def] >> strip_tac >>
  drule focus_cursor_native_result >> disch_then (qspec_then `fuel` mp_tac) >>
  simp[step_inst_non_invoke] >> strip_tac >>
  qpat_x_assum `lift_result _ _ _ _ _` mp_tac >> simp[step_inst_non_invoke]
QED

Theorem focus_revert_forward_observation[local]:
  wf_function fn /\ active_inst fn inst s /\ in_revert_forward fn s ==>
  inv_memory_observation inst.inst_opcode
Proof
  strip_tac >>
  fs[active_inst_def, in_revert_forward_def, revert_forward_at_def] >>
  `MEM bb' fn.fn_blocks /\ bb'.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `bb' = bb` by metis_tac[same_label_same_block] >>
  gvs[get_instruction_def, revert_forward_pair_def, inv_memory_observation_def,
      AllCaseEqs()]
QED

Theorem focus_ungated_current_guards[local]:
  wf_function fn9 /\ inst_shape_ok inst9 /\ active_inst fn9 inst9 s9 /\
  (inst9 = inst8 \/ MEM inst9.inst_opcode [PHI; ASSIGN; JMP; JNZ]) /\
  ~(inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
    inst8.inst_opcode = INVOKE \/ is_terminator inst8.inst_opcode) ==>
  ~in_revert_forward fn9 s9 /\ inst9.inst_opcode <> CODECOPY /\
  source_memory_reads_disjoint cpl inst9 s9 /\
  context_source_memory_writes_disjoint cpl inst9 s9
Proof
  strip_tac >>
  `~inv_memory_observation inst9.inst_opcode` by
    (gvs[inv_memory_observation_def] >> metis_tac[]) >>
  `inst9.inst_opcode <> CODECOPY` by fs[inv_memory_observation_def] >>
  `~in_revert_forward fn9 s9` by metis_tac[focus_revert_forward_observation] >>
  `inst_mem_ranges inst9 s9 = []` by
    metis_tac[inv_memory_observation_covers_ranges] >>
  fs[inst_mem_ranges_def, source_memory_reads_disjoint_def,
     context_source_memory_writes_disjoint_def]
QED

(* The terminator is last in both rows. Every earlier source index
   therefore occurs in the scheduled prefix, even if INVOKEs moved. *)
Theorem focus_ordered_terminal_cut[local]:
  bb_well_formed bb /\ bb_well_formed bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  PERM row_order (COUNT_LIST (LENGTH xs)) /\ ix < LENGTH ys /\
  LIST_REL (\q y. q < LENGTH xs /\
    y.inst_id = (EL q xs).inst_id /\ from_block [EL q xs] y) row_order ys /\
  inst = EL ix ys /\ is_terminator inst.inst_opcode ==>
  EL ix row_order < LENGTH xs /\ EL (EL ix row_order) xs = inst /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (EL ix row_order) xs) /\
  (!r. r < EL ix row_order ==> MEM r (TAKE ix row_order))
Proof
  strip_tac >>
  `LENGTH row_order = LENGTH ys` by fs[LIST_REL_EL_EQN] >>
  `EL ix row_order < LENGTH xs /\ from_block [EL (EL ix row_order) xs] inst` by
    (fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  `EL (EL ix row_order) xs = inst` by
    (fs[dftStructuralTheory.from_block_def] >>
     metis_tac[inv_ev_flip_nonterminator]) >>
  `is_terminator (EL ix ys).inst_opcode /\
   is_terminator (EL (EL ix row_order) xs).inst_opcode` by metis_tac[] >>
  simp[] >>
  `SUC ix = LENGTH ys` by
    (qpat_x_assum `bb_well_formed bt` mp_tac >>
     simp[bb_well_formed_def] >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH ps + LENGTH ys /\ _ ==> _`
       (qspec_then `LENGTH ps + ix` mp_tac) >>
     simp[EL_APPEND2] >> decide_tac) >>
  conj_tac
  >- (simp[EVERY_EL,EL_TAKE,LENGTH_TAKE_EQ] >> rpt strip_tac >>
      qpat_x_assum `bb_well_formed bb`
        (strip_assume_tac o REWRITE_RULE [bb_well_formed_def]) >>
      qpat_x_assum `!i. i < LENGTH bb.bb_instructions /\ _ ==> _`
        (fn th => mp_tac (Q.SPEC `LENGTH (ps:instruction list) + n` th) >>
                  mp_tac (Q.SPEC `LENGTH (ps:instruction list) + EL ix row_order` th)) >>
      simp[EL_APPEND_EQN] >> decide_tac) >>
  rpt strip_tac >>
  `MEM r row_order` by metis_tac[PERM_MEM_EQ,MEM_COUNT_LIST,LESS_TRANS] >>
  qpat_x_assum `MEM r row_order` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  `n < ix` by (CCONTR_TAC >> `n = ix` by decide_tac >> gvs[]) >>
  simp[MEM_EL,LENGTH_TAKE_EQ] >> qexists `n` >> simp[EL_TAKE]
QED

Theorem focus_guarded_singleton[local]:
  from_block [i] inst /\ (is_fallible inst \/ inst.inst_opcode = INVOKE) ==>
  i = inst
Proof
  rw[dftStructuralTheory.from_block_def] >>
  Cases_on `i.inst_operands` >> gvs[dftDefsTheory.flip_operands_def] >>
  Cases_on `t` >> gvs[dftDefsTheory.flip_operands_def] >>
  Cases_on `t'` >> gvs[dftDefsTheory.flip_operands_def] >>
  Cases_on `i.inst_opcode` >>
  gvs[dftDefsTheory.is_fallible_def, venomEffectsTheory.opcode_fail_class_def,
      dftDefsTheory.is_flippable_def, venomEffectsTheory.is_commutative_def,
      passSharedDefsTheory.is_comparator_def, passSharedDefsTheory.flip_comparison_opcode_def]
QED

Theorem focus_selectable_opcode_not_pseudo[local]:
  inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
  inst.inst_opcode = INVOKE \/ is_terminator inst.inst_opcode ==>
  ~is_pseudo inst.inst_opcode
Proof
  Cases_on `inst.inst_opcode` >>
  simp[inv_memory_observation_def,is_fallible_def,venomEffectsTheory.opcode_fail_class_def,
       is_terminator_def,is_pseudo_def]
QED

(* Select cuts even in a revert-forwarding row: the retained memory
   predecessor clause has no non-forwarding hypothesis. *)
Theorem focus_current_row_cut[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs hist) raw_slots sites unused /\
  (inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
   inst.inst_opcode = INVOKE \/ is_terminator inst.inst_opcode) ==>
  ?sf inc entry order bb bt ps xs ys row_order in_state h0 body ix q z.
    FLOOKUP acts p = SOME (sf,fn,inc,entry,order,NONE,NONE) /\
    FLOOKUP blocks (p,d) =
      SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body,ix,OK s,F,NONE) /\
    get_instruction bt s.vs_inst_idx = SOME inst /\
    IS_SOME body /\ s.vs_inst_idx = LENGTH ps + ix /\ ix < LENGTH row_order /\
    q = EL ix row_order /\ q < LENGTH xs /\ EL q xs = inst /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
    (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE ix row_order))
Proof
  disch_then (CONJUNCTS_THEN2
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) assume_tac) >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `FLOOKUP acts p = _` mp_tac >>
  qpat_x_assum `FLOOKUP blocks (p,d) = _` mp_tac >>
  qpat_x_assum `get_instruction _ _ = _` mp_tac >>
  qpat_x_assum `case body_entry of NONE => _ | SOME v => _` mp_tac >>
  qpat_x_assum `o1_ctx_shape C8` mp_tac >>
  qpat_x_assum `LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions` mp_tac >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry c front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,c,front,closed,brest) ==>
    ?sf tf inc entry order res nrest sp. _` mp_tac >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` mp_tac >>
  qpat_x_assum `!bb bt ps xs ys row_order in_state h0 be hbe c sf inc entry order.
    FLOOKUP acts p = _ /\ FLOOKUP blocks (p,d) = _ /\ inv_memory_observation _ ==> _` mp_tac >>
  qpat_x_assum `_ \/ _ \/ _ \/ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> disch_then (mk_asm "gate") >> rpt disch_tac >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _`
    (strip_assume_tac o SRULE []) >>
  gnvs[] >>
  Cases_on `body_entry`
  >- (gvs[] >>
      qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry c front closed brest.
        FLOOKUP blocks (a,e) = _ ==> _` (drule_then strip_assume_tac) >>
      `is_pseudo inst.inst_opcode` by gvs[get_instruction_def,EL_APPEND_EQN,EVERY_EL] >>
      asm_x "gate" assume_tac >>
      drule focus_selectable_opcode_not_pseudo >> simp[]) >>
  PairCases_on `x` >> gvs[] >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry c front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _` drule >> strip_tac >> gnvs[] >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = _ ==> _` drule >> strip_tac >>
  `count' < LENGTH rho' /\ EL count' rho' < LENGTH xs /\
    from_block [EL (EL count' rho') xs] (EL count' ys)` by
    (qpat_assum `LIST_REL _ rho' ys` (mp_tac o SRULE [LIST_REL_EL_EQN]) >>
     disch_then (CONJUNCTS_THEN2 assume_tac (qspec_then `count'` mp_tac)) >> simp[]) >>
  simp[] >> asm_x "gate" assume_tac >>
  Cases_on `inv_memory_observation (EL count' ys).inst_opcode`
  >- gvs[] >>
  Cases_on `is_fallible (EL count' ys) \/ (EL count' ys).inst_opcode = INVOKE`
  >- (`EL (EL count' rho') xs = EL count' ys` by
        metis_tac[focus_guarded_singleton] >>
      simp[] >> irule dft_packet_schedule_predecessors >>
      rpt (first_assum (irule_at Any)) >> simp[]) >>
  `is_terminator (EL count' ys).inst_opcode` by metis_tac[] >>
  `MEM fn C8.ctx_functions` by
    (drule_all LIST_REL_MEM_IMP >> simp[]) >>
  `wf_function sf /\ wf_function fn` by
    (qpat_assum `dft_fn_rel sf fn` (mp_tac o SRULE [dft_fn_rel_def]) >>
     qpat_assum `o1_ctx_shape C8` (mp_tac o SRULE [o1_ctx_shape_def, EVERY_MEM]) >>
     rpt strip_tac >> fs[o1_fn_shape_def]) >>
  `bb_well_formed bb /\ bb_well_formed bt` by
    (conj_tac >> irule (cj 3 (iffLR wf_function_def)) >>
     metis_tac[lookup_block_MEM]) >>
  `EL count' rho' < LENGTH xs /\ EL (EL count' rho') xs = EL count' ys /\
   EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (EL count' rho') xs) /\
   (!r. r < EL count' rho' ==> MEM r (TAKE count' rho'))` by
    (irule (SIMP_RULE bool_ss []
      (Q.INST [`inst` |-> `EL ix ys`] focus_ordered_terminal_cut)) >>
     simp[] >> qexistsl [`bb`,`bt`,`ps`] >> simp[]) >>
  simp[]
QED

Theorem focus_root_cursor_no_intret[local]:
  joint_trace vs0 C q0 evs qs (JointConfig [] PG G tn fn inst s oms om hs h) /\
  C.ctx_entry = SOME entry /\ o1_fn_shape C fn /\ active_inst fn inst s ==>
  step_inst fuel C inst s <> IntRet ir u
Proof
  strip_tac >> strip_tac >>
  drule joint_trace_reachable >> simp[joint_config_reachable_def] >>
  disch_then (mp_tac o MATCH_MP frameOriginHistoryTheory.joint_origin_history_erasure) >>
  disch_then (mp_tac o MATCH_MP frameOriginReachableTheory.origin_frame_erasure) >>
  disch_then (mp_tac o MATCH_MP fmpStageRunnerFactsTheory.fmp_frame_reachable_entry_last) >>
  simp[] >> strip_tac >>
  `entry_fn_no_return fn` by fs[o1_fn_shape_def] >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def,fn_insts_def,MEM_fn_insts_blocks_iff] >>
     qexists `bb` >> simp[] >> metis_tac[EL_MEM]) >>
  drule o1ContractSimplifyCfgSrcFrameTheory.step_inst_intret_opcodes >>
  fs[entry_fn_no_return_def,EVERY_MEM,PULL_FORALL] >> metis_tac[]
QED

Theorem focus_stopped_base_row[local]:
  (inst9 = inst8 \/ MEM inst9.inst_opcode [PHI; ASSIGN; JMP; JNZ]) /\
  ((?u. step_inst_base inst9 s9 = Halt u) \/
   (?ex u. step_inst_base inst9 s9 = Abort ex u)) ==>
  inst9 = inst8 /\ inst8.inst_opcode <> INVOKE /\
  (is_fallible inst8 \/ is_terminator inst8.inst_opcode)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac)
  >- (drule opcodeClassTheory.step_inst_base_halt_opcodes >>
      strip_tac >> gvs[is_terminator_def]) >>
  drule opcodeClassTheory.step_inst_base_abort_opcodes >> strip_tac >>
  gvs[is_fallible_def,venomEffectsTheory.opcode_fail_class_def,is_terminator_def] >>
  metis_tac[]
QED

Theorem focus_native_stop_transfer[local]:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  inst9.inst_opcode <> INVOKE /\
  ((?u. step_inst 0 C9 inst9 s9 = Halt u) \/
   (?ex u. step_inst 0 C9 inst9 s9 = Abort ex u)) ==>
  inst9 = inst8 /\ inst8.inst_opcode <> INVOKE /\
  (is_fallible inst8 \/ is_terminator inst8.inst_opcode) /\
  ((?u. step_inst fuel C8 inst8 s8 = Halt u) \/
   (?ex u. step_inst fuel C8 inst8 s8 = Abort ex u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule focus_current_instruction >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `inst9 = inst8 /\ inst8.inst_opcode <> INVOKE /\
   (is_fallible inst8 \/ is_terminator inst8.inst_opcode)` by
    (irule focus_stopped_base_row >> simp[] >>
     qexists `s9` >> gnvs[step_inst_non_invoke]) >>
  gnvs[] >> drule_all focus_joint_cursor_native_result >>
  disch_then (qspec_then `fuel` mp_tac) >>
  Cases_on `step_inst fuel C8 inst8 s8` >>
  Cases_on `step_inst 0 C9 inst8 s9` >> gvs[stateEquivTheory.lift_result_def]
QED

Theorem focus_cursor_noninvoke_cases[local]:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  joint_trace vs0 C9 q0 evs qs (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  C9.ctx_entry = SOME entry /\ o1_fn_shape C9 fn9 /\ inst9.inst_opcode <> INVOKE ==>
  ((?u. step_inst 0 C9 inst9 s9 = OK u /\ ~u.vs_halted) \/
   (stk9 <> [] /\ ?ir u. step_inst 0 C9 inst9 s9 = IntRet ir u)) \/
  (inst9 = inst8 /\ inst8.inst_opcode <> INVOKE /\
   (is_fallible inst8 \/ is_terminator inst8.inst_opcode) /\
   ((?u. step_inst fuel C8 inst8 s8 = Halt u) \/
    (?ex u. step_inst fuel C8 inst8 s8 = Abort ex u))) \/
  (?err. step_inst 0 C9 inst9 s9 = Error err)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (map_every assume_tac o CONJUNCTS) focus_current_instruction >>
  Cases_on `step_inst 0 C9 inst9 s9` >> simp[]
  >- (disj1_tac >>
      metis_tac[step_inst_non_invoke,step_inst_base_OK_preserves_halted])
  >- metis_tac[focus_native_stop_transfer]
  >- metis_tac[focus_native_stop_transfer]
  >- (disch_tac >> gvs[] >> metis_tac[focus_root_cursor_no_intret])
QED

(* Readiness at a reached GAS does not require a selectable packet cut. *)
Theorem focus_cursor_gas_available[local]:
  generate_context_plan u.cu_context = SOME cpl /\
  codegen_assembly rp u = SOME prog /\ unit_shape_ok u /\
  fin IN accepted_finalizers /\ fin rp prog = SOME prog' /\
  (fin = asm_opt_finalizer ==>
    codegen_ready u.cu_context /\ focus_s7_symbolic_context u prog) /\
  vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es0
    (entry_asm_state vs0 es0 with as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
  run_call es0 = SOME (result,final) /\ ~frame_resource_starved es0 result final /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog n (entry_asm_state vs0 es0) = AsmOK ast /\
  (fin = K SOME ==> normal_frame_plan rp u cpl prog
    (vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
                vs_return_pc_token := 0w; vs_inst_idx := 0|>) es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps prog (asm_data_env prog vs0.vs_code) n
      (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rp u cpl prog vs0 es0
      (JointConfig stk PG G tn fn inst s oms om hs h) ast ss) /\
  active_inst fn inst s /\ inst.inst_opcode = GAS ==>
  s.vs_gas_readings <> []
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
  pop_assum strip_assume_tac
  >- (`prog' = prog` by fs[combinTheory.K_THM] >>
      `(entry_asm_state vs0 es0 with as_code := assemble prog ++ vs0.vs_data_section) =
       entry_asm_state vs0 es0` by simp[entry_asm_state_def] >>
      `asm_frame_rel_tail [] prog vs0.vs_data_section es0 (entry_asm_state vs0 es0) es0`
        by fs[] >>
      `asm_frame_prog_ok prog` by metis_tac[codegen_assembly_frame_prog_ok] >>
      `normal_frame_plan rp u cpl prog
        (vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
                    vs_return_pc_token := 0w; vs_inst_idx := 0|>) es0
        (JointConfig stk PG G tn fn inst s oms om hs h) ast` by fs[] >>
      drule_all focus_plain_frame_gas_available >> simp[]) >>
  gvs[] >> drule_all focus_normal_frame_gas_available >>
  disch_then (qx_choose_then `bound` assume_tac) >>
  qpat_x_assum `!n ast ss stk PG G tn fn inst s oms om hs h. _`
    (assume_tac o SRULE [ASSUME ``vs0.vs_code = assemble prog ++ vs0.vs_data_section``]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem focus_after_params[local]:
  !xs. LENGTH (get_params xs) < LENGTH xs ==>
    ~is_param_opcode (EL (LENGTH (get_params xs)) xs).inst_opcode
Proof
  Induct >> simp[stackPlanGenTheory.get_params_def] >>
  rw[stackPlanGenTheory.get_params_def] >> gvs[]
QED

Theorem focus_entry_cursor_phase[local]:
  entry_frame_plan rp u cpl prog fn entry s ast ra pc_ret rest mem0 /\
  active_inst fn inst s /\ o1_fn_shape u.cu_context fn ==>
  (?post. step_inst fuel u.cu_context inst s = OK post) \/
  (inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode)
Proof
  strip_tac >>
  Cases_on `s.vs_inst_idx < LENGTH (get_params (HD fn.fn_blocks).bb_instructions)`
  >- (drule_all entry_frame_active_param >> strip_tac >>
      drule_all entry_frame_plan_next >> metis_tac[]) >>
  disj2_tac >>
  qpat_x_assum `entry_frame_plan _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [entry_frame_plan_def]) >>
  `s.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions)`
    by fs[] >>
  `wf_function fn /\ fn.fn_blocks <> [] /\ first_block_no_phi fn` by
    fs[o1_fn_shape_def,wf_function_def,fn_has_entry_def] >>
  `s.vs_current_bb = (HD fn.fn_blocks).bb_label` by
    fs[fn_entry_state_rel_def,entry_bind_pairs_normal] >>
  qpat_x_assum `active_inst fn inst s`
    (strip_assume_tac o REWRITE_RULE [active_inst_def]) >>
  `bb = HD fn.fn_blocks` by metis_tac[same_label_same_block,HEAD_MEM] >>
  conj_tac >- (fs[first_block_no_phi_def,EVERY_EL] >> metis_tac[]) >>
  metis_tac[focus_after_params]
QED

Theorem focus_body_cursor_phase[local]:
  active_frame_plan rp u cpl prog fn s ast ra rest mem0 /\
  active_inst fn inst s /\ wf_function fn ==>
  inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode
Proof
  simp[active_frame_plan_def] >> strip_tac >>
  qhdtm_assum `body_plan_inv`
    (strip_assume_tac o REWRITE_RULE [body_plan_inv_def]) >>
  fs[active_inst_def] >>
  `bb' = bb` by metis_tac[same_label_same_block,lookup_block_MEM,lookup_block_label] >>
  fs[] >> reverse conj_tac
  >- (drule (cj 4 body_plan_inv_static) >> simp[]) >>
  `bb_well_formed bb` by metis_tac[wf_function_def,lookup_block_MEM] >>
  fs[bb_well_formed_def] >> metis_tac[phi_prefix_not_phi]
QED

Theorem focus_frame_cursor_phase[local]:
  fin IN accepted_finalizers /\
  (fin = K SOME ==> normal_frame_plan rp u cpl prog entry0 es0
    (JointConfig stk PG G tn fn inst s oms om hs hist) ast) /\
  (fin = asm_opt_finalizer ==> normal_frame_symbolic_plan env rp u cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs hist) ast ss) /\
  active_inst fn inst s /\ o1_fn_shape u.cu_context fn ==>
  (?post. step_inst fuel u.cu_context inst s = OK post) \/
  (inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `wf_function fn` by fs[o1_fn_shape_def] >>
  `fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
  pop_assum strip_assume_tac >>
  fs[normal_frame_plan_def,normal_frame_symbolic_plan_def,
     active_frame_symbolic_plan_def,entry_frame_symbolic_plan_def] >>
  metis_tac[focus_entry_cursor_phase,focus_body_cursor_phase,active_frame_plan_def]
QED

(* For a branch only the condition is evaluated; its destination labels
   are not operands of the native evaluator. *)
Theorem focus_plain_body_not_error[local]:
  inst_wf inst /\ inst_shape_ok inst /\ inst.inst_opcode <> PHI /\
  ~is_param_opcode inst.inst_opcode /\
  ~(inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
    inst.inst_opcode = INVOKE \/
    (is_terminator inst.inst_opcode /\ ~MEM inst.inst_opcode [JMP; JNZ])) /\
  (!op. MEM op inst.inst_operands /\
        (~is_terminator inst.inst_opcode \/ ~is_label_operand op) ==>
        eval_operand op s <> NONE) ==>
  step_inst_base inst s <> Error err
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  fs[inv_memory_observation_def,is_fallible_def,
     venomEffectsTheory.opcode_fail_class_def,is_param_opcode_def,
     is_terminator_def] >>
  qpat_x_assum `inst_wf inst`
    (mp_tac o REWRITE_RULE [inst_wf_def]) >>
  asm_rewrite_tac [opcode_case_def] >>
  simp_tac std_ss [LENGTH_EQ_NUM_compute] >>
  disch_then strip_assume_tac >>
  ASM_SIMP_TAC std_ss [step_inst_base_opcode_eqs,
      exec_pure1_def,exec_pure2_def,exec_pure3_def,
      exec_read0_def,exec_read1_def,exec_gas_def,exec_alloca_def] >>
  qpat_x_assum `!op. _ ==> eval_operand op s <> NONE` mp_tac >>
  ASM_SIMP_TAC (srw_ss()) [DISJ_IMP_THM,FORALL_AND_THM] >>
  strip_tac >>
  ASM_SIMP_TAC (srw_ss()) [CaseEq "option"]
  >- (fs[inst_shape_ok_def,label_positions_ok_def] >>
      `eval_operand c s <> NONE` by metis_tac[] >>
      simp[COND_RATOR,COND_RAND])
  >> simp[CaseEq "list",pairTheory.FORALL_PROD]
QED

Theorem focus_cursor_ready_context[local]:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ==>
  C9.ctx_entry = C8.ctx_entry /\ MEM fn9 C9.ctx_functions /\
  supply_prefix_defined fn9 s9 /\ ?supply. supply_norm_inv supply fn9
Proof
  PairCases_on `current` >> simp[cfg_norm_joint_cursors_def] >> strip_tac >>
  qpat_x_assum `EVERY _ schedules`
    (drule_then strip_assume_tac o REWRITE_RULE [EVERY_MEM]) >>
  drule_then strip_assume_tac cfg_norm_cursors_last >>
  conj_tac
  >- (qpat_x_assum `MAP (FST o SND) schedules = _` (SUBST1_TAC o SYM) >>
      simp[MEM_MAP] >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> goal_assum drule
QED

Theorem focus_plain_cursor_operand[local]:
  supply_norm_inv supply fn /\ supply_prefix_defined fn s /\
  active_inst fn inst s /\ MEM inst (fn_insts fn) /\ MEM fn C.ctx_functions /\
  ctx_labels_bound C s.vs_labels /\ inst.inst_opcode <> PHI /\
  ~is_param_opcode inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> CODECOPY /\ MEM op inst.inst_operands /\
  (~is_terminator inst.inst_opcode \/ ~is_label_operand op) ==>
  eval_operand op s <> NONE
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `op` >> simp[eval_operand_def]
  >- metis_tac[focus_active_var_ready,eval_operand_def] >>
  `~is_pseudo inst.inst_opcode` by metis_tac[fmpStepContractTheory.is_pseudo_param_or_phi] >>
  fs[ctx_labels_bound_def,stackPlanTypesTheory.is_label_operand_def,FLOOKUP_DEF] >>
  metis_tac[]
QED

Theorem focus_active_inst_shape[local]:
  o1_fn_shape C fn /\ active_inst fn inst s ==>
  inst_wf inst /\ inst_shape_ok inst /\ MEM inst (fn_insts fn)
Proof
  simp[o1_fn_shape_def,active_inst_def,fn_inst_wf_def,fn_shape_ok_def,EVERY_MEM] >>
  strip_tac >>
  `MEM inst bb.bb_instructions` by metis_tac[EL_MEM] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def,MEM_fn_insts_blocks_iff] >> qexists `bb` >> simp[]) >>
  simp[] >>
  qpat_assum `!b i. _ ==> inst_wf i` (qspecl_then [`bb`,`inst`] mp_tac) >> simp[]
QED

Theorem focus_cursor_labels_bound[local]:
  joint_trace vs0 C q0 evs qs (JointConfig stk PG G tn fn inst s oms om hs h) /\
  o1_ctx_shape C /\ code_layout_valid vs0 ==> ctx_labels_bound C s.vs_labels
Proof
  strip_tac >>
  drule joint_trace_reachable >> simp[joint_config_reachable_def] >>
  disch_then (mp_tac o MATCH_MP frameOriginHistoryTheory.joint_origin_history_erasure) >>
  disch_then (mp_tac o MATCH_MP frameOriginReachableTheory.origin_frame_erasure) >>
  disch_then (mp_tac o MATCH_MP o1FrameLockstepTheory.frame_reachable_labels) >>
  simp[dftContractGasTheory.dft_ctx_labels_bound]
QED

Theorem focus_ungated_cursor_not_error[local]:
  o1_fn_shape C fn /\ active_inst fn inst s /\ MEM fn C.ctx_functions /\
  supply_norm_inv supply fn /\ supply_prefix_defined fn s /\
  ctx_labels_bound C s.vs_labels /\
  ((?post. step_inst 0 C inst s = OK post) \/
   (inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode)) /\
  (inst = prev \/ MEM inst.inst_opcode [PHI; ASSIGN; JMP; JNZ]) /\
  ~(inv_memory_observation prev.inst_opcode \/ is_fallible prev \/
    prev.inst_opcode = INVOKE \/ is_terminator prev.inst_opcode) ==>
  step_inst 0 C inst s <> Error err
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `(?post. _ = OK post) \/ _` strip_assume_tac >- simp[] >>
  drule_all_then (map_every assume_tac o CONJUNCTS) focus_active_inst_shape >>
  `~(inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
      inst.inst_opcode = INVOKE \/
      is_terminator inst.inst_opcode /\ ~MEM inst.inst_opcode [JMP; JNZ])` by
    (qpat_x_assum `inst = prev \/ _` strip_assume_tac >- fs[] >>
     fs[is_fallible_def,venomEffectsTheory.opcode_fail_class_def,
        inv_memory_observation_def,is_terminator_def]) >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> CODECOPY` by
    fs[inv_memory_observation_def] >>
  simp[step_inst_non_invoke] >> irule focus_plain_body_not_error >>
  conj_tac
  >- (gen_tac >> disch_tac >> irule focus_plain_cursor_operand >>
      qexistsl [`C`,`fn`,`inst`,`supply`] >> fs[]) >>
  gvs[]
QED

(* The stop branch returns the opcode gate for focus_current_row_cut, so
   all reasons select a cut of the existing packet rather than a new one. *)
Theorem focus_joint_selectable_stop_or_guards[local]:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  joint_trace vs0 C9 q90 evs9 qs9
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  C8.ctx_entry = SOME entry /\ o1_ctx_shape C9 /\ code_layout_valid vs0 /\
  ((?post. step_inst 0 C9 inst9 s9 = OK post) \/
   (inst9.inst_opcode <> PHI /\ ~is_param_opcode inst9.inst_opcode)) ==>
  ((~in_revert_forward fn9 s9 /\
    (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode ==>
      source_memory_reads_disjoint cpl inst9 s9 /\
      context_source_memory_writes_disjoint cpl inst9 s9) /\
    (fin = asm_opt_finalizer ==>
      !dst x sz src off.
        inst9.inst_opcode = CODECOPY /\ inst9.inst_operands = [dst; Var x; sz] /\
        code_end_var fn9 x /\ eval_operand (Var x) s9 = SOME src /\
        FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off ==>
        w2n (src - n2w off) < dimword (:256) DIV 2) /\
    active_inst fn9 inst9 s9 /\
    (inst9.inst_opcode = INVOKE ==>
      ?nm ops callee args ent.
        decode_invoke inst9 = SOME (nm,ops) /\
        lookup_function nm C9.ctx_functions = SOME callee /\
        eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent) /\
    (inst9.inst_opcode <> INVOKE ==>
      (?u. step_inst 0 C9 inst9 s9 = OK u /\ ~u.vs_halted) \/
      (stk9 <> [] /\ ?ir u. step_inst 0 C9 inst9 s9 = IntRet ir u))) \/
   ((inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
     inst8.inst_opcode = INVOKE \/ is_terminator inst8.inst_opcode) /\
    ((inst9 = inst8 /\ inst8.inst_opcode <> INVOKE /\
       ((?u. step_inst fuel C8 inst8 s8 = Halt u) \/
        (?ex u. step_inst fuel C8 inst8 s8 = Abort ex u))) \/
     in_revert_forward fn9 s9 \/
     (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode /\
      (~source_memory_reads_disjoint cpl inst9 s9 \/
       ~context_source_memory_writes_disjoint cpl inst9 s9)) \/
     (fin = asm_opt_finalizer /\
      ?dst x sz src off.
        inst9.inst_opcode = CODECOPY /\ inst9.inst_operands = [dst; Var x; sz] /\
        code_end_var fn9 x /\ eval_operand (Var x) s9 = SOME src /\
        FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off /\
        ~(w2n (src - n2w off) < dimword (:256) DIV 2)) \/
     (inst9.inst_opcode = INVOKE /\
      ~(?nm ops callee args ent.
        decode_invoke inst9 = SOME (nm,ops) /\
        lookup_function nm C9.ctx_functions = SOME callee /\
        eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent)) \/
     (inst9.inst_opcode <> INVOKE /\ ?err. step_inst 0 C9 inst9 s9 = Error err))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (map_every assume_tac o CONJUNCTS) focus_current_instruction >>
  drule_then strip_assume_tac focus_cursor_ready_context >>
  `C9.ctx_entry = SOME entry /\ o1_fn_shape C9 fn9` by fs[o1_ctx_shape_def,EVERY_MEM] >>
  `wf_function fn9` by fs[o1_fn_shape_def] >>
  drule_all_then (map_every assume_tac o CONJUNCTS) focus_active_inst_shape >>
  qmatch_goalsub_abbrev_tac `~in_revert_forward fn9 s9 /\ spill /\ opt /\ rest` >>
  qabbrev_tac `gate = (inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
    inst8.inst_opcode = INVOKE \/ is_terminator inst8.inst_opcode)` >>
  Cases_on `~in_revert_forward fn9 s9 /\ spill /\ opt`
  >- (qpat_x_assum `~in_revert_forward fn9 s9 /\ spill /\ opt` strip_assume_tac >>
      Cases_on `inst9.inst_opcode = INVOKE`
      >- (`gate` by (qpat_x_assum `inst9 = inst8 \/ _` strip_assume_tac >> gvs[Abbr `gate`]) >>
          simp[Abbr `rest`] >> metis_tac[]) >>
      drule_all focus_cursor_noninvoke_cases >>
      disch_then (qspec_then `fuel`
        (DISJ_CASES_THEN2 assume_tac (DISJ_CASES_THEN2 assume_tac assume_tac)))
      >- simp[Abbr `rest`]
      >- (simp[Abbr `gate`] >> metis_tac[]) >>
      `gate` by
        (spose_not_then assume_tac >>
         `ctx_labels_bound C9 s9.vs_labels` by (irule focus_cursor_labels_bound >> metis_tac[]) >>
         `~(inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
            inst8.inst_opcode = INVOKE \/ is_terminator inst8.inst_opcode)` by
           (qpat_x_assum `~gate` mp_tac >> simp[Abbr `gate`]) >>
         drule_all focus_ungated_cursor_not_error >> simp[]) >>
      simp[]) >>
  `gate` by
    (spose_not_then assume_tac >>
     `~(inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
        inst8.inst_opcode = INVOKE \/ is_terminator inst8.inst_opcode)` by
       (qpat_x_assum `~gate` mp_tac >> simp[Abbr `gate`]) >>
     drule_all_then strip_assume_tac focus_ungated_current_guards >>
     qpat_x_assum `~(~in_revert_forward fn9 s9 /\ spill /\ opt)` mp_tac >>
     simp[Abbr `spill`,Abbr `opt`]) >>
  disj2_tac >> simp[] >>
  qpat_x_assum `~(~in_revert_forward fn9 s9 /\ spill /\ opt)` mp_tac >>
  simp[Abbr `spill`,Abbr `opt`,NOT_FORALL_THM] >> metis_tac[]
QED

Theorem focus_ledger_pairs_snoc[local]:
  LENGTH qs = m /\ EL m (q0::qs) = q /\
  LIST_REL R costs (ZIP (TAKE m (q0::qs),qs)) /\ R n (q,next) ==>
  LIST_REL R (costs ++ [n])
    (ZIP (TAKE (SUC m) (q0::(qs ++ [next])),qs ++ [next]))
Proof
  strip_tac >>
  `TAKE (SUC m) (q0::(qs ++ [next])) = TAKE (SUC m) (q0::qs)` by
    (simp[Once (GSYM APPEND)] >> irule listTheory.TAKE_APPEND1 >> simp[]) >>
  `TAKE (SUC m) (q0::qs) = TAKE m (q0::qs) ++ [q]` by
    (mp_tac (Q.SPECL [`m`,`q0::qs`] TAKE_SUC_BY_TAKE) >>
     simp[SNOC_APPEND]) >>
  `LENGTH (TAKE m (q0::qs)) = LENGTH qs` by simp[LENGTH_TAKE] >>
  qpat_x_assum `TAKE (SUC m) (q0::(qs ++ [next])) = _` SUBST1_TAC >>
  qpat_x_assum `TAKE (SUC m) (q0::qs) = _` SUBST1_TAC >>
  `ZIP (TAKE m (q0::qs) ++ [q],qs ++ [next]) =
     ZIP (TAKE m (q0::qs),qs) ++ [(q,next)]` by
    (CONV_TAC SYM_CONV >>
     irule (SIMP_RULE (srw_ss()) []
       (Q.SPECL [`a`,`b`,`[x]`,`[y]`] ZIP_APPEND)) >> simp[]) >>
  asm_rewrite_tac[LIST_REL_APPEND_SING]
QED

Theorem focus_ledger_cons_append[local]:
  i <= LENGTH xs ==> EL i (x::(xs ++ ys)) = EL i (x::xs)
Proof
  Cases_on `i` >> simp[EL_APPEND_EQN]
QED

Theorem focus_ledger_new_endpoint[local]:
  LENGTH xs = m ==> EL (SUC m) (x::(xs ++ [y])) = y
Proof
  simp[EL_APPEND_EQN]
QED

(* A C9 edge extends the ledger at m, while the aligned C8 trace either
   stays fixed or gains its next configuration. *)
Theorem focus_stop_aligned_ledger_snoc[local]:
  LENGTH qs8 = j /\ LENGTH qs9 = m /\
  EL j (q80::qs8) = q8 /\ EL m (q90::qs9) = q9 /\
  j' = j + LENGTH add8 /\ LENGTH add8 <= 1 /\
  LENGTH costs = m /\ LENGTH old_asm = m /\
  (opt ==> LENGTH old_sym = m) /\
  align 0 = 0 /\ align m = j /\
  fuel = SUM costs /\ ast = EL m (a0::old_asm) /\
  (opt ==> ss = EL m (s0::old_sym)) /\
  LIST_REL cost_ok costs (ZIP (TAKE m (q90::qs9),qs9)) /\
  (!k. k < m ==>
    align k <= j /\
    (align (SUC k) = align k \/ align (SUC k) = SUC (align k)) /\
    align (SUC k) <= j /\
    cursors (old_cursors k) (EL (align k) (q80::qs8)) (EL k (q90::qs9)) /\
    asm_edge (EL k costs) (EL k (a0::old_asm)) (EL (SUC k) (a0::old_asm)) /\
    (opt ==> sym_edge (EL k costs) (EL k (s0::old_sym)) (EL (SUC k) (s0::old_sym))) /\
    edge_ok (align (SUC k) = SUC (align k)) (EL (align k) (q80::qs8)) (EL k (q90::qs9))) /\
  cursors current q8 q9 /\ asm_edge n ast ast' /\ (opt ==> sym_edge n ss ss') /\
  edge_ok (j' = SUC j) q8 q9 /\ cost_ok n (q9,q9') ==>
  ?align' old_cursors'.
    LENGTH (costs ++ [n]) = SUC m /\ LENGTH (old_asm ++ [ast']) = SUC m /\
    (opt ==> LENGTH (old_sym ++ [ss']) = SUC m) /\
    align' 0 = 0 /\ align' (SUC m) = j' /\
    fuel + n = SUM (costs ++ [n]) /\ ast' = EL (SUC m) (a0::(old_asm ++ [ast'])) /\
    (opt ==> ss' = EL (SUC m) (s0::(old_sym ++ [ss']))) /\
    LIST_REL cost_ok (costs ++ [n])
      (ZIP (TAKE (SUC m) (q90::(qs9 ++ [q9'])),qs9 ++ [q9'])) /\
    (!k. k < SUC m ==>
      align' k <= j' /\
      (align' (SUC k) = align' k \/ align' (SUC k) = SUC (align' k)) /\
      align' (SUC k) <= j' /\
      cursors (old_cursors' k) (EL (align' k) (q80::(qs8 ++ add8))) (EL k (q90::(qs9 ++ [q9']))) /\
      asm_edge (EL k (costs ++ [n])) (EL k (a0::(old_asm ++ [ast'])))
        (EL (SUC k) (a0::(old_asm ++ [ast']))) /\
      (opt ==> sym_edge (EL k (costs ++ [n])) (EL k (s0::(old_sym ++ [ss'])))
        (EL (SUC k) (s0::(old_sym ++ [ss'])))) /\
      edge_ok (align' (SUC k) = SUC (align' k))
        (EL (align' k) (q80::(qs8 ++ add8))) (EL k (q90::(qs9 ++ [q9']))))
Proof
  strip_tac >>
  `j <= j'` by decide_tac >>
  `LIST_REL cost_ok (costs ++ [n])
     (ZIP (TAKE (SUC m) (q90::(qs9 ++ [q9'])),qs9 ++ [q9']))`
    by (irule focus_ledger_pairs_snoc >> metis_tac[]) >>
  qexistsl [`\k. if k = SUC m then j' else align k`,
            `\k. if k = m then current else old_cursors k`] >>
  simp[listTheory.SUM_APPEND,focus_ledger_new_endpoint] >>
  qx_gen_tac `k` >> strip_tac >>
  Cases_on `k = m`
  >- (`j' = j \/ j' = SUC j` by decide_tac >>
      gvs[focus_ledger_cons_append,focus_ledger_new_endpoint,EL_LENGTH_APPEND_rwt] >>
      metis_tac[]) >>
  `k < m /\ k <> SUC m /\ SUC k <> SUC m` by decide_tac >>
  qpat_x_assum `!k. k < m ==> _` (qspec_then `k` (drule_then strip_assume_tac)) >>
  gvs[focus_ledger_cons_append,EL_APPEND1] >> decide_tac
QED

(* Progress either spends assembly fuel or advances within the same block. *)
Theorem focus_ledger_rank_step[local]:
  (0 < n \/
    fn' = fn /\ s'.vs_current_bb = s.vs_current_bb /\
    ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      LENGTH bb.bb_instructions - s'.vs_inst_idx <
      LENGTH bb.bb_instructions - s.vs_inst_idx) ==>
  0 < n \/
  (\u. case u of JointConfig stk PG G tn fn inst s oms om hs hist =>
         case lookup_block s.vs_current_bb fn.fn_blocks of
           NONE => 0
         | SOME bb => LENGTH bb.bb_instructions - s.vs_inst_idx)
       (JointConfig stk' PG' G' tn' fn' inst' s' oms' om' hs' hist') <
  (\u. case u of JointConfig stk PG G tn fn inst s oms om hs hist =>
         case lookup_block s.vs_current_bb fn.fn_blocks of
           NONE => 0
         | SOME bb => LENGTH bb.bb_instructions - s.vs_inst_idx)
       (JointConfig stk PG G tn fn inst s oms om hs hist)
Proof
  strip_tac >> gvs[]
QED

(* Convert a successful native slice before comparing either endpoint. *)
Theorem focus_native_prefix_oracle[local]:
  bb.bb_instructions = ps ++ insts /\ be.vs_inst_idx = LENGTH ps /\
  m <= LENGTH insts /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE m insts) /\
  FOLDR (dft_exec_cons fuel C) OK (TAKE m insts) be = OK u /\
  trace_agrees orc (trace_block p d fuel C fn
    (bb with bb_instructions := TAKE (LENGTH ps + m) bb.bb_instructions) be) ==>
  inv_ev_prefix orc p d C bb m (be with vs_gas_readings := reads)
    (u with vs_gas_readings := reads)
Proof
  strip_tac >> irule native_prefix_oracle >> simp[DROP_LENGTH_APPEND] >>
  qexistsl [`fuel`, `fn`] >> gvs[AC ADD_ASSOC ADD_COMM]
QED

Theorem focus_common_oracle_prefixes[local]:
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  be.vs_inst_idx = LENGTH ps /\ dft_remaining_inv sf bb xs be /\
  q <= LENGTH xs /\ k <= LENGTH ys /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k ys) /\
  FOLDR (dft_exec_cons source_fuel C7) OK (TAKE q xs)
    (be with vs_gas_readings := gs) = OK u /\
  FOLDR (dft_exec_cons target_fuel C8) OK (TAKE k ys) be = OK s /\
  ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT keys /\
  LIST_REL (\key slot. slot = ALOOKUP obs key) keys slots /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots vals /\
  trace_gas (trace_block p d source_fuel C7 sf
    (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
    (be with vs_gas_readings := gs)) = ZIP (keys,vals) /\
  EVERY (\kw. MEM kw obs) (trace_gas (trace_block p d target_fuel C8 tf
    (bt with bb_instructions := TAKE (LENGTH ps + k) bt.bb_instructions) be)) ==>
  dft_remaining_inv sf bb xs (be with vs_gas_readings := s.vs_gas_readings) /\
  ?orc.
    inv_ev_ftrace orc p d C7 (TAKE q xs)
      (be with vs_gas_readings := s.vs_gas_readings)
      (u with vs_gas_readings := s.vs_gas_readings) /\
    inv_ev_ftrace orc p d C7 (TAKE k ys)
      (be with vs_gas_readings := s.vs_gas_readings) s
Proof
  strip_tac >> drule_all dft_packet_common_oracle >> strip_tac >>
  qmatch_asmsub_abbrev_tac `trace_agrees orc` >>
  conj_tac >- (irule dft_remaining_inv_gas_variant >> qexists `be` >> simp[]) >>
  `inv_ev_prefix orc p d C7 bb q
    (be with vs_gas_readings := s.vs_gas_readings)
    (u with vs_gas_readings := s.vs_gas_readings)` by
      (qpat_assum `trace_agrees _ (trace_block _ _ _ C7 sf _ _)`
         (mp_then (Pat `trace_agrees _ _`) mp_tac focus_native_prefix_oracle) >>
       simp[] >> disch_then irule >> qexists `xs` >> simp[]) >>
  `inv_ev_prefix orc p d C8 bt k
    (be with vs_gas_readings := s.vs_gas_readings)
    (s with vs_gas_readings := s.vs_gas_readings)` by
      (qpat_assum `trace_agrees _ (trace_block _ _ _ C8 tf _ _)`
         (mp_then (Pat `trace_agrees _ _`) mp_tac focus_native_prefix_oracle) >>
       simp[] >> disch_then irule >> qexists `ys` >> simp[]) >>
  `inv_ev_prefix orc p d C7 bt k
    (be with vs_gas_readings := s.vs_gas_readings) s` by
      (drule inv_ev_prefix_context_reflect >>
       disch_then (drule_at (Pat `inv_ev_prefix _ _ _ C8 _ _ _ _`)) >> simp[]) >>
  qexists `orc` >> conj_tac
  >- (qpat_assum `inv_ev_prefix _ _ _ C7 bb _ _ _` (mp_tac o MATCH_MP inv_ev_prefix_ftrace) >>
      simp[DROP_LENGTH_APPEND]) >>
  qpat_assum `inv_ev_prefix _ _ _ C7 bt _ _ _` (mp_tac o MATCH_MP inv_ev_prefix_ftrace) >>
  simp[DROP_LENGTH_APPEND]
QED

(* Opposite orders in the full row certify an exchange in either trace. *)
Theorem focus_terminal_row_swap[local]:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ src /\
  EVERY (\i. ~is_pseudo i.inst_opcode) src /\
  MAP (\i. i.inst_id) bt.bb_instructions = MAP (\i. i.inst_id) ps ++ MAP (\i. i.inst_id) dst ==>
  !x y. id_before src x y /\ id_before dst y x ==>
    dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `MEM x src /\ MEM y src` by metis_tac[dftScheduleOrderTheory.id_before_mem] >>
  `MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
   ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
   id_before (MAP (\i. i.inst_id) bt.bb_instructions) y.inst_id x.inst_id` by
    (asm_rewrite_tac[MAP_APPEND] >>
     metis_tac[dftSsaPreserveTheory.id_before_map, id_before_append_right]) >>
  drule_all inv_lookup_inversion_swap >> simp[]
QED

Theorem focus_partition_inversion[local]:
  ALL_DISTINCT xs /\ id_before xs y x /\
  id_before (FILTER (\z. MEM z ys) xs ++ FILTER (\z. ~MEM z ys) xs) x y ==>
  MEM x ys /\ ~MEM y ys
Proof
  simp[dftSsaPreserveTheory.id_before_append, MEM_FILTER] >>
  metis_tac[inv_id_before_filter_reflect, id_before_asym]
QED

Theorem focus_ftrace_unique[local]:
  !xs s u v. inv_ev_ftrace orc p d ctx xs s u /\
    inv_ev_ftrace orc p d ctx xs s v ==> u = v
Proof
  Induct >> simp[Once inv_ev_ftrace_def] >>
  simp[Once inv_ev_ftrace_def] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `ev_step _ _ _ _ _ _ _ = OK _` mp_tac >>
  rename1 `ev_step orc p d f ctx inst s = OK a` >> disch_tac >>
  rename1 `ev_step orc p d g ctx inst s = OK b` >>
  `ev_step orc p d (f + g) ctx inst s = OK a` by
    (irule ev_step_fuel_extend >> simp[]) >>
  `ev_step orc p d (g + f) ctx inst s = OK b` by
    (irule ev_step_fuel_extend >> simp[]) >>
  fs[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

(* The common list I is the executed intersection in source order.  An
   exchange in the stable partition of pre puts a consumed instruction
   before a missing one, so the schedule witnesses that inversion. *)
Theorem focus_terminal_prefix_factor_normalized[local]:
  ALL_DISTINCT (pre ++ i::post) /\
  PERM (consumed ++ i::later) (pre ++ i::post) /\
  (!x y. id_before (pre ++ i::post) x y /\
    id_before (consumed ++ i::later) y x ==>
      dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y) /\
  inv_ev_ftrace orc p d ctx pre s0 u /\
  inv_ev_ftrace orc p d ctx consumed s0 v ==>
  ?sI M P. inv_ev_ftrace orc p d ctx M sI u /\
    inv_ev_ftrace orc p d ctx P sI v /\
    EVERY (\x. dft_gas_swap_pair i x /\ inst_wf x) (M ++ P) /\
    (is_terminator i.inst_opcode ==> M = [] /\ P = [])
Proof
  strip_tac >>
  `ALL_DISTINCT (consumed ++ i::later)` by metis_tac[ALL_DISTINCT_PERM] >>
  `!x. MEM x consumed \/ x = i \/ MEM x later <=>
        MEM x pre \/ x = i \/ MEM x post` by (drule PERM_MEM_EQ >> simp[]) >>
  `ALL_DISTINCT consumed /\ ~MEM i consumed /\ ~MEM i pre /\
   ALL_DISTINCT pre /\ ALL_DISTINCT (pre ++ post)` by (fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `!x. MEM x pre /\ ~MEM x consumed ==> MEM x later` by metis_tac[] >>
  qabbrev_tac `shared = FILTER (\x. MEM x consumed) pre` >>
  qabbrev_tac `missing = FILTER (\x. ~MEM x consumed) pre` >>
  qabbrev_tac `extra = FILTER (\x. MEM x consumed) post` >>
  `ALL_DISTINCT (shared ++ missing) /\ PERM pre (shared ++ missing)` by
    (simp[Abbr `shared`, Abbr `missing`, ALL_DISTINCT_APPEND, MEM_FILTER, FILTER_ALL_DISTINCT] >>
     irule PERM_ALL_DISTINCT >> simp[ALL_DISTINCT_APPEND, MEM_FILTER, FILTER_ALL_DISTINCT] >>
     gen_tac >> Cases_on `MEM x consumed` >> simp[]) >>
  `ALL_DISTINCT (shared ++ extra) /\ PERM consumed (shared ++ extra)` by
    (simp[Abbr `shared`, Abbr `extra`, GSYM FILTER_APPEND_DISTRIB, FILTER_ALL_DISTINCT] >>
     irule PERM_ALL_DISTINCT >> simp[MEM_FILTER, FILTER_ALL_DISTINCT] >> metis_tac[]) >>
  `inv_ev_ftrace orc p d ctx (shared ++ missing) s0 u` by
    (irule inv_ftrace_source_sort >> simp[] >> qexists `pre` >> simp[] >>
     rpt gen_tac >> strip_tac >>
     `MEM x consumed /\ ~MEM z consumed` by
       (irule focus_partition_inversion >> qexists `pre` >>
        fs[Abbr `shared`, Abbr `missing`]) >>
     `MEM z later` by metis_tac[dftScheduleOrderTheory.id_before_mem] >>
     `id_before (pre ++ i::post) z x /\ id_before (consumed ++ i::later) x z` by
       simp[dftSsaPreserveTheory.id_before_append] >>
     metis_tac[dft_gas_swap_pair_sym]) >>
  `inv_ev_ftrace orc p d ctx (shared ++ extra) s0 v` by
    (irule inv_ftrace_source_sort >> simp[] >> qexists `consumed` >> simp[] >>
     rpt gen_tac >> strip_tac >>
     `id_before (pre ++ i::post) x z` by
       (`id_before (pre ++ post) x z` by
          (irule inv_id_before_filter_reflect >> qexists `\x. MEM x consumed` >>
           simp[Abbr `shared`, Abbr `extra`, FILTER_APPEND_DISTRIB]) >>
        fs[dftSsaPreserveTheory.id_before_append, dftScheduleOrderTheory.id_before_cons]) >>
     `id_before (consumed ++ i::later) z x` by simp[dftSsaPreserveTheory.id_before_append] >>
     metis_tac[]) >>
  qpat_x_assum `inv_ev_ftrace _ _ _ _ (shared ++ missing) _ _`
    (strip_assume_tac o REWRITE_RULE [inv_ev_ftrace_append]) >>
  qpat_x_assum `inv_ev_ftrace _ _ _ _ (shared ++ extra) _ _`
    (strip_assume_tac o REWRITE_RULE [inv_ev_ftrace_append]) >>
  `EVERY (\x. dft_gas_swap_pair i x /\ inst_wf x) (missing ++ extra)` by
    (simp[Abbr `missing`, Abbr `extra`, EVERY_MEM, MEM_FILTER] >> rpt strip_tac >>
     metis_tac[dftSsaPreserveTheory.id_before_append,
               dftScheduleOrderTheory.id_before_cons, dft_gas_swap_pair_sym, MEM]) >>
  `is_terminator i.inst_opcode ==> missing = [] /\ extra = []` by
    (strip_tac >> Cases_on `missing` >> Cases_on `extra` >> gvs[dft_gas_swap_pair_def]) >>
  metis_tac[focus_ftrace_unique]
QED

Theorem focus_terminal_prefix_factor[local]:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ (pre ++ i::post) /\
  bt.bb_instructions = ps ++ (scheduled ++ yi::later) /\
  EVERY (\x. is_pseudo x.inst_opcode) ps /\
  EVERY (\x. ~is_pseudo x.inst_opcode) (pre ++ i::post) /\
  yi.inst_id = i.inst_id /\ dft_remaining_inv fn bb (pre ++ i::post) s0 /\
  inv_ev_ftrace orc p d ctx pre s0 u /\
  inv_ev_ftrace orc p d ctx scheduled s0 v ==>
  (yi = i \/ yi = flip_operands i /\ is_flippable i.inst_opcode) /\
  ?sI M P. inv_ev_ftrace orc p d ctx M sI u /\
    inv_ev_ftrace orc p d ctx P sI v /\
    EVERY (\x. dft_gas_swap_pair i x /\ inst_wf x) (M ++ P) /\
    (is_terminator i.inst_opcode ==> M = [] /\ P = [])
Proof
  strip_tac >>
  `FILTER (\x. is_pseudo x.inst_opcode) bb.bb_instructions = ps /\
   FILTER (\x. ~is_pseudo x.inst_opcode) bb.bb_instructions = pre ++ i::post` by
    (`FILTER (\x. is_pseudo x.inst_opcode) ps = ps /\
      FILTER (\x. ~is_pseudo x.inst_opcode) ps = [] /\
      FILTER (\x. is_pseudo x.inst_opcode) (pre ++ i::post) = [] /\
      FILTER (\x. ~is_pseudo x.inst_opcode) (pre ++ i::post) = pre ++ i::post` by
       (simp[FILTER_EQ_ID, FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
     asm_rewrite_tac[FILTER_APPEND_DISTRIB, APPEND_NIL, APPEND]) >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  qpat_x_assum `dft_block_rel _ _` mp_tac >>
  simp[dftScheduleOrderTheory.dft_block_rel_def] >> strip_tac >> gvs[] >>
  `EVERY (from_block bb.bb_instructions) scheduled /\
   from_block bb.bb_instructions yi /\ EVERY (from_block bb.bb_instructions) later` by
    metis_tac[APPEND_ASSOC, APPEND] >>
  drule_all inv_ftrace_original_representatives >> strip_tac >>
  rename1 `inv_ev_ftrace orc p d ctx consumed s0 v` >>
  qpat_assum `EVERY (from_block _) later`
    (mp_tac o MATCH_MP inv_from_block_representatives) >> strip_tac >>
  rename1 `MAP (\x. x.inst_id) later0 = MAP (\x. x.inst_id) later` >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions)` by
    metis_tac[dft_fn_rel_def, wf_fn_block_inst_ids_distinct] >>
  `MEM i bb.bb_instructions` by simp[] >>
  conj_tac
  >- (qpat_assum `from_block _ yi` (strip_assume_tac o REWRITE_RULE [dftStructuralTheory.from_block_def]) >>
      metis_tac[dftCorrectnessTheory.all_distinct_map_mem_inj, dftStructuralTheory.flip_operands_inst_id]) >>
  `PERM (consumed ++ i::later0) (pre ++ i::post)` by
    (irule inv_original_ids_perm >> conj_tac
     >- (qexists `bb.bb_instructions` >> fs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
     asm_rewrite_tac[MAP_APPEND, MAP] >> metis_tac[APPEND_ASSOC, APPEND]) >>
  `MAP (\x. x.inst_id) bt.bb_instructions =
    MAP (\x. x.inst_id) ps ++ MAP (\x. x.inst_id) (consumed ++ i::later0)` by
    (asm_rewrite_tac[MAP_APPEND, MAP] >> metis_tac[APPEND_ASSOC, APPEND]) >>
  `ALL_DISTINCT (pre ++ i::post)` by metis_tac[dft_remaining_inv_def] >>
  `!x y. id_before (pre ++ i::post) x y /\ id_before (consumed ++ i::later0) y x ==>
    dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y` by
    (rpt gen_tac >> strip_tac >> irule focus_terminal_row_swap >>
     qpat_assum `dft_fn_rel fn fn'` (irule_at Any) >>
     qpat_assum `MEM bb fn.fn_blocks` (irule_at Any) >>
     rpt (first_assum (irule_at Any)) >> simp[APPEND_ASSOC]) >>
  once_rewrite_tac[GSYM EVERY_APPEND] >>
  irule focus_terminal_prefix_factor_normalized >>
  rpt (first_assum (irule_at Any)) >> simp[] >> metis_tac[]
QED

(* The swap's effect separation rules out calls when the pending
   instruction reads returndata or may itself consume a call outcome. *)
Theorem focus_swap_stop_effects[local]:
  dft_gas_swap_pair i x ==>
  (i.inst_opcode = RETURNDATACOPY ==>
   x.inst_opcode <> INVOKE /\
   Eff_RETURNDATA NOTIN venomEffects$write_effects x.inst_opcode) /\
  (is_ext_call_op i.inst_opcode ==>
   ~MEM x.inst_opcode [INVOKE;CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2])
Proof
  simp[dft_gas_swap_pair_def, venomEffectsTheory.effects_independent_def,
       pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  strip_tac >> conj_tac
  >- (strip_tac >> fs[venomEffectsTheory.read_effects_def] >>
      metis_tac[venomEffectsTheory.write_effects_def, venomEffectsTheory.all_effects_def,
                pred_setTheory.IN_INSERT]) >>
  `is_ext_call_op i.inst_opcode ==> venomEffects$read_effects i.inst_opcode =
      venomEffects$all_effects` by
    (Cases_on `i.inst_opcode` >> simp[is_ext_call_op_def, venomEffectsTheory.read_effects_def]) >>
  strip_tac >>
  `venomEffects$read_effects i.inst_opcode = venomEffects$all_effects` by metis_tac[] >>
  `Eff_RETURNDATA IN venomEffects$read_effects i.inst_opcode` by
    simp[venomEffectsTheory.all_effects_def] >>
  `Eff_RETURNDATA NOTIN venomEffects$write_effects x.inst_opcode` by metis_tac[] >>
  rpt strip_tac >> gvs[venomEffectsTheory.write_effects_def, venomEffectsTheory.all_effects_def]
QED

Theorem focus_swap_event_step_stop_frame[local]:
  dft_gas_swap_pair i x /\ ev_step orc p d fuel ctx x s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\
  (i.inst_opcode = RETURNDATACOPY ==> t.vs_returndata = s.vs_returndata) /\
  (is_ext_call_op i.inst_opcode ==> (t.vs_outcomes = [] <=> s.vs_outcomes = []))
Proof
  strip_tac >>
  conj_tac >- metis_tac[dftGasInvOracleFrameTheory.inv_ev_step_call_ctx] >>
  Cases_on `x.inst_opcode = GAS`
  >- gvs[Once ev_step_def, ev_gas_def, AllCaseEqs()] >>
  drule_then strip_assume_tac focus_swap_stop_effects >>
  Cases_on `x.inst_opcode = INVOKE` >- fs[] >>
  `step_inst fuel ctx x s = OK t` by
    (fs[Once ev_step_def] >> simp[step_inst_non_invoke]) >>
  conj_tac
  >- (strip_tac >> irule venomInstProofsTheory.write_effects_sound_returndata >>
      qexistsl [`ctx`,`fuel`,`x`] >> gvs[dft_gas_swap_pair_def]) >>
  strip_tac >>
  `~MEM x.inst_opcode [INVOKE;CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]` by simp[] >>
  fs[] >> drule_all oracleExecPropsTheory.step_inst_noninvoke_oracle >> simp[]
QED

Theorem focus_terminal_trace_stop_frame[local]:
  !xs s t. EVERY (\x. dft_gas_swap_pair i x /\ inst_wf x) xs /\
    inv_ev_ftrace orc p d ctx xs s t ==>
    t.vs_call_ctx = s.vs_call_ctx /\
    (i.inst_opcode = RETURNDATACOPY ==> t.vs_returndata = s.vs_returndata) /\
    (is_ext_call_op i.inst_opcode ==> (t.vs_outcomes = [] <=> s.vs_outcomes = []))
Proof
  Induct >> simp[inv_ev_ftrace_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all focus_swap_event_step_stop_frame >> gvs[]
QED

Theorem focus_base_stop_opcode[local]:
  (is_terminator i.inst_opcode \/ ~v.vs_halted) /\
  ((?t. step_inst_base i v = OK t /\ t.vs_halted) \/
   (?t. step_inst_base i v = Halt t) \/
   (?ex t. step_inst_base i v = Abort ex t)) ==>
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
  (~is_terminator i.inst_opcode ==> ?ex t. step_inst_base i v = Abort ex t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `(?t. step_inst_base _ _ = OK t /\ _) \/ _` strip_assume_tac
  >- (`is_terminator i.inst_opcode` by metis_tac[step_inst_base_OK_preserves_halted] >>
      Cases_on `i.inst_opcode` >> gvs[is_terminator_def])
  >- (drule opcodeClassTheory.step_inst_base_halt_opcodes >>
      strip_tac >> gvs[is_terminator_def]) >>
  drule opcodeClassTheory.step_inst_base_abort_opcodes >> strip_tac >> gvs[] >> metis_tac[]
QED

(* Replay the stopping instruction on the unnormalized C7 state.  An
   ordered terminator has no residual steps; an abort instead uses the
   three inspected fields and the operand frame of both residual traces. *)
Theorem focus_terminal_residual_replay[local]:
  inv_ev_ftrace orc p d C M sI (u with vs_gas_readings := v.vs_gas_readings) /\
  inv_ev_ftrace orc p d C P sI v /\
  EVERY (\x. dft_gas_swap_pair i x /\ inst_wf x) (M ++ P) /\
  (is_terminator i.inst_opcode ==> M = [] /\ P = []) /\
  (yi = i \/ yi = flip_operands i /\ is_flippable i.inst_opcode) /\
  yi.inst_opcode <> INVOKE /\ (is_terminator i.inst_opcode \/ ~v.vs_halted) /\
  ((?t. step_inst fuel8 C8 yi v = OK t /\ t.vs_halted) \/
   (?t. step_inst fuel8 C8 yi v = Halt t) \/
   (?ex t. step_inst fuel8 C8 yi v = Abort ex t)) ==>
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
  ((?t. step_inst fuel7 C i u = Halt t) \/
   (?ex t. step_inst fuel7 C i u = Abort ex t) \/
   (is_terminator i.inst_opcode /\ ?t. step_inst fuel7 C i u = OK t /\ t.vs_halted))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `step_inst fuel8 C8 yi v = step_inst_base i v` by
    (simp[step_inst_non_invoke] >>
     metis_tac[dftPermSimTheory.flip_operands_step_inst_base]) >>
  pop_assum (fn eq =>
    qpat_x_assum `(?t. step_inst fuel8 _ _ _ = OK t /\ _) \/ _`
      (assume_tac o REWRITE_RULE [eq])) >>
  drule_all_then strip_assume_tac focus_base_stop_opcode >>
  simp[step_inst_non_invoke] >>
  Cases_on `is_terminator i.inst_opcode`
  >- suspend "ordered"
  >> suspend "abort"
QED

Resume focus_terminal_residual_replay[ordered]:
  `v = u with vs_gas_readings := v.vs_gas_readings` by
    fs[inv_ev_ftrace_def] >>
  `dftGasFromListRestore$restore_rel v.vs_gas_readings
    (step_inst_base i u) (step_inst_base i (u with vs_gas_readings := v.vs_gas_readings))` by
    (irule dftGasFromListRestoreTheory.step_base_restore >> simp[]) >>
  qpat_assum `v = u with vs_gas_readings := _` (fn eq =>
    pop_assum (mp_tac o ONCE_REWRITE_RULE [GSYM eq])) >>
  Cases_on `step_inst_base i u` >> Cases_on `step_inst_base i v` >>
  fs[dftGasFromListRestoreTheory.restore_rel_def] >> strip_tac >> gvs[]
QED

Resume focus_terminal_residual_replay[abort]:
  `?ex t. step_inst fuel7 C i v = Abort ex t` by simp[step_inst_non_invoke] >>
  gvs[EVERY_APPEND] >>
  qpat_x_assum `inv_ev_ftrace _ _ _ _ _ _ (_ with vs_gas_readings := _)` mp_tac >>
  drule_all_then strip_assume_tac inv_ev_trailing_trace_frame >>
  drule_all_then strip_assume_tac focus_terminal_trace_stop_frame >>
  qhdtm_x_assum `inv_ev_ftrace` kall_tac >> disch_tac >>
  drule_all_then strip_assume_tac inv_ev_trailing_trace_frame >>
  drule_all_then strip_assume_tac focus_terminal_trace_stop_frame >>
  fs[gasOracleReplayTheory.gas_eval_operand] >>
  disj2_tac >>
  `?ex t. step_inst fuel7 C i u = Abort ex t` suffices_by simp[step_inst_non_invoke] >>
  rename1 `step_inst fuel7 C i v = Abort ex r` >>
  `?t'. step_inst fuel7 C i u = Abort ex t'` by
    (irule dft_swap_noninvoke_abort_replay >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Finalise focus_terminal_residual_replay

Theorem focus_terminal_native_row[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn tf inst s oms om hs hist) raw_slots sites unused /\
  FLOOKUP acts p = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,sched,input,h0,SOME (be,hbe),k,OK s,F,NONE) /\
  FLOOKUP ms_tab (p,d) = SOME ms /\ FLOOKUP es_tab (p,d) = SOME es /\
  FLOOKUP ks_tab (p,d) = SOME ks ==>
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT (FLAT ks) /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  be.vs_inst_idx = LENGTH ps /\ dft_remaining_inv sf bb xs be /\
  k < LENGTH ys /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k ys) /\
  FOLDR (dft_exec_cons (N-d) C8) OK (TAKE k ys) be = OK s
Proof
  strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe k front closed brest ms ess ks.
    FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
    FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry k front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (fn rule => qpat_assum
      `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,sched,input,h0,SOME (be,hbe),k,OK s,F,NONE)`
      (mp_then Any strip_assume_tac rule)) >>
  qpat_x_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
    (fn rule => qpat_assum `FLOOKUP acts p = SOME (sf,tf,inc,entry,order,NONE,NONE)`
      (mp_then Any strip_assume_tac rule)) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`(j,obs) = _`,`JointConfig stk PG G tn tf inst s oms om hs hist = _`,
     `ALL_DISTINCT (MAP FST _)`,`ALL_DISTINCT (FLAT ks)`,
     `LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions`,
     `LIST_REL (\f g. g = dft_fn f) _ _`, `o1_ctx_shape C8`,
     `FLOOKUP acts p = SOME (sf,tf,inc,entry,order,NONE,NONE)`,
     `FLOOKUP acts p = SOME (_,_,_,_,_,_,_)`,
     `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,sched,input,h0,SOME (be,hbe),k,OK s,F,NONE)`,
     `FLOOKUP blocks (p,d) = SOME (_,_,_,_,_,_,_,_,_,_,_,_,_)`,
     `MEM _ C7.ctx_functions`, `_ = dft_fn _`,
     `bb.bb_instructions = ps ++ xs`,`bt.bb_instructions = ps ++ ys`,
     `lookup_block bb.bb_label _ = SOME bt`,
     `case SOME (be,hbe) of NONE => _ | SOME v => _`,
     `case _ of NONE => _ | SOME v => (_.vs_inst_idx = _ /\ _)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[] >>
  `MEM (dft_fn sf) C8.ctx_functions` by
    (qpat_assum `LIST_REL (\f g. g = dft_fn f) _ _`
       (mp_then Any (drule_then strip_assume_tac) LIST_REL_MEM_IMP) >> gvs[]) >>
  `wf_function (dft_fn sf)` by
    (drule_then mp_tac dftContractGasTheory.o1_ctx_shape_wf_functions >>
     simp[EVERY_MEM]) >>
  `bb_well_formed bt` by
    (drule venomExecPropsTheory.lookup_block_MEM >> fs[wf_function_def]) >>
  rename1 `pos < LENGTH ys` >>
  qpat_assum `bb_well_formed bt` mp_tac >>
  qpat_assum `bt.bb_instructions = ps ++ ys` mp_tac >>
  qpat_assum `pos < LENGTH ys` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  gvs[bb_well_formed_def] >> simp[EVERY_EL,EL_TAKE] >> rpt strip_tac >>
  qpat_x_assum `!i. i < _ /\ is_terminator _ ==> _`
    (qspec_then `LENGTH ps + n` mp_tac) >>
  simp[EL_APPEND2] >> decide_tac
QED

Theorem focus_terminal_native_prefixes[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn tf inst s oms om hs hist) raw_slots sites unused /\
  FLOOKUP acts p = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,sched,input,h0,SOME (be,hbe),k,OK s,F,NONE) /\
  FLOOKUP ms_tab (p,d) = SOME ms /\ FLOOKUP es_tab (p,d) = SOME ess /\
  FLOOKUP ks_tab (p,d) = SOME ks /\
  q < LENGTH xs /\ z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE k sched)) /\
  MAP (\(ai,ds,ei,qi,zi). ai) cuts =
    REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
  LENGTH cuts = LENGTH levels /\
  (!i ai ds ei qi zi.
    i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then
        ai = p /\ ei = d /\ qi = q /\ zi = z
      else
        ?cid call_h b0 done_at_call child_entry ret.
          EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) =
            SOME (qi,call_h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
            MEM r done_at_call)) /\
      EL i levels =
        (sfi,
         MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
           DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
             (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
           [(bbi,ei,zi)],
         if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
  Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
  N <= fuel /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
  rooted_eval fuel C7 levels (root_entry with vs_gas_readings := gs ++ tail) =
    (events,OK u) ==>
  dft_remaining_inv sf bb xs (be with vs_gas_readings := s.vs_gas_readings) /\
  ?orc.
    inv_ev_ftrace orc p d C7 (TAKE q xs)
      (be with vs_gas_readings := s.vs_gas_readings)
      (u with vs_gas_readings := s.vs_gas_readings) /\
    inv_ev_ftrace orc p d C7 (TAKE k ys)
      (be with vs_gas_readings := s.vs_gas_readings) s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac focus_terminal_native_row >>
  drule_all_then assume_tac dft_packet_current_prefix_observations >>
  drule_all_then (qspec_then `q` assume_tac) dft_packet_retained_prefix_lookup >>
  `FDOM ms_tab = FDOM ms_tab` by simp[] >>
  `!key old new. FLOOKUP ms_tab key = SOME old /\ FLOOKUP ms_tab key = SOME new ==>
    LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) old new` by
    (rpt strip_tac >> gvs[LIST_REL_EL_EQN]) >>
  drule_all_then strip_assume_tac dft_packet_cut_row_trace >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE q ms)) (FLAT kgss)` by
    (irule (REWRITE_RULE [transferTheory.FUN_REL_def] finite_setTheory.FLAT_relates) >> gvs[]) >>
  `ALL_DISTINCT (FLAT (TAKE q ks))` by
    (`FLAT (TAKE q ks) ++ FLAT (DROP q ks) = FLAT ks` by
       (once_rewrite_tac [GSYM FLAT_APPEND] >> rewrite_tac [TAKE_DROP]) >>
     pop_assum (fn eq => qpat_assum `ALL_DISTINCT (FLAT ks)`
       (mp_tac o REWRITE_RULE [GSYM eq])) >> simp[ALL_DISTINCT_APPEND]) >>
  qpat_x_assum `trace_gas _ = ZIP _` mp_tac >>
  qpat_x_assum `EVERY _ (trace_gas _)` mp_tac >>
  simp[] >> rpt disch_tac >>
  irule focus_common_oracle_prefixes >> simp[] >>
  rpt (first_assum (irule_at Any))
  >> (metis_tac[])
QED

(* Scratch statement for elaboration and independent review.
   Maximal means a guarded prefix ending at a concrete obstruction.
   The alignment index counts C8 motion across C9 steps. Each prefix
   keeps its own assembly segment, with the symbolic segment at the
   same cost on the optimizer arm. Native termination is read at C8. *)
(* The literals used by the packet only inspect each block's suffix at
   the native cursor.  On an open row, preserve both sides of the split. *)
Theorem focus_open_row_boundary[local]:
  !f C sf bb s z u.
    LENGTH z < LENGTH (DROP s.vs_inst_idx bb.bb_instructions) /\
    z = TAKE (LENGTH z) (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. ~is_terminator i.inst_opcode) z /\
    FOLDR (dft_exec_cons f C) OK z s = OK u ==>
    u.vs_inst_idx = s.vs_inst_idx + LENGTH z /\
    exec_block f C bb s = exec_block f C bb u /\
    gas_events_block f C sf.fn_name bb s =
      gas_events_block f C sf.fn_name
        (bb with bb_instructions := TAKE s.vs_inst_idx bb.bb_instructions ++ z) s ++
      gas_events_block f C sf.fn_name bb u
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `j = s.vs_inst_idx` >>
  qabbrev_tac `rest = DROP (j + LENGTH z) bb.bb_instructions` >>
  `z ++ rest = DROP j bb.bb_instructions` by
    (simp[Abbr `rest`] >>
     `DROP (j + LENGTH z) bb.bb_instructions =
      DROP (LENGTH z) (DROP j bb.bb_instructions)` by simp[DROP_DROP_T, ADD_COMM] >>
     metis_tac[TAKE_DROP]) >>
  qspecl_then [`z`,`s`,`j`] mp_tac dftGasPrefixProviderTheory.native_prefix_cut >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`f`,`C`,`sf`,`[]`,`0`,`rest`,`bb`,`ARB`] mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  `j <= LENGTH bb.bb_instructions` by fs[LENGTH_DROP] >>
  `exec_block f C bb s = exec_block f C bb u` by
    (irule dftPacketClosedRowNativeTheory.native_exec_block_prefix_skip >>
     qexists `LENGTH z` >> fs[LENGTH_DROP] >> metis_tac[]) >>
  `gas_events_block f C sf.fn_name bb s = gas_events_block f C sf.fn_name
      (bb with bb_instructions := REPLICATE j ARB ++ (z ++ rest)) s` by
    (irule gas_events_block_suffix_cong >>
     `j - (j + LENGTH z) = 0` by decide_tac >> simp[DROP_APPEND]) >>
  `gas_events_block f C sf.fn_name bb u = gas_events_block f C sf.fn_name
      (bb with bb_instructions := REPLICATE (j + LENGTH z) ARB ++ rest) u` by
    (irule gas_events_block_suffix_cong >> simp[DROP_APPEND2,Abbr `rest`]) >>
  `gas_events_block f C sf.fn_name
      (bb with bb_instructions := TAKE j bb.bb_instructions ++ z) s =
    gas_events_block f C sf.fn_name
      (bb with bb_instructions := REPLICATE j ARB ++ z) s` by
    (irule gas_events_block_suffix_cong >> simp[DROP_APPEND2,LENGTH_TAKE]) >>
  (simp[])
QED

Theorem focus_closed_row_continue[local]:
  !f C sf bb s sp t.
    lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK sp /\
    bb.bb_instructions <> [] /\ is_terminator (LAST bb.bb_instructions).inst_opcode /\
    FOLDR (dft_exec_cons f C) OK
      (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK t /\
    ~t.vs_halted ==>
    run_blocks (SUC f) C sf s = run_blocks f C sf t /\
    gas_events_blocks (SUC f) C sf s =
      gas_events_block f C sf.fn_name bb
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) ++
      gas_events_blocks f C sf t
Proof
  rpt gen_tac >> strip_tac >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
    metis_tac[phi_prefix_length_lt_last_non_phi,is_terminator_not_phi] >>
  `exec_block f C bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK t` by
    (qpat_assum `FOLDR _ _ _ _ = OK t` (SUBST1_TAC o SYM) >>
     irule dftPacketClosedRowNativeTheory.native_exec_block_terminated_fold >>
     simp[DROP_EQ_NIL,last_drop]) >>
  conj_tac
  >- (CONV_TAC (LAND_CONV (REWR_CONV venomExecSemanticsTheory.run_blocks_def)) >> simp[]) >>
  CONV_TAC (LAND_CONV (REWR_CONV gas_events_blocks_def)) >> simp[]
QED

Theorem focus_open_row_stop[local]:
  !f C sf bb s sp z u.
    lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK sp /\
    LENGTH z < LENGTH bb.bb_instructions - phi_prefix_length bb.bb_instructions /\
    z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    EVERY (\i. ~is_terminator i.inst_opcode) z /\
    FOLDR (dft_exec_cons f C) OK z
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK u ==>
    get_instruction bb u.vs_inst_idx =
      SOME (EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) /\
    !r. exec_block f C bb u = r /\ ((?v. r = Halt v) \/ (?ex v. r = Abort ex v)) ==>
      run_blocks (SUC f) C sf s = r /\
      gas_events_blocks (SUC f) C sf s =
        gas_events_block f C sf.fn_name
          (bb with bb_instructions := TAKE (phi_prefix_length bb.bb_instructions)
             bb.bb_instructions ++ z)
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) ++
        gas_events_block f C sf.fn_name bb u
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`f`,`C`,`sf`,`bb`,
    `sp with vs_inst_idx := phi_prefix_length bb.bb_instructions`,`z`,`u`] mp_tac
    focus_open_row_boundary >> simp[LENGTH_DROP] >> strip_tac >>
  conj_tac
  >- (`LENGTH z + phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
        fs[LENGTH_DROP] >>
      simp[get_instruction_def,EL_DROP,ADD_COMM]) >>
  rpt strip_tac >>
  (CONV_TAC (LAND_CONV (REWR_CONV venomExecSemanticsTheory.run_blocks_def)) ORELSE
   CONV_TAC (LAND_CONV (REWR_CONV gas_events_blocks_def))) >> simp[]
QED

Theorem focus_plan_snoc_ok[local]:
  plan_eval = (\F C owner rows ent.
    FOLDL (\(es,r) row. case r of
      OK s => (es ++ FST (row_eval F C owner row s), SND (row_eval F C owner row s))
    | other => (es,other)) ([],OK ent) rows) /\
  k < LENGTH rows /\ plan_eval fuel C owner (TAKE (SUC k) rows) ent = (E,OK t) ==>
  ?pre s rowE. plan_eval fuel C owner (TAKE k rows) ent = (pre,OK s) /\
    row_eval fuel C owner (EL k rows) s = (rowE,OK t) /\ E = pre ++ rowE
Proof
  strip_tac >>
  Cases_on `plan_eval fuel C owner (TAKE k rows) ent` >>
  rename1 `plan_eval _ _ _ _ _ = (pre,res)` >>
  `plan_eval fuel C owner (TAKE (SUC k) rows) ent =
    (case res of
      OK s => (pre ++ FST (row_eval fuel C owner (EL k rows) s),
               SND (row_eval fuel C owner (EL k rows) s))
    | other => (pre,other))` by
    (qpat_x_assum `plan_eval _ _ _ (TAKE (SUC k) rows) _ = _` kall_tac >>
     gvs[TAKE_SUC_BY_TAKE,FOLDL_SNOC]) >>
  Cases_on `res` >> gvs[quantHeuristicsTheory.FST_PAIR_EQ_SYM]
QED

Theorem focus_row_eval_ok[local]:
  row_eval = (\F C owner (bb,e,z) s.
    case eval_phis s bb.bb_instructions of
      OK sp =>
       (gas_events_block (F-e) C owner
         (bb with bb_instructions := TAKE (phi_prefix_length bb.bb_instructions)
            bb.bb_instructions ++ z)
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
        FOLDR (dft_exec_cons (F-e) C) OK z
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  row_eval fuel C owner (bb,e,z) s = (E,OK u) ==>
  ?sp. eval_phis s bb.bb_instructions = OK sp /\
    FOLDR (dft_exec_cons (fuel-e) C) OK z
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK u /\
    E = gas_events_block (fuel-e) C owner
      (bb with bb_instructions := TAKE (phi_prefix_length bb.bb_instructions)
         bb.bb_instructions ++ z)
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  strip_tac >> Cases_on `eval_phis s bb.bb_instructions` >> gvs[]
QED

Theorem focus_plan_residual_stop[local]:
  row_eval = (\F C owner (bb,e,z) s.
    case eval_phis s bb.bb_instructions of
      OK sp =>
       (gas_events_block (F-e) C owner
         (bb with bb_instructions := TAKE (phi_prefix_length bb.bb_instructions)
            bb.bb_instructions ++ z)
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
        FOLDR (dft_exec_cons (F-e) C) OK z
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  plan_eval = (\F C owner rows ent.
    FOLDL (\(es,r) row. case r of
      OK s => (es ++ FST (row_eval F C owner row s), SND (row_eval F C owner row s))
    | other => (es,other)) ([],OK ent) rows) /\
  plan_ok = (\F C sf a plan entry.
    plan <> [] /\
    MAP (\(bb,e,z). e) plan = GENLIST (\r. a + SUC r) (LENGTH plan) /\
    (!r bb e z. r < LENGTH plan /\ EL r plan = (bb,e,z) ==>
      e <= F /\ MEM bb sf.fn_blocks /\
      (if SUC r < LENGTH plan then
        bb.bb_instructions <> [] /\
        EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
        is_terminator (LAST bb.bb_instructions).inst_opcode /\
        ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
        z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions
       else
        LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions)
          bb.bb_instructions) /\
        z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
          bb.bb_instructions) /\
        EVERY (\i. ~is_terminator i.inst_opcode) z)) /\
    (!r bb e z es s.
      r < LENGTH plan /\ EL r plan = (bb,e,z) /\
      plan_eval F C sf.fn_name (TAKE r plan) entry = (es,OK s) ==>
      lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
      (0 < r ==> ~s.vs_halted))) /\
  plan_ok fuel C sf a rows ent /\ LAST rows = (bb,e,z) /\
  plan_eval fuel C sf.fn_name rows ent = (E,OK u) ==>
  get_instruction bb u.vs_inst_idx =
    SOME (EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) /\
  !r. exec_block (fuel-e) C bb u = r /\ ((?v. r = Halt v) \/ (?ex v. r = Abort ex v)) ==>
    run_blocks (fuel-a) C sf ent = r /\
    gas_events_blocks (fuel-a) C sf ent = E ++ gas_events_block (fuel-e) C sf.fn_name bb u
Proof
  strip_tac >>
  qpat_x_assum `plan_ok fuel C sf a rows ent` mp_tac >>
  qpat_x_assum `plan_ok = _` (fn th => simp_tac bool_ss [th]) >> strip_tac >>
  qpat_x_assum `!i b d xs. _ ==> d <= _ /\ _` (mk_asm "row_shape") >>
  qpat_x_assum `!i b d xs es s. _` (mk_asm "entry") >>
  `!k b d xs. k < LENGTH rows /\ EL k rows = (b,d,xs) ==> d = a + SUC k` by
    (rpt strip_tac >> qpat_assum `MAP _ rows = _` (mp_tac o AP_TERM ``EL k:num list -> num``) >>
     simp[EL_MAP]) >>
  `!k pre s. k < LENGTH rows /\
      plan_eval fuel C sf.fn_name (TAKE k rows) ent = (pre,OK s) ==>
      run_blocks (fuel-a) C sf ent = run_blocks (fuel-(a+k)) C sf s /\
      gas_events_blocks (fuel-a) C sf ent = pre ++ gas_events_blocks (fuel-(a+k)) C sf s` by
    (Induct >- simp[] >> rpt gen_tac >> strip_tac >>
     `k < LENGTH rows` by decide_tac >>
     drule_all_then strip_assume_tac focus_plan_snoc_ok >>
     Cases_on `EL k rows` >> rename1 `EL k rows = (b,rest)` >> PairCases_on `rest` >>
     Cases_on `EL (SUC k) rows` >> rename1 `EL (SUC k) rows = (b',rest')` >> PairCases_on `rest'` >>
     drule_all_then strip_assume_tac focus_row_eval_ok >>
     asm "row_shape" (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
     asm "entry" (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
     asm "entry" (qspec_then `SUC k` mp_tac) >> simp[] >> strip_tac >>
     qpat_assum `!k b d xs. _ ==> d = _` (drule_all_then assume_tac) >>
     qpat_assum `!pre s. _ ==> _` (drule_all_then strip_assume_tac) >>
     `fuel - (a+k) = SUC (fuel-rest0) /\ fuel - (a+SUC k) = fuel-rest0` by decide_tac >>
     qpat_x_assum `rest1 = _` SUBST_ALL_TAC >>
     qpat_x_assum `rest0 = a + SUC k` kall_tac >>
     drule_all_then strip_assume_tac focus_closed_row_continue >>
     simp[TAKE_DROP]) >>
  qabbrev_tac `k = PRE (LENGTH rows)` >>
  `SUC k = LENGTH rows /\ k < LENGTH rows` by
    (Cases_on `rows` >> gvs[Abbr `k`]) >>
  `EL k rows = (bb,e,z)` by fs[Abbr `k`,GSYM LAST_EL] >>
  `TAKE (SUC k) rows = rows` by simp[] >>
  `plan_eval fuel C sf.fn_name (TAKE (SUC k) rows) ent = (E,OK u)` by
    (qpat_assum `TAKE _ rows = _` SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC) >>
  drule_all_then strip_assume_tac focus_plan_snoc_ok >>
  qpat_assum `EL k rows = _` (fn th =>
    qpat_x_assum `row_eval _ _ _ (EL k rows) _ = _`
      (assume_tac o PURE_REWRITE_RULE [th])) >>
  drule_all_then strip_assume_tac focus_row_eval_ok >>
  asm_x "row_shape" (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
  asm_x "entry" (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
  qpat_assum `!k b d xs. _ ==> d = _` (drule_all_then assume_tac) >>
  qpat_assum `!k pre s. _ ==> _` (drule_all_then strip_assume_tac) >>
  `fuel - (a+k) = SUC (fuel-e)` by decide_tac >>
  drule_all_then strip_assume_tac focus_open_row_stop >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disch_tac >>
  qpat_assum `!r. exec_block _ _ _ _ = r /\ _ ==> _`
    (qspec_then `exec_block (fuel-e) C bb u` mp_tac) >>
  simp[]
QED

(* A successful extra level exposes both the caller position reached by
   its plan and the next entry produced by the pending call. *)
Theorem focus_rooted_snoc_ok[local]:
  rooted_eval = (\F C levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
         (prior ++ FST (plan_eval F C sf.fn_name plan ent),
          case SND (plan_eval F C sf.fn_name plan ent) of
            OK caller =>
              (case call of NONE => OK caller | SOME c => call_setup C c caller)
          | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  i < LENGTH levels /\ EL i levels = (sf,rows,call) /\
  rooted_eval fuel C (TAKE (SUC i) levels) R = (evs,OK next) ==>
  ?prior ent E caller.
    rooted_eval fuel C (TAKE i levels) R = (prior,OK ent) /\
    plan_eval fuel C sf.fn_name rows ent = (E,OK caller) /\
    evs = prior ++ E /\
    (case call of NONE => OK caller | SOME c => call_setup C c caller) = OK next
Proof
  strip_tac >>
  Cases_on `rooted_eval fuel C (TAKE i levels) R` >>
  rename1 `rooted_eval _ _ _ _ = (prior,res)` >>
  `rooted_eval fuel C (TAKE (SUC i) levels) R =
    (case res of
       OK ent =>
         (prior ++ FST (plan_eval fuel C sf.fn_name rows ent),
          case SND (plan_eval fuel C sf.fn_name rows ent) of
            OK caller =>
              (case call of NONE => OK caller | SOME c => call_setup C c caller)
          | other => other)
     | other => (prior,other))` by
    (qpat_x_assum `rooted_eval _ _ (TAKE (SUC i) levels) _ = _` kall_tac >>
     gvs[TAKE_SUC_BY_TAKE,FOLDL_SNOC]) >>
  Cases_on `res` >> gvs[] >>
  rename1 `plan_eval _ _ _ _ ent` >>
  Cases_on `plan_eval fuel C sf.fn_name rows ent` >>
  rename1 `plan_eval _ _ _ _ _ = (E,pr)` >>
  Cases_on `pr` >> gvs[]
QED

Theorem focus_invoke_residual_stop[local]:
  call_setup = (\C c s.
    case decode_invoke c of
      NONE => Error "invoke: bad operand format"
    | SOME (nm,ops) =>
      case lookup_function nm C.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee =>
        case eval_operands ops s of
          NONE => Error "invoke: undefined argument"
        | SOME args =>
          case setup_callee callee args s of
            NONE => Error "invoke: empty function"
          | SOME cs => OK cs) /\
  get_instruction bb s.vs_inst_idx = SOME c /\
  c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  call_setup C c s = OK ent /\
  run_blocks f C callee ent = r /\ ((?v. r = Halt v) \/ (?ex v. r = Abort ex v)) ==>
  exec_block f C bb s = r /\
  gas_events_block f C owner bb s = gas_events_blocks f C callee ent
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `call_setup C c s = _` mp_tac >>
  qpat_x_assum `call_setup = _` (fn th => simp_tac bool_ss [th]) >>
  simp[] >> Cases_on `eval_operands ops s` >> simp[] >>
  rename1 `eval_operands ops s = SOME args` >>
  Cases_on `setup_callee callee args s` >> simp[] >>
  disch_then (SUBST_ALL_TAC o SYM) >>
  `step_inst f C c s = r` by
    (Cases_on `r` >> fs[Once venomExecSemanticsTheory.step_inst_def]) >>
  Cases_on `r` >> fs[] >>
  (conj_tac >-
     (CONV_TAC (LAND_CONV (REWR_CONV venomExecSemanticsTheory.exec_block_def)) >> simp[]) >>
   CONV_TAC (LAND_CONV (REWR_CONV gas_events_block_def)) >>
   simp[Once gas_events_step_def])
QED

Theorem focus_levels_stop_by_plan[local]:
  rooted_eval = (\F C levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
         (prior ++ FST (plan_eval F C sf.fn_name plan ent),
          case SND (plan_eval F C sf.fn_name plan ent) of
            OK caller =>
              (case call of NONE => OK caller | SOME c => call_setup C c caller)
          | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  call_setup = (\C c s.
    case decode_invoke c of
      NONE => Error "invoke: bad operand format"
    | SOME (nm,ops) =>
      case lookup_function nm C.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee =>
        case eval_operands ops s of
          NONE => Error "invoke: undefined argument"
        | SOME args =>
          case setup_callee callee args s of
            NONE => Error "invoke: empty function"
          | SOME cs => OK cs) /\
  levels_ok = (\F C levels paths incoming root_fn root_entry root_path root_depth.
    levels <> [] /\ LENGTH paths = LENGTH levels /\
    LENGTH incoming = LENGTH levels /\
    HD paths = root_path /\ HD incoming = root_depth /\
    FST (HD levels) = root_fn /\
    (!i sf plan call.
      i < LENGTH levels /\ EL i levels = (sf,plan,call) ==>
      plan <> [] /\
      (!prior ent.
        rooted_eval F C (TAKE i levels) root_entry = (prior,OK ent) ==>
        plan_ok F C sf (EL i incoming) plan ent) /\
      (if SUC i < LENGTH levels then
        ?c nm ops bb e z.
          call = SOME c /\ LAST plan = (bb,e,z) /\
          c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
            bb.bb_instructions) /\
          c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
          lookup_function nm C.ctx_functions = SOME (FST (EL (SUC i) levels)) /\
          EL (SUC i) incoming = e /\
          EL (SUC i) paths = (e,c.inst_id)::EL i paths
       else call = NONE))) /\
  (!sf a rows ent bb e z E w.
    plan_ok fuel C sf a rows ent /\ LAST rows = (bb,e,z) /\
    plan_eval fuel C sf.fn_name rows ent = (E,OK w) ==>
    get_instruction bb w.vs_inst_idx =
      SOME (EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) /\
    !res. exec_block (fuel-e) C bb w = res /\ ((?v. res = Halt v) \/ (?ex v. res = Abort ex v)) ==>
      run_blocks (fuel-a) C sf ent = res /\
      gas_events_blocks (fuel-a) C sf ent = E ++ gas_events_block (fuel-e) C sf.fn_name bb w) /\
  levels_ok fuel C levels paths incoming root_fn R root_path 0 /\
  rooted_eval fuel C levels R = (Ecut,OK u) /\
  LAST levels = (sf,rows,NONE) /\ LAST rows = (bb,d,z) /\
  gas_events_block (fuel-d) C sf.fn_name bb u = [] /\
  exec_block (fuel-d) C bb u = r /\ ((?v. r = Halt v) \/ (?ex v. r = Abort ex v)) ==>
  gas_events_blocks fuel C root_fn R = Ecut
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `levels_ok fuel C levels paths incoming root_fn R root_path 0` mp_tac >>
  qpat_x_assum `levels_ok = _` (fn th => simp_tac bool_ss [th]) >> strip_tac >>
  qpat_x_assum `!i sf plan call. _ ==> _` (mk_asm "level") >>
  qpat_x_assum `!sf a rows ent bb e z E w. _ ==> _` (mk_asm "plan") >>
  `!n i. LENGTH levels = i + SUC n ==>
    ?prior ent. rooted_eval fuel C (TAKE i levels) R = (prior,OK ent) /\
      run_blocks (fuel - EL i incoming) C (FST (EL i levels)) ent = r /\
      prior ++ gas_events_blocks (fuel - EL i incoming) C (FST (EL i levels)) ent = Ecut` by
    (Induct
     >- (rpt strip_tac >> `i < LENGTH levels` by decide_tac >>
         `EL i levels = (sf,rows,NONE)` by
           (`i = PRE (LENGTH levels)` by decide_tac >> metis_tac[LAST_EL]) >>
         `TAKE (SUC i) levels = levels` by
           (`SUC i = LENGTH levels` by decide_tac >> pop_assum SUBST1_TAC >> simp[NoAsms]) >>
         `rooted_eval fuel C (TAKE (SUC i) levels) R = (Ecut,OK u)` by
           (qpat_assum `TAKE _ levels = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
         drule_all_then strip_assume_tac focus_rooted_snoc_ok >>
         qpat_x_assum `(case NONE of NONE => OK caller | SOME c => call_setup C c caller) = OK u`
           (SUBST_ALL_TAC o SRULE []) >>
         asm "level" (qspecl_then [`i`,`sf`,`rows`,`NONE`] mp_tac) >>
         (impl_tac >- simp[]) >> disch_then (map_every assume_tac o CONJUNCTS) >>
         qpat_assum `!prior ent. _ ==> plan_ok _ _ _ _ _ _` (drule_all_then assume_tac) >>
         asm "plan" (drule_all_then strip_assume_tac) >>
         qpat_assum `!res. _ ==> _` (qspec_then `r` mp_tac) >> simp[] >> strip_tac >>
         qexistsl [`prior`,`ent`] >> simp[]) >>
     rpt strip_tac >> `i < LENGTH levels /\ SUC i < LENGTH levels` by decide_tac >>
     `LENGTH levels = SUC i + SUC n` by decide_tac >>
     qpat_assum `!i. _ ==> ?prior ent. _` (drule_all_then strip_assume_tac) >>
     rename1 `rooted_eval fuel C (TAKE (SUC i) levels) R = (nextE,OK next)` >>
     Cases_on `EL i levels` >> rename1 `EL i levels = (parent,lev)` >> PairCases_on `lev` >>
     drule_all_then strip_assume_tac focus_rooted_snoc_ok >>
     asm "level" (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
     asm "plan" (drule_all_then strip_assume_tac) >>
     rename1 `LAST lev0 = (pb,EL (SUC i) incoming,pz)` >>
     qabbrev_tac `c = EL (LENGTH pz) (DROP (phi_prefix_length pb.bb_instructions) pb.bb_instructions)` >>
     `call_setup C c caller = OK next` by
       (qpat_x_assum `(case lev1 of NONE => OK caller | SOME ci => call_setup C ci caller) = _`
          mp_tac >> simp[IgnAsm `call_setup = _`]) >>
     drule_all_then strip_assume_tac focus_invoke_residual_stop >>
     qpat_assum `!res. _ ==> _` (qspec_then `r` mp_tac) >> simp[] >> strip_tac >>
     metis_tac[APPEND_ASSOC]) >>
  `LENGTH levels = 0 + SUC (PRE (LENGTH levels))` by (Cases_on `levels` >> gvs[]) >>
  qpat_assum `!n i. _ ==> _` (drule_all_then strip_assume_tac) >>
  qpat_x_assum `rooted_eval fuel C (TAKE 0 levels) R = _` mp_tac >>
  qpat_x_assum `rooted_eval = _` (fn th => simp_tac bool_ss [th,TAKE,FOLDL]) >>
  strip_tac >> gvs[]
QED

Theorem focus_rooted_silent_stop_events[local]:
  row_eval = (\F C owner (bb,e,z) s.
    case eval_phis s bb.bb_instructions of
      OK sp =>
       (gas_events_block (F-e) C owner
         (bb with bb_instructions := TAKE (phi_prefix_length bb.bb_instructions)
            bb.bb_instructions ++ z)
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
        FOLDR (dft_exec_cons (F-e) C) OK z
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  plan_eval = (\F C owner rows ent.
    FOLDL (\(es,r) row. case r of
      OK s => (es ++ FST (row_eval F C owner row s), SND (row_eval F C owner row s))
    | other => (es,other)) ([],OK ent) rows) /\
  plan_ok = (\F C sf a plan entry.
    plan <> [] /\
    MAP (\(bb,e,z). e) plan = GENLIST (\r. a + SUC r) (LENGTH plan) /\
    (!r bb e z. r < LENGTH plan /\ EL r plan = (bb,e,z) ==>
      e <= F /\ MEM bb sf.fn_blocks /\
      (if SUC r < LENGTH plan then
        bb.bb_instructions <> [] /\
        EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
        is_terminator (LAST bb.bb_instructions).inst_opcode /\
        ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
        z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions
       else
        LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions)
          bb.bb_instructions) /\
        z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
          bb.bb_instructions) /\
        EVERY (\i. ~is_terminator i.inst_opcode) z)) /\
    (!r bb e z es s.
      r < LENGTH plan /\ EL r plan = (bb,e,z) /\
      plan_eval F C sf.fn_name (TAKE r plan) entry = (es,OK s) ==>
      lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
      (0 < r ==> ~s.vs_halted))) /\
  rooted_eval = (\F C levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
         (prior ++ FST (plan_eval F C sf.fn_name plan ent),
          case SND (plan_eval F C sf.fn_name plan ent) of
            OK caller =>
              (case call of NONE => OK caller | SOME c => call_setup C c caller)
          | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  call_setup = (\C c s.
    case decode_invoke c of
      NONE => Error "invoke: bad operand format"
    | SOME (nm,ops) =>
      case lookup_function nm C.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee =>
        case eval_operands ops s of
          NONE => Error "invoke: undefined argument"
        | SOME args =>
          case setup_callee callee args s of
            NONE => Error "invoke: empty function"
          | SOME cs => OK cs) /\
  levels_ok = (\F C levels paths incoming root_fn root_entry root_path root_depth.
    levels <> [] /\ LENGTH paths = LENGTH levels /\
    LENGTH incoming = LENGTH levels /\
    HD paths = root_path /\ HD incoming = root_depth /\
    FST (HD levels) = root_fn /\
    (!i sf plan call.
      i < LENGTH levels /\ EL i levels = (sf,plan,call) ==>
      plan <> [] /\
      (!prior ent.
        rooted_eval F C (TAKE i levels) root_entry = (prior,OK ent) ==>
        plan_ok F C sf (EL i incoming) plan ent) /\
      (if SUC i < LENGTH levels then
        ?c nm ops bb e z.
          call = SOME c /\ LAST plan = (bb,e,z) /\
          c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
            bb.bb_instructions) /\
          c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
          lookup_function nm C.ctx_functions = SOME (FST (EL (SUC i) levels)) /\
          EL (SUC i) incoming = e /\
          EL (SUC i) paths = (e,c.inst_id)::EL i paths
       else call = NONE))) /\
  levels_ok fuel C levels paths incoming root_fn R root_path 0 /\
  rooted_eval fuel C levels R = (Ecut,OK u) /\
  LAST levels = (sf,rows,NONE) /\ LAST rows = (bb,d,z) /\
  get_instruction bb u.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ((?v. step_inst (fuel-d) C inst u = Halt v) \/
   (?ex v. step_inst (fuel-d) C inst u = Abort ex v) \/
   (is_terminator inst.inst_opcode /\
    ?v. step_inst (fuel-d) C inst u = OK v /\ v.vs_halted)) ==>
  gas_events_blocks fuel C root_fn R = Ecut
Proof
  disch_tac >>
  pop_assum (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `!sf a rows ent bb e z E w.
    plan_ok fuel C sf a rows ent /\ LAST rows = (bb,e,z) /\
    plan_eval fuel C sf.fn_name rows ent = (E,OK w) ==>
    get_instruction bb w.vs_inst_idx =
      SOME (EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) /\
    !res. exec_block (fuel-e) C bb w = res /\ ((?v. res = Halt v) \/ (?ex v. res = Abort ex v)) ==>
      run_blocks (fuel-a) C sf ent = res /\
      gas_events_blocks (fuel-a) C sf ent = E ++ gas_events_block (fuel-e) C sf.fn_name bb w` by
    (rpt gen_tac >> strip_tac >> drule_all focus_plan_residual_stop >> simp_tac bool_ss []) >>
  qabbrev_tac `r = exec_block (fuel-d) C bb u` >>
  `exec_block (fuel-d) C bb u = r` by simp[Abbr `r`] >>
  Q.SUBGOAL_THEN `gas_events_block (fuel-d) C sf.fn_name bb u = [] /\
    ((?v. r = Halt v) \/ (?ex v. r = Abort ex v))`
    (map_every assume_tac o CONJUNCTS)
  >- (drule gas_events_block_at >> disch_then (rewrite_tac o single) >>
      simp_tac bool_ss [Abbr `r`] >>
      once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >>
      qpat_x_assum `(?v. step_inst _ _ _ _ = Halt v) \/ _` strip_assume_tac >>
      simp[Once gas_events_step_def]) >>
  drule_all focus_levels_stop_by_plan >> simp_tac bool_ss []
QED

(* A pseudo cut fetches from the common prefix of both retained rows. *)
Theorem focus_pseudo_cut_instruction[local]:
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  phi_prefix_length bt.bb_instructions <= k /\ k < LENGTH ps /\
  get_instruction bt k = SOME inst /\
  z = DROP (phi_prefix_length bb.bb_instructions) (TAKE k ps) ==>
  EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = inst /\
  MEM inst bb.bb_instructions
Proof
  rpt strip_tac >>
  `phi_prefix_length bb.bb_instructions = phi_prefix_length ps /\
   phi_prefix_length bt.bb_instructions = phi_prefix_length ps` by
    (simp[] >> conj_tac >> irule dftIndexedExecTheory.dft_phi_prefix_append >>
     fs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  `EL k ps = inst` by gvs[get_instruction_def,EL_APPEND_EQN] >>
  simp[LENGTH_TAKE,LENGTH_DROP,EL_DROP,EL_APPEND_EQN] >>
  disj1_tac >> metis_tac[EL_MEM]
QED

Theorem focus_cut_observation_identity[local]:
  (src = inst \/ from_block [src] inst) /\ inv_memory_observation src.inst_opcode ==>
  src = inst
Proof
  rw[dftStructuralTheory.from_block_def] >>
  Cases_on `src.inst_opcode` >>
  gvs[inv_memory_observation_def,is_flippable_def,venomEffectsTheory.is_commutative_def,
      passSharedDefsTheory.is_comparator_def]
QED

Theorem focus_cut_static_safety[local]:
  raw_reachable (root_entry with vs_gas_readings := gs ++ tail) C sf src u /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
  LENGTH Mcut < n /\ u.vs_gas_readings = tail /\
  mem_inv (\ctx f i v. gas_cut n (root_entry with vs_gas_readings := gs ++ tail) v ==>
    static_mem_ok limit ctx f i v) C (root_entry with vs_gas_readings := gs ++ tail) ==>
  static_mem_ok limit C sf src u
Proof
  strip_tac >>
  `LENGTH gs = LENGTH Mcut` by metis_tac[LIST_REL_LENGTH] >>
  `gas_cut n (root_entry with vs_gas_readings := gs ++ tail) u` by simp[gas_cut_def] >>
  fs[mem_inv_raw_reachable] >> metis_tac[]
QED

Theorem focus_cut_nonforwarding[local]:
  raw_reachable R C sf src u /\
  o1_ctx_shape C /\ MEM sf C.ctx_functions /\ tf = dft_fn sf /\ dft_fn_rel sf tf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\ MEM src bb.bb_instructions /\
  lookup_block s.vs_current_bb tf.fn_blocks = SOME bt /\ bt.bb_label = bb.bb_label /\
  get_instruction bt s.vs_inst_idx = SOME inst /\ (src = inst \/ from_block [src] inst) /\
  ~in_revert_forward tf s ==> ~in_revert_forward sf u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> strip_tac >>
  drule_then assume_tac stepWriteFootprintBaseTheory.raw_reachable_active >>
  `wf_function sf` by fs[dft_fn_rel_def] >>
  drule_all_then assume_tac dft_packet_active_block >>
  `s.vs_current_bb = bb.bb_label` by metis_tac[simplifyCfgDefsTheory.lookup_block_member_label] >>
  `inv_memory_observation src.inst_opcode` by
    (qpat_x_assum `in_revert_forward sf u`
       (strip_assume_tac o REWRITE_RULE [in_revert_forward_def]) >>
     qpat_assum `active_inst sf src u`
       (strip_assume_tac o REWRITE_RULE [active_inst_def]) >>
     drule_all_then assume_tac venomExecProofsTheory.wf_lookup_block >>
     `get_instruction bb u.vs_inst_idx = SOME src` by gvs[get_instruction_def] >>
     `revert_forward_at bb u.vs_inst_idx` by gvs[] >>
     drule_all revert_forward_at_opcode >>
     simp[inv_memory_observation_def] >> metis_tac[]) >>
  `src = inst` by (irule focus_cut_observation_identity >> simp[]) >>
  `MEM bt tf.fn_blocks` by metis_tac[simplifyCfgDefsTheory.lookup_block_member_label] >>
  `active_inst tf inst s` by (simp[active_inst_def] >> qexists `bt` >> gvs[get_instruction_def]) >>
  qpat_x_assum `tf = dft_fn sf` SUBST_ALL_TAC >>
  qpat_x_assum `src = inst` SUBST_ALL_TAC >>
  `u.vs_current_bb = s.vs_current_bb` by simp[] >>
  drule_all dftGasInvForwardActiveTheory.inv_forward_active >> simp[]
QED

(* The caller supplies the prefix at the actual retained row. The cut and all
   three inventory splits below are taken from that same packet. *)
Theorem focus_selected_endpoint_cut[local]:
  !rho count. dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn8 inst8 s8 oms om hs hist) raw_slots sites unused /\
  FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,NONE,NONE) /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,OK s8,F,NONE) /\
  ((IS_SOME body_entry /\ q = EL count rho /\ q < LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
    (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
   (body_entry = NONE /\ q = 0 /\
    z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s8.vs_inst_idx ps))) ==>
  get_instruction bt s8.vs_inst_idx = SOME inst8 /\
  ?src_inst cuts levels Mcut Ecut Kcut mr er kr.
    src_inst = EL (LENGTH z)
      (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    ((IS_SOME body_entry /\ LENGTH ps <= s8.vs_inst_idx /\
      s8.vs_inst_idx - LENGTH ps < LENGTH rho /\
      q = EL (s8.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
      (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
      (inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
        inst8.inst_opcode = INVOKE ==> EL q xs = inst8) /\
      z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
     (body_entry = NONE /\ s8.vs_inst_idx < LENGTH ps /\ q = 0 /\
      z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s8.vs_inst_idx ps))) /\
    MAP (\(ai,ds,ei,qi,zi). ai) cuts =
      REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
    LENGTH cuts = LENGTH levels /\
    (!i ai ds ei qi zi.
      i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
        ini hi bei counti fronti closedi resti later.
        FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
        FLOOKUP blocks (ai,ei) =
          SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
        orderi = ds ++ ei::later /\
        (if SUC i = LENGTH cuts then
          ai = p /\ ei = d /\ qi = q /\ zi = z
        else
          ?cid h b0 done_at_call child_entry ret.
            EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
            FLOOKUP calls (ai,ei,cid) =
              SOME (qi,h,b0,done_at_call,child_entry,ret) /\
            qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
            zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
            EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
            (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
        EL i levels =
          (sfi,
           MAP (\f.
             (FST (THE (FLOOKUP blocks (ai,f))),f,
              DROP (phi_prefix_length
                (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
             [(bbi,ei,zi)],
           if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
    Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
    Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
    Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
    raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\
    FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts [])))))))) = Kcut ++ kr /\
    LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
    (!F gs tail.
      N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
      (?extra. Ecut = FST (rooted_eval F C7 levels
        (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
      (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
        OK u =>
          FST (rooted_eval F C7 levels
            (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
          u.vs_gas_readings = tail /\
          (?before after.
            dftGasFromListTraceDefs$trace_blocks [] 0 F C7 root_sf
              (root_entry with vs_gas_readings := gs ++ tail) =
              before ++ [((p,d,(EL (LENGTH z)
                (DROP (phi_prefix_length bb.bb_instructions)
                  bb.bb_instructions)).inst_id),sf,
                EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                  bb.bb_instructions),u)] ++ after /\
            dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
          (!tail'. rooted_eval F C7 levels
            (root_entry with vs_gas_readings := gs ++ tail') =
              (Ecut,OK (u with vs_gas_readings := tail'))) /\
          (body_entry = NONE ==>
            u with vs_gas_readings := s8.vs_gas_readings = s8) /\
          (IS_SOME body_entry /\ inv_memory_observation inst8.inst_opcode /\ EL q xs = inst8 ==>
            (!op. MEM op inst8.inst_operands ==> eval_operand op u = eval_operand op s8) /\
            u.vs_initial_fmp = s8.vs_initial_fmp)
      | stopped =>
          run_blocks F C7 root_sf
            (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
          gas_events_blocks F C7 root_sf
            (root_entry with vs_gas_readings := gs ++ tail) =
            FST (rooted_eval F C7 levels
              (root_entry with vs_gas_readings := gs ++ tail)))) /\
    (!F gs tail n u.
      N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
      LENGTH Mcut < n /\
      mem_inv (\ctx src_fn src_inst src_state.
        gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
          static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
        C7 (root_entry with vs_gas_readings := gs ++ tail) /\
      rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail) =
        (Ecut,OK u) ==>
      static_mem_ok cpl.cp_max_static_eom C7 sf src_inst u /\
      (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
      (inv_memory_observation src_inst.inst_opcode ==>
        (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op s8) /\
        u.vs_initial_fmp = s8.vs_initial_fmp))
Proof
  map_every qx_gen_tac [`sched`,`done`] >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "packet")
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,NONE,NONE)` (mk_asm "act") >>
  qpat_assum `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,sched,in_state,h0,body_entry,done,OK s8,F,NONE)`
    (mk_asm "block") >>
  asm_x "packet" (strip_assume_tac o PURE_REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _`
    (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o PURE_REWRITE_RULE [joint_config_11]) >>
  qpat_x_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
       body_entry count front closed brest q z. _` rev_drule >>
  disch_then rev_drule >>
  disch_then (qspecl_then [`q`,`z`] mp_tac) >>
  (impl_tac >- (simp_tac bool_ss [] >> metis_tac[])) >>
  strip_tac >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> ?sf tf inc entry order res nrest sp. _`
    rev_drule >> strip_tac >>
  qpat_x_assum `FLOOKUP acts p = SOME _` mp_tac >>
  asm "act" (CONV_TAC o LAND_CONV o SIMP_CONV (srw_ss()) o single) >>
  disch_then (map_every (fn th => VSUBST_TAC (SYM th) ORELSE VSUBST_TAC th) o CONJUNCTS) >>
  qpat_x_assum `FLOOKUP blocks (p,d) = SOME _` mp_tac >>
  asm "block" (CONV_TAC o LAND_CONV o SIMP_CONV (srw_ss()) o single) >>
  disch_then (map_every (fn th => VSUBST_TAC (SYM th) ORELSE VSUBST_TAC th) o CONJUNCTS) >>
  qpat_x_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
    rev_drule >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rename1 `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,schedule,in_state,h0,body_entry,n_done,OK s8,F,NONE)` >>
  `(body_entry = NONE ==>
      phi_prefix_length bt.bb_instructions <= s8.vs_inst_idx /\ s8.vs_inst_idx < LENGTH ps) /\
    (IS_SOME body_entry ==> s8.vs_inst_idx = LENGTH ps + n_done /\ n_done < LENGTH schedule /\
    from_block [EL q xs] inst8)` by
    (qpat_assum `(case body_entry of NONE => _ | SOME _ => s8.vs_inst_idx = _ /\ _)` mp_tac >>
     qpat_assum `(IS_SOME body_entry /\ q = _ /\ _) \/ _` mp_tac >>
     qpat_assum `LIST_REL _ schedule ys` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `body_entry` >> simp[LIST_REL_EL_EQN] >> metis_tac[]) >>
  qexistsl [`EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)`,
    `cuts`,`levels`,`Mcut`,`Ecut`,`Kcut`,`mr`,`er`,`kr`] >>
  (conj_tac >- REFL_TAC) >>
  (conj_tac >-
    (qpat_assum `IS_SOME body_entry ==> _` mp_tac >>
     qpat_assum `body_entry = NONE ==> _` mp_tac >>
     qpat_assum `(IS_SOME body_entry /\ q = _ /\ _) \/ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `body_entry` >> simp[] >>
     metis_tac[focus_guarded_singleton,dftGasInvMemoryObservationTheory.inv_memory_observation_original,MEM])) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (qpat_x_assum `!i ai ds ei qi zi. _` mp_tac >>
    pure_rewrite_tac [pairTheory.pair_CASE_def] >> simp_tac bool_ss [])) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (qpat_assum `raw_slots = AM []` SUBST1_TAC >> first_assum ACCEPT_TAC)) >>
  (conj_tac >- (qpat_assum `sites = AE []` SUBST1_TAC >> first_assum ACCEPT_TAC)) >>
  (conj_tac >- (qpat_assum `AK [] = Kcut ++ kr` mp_tac >>
    qpat_assum `AK = _` (fn th => simp_tac bool_ss [th]))) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >-
    (map_every qx_gen_tac [`fuel`,`gs`,`tail`] >> strip_tac >>
     qpat_assum `!F gs tail. _ ==> levels_ok _ _ _ _ _ _ _ _ _ /\ _`
       (qspecl_then [`fuel`,`gs`,`tail`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [])) >>
  map_every qx_gen_tac [`fuel`,`gs`,`tail`,`n`,`u`] >> strip_tac >>
  qpat_x_assum `!F gs tail. _ ==> levels_ok _ _ _ _ _ _ _ _ _ /\ _`
    (qspecl_then [`fuel`,`gs`,`tail`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `rooted_eval fuel _ _ _ = (Ecut,OK u)`
    (fn th => pure_rewrite_tac [th]) >>
  disch_then (strip_assume_tac o SRULE []) >>
  qabbrev_tac `src = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` >>
  qabbrev_tac `R = root_entry with vs_gas_readings := gs ++ tail` >>
  `MEM ((p,d,src.inst_id),sf,src,u) (dftGasFromListTraceDefs$trace_blocks [] 0 fuel C7 root_sf R)` by
    (qpat_assum `dftGasFromListTraceDefs$trace_blocks [] 0 fuel C7 root_sf R = _`
      (fn th => simp_tac (srw_ss()) [th])) >>
  `R.vs_prev_bb = NONE /\ R.vs_current_bb = lbl /\ R.vs_inst_idx = 0` by simp[Abbr `R`] >>
  `raw_reachable R C7 sf src u` by
    (qpat_assum `MEM ((p,d,src.inst_id),sf,src,u) _` mp_tac >>
     qpat_assum `R.vs_prev_bb = NONE` mp_tac >>
     qpat_assum `R.vs_current_bb = lbl` mp_tac >>
     qpat_assum `R.vs_inst_idx = 0` mp_tac >>
     qpat_assum `C7.ctx_entry = SOME nm` mp_tac >>
     qpat_assum `lookup_function nm C7.ctx_functions = SOME root_sf` mp_tac >>
     qpat_assum `fn_entry_label root_sf = SOME lbl` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[dftFinitePacketReachabilityTheory.dft_packet_trace_raw_reachable]) >>
  `(body_entry = NONE ==> z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s8.vs_inst_idx ps)) /\
   (IS_SOME body_entry ==> q < LENGTH xs /\ z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs)` by
    (qpat_assum `(IS_SOME body_entry /\ q = _ /\ _) \/ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `body_entry` >> simp[]) >>
  `IS_SOME body_entry ==> src = EL q xs /\ MEM src bb.bb_instructions /\ from_block [src] inst8` by
    (strip_tac >>
     qpat_assum `IS_SOME body_entry ==> q < LENGTH xs /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `IS_SOME body_entry ==> s8.vs_inst_idx = _ /\ _` (drule_then strip_assume_tac) >>
     `src = EL q xs` by
       (simp_tac bool_ss [Abbr `src`] >> drule_all dft_packet_cut_instruction >> simp_tac bool_ss []) >>
     qpat_assum `bb.bb_instructions = ps ++ xs` SUBST1_TAC >> simp[EL_MEM]) >>
  `body_entry = NONE ==> src = inst8 /\ MEM src bb.bb_instructions` by
    (strip_tac >>
     qpat_assum `body_entry = NONE ==> z = _` (drule_then assume_tac) >>
     qpat_assum `body_entry = NONE ==> phi_prefix_length _ <= _ /\ _` (drule_then strip_assume_tac) >>
     `EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = inst8 /\
        MEM inst8 bb.bb_instructions` by (drule_all focus_pseudo_cut_instruction >> simp_tac bool_ss []) >>
     simp_tac bool_ss [Abbr `src`] >>
     qpat_assum `EL (LENGTH z) _ = inst8` SUBST1_TAC >>
     simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  `MEM src bb.bb_instructions /\ (src = inst8 \/ from_block [src] inst8)` by
    (qpat_assum `body_entry = NONE ==> src = inst8 /\ _` mp_tac >>
     qpat_assum `IS_SOME body_entry ==> src = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `body_entry` >> simp[]) >>
  (conj_tac >-
    (qunabbrev_tac `R` >> irule focus_cut_static_safety >>
     qexistsl [`Mcut`,`gs`,`n`,`root_entry`,`tail`] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  (conj_tac >-
    (strip_tac >> irule focus_cut_nonforwarding >>
     qexistsl [`C7`,`R`,`bb`,`bt`,`inst8`,`s8`,`src`,`fn8`] >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, disj1_tac >> first_assum ACCEPT_TAC,
            disj2_tac >> first_assum ACCEPT_TAC])) >>
  strip_tac >>
  `src = inst8` by
    (first_assum ACCEPT_TAC ORELSE
     (irule focus_cut_observation_identity >>
      (conj_tac >- first_assum ACCEPT_TAC) >> disj2_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `src = inst8` SUBST1_TAC >>
  (Cases_on `body_entry`
   >- (qpat_assum `NONE = NONE ==> (_ with vs_gas_readings := _) = _`
         (SUBST1_TAC o SYM o SRULE []) >>
       simp[gasOracleReplayTheory.gas_eval_operand])) >>
  qpat_assum `IS_SOME (SOME _) ==> src = _ /\ _`
    (map_every assume_tac o CONJUNCTS o SRULE []) >>
  `EL q xs = inst8` by
    (qpat_assum `src = EL q xs` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `inv_memory_observation inst8.inst_opcode` by
    (qpat_assum `src = inst8` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qpat_assum `IS_SOME (SOME _) /\ inv_memory_observation _ /\ _ ==> _`
    (mp_tac o SRULE [optionTheory.IS_SOME_DEF]) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC
QED

(* The visit recursion and native execution have the same continuation
   boundaries.  A halt or abort is propagated unchanged out of INVOKE. *)
Theorem focus_native_terminal_visit_mutual[local]:
  (!P D fuel C f outer s p d g i u r.
    MEM ((p,d,i.inst_id),g,i,u) (trace_step P D fuel C f outer s) /\
    ((?t. step_inst (D + fuel - d) C i u = OK t /\ t.vs_halted /\
          is_terminator i.inst_opcode /\ r = Halt t) \/
     ((?t. r = Halt t) \/ (?a t. r = Abort a t)) /\
      step_inst (D + fuel - d) C i u = r) ==>
    step_inst fuel C outer s = r) /\
  (!P D fuel C f bb s p d g i u r.
    MEM ((p,d,i.inst_id),g,i,u) (trace_block P D fuel C f bb s) /\
    ((?t. step_inst (D + fuel - d) C i u = OK t /\ t.vs_halted /\
          is_terminator i.inst_opcode /\ r = Halt t) \/
     ((?t. r = Halt t) \/ (?a t. r = Abort a t)) /\
      step_inst (D + fuel - d) C i u = r) ==>
    exec_block fuel C bb s = r) /\
  (!P D fuel C f s p d g i u r.
    MEM ((p,d,i.inst_id),g,i,u) (trace_blocks P D fuel C f s) /\
    ((?t. step_inst (D + fuel - d) C i u = OK t /\ t.vs_halted /\
          is_terminator i.inst_opcode /\ r = Halt t) \/
     ((?t. r = Halt t) \/ (?a t. r = Abort a t)) /\
      step_inst (D + fuel - d) C i u = r) ==>
    run_blocks fuel C f s = r)
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume focus_native_terminal_visit_mutual[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  Cases_on `outer.inst_opcode = INVOKE` >> gnvs[Once (cj 1 trace_defs)] >>
  Cases_on `decode_invoke outer` >> gnvs[] >>
  rename1 `decode_invoke outer = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 C.ctx_functions` >> gnvs[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> gnvs[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> gnvs[] >>
  rename1 `setup_callee _ _ _ = SOME cs` >>
  `run_blocks fuel C callee cs = r` by (first_x_assum irule >> metis_tac[]) >>
  `(?t. r = Halt t) \/ (?a t. r = Abort a t)` by metis_tac[] >>
  once_rewrite_tac[venomExecSemanticsTheory.step_inst_def] >> gvs[]
QED

Resume focus_native_terminal_visit_mutual[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `MEM _ _` mp_tac >> simp[Once (cj 2 trace_defs)]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME head` >>
  drule_then assume_tac trace_block_visit >>
  qpat_x_assum `MEM _ (trace_block _ _ _ _ _ _ _)` mp_tac >>
  simp[MEM_APPEND] >> simp[Once exec_block_def] >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac assume_tac)
  >- gvs[] >>
  Cases_on `MEM ((p,d,i.inst_id),g,i,u) (trace_step P D fuel C f head s)`
  >- (`step_inst fuel C head s = r` by
        (first_x_assum irule >> metis_tac[]) >>
      `(?t. r = Halt t) \/ (?a t. r = Abort a t)` by metis_tac[] >>
      gvs[]) >>
  Cases_on `step_inst fuel C head s` >> gnvs[] >>
  Cases_on `is_terminator head.inst_opcode` >> gnvs[] >>
  first_x_assum irule >> metis_tac[]
QED

Resume focus_native_terminal_visit_mutual[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  Cases_on `fuel` >- gvs[] >>
  rename1 `trace_blocks P D (SUC n) C f s` >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks`
  >- (qpat_x_assum `MEM _ _` mp_tac >> simp[Once (cj 3 trace_defs)]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> gnvs[] >>
  qpat_x_assum `MEM _ _` mp_tac >>
  once_rewrite_tac[cj 3 trace_defs] >> simp[] >> disch_tac >>
  rename1 `eval_phis _ _ = OK sp` >>
  CONV_TAC (LAND_CONV (REWR_CONV venomExecSemanticsTheory.run_blocks_def)) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `exec_block n C bb start` >>
  Cases_on `MEM ((p,d,i.inst_id),g,i,u) (trace_block P (SUC D) n C f bb start)`
  >- (`exec_block n C bb start = r` by
        (first_x_assum irule >> gvs[ADD_CLAUSES] >> metis_tac[]) >>
      `(?t. r = Halt t) \/ (?a t. r = Abort a t)` by metis_tac[] >> gvs[]) >>
  Cases_on `exec_block n C bb start` >> gnvs[MEM_APPEND] >>
  rename1 `exec_block _ _ _ _ = OK post` >>
  Cases_on `post.vs_halted` >> gnvs[] >>
  first_x_assum irule >> gvs[ADD_CLAUSES] >> metis_tac[]
QED

Finalise focus_native_terminal_visit_mutual

Theorem focus_native_terminal_visit_result[local]:
  h < LENGTH (trace_blocks P D fuel C f s) /\
  EL h (trace_blocks P D fuel C f s) = ((p,d,i.inst_id),g,i,u) /\
  step_inst (D + fuel - d) C i u = r /\
  ((?v. r = OK v /\ v.vs_halted /\ is_terminator i.inst_opcode) \/
   (?v. r = Halt v) \/ (?a v. r = Abort a v)) ==>
  run_blocks fuel C f s = (case r of OK v => Halt v | other => other)
Proof
  strip_tac >> gvs[] >>
  `MEM ((p,d,i.inst_id),g,i,u) (trace_blocks P D fuel C f s)` by metis_tac[MEM_EL] >>
  irule (cj 3 focus_native_terminal_visit_mutual) >>
  goal_assum $ drule_at Any >> simp[] >> metis_tac[]
QED

(* A native stop is replayed in the same inventory, with the unused
   suffix of each filling passed to the rooted cut as its tail. *)
Theorem focus_same_inventory_terminal_stop[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn tf inst s oms om hs hist) raw_slots sites unused /\
  ~s.vs_halted /\ inst.inst_opcode <> INVOKE /\
  ((?v. step_inst (N-d) C8 inst s = Halt v) \/
   (?ex v. step_inst (N-d) C8 inst s = Abort ex v)) ==>
  ?r r8. step_inst (N-d) C8 inst s = r /\
    r8 = (case r of OK v => Halt v | other => other) /\
    ((?v. r = OK v /\ v.vs_halted) \/ (?v. r = Halt v) \/
     (?ex v. r = Abort ex v)) /\
    inst.inst_opcode <> INVOKE /\
    run_blocks N C8 root_tf root_entry = r8 /\
    (!fuel gs tail. N <= fuel /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
        raw_slots gs ==>
      ?extra. sites = gas_events_blocks fuel C7 root_sf
        (root_entry with vs_gas_readings := gs ++ tail) ++ extra)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `r = step_inst (N-d) C8 inst s` >>
  qexistsl [`r`,`r`] >>
  conj_tac >- REFL_TAC >>
  conj_tac >- (Cases_on `r` >> gvs[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qunabbrev_tac `r` >>
  drule focus_current_row_cut >>
  (impl_tac >-
     (`(?v. step_inst_base inst s = Halt v) \/
       (?ex v. step_inst_base inst s = Abort ex v)` suffices_by
        metis_tac[focus_stopped_base_row] >>
      gvs[step_inst_non_invoke])) >>
  strip_tac >>
  conj_tac
  >- (qhdtm_x_assum `dft_focus_packet_rel`
        (strip_assume_tac o PURE_REWRITE_RULE [dft_focus_packet_rel_def]) >>
      qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _`
        (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o PURE_REWRITE_RULE [joint_config_11]) >>
      qpat_x_assum `(j,obs) = _` (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o
        PURE_REWRITE_RULE [pairTheory.PAIR_EQ]) >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry)`,
         `EL j (trace_blocks [] 0 N C8 root_tf root_entry) = _`,
         `(?v. step_inst (N-d) C8 inst s = Halt v) \/ _`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
      `run_blocks N C8 root_tf root_entry =
        (case step_inst (N-d) C8 inst s of OK v => Halt v | other => other)` by
        (irule focus_native_terminal_visit_result >> simp[] >>
         qexistsl [`0`,`[]`,`d`,`tf`,`j`,`inst`,`p`,`s`] >> simp[]) >>
      Cases_on `step_inst (N-d) C8 inst s` >> gvs[]) >>
  suspend "cut_selection"
QED

Resume focus_same_inventory_terminal_stop[cut_selection]:
  qpat_assum `FLOOKUP acts p = SOME _` (mk_asm "act") >>
  qpat_assum `FLOOKUP blocks (p,d) = SOME _` (mk_asm "row") >>
  qhdtm_assum `dft_focus_packet_rel`
    (strip_assume_tac o PURE_REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _`
    (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o PURE_REWRITE_RULE [joint_config_11]) >>
  qpat_x_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
       body_entry count front closed brest q z. _`
    (fn rule => asm "act" (mp_then Any mp_tac rule)) >>
  disch_then (fn rule => asm "row" (mp_then Any mp_tac rule)) >>
  disch_then (qspecl_then [`q`,`z`] mp_tac) >>
  (impl_tac >- (simp_tac bool_ss [] >> metis_tac[])) >>
  strip_tac >>
  `raw_slots = Mcut ++ mr /\ sites = Ecut ++ er` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`raw_slots = AM []`,`sites = AE []`,`AM [] = Mcut ++ mr`,`AE [] = Ecut ++ er`] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  map_every qx_gen_tac [`fuel`,`gs`,`tail`] >> strip_tac >>
  qpat_assum `raw_slots = Mcut ++ mr` (fn eq =>
    qpat_x_assum `LIST_REL _ raw_slots gs`
      (qx_choose_then `gcut` (qx_choose_then `gr` strip_assume_tac) o
       REWRITE_RULE [eq, LIST_REL_SPLIT1])) >>
  qpat_x_assum `gs = _ ++ _` SUBST1_TAC >>
  rewrite_tac [GSYM APPEND_ASSOC] >>
  qpat_assum `!F gs tail. N <= F /\ LIST_REL _ Mcut gs ==> _`
    (qspecl_then [`fuel`,`gcut`,`gr ++ tail`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  qmatch_goalsub_abbrev_tac `rooted_eval fuel C7 levels R` >>
  Cases_on `rooted_eval fuel C7 levels R` >>
  rename1 `rooted_eval fuel C7 levels R = (events,r7)` >>
  Cases_on `r7` >> simp_tac bool_ss [pairTheory.FST,pairTheory.SND,exec_result_case_def] >> strip_tac
  >- suspend "successful_cut" >>
  qexists `extra ++ er` >>
  qpat_assum `sites = Ecut ++ er` SUBST1_TAC >>
  qpat_assum `Ecut = events ++ extra` SUBST1_TAC >>
  qpat_assum `gas_events_blocks fuel C7 root_sf R = events` SUBST1_TAC >>
  simp_tac bool_ss [APPEND_ASSOC]
QED

Resume focus_same_inventory_terminal_stop[successful_cut]:
  qpat_x_assum `IS_SOME _` (qx_choose_then `body_pair` (fn th =>
    asm_x "row" (assume_tac o PURE_REWRITE_RULE [th])) o
    REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  namedCases_on `body_pair` ["be hbe"] >>
  `(p,d) IN FDOM blocks` by simp[venomExecProofsTheory.FDOM_FLOOKUP] >>
  `?ms ess ks. FLOOKUP ms_tab (p,d) = SOME ms /\ FLOOKUP es_tab (p,d) = SOME ess /\
    FLOOKUP ks_tab (p,d) = SOME ks` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`(p,d) IN FDOM blocks`,`FDOM blocks = FDOM ms_tab`,
        `FDOM blocks = FDOM es_tab`,`FDOM blocks = FDOM ks_tab`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     metis_tac[venomExecProofsTheory.FDOM_FLOOKUP]) >>
  qpat_x_assum `!i ai ds ei qi zi. _`
    (assume_tac o BETA_RULE o PURE_REWRITE_RULE [pairTheory.pair_CASE_def]) >>
  `rooted_eval fuel C7 levels (root_entry with vs_gas_readings := gcut ++ (gr ++ tail)) =
    (events,OK v)` by
    (qpat_assum `rooted_eval fuel C7 levels R = (events,OK v)` mp_tac >> simp[Abbr `R`]) >>
  drule_all_then strip_assume_tac focus_terminal_native_prefixes >>
  drule_all_then strip_assume_tac focus_terminal_native_row >>
  `dft_fn_rel sf tf` by
    (qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
       (fn rule => asm "act" (mp_then Any strip_assume_tac rule)) >>
     first_assum ACCEPT_TAC) >>
  `lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
   lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
   EVERY (\i. is_pseudo i.inst_opcode) ps /\ EVERY (\i. ~is_pseudo i.inst_opcode) xs` by
    (qpat_assum `!a e bb bt ps xs ys rho in_state h0 body count front closed brest.
         FLOOKUP blocks (a,e) = _ ==> ?sf tf inc entry order res nrest sp. _`
       (fn rule => qpat_assum `FLOOKUP blocks (p,d) = SOME (_,_,_,_,_,_,_,_,SOME (be,hbe),_,_,_,_)`
         (mp_then Any strip_assume_tac rule)) >>
     asm "act" (fn rule => qpat_x_assum `FLOOKUP acts p = SOME _` mp_tac >>
       simp_tac (srw_ss()) [NoAsms,rule]) >>
     strip_tac >> simp[]) >>
  `MEM bb sf.fn_blocks` by
    (qpat_assum `lookup_block bb.bb_label sf.fn_blocks = SOME bb`
      (mp_then Any ACCEPT_TAC venomExecPropsTheory.lookup_block_MEM)) >>
  `EL ix ys = inst` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`get_instruction bt s.vs_inst_idx = SOME inst`,
        `s.vs_inst_idx = LENGTH ps + ix`, `bt.bb_instructions = ps ++ ys`,
        `ix < LENGTH ys`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     gvs[get_instruction_def,LENGTH_APPEND,EL_APPEND_EQN]) >>
  `xs = TAKE q xs ++ inst::DROP (SUC q) xs /\
   ys = TAKE ix ys ++ inst::DROP (SUC ix) ys` by
    (conj_tac
     >- (qspecl_then [`q`,`xs`] (CONV_TAC o LAND_CONV o REWR_CONV) (GSYM TAKE_DROP) >>
         simp[Once rich_listTheory.DROP_CONS_EL]) >>
     qspecl_then [`ix`,`ys`] (CONV_TAC o LAND_CONV o REWR_CONV) (GSYM TAKE_DROP) >>
     simp[Once rich_listTheory.DROP_CONS_EL]) >>
  `sf' = sf` by
    (qpat_assum `FLOOKUP acts p = SOME (sf',tf,inc',entry',order'',NONE,NONE)` mp_tac >>
     asm "act" (simp_tac (srw_ss()) o single)) >>
  qpat_x_assum `sf' = sf` SUBST_ALL_TAC >>
  qpat_x_assum `xs = TAKE q xs ++ inst::DROP (SUC q) xs` (fn eq =>
    map_every (fn pat => qpat_assum pat (assume_tac o ONCE_REWRITE_RULE [eq]))
      [`bb.bb_instructions = ps ++ xs`, `EVERY (\i. ~is_pseudo i.inst_opcode) xs`,
       `dft_remaining_inv sf bb xs (be with vs_gas_readings := s.vs_gas_readings)`]) >>
  qpat_x_assum `ys = TAKE ix ys ++ inst::DROP (SUC ix) ys` (fn eq =>
    qpat_assum `bt.bb_instructions = ps ++ ys` (assume_tac o ONCE_REWRITE_RULE [eq])) >>
  `inst.inst_id = inst.inst_id` by REFL_TAC >>
  drule_all_then (strip_assume_tac o CONJUNCT2) focus_terminal_prefix_factor >>
  Q.SUBGOAL_THEN `inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
    ((?t. step_inst (fuel-d) C7 inst v = Halt t) \/
     (?ex t. step_inst (fuel-d) C7 inst v = Abort ex t) \/
     (is_terminator inst.inst_opcode /\
      ?t. step_inst (fuel-d) C7 inst v = OK t /\ t.vs_halted))`
    (map_every assume_tac o CONJUNCTS)
  >- (irule focus_terminal_residual_replay >>
      qpat_assum `inv_ev_ftrace _ p d C7 M _ (_ with vs_gas_readings := _)` (irule_at Any) >>
      qpat_assum `inv_ev_ftrace _ p d C7 P _ s` (irule_at Any) >>
      qexistsl [`inst`,`N-d`,`C8`] >> simp_tac bool_ss [] >>
      map_every (fn pat => qpat_assum pat mp_tac)
       [`EVERY _ (M ++ P)`,`is_terminator inst.inst_opcode ==> _`,
        `~s.vs_halted`,`inst.inst_opcode <> INVOKE`,
        `(?v. step_inst (N-d) C8 inst s = Halt v) \/ _`] >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `LENGTH z = LENGTH ps - phi_prefix_length bb.bb_instructions + q` by
    simp[LENGTH_DROP,LENGTH_TAKE,MIN_DEF] >>
  `phi_prefix_length bb.bb_instructions <= LENGTH ps` by
    (`phi_prefix_length bb.bb_instructions = phi_prefix_length ps` by
       (qpat_assum `bb.bb_instructions = ps ++ xs` SUBST1_TAC >>
        irule dftIndexedExecTheory.dft_phi_prefix_append >>
        qpat_assum `EVERY (\i. ~is_pseudo i.inst_opcode) xs` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp_tac bool_ss [EVERY_MEM] >> metis_tac[cj 1 is_pseudo_def]) >>
     simp[phi_prefix_length_le]) >>
  `EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = inst` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH z = _`, `phi_prefix_length bb.bb_instructions <= LENGTH ps`,
        `bb.bb_instructions = ps ++ xs`, `q < LENGTH xs`, `EL q xs = inst`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     `LENGTH z + phi_prefix_length bb.bb_instructions = LENGTH ps + q` by decide_tac >>
     `LENGTH z + phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
       simp[LENGTH_APPEND] >>
     drule listTheory.EL_DROP >> disch_then SUBST1_TAC >> simp[EL_APPEND_EQN]) >>
  `v.vs_current_bb = bb.bb_label` by
    (qpat_assum `inv_ev_ftrace _ _ _ _ (TAKE q xs) _ _`
      (mp_then Any mp_tac dftGasInvTerminalReachTheory.inv_ev_ftrace_current_bb) >>
     qpat_assum `dft_remaining_inv sf bb xs be` mp_tac >>
     simp_tac (srw_ss() ++ CONJ_ss) [dft_remaining_inv_def]) >>
  `get_instruction bb v.vs_inst_idx = SOME inst` by
    (`LENGTH before < LENGTH (trace_blocks [] 0 fuel C7 root_sf R) /\
      EL (LENGTH before) (trace_blocks [] 0 fuel C7 root_sf R) = ((p,d,inst.inst_id),sf,inst,v)` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`trace_blocks [] 0 fuel C7 root_sf R = _`, `EL (LENGTH z) (DROP _ _) = inst`] >>
        POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> simp[EL_APPEND_EQN]) >>
     drule_all_then strip_assume_tac dftPacketNativeContinuationTheory.native_trace_blocks_continuation >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`v.vs_current_bb = bb.bb_label`, `lookup_block bb.bb_label sf.fn_blocks = SOME bb`,
        `lookup_block v.vs_current_bb sf.fn_blocks = SOME _`, `get_instruction _ v.vs_inst_idx = SOME inst`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  `?rows. LAST levels = (sf,rows,NONE) /\ LAST rows = (bb,d,z)` by
    (`cuts <> []` by
       (qpat_assum `MAP _ cuts = REVERSE _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> Cases_on `cuts` >>
        simp[EQ_SYM_EQ,GENLIST_EQ_NIL]) >>
     `PRE (LENGTH cuts) < LENGTH cuts /\ SUC (PRE (LENGTH cuts)) = LENGTH cuts` by
       (qpat_assum `cuts <> []` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
        Cases_on `cuts` >> simp[]) >>
     qpat_assum `!i ai ds ei qi zi. _`
       (qspec_then `PRE (LENGTH cuts)` mp_tac) >>
     qabbrev_tac `lc = EL (PRE (LENGTH cuts)) cuts` >>
     PairCases_on `lc` >>
     simp_tac (srw_ss()) [] >> strip_tac >>
     qpat_assum `LENGTH cuts = LENGTH levels` mp_tac >>
     qpat_assum `cuts <> []` mp_tac >>
     qpat_assum `FLOOKUP acts p = SOME (sf,tf,inc,entry,order,NONE,NONE)` mp_tac >>
     qpat_assum `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,SOME (be,hbe),ix,OK s,F,NONE)` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`PRE (LENGTH cuts) < LENGTH cuts ==> ?sfi. _`,
        `PRE (LENGTH cuts) < LENGTH cuts`, `SUC (PRE (LENGTH cuts)) = LENGTH cuts`] >>
     POP_ASSUM_LIST (K all_tac) >> ntac 2 disch_tac >>
     simp[] >> rpt strip_tac >>
     `levels <> []` by (Cases_on `levels` >> fs[]) >>
     drule listTheory.LAST_EL >> disch_then SUBST1_TAC >>
     gvs[] >> simp[]) >>
  qexists `er` >>
  `gas_events_blocks fuel C7 root_sf R = Ecut` suffices_by
    (qpat_assum `sites = Ecut ++ er` (simp_tac bool_ss o single)) >>
  qpat_assum `events = Ecut` (fn eq =>
    qpat_assum `rooted_eval fuel C7 levels R = (events,OK v)`
      (assume_tac o REWRITE_RULE [eq])) >>
  drule_all focus_rooted_silent_stop_events >> simp_tac bool_ss []
QED

Finalise focus_same_inventory_terminal_stop

(* The completed EVM run bounds the assembly fuel independently of the packet. *)
Theorem focus_stop_run_budget[local]:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy out.po_unit = SOME prog /\ unit_shape_ok out.po_unit /\
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
  (fin = asm_opt_finalizer ==>
     label_flow_ok unit.cu_context /\
     (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                ~MEM (Label "code_end") inst.inst_operands) /\
     EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                       ds.ds_items) unit.cu_data_segment /\
     ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                 MEM inst (fn_insts fn) /\
                 MEM (Label "runtime_begin") inst.inst_operands) ==>
      EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment)) /\
  vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es0
    (entry_asm_state vs0 es0 with as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
  run_call es0 = SOME (result,final) /\ ~frame_resource_starved es0 result final ==>
  ?B. !n ast.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n (entry_asm_state vs0 es0) = AsmOK ast /\
    (fin = asm_opt_finalizer ==>
      ?ss. sym_steps prog (asm_data_env prog vs0.vs_code) n
        (sym_init (entry_asm_state vs0 es0)) = SymOK ss) ==>
    n <= B
Proof
  strip_tac >>
  `fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
  pop_assum strip_assume_tac
  >- (`prog' = prog` by fs[combinTheory.K_THM] >>
      `(entry_asm_state vs0 es0 with as_code := assemble prog ++ vs0.vs_data_section) =
       entry_asm_state vs0 es0` by simp[entry_asm_state_def] >>
      drule_all_then assume_tac codegen_assembly_frame_prog_ok >>
      `asm_frame_rel_tail [] prog vs0.vs_data_section es0 (entry_asm_state vs0 es0) es0`
        by fs[] >>
      drule_all finalizer_frame_prefix_ready >> metis_tac[]) >>
  qpat_assum `fin = asm_opt_finalizer ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule_all_then assume_tac focus_opt_label_flow >>
  drule_all_then strip_assume_tac focus_opt_static_assembly >>
  `codegen_ready out.po_unit.cu_context` by
    (drule_all focus_false_codegen_context >> simp[codegen_context_obligations_def]) >>
  drule_all focus_finalizer_prefix_bridge >> metis_tac[]
QED

Theorem focus_uniform_frontier:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
    o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
    code_layout_valid vs0 /\
    unit_shape_ok out.po_unit /\
    generate_context_plan out.po_unit.cu_context = SOME cpl /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    (fin = asm_opt_finalizer ==>
       label_flow_ok unit.cu_context /\
       (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                  ~MEM (Label "code_end") inst.inst_operands) /\
       EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                         ds.ds_items) unit.cu_data_segment /\
       ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                   MEM inst (fn_insts fn) /\
                   MEM (Label "runtime_begin") inst.inst_operands) ==>
        EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) /\
       LENGTH vs0.vs_data_section < dimword (:256) DIV 2) /\
    (vs0.vs_call_ctx.cc_static ==>
       !fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                 ~MEM (Label "runtime_begin") inst.inst_operands) /\
    vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
    codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
    asm_frame_rel_tail [] prog' vs0.vs_data_section es0
      (entry_asm_state vs0 es0 with
        as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
    unit.cu_context.ctx_entry = SOME nm /\
    lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
    fn_entry_label entryfn = SOME lbl /\
    w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final /\
    run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
      (init_ir_supply unit) = SOME (pre,t) /\
    pre.cu_context.ctx_entry = SOME nm /\
    run_callee_first rpolicy o1_fn_passes
      (fcg_postorder (fcg_analyze pre.cu_context) nm)
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
      SOME (out.po_unit,t') /\
    stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
    stage 9 = out.po_unit.cu_context /\
    (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
      (stage k) (stage (SUC k))) /\
    (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
      EVERY (o1_fn_row k) (stage k).ctx_functions) ==>
    ?raw_slots sites unused N root_sf root_tf root_entry lbl7
      q80 q90 evs8 qs8 evs9 qs9 schedules current saved asm_fuel ast ss j obs
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
      stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8
      stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9.
  0 < N /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|> /\
  (stage 7).ctx_entry = SOME nm /\ (stage 8).ctx_entry = SOME nm /\
  lookup_function nm (stage 7).ctx_functions = SOME root_sf /\
  lookup_function nm (stage 8).ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl7 /\ fn_entry_label root_tf = SOME lbl7 /\
  joint_initial vs0 (stage 8) q80 /\ joint_initial vs0 (stage 9) q90 /\
  joint_trace vs0 (stage 8) q80 evs8 qs8 (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8) /\
  joint_trace vs0 (stage 9) q90 evs9 qs9 (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  cfg_norm_joint_cursors (stage 8) (stage 9) (schedules,current,saved) (JointConfig stk8 PG8 G8 tn8 fn8
    inst8 s8 oms8 om8 hs8 hist8) (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog asm_fuel (entry_asm_state vs0 es0) = AsmOK ast /\
  (fin = K SOME ==> normal_frame_plan rpolicy out.po_unit cpl prog (vs0 with
    <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp; vs_return_pc_token := 0w;
    vs_inst_idx := 0|>) es0 (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps prog (asm_data_env prog vs0.vs_code) asm_fuel (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rpolicy out.po_unit cpl prog vs0 es0
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast ss) /\
  dft_focus_packet_rel N (stage 7) (stage 8) root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8
      om8 hs8 hist8) raw_slots sites unused /\
  j = LENGTH evs8 /\ LENGTH evs8 <= LENGTH evs9 /\ LENGTH (TAKE j (dftGasFromListTraceDefs$trace_blocks []
    0 N (stage 8) root_tf root_entry)) = j /\
  j < LENGTH (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) /\ obs =
    dftGasFromListTraceDefs$trace_gas (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8)
    root_tf root_entry)) /\
  EL j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) =
    ((p,d,inst8.inst_id),fn8,inst8,s8) /\
  LENGTH raw_slots = LENGTH sites /\
  PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
  (?align old_cursors old_asm old_sym costs.
    LENGTH costs = LENGTH evs9 /\ LENGTH old_asm = LENGTH evs9 /\
    (fin = asm_opt_finalizer ==> LENGTH old_sym = LENGTH evs9) /\
    align 0 = 0 /\ align (LENGTH evs9) = j /\
    asm_fuel = SUM costs /\ ast = EL (LENGTH evs9) ((entry_asm_state vs0 es0)::old_asm) /\
    (fin = asm_opt_finalizer ==> ss = EL (LENGTH evs9) (sym_init (entry_asm_state vs0 es0)::old_sym)) /\
    LIST_REL (\cost edge. 0 < cost \/
      (\q. case q of JointConfig stk PG G tn fn inst s oms om hs h =>
         case lookup_block s.vs_current_bb fn.fn_blocks of
           NONE => 0
         | SOME bb => LENGTH bb.bb_instructions - s.vs_inst_idx) (SND edge) <
      (\q. case q of JointConfig stk PG G tn fn inst s oms om hs h =>
         case lookup_block s.vs_current_bb fn.fn_blocks of
           NONE => 0
         | SOME bb => LENGTH bb.bb_instructions - s.vs_inst_idx) (FST edge))
      costs (ZIP (TAKE (LENGTH evs9) (q90::qs9),qs9)) /\
    (!k. k < LENGTH evs9 ==>
      align k <= j /\
      (align (SUC k) = align k \/ align (SUC k) = SUC (align k)) /\
      align (SUC k) <= j /\
      cfg_norm_joint_cursors (stage 8) (stage 9) (old_cursors k) (EL (align k) (q80::qs8)) (EL k
        (q90::qs9)) /\
      asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        prog (EL k costs) (EL k ((entry_asm_state vs0 es0)::old_asm)) =
          AsmOK (EL (SUC k) ((entry_asm_state vs0 es0)::old_asm)) /\
      (fin = asm_opt_finalizer ==>
        sym_steps prog (asm_data_env prog vs0.vs_code) (EL k costs) (EL k (sym_init (entry_asm_state vs0
          es0)::old_sym)) =
          SymOK (EL (SUC k) (sym_init (entry_asm_state vs0 es0)::old_sym))) /\
      (case ((EL (align k) (q80::qs8)),(EL k (q90::qs9))) of
        (JointConfig frames8 p8 g8 t8 f8 i8 u8 o8 m8 sh8 oh8,
         JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) =>
          (~in_revert_forward fn9 s9 /\
  (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode ==>
    source_memory_reads_disjoint cpl inst9 s9 /\
    context_source_memory_writes_disjoint cpl inst9 s9) /\
  (fin = asm_opt_finalizer ==>
    !dst x sz src off.
      inst9.inst_opcode = CODECOPY /\ inst9.inst_operands = [dst; Var x; sz] /\
      code_end_var fn9 x /\ eval_operand (Var x) s9 = SOME src /\
      FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off ==>
      w2n (src - n2w off) < dimword (:256) DIV 2)) /\ (active_inst fn9 inst9 s9 /\
  (inst9.inst_opcode = INVOKE ==>
    ?nm' ops callee args ent.
      decode_invoke inst9 = SOME (nm',ops) /\
      lookup_function nm' (stage 9).ctx_functions = SOME callee /\
      eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent) /\
  (inst9.inst_opcode <> INVOKE ==>
    (?u. step_inst 0 (stage 9) inst9 s9 = OK u /\ ~u.vs_halted) \/
    (stk9 <> [] /\ ?ir u. step_inst 0 (stage 9) inst9 s9 = IntRet ir u))) /\
          (align (SUC k) = SUC (align k) /\ i8.inst_opcode = GAS ==>
            u8.vs_gas_readings <> [])))) /\
  (?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
      body_entry count front closed brest.
      FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (p,d) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
      get_instruction bt s8.vs_inst_idx = SOME inst8 /\
      ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
        src_inst = EL (LENGTH z)
          (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        ((IS_SOME body_entry /\ LENGTH ps <= s8.vs_inst_idx /\
          s8.vs_inst_idx - LENGTH ps < LENGTH rho /\
          q = EL (s8.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
          (p <> p \/ d <> d \/ s8 <> s8 \/
            (EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
             (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)))) /\
          (inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
             inst8.inst_opcode = INVOKE ==> EL q xs = inst8) /\
          z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
         (p = p /\ d = d /\ s8 = s8 /\ body_entry = NONE /\
          s8.vs_inst_idx < LENGTH ps /\ q = 0 /\
          z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s8.vs_inst_idx ps))) /\
        MAP (\(ai,ds,ei,qi,zi). ai) cuts =
          REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
        LENGTH cuts = LENGTH levels /\
        (!i ai ds ei qi zi.
          i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
          ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
            ini hi bei counti fronti closedi resti later.
            FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
            FLOOKUP blocks (ai,ei) =
              SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
            orderi = ds ++ ei::later /\
            (if SUC i = LENGTH cuts then
              ai = p /\ ei = d /\ qi = q /\ zi = z
            else
              ?cid h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls (ai,ei,cid) =
                  SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                  MEM r done_at_call)) /\
            EL i levels =
              (sfi,
               MAP (\f.
                 (FST (THE (FLOOKUP blocks (ai,f))),f,
                  DROP (phi_prefix_length
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                 [(bbi,ei,zi)],
               if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
        Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
        Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
        Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
        raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\ (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab
          ([],e)))) (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))) = Kcut ++ kr /\
        LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
        (!F gs tail.
          N <= F /\
          LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
          (?extra. Ecut = FST (rooted_eval F (stage 7) levels
            (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
          (case SND (rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail)) of
            OK u =>
              FST (rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
              u.vs_gas_readings = tail /\
              (?before after.
                dftGasFromListTraceDefs$trace_blocks [] 0 F (stage 7) root_sf
                  (root_entry with vs_gas_readings := gs ++ tail) =
                  before ++ [((p,d,(EL (LENGTH z)
                    (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions)).inst_id),sf,
                    EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions),u)] ++ after /\
                dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
              (!tail'. rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail') =
                  (Ecut,OK (u with vs_gas_readings := tail'))) /\
              (body_entry = NONE ==>
                u with vs_gas_readings := s8.vs_gas_readings = s8) /\
              (p = p /\ d = d /\ IS_SOME body_entry /\
               inv_memory_observation inst8.inst_opcode /\ EL q xs = inst8 ==>
                (!op. MEM op inst8.inst_operands ==>
                  eval_operand op u = eval_operand op s8) /\
                u.vs_initial_fmp = s8.vs_initial_fmp)
          | stopped =>
              run_blocks F (stage 7) root_sf
                (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
              gas_events_blocks F (stage 7) root_sf
                (root_entry with vs_gas_readings := gs ++ tail) =
                  FST (rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail)))) /\
        (!F gs tail n u.
          N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
          LENGTH Mcut < n /\
          mem_inv (\ctx src_fn src_inst src_state.
            gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
              static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
            (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
          rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
            (Ecut,OK u) ==>
          static_mem_ok cpl.cp_max_static_eom (stage 7) sf src_inst u /\
          (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
          (inv_memory_observation src_inst.inst_opcode ==>
            (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op s8) /\
            u.vs_initial_fmp = s8.vs_initial_fmp))) /\
  (!h. h < j ==>
    ?a e tf inst visit_state stk PG G tn oms om hs hist.
      EL h (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry)) =
        ((a,e,inst.inst_id),tf,inst,visit_state) /\
      EL h (q80::qs8) = JointConfig stk PG G tn tf inst visit_state oms om hs hist /\
      ?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
        body_entry count front closed brest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
        get_instruction bt visit_state.vs_inst_idx = SOME inst /\
        ((inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
          inst.inst_opcode = INVOKE) /\ ~in_revert_forward tf visit_state ==>
          ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
            src_inst = EL (LENGTH z)
              (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
            ((IS_SOME body_entry /\ LENGTH ps <= visit_state.vs_inst_idx /\
              visit_state.vs_inst_idx - LENGTH ps < LENGTH rho /\
              q = EL (visit_state.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
              (a <> p \/ e <> d \/ visit_state <> s8 \/
                (EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
                 (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)))) /\
              (inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
                 inst.inst_opcode = INVOKE ==> EL q xs = inst) /\
              z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
             (a = p /\ e = d /\ visit_state = s8 /\ body_entry = NONE /\
              visit_state.vs_inst_idx < LENGTH ps /\ q = 0 /\
              z = DROP (phi_prefix_length bb.bb_instructions) (TAKE visit_state.vs_inst_idx ps))) /\
            MAP (\(ai,ds,ei,qi,zi). ai) cuts =
              REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
            LENGTH cuts = LENGTH levels /\
            (!i ai ds ei qi zi.
              i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
              ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
                ini hi bei counti fronti closedi resti later.
                FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
                FLOOKUP blocks (ai,ei) =
                  SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
                orderi = ds ++ ei::later /\
                (if SUC i = LENGTH cuts then
                  ai = a /\ ei = e /\ qi = q /\ zi = z
                else
                  ?cid h b0 done_at_call child_entry ret.
                    EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                    FLOOKUP calls (ai,ei,cid) =
                      SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                    qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                    zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                    EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                    (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                      MEM r done_at_call)) /\
                EL i levels =
                  (sfi,
                   MAP (\f.
                     (FST (THE (FLOOKUP blocks (ai,f))),f,
                      DROP (phi_prefix_length
                        (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                        (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                     [(bbi,ei,zi)],
                   if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
            Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
            Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
            Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
            raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\ (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab
              ([],e)))) (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))) = Kcut ++ kr /\
            LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
            (!F gs tail.
              N <= F /\
              LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
              (?extra. Ecut = FST (rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
              (case SND (rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail)) of
                OK u =>
                  FST (rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
                  u.vs_gas_readings = tail /\
                  (?before after.
                    dftGasFromListTraceDefs$trace_blocks [] 0 F (stage 7) root_sf
                      (root_entry with vs_gas_readings := gs ++ tail) =
                      before ++ [((a,e,(EL (LENGTH z)
                        (DROP (phi_prefix_length bb.bb_instructions)
                          bb.bb_instructions)).inst_id),sf,
                        EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                          bb.bb_instructions),u)] ++ after /\
                    dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
                  (!tail'. rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail') =
                      (Ecut,OK (u with vs_gas_readings := tail'))) /\
                  (body_entry = NONE ==>
                    u with vs_gas_readings := visit_state.vs_gas_readings = visit_state) /\
                  (a = p /\ e = d /\ IS_SOME body_entry /\
                   inv_memory_observation inst.inst_opcode /\ EL q xs = inst ==>
                    (!op. MEM op inst.inst_operands ==>
                      eval_operand op u = eval_operand op visit_state) /\
                    u.vs_initial_fmp = visit_state.vs_initial_fmp)
              | stopped =>
                  run_blocks F (stage 7) root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
                  gas_events_blocks F (stage 7) root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) =
                      FST (rooted_eval F (stage 7) levels
                        (root_entry with vs_gas_readings := gs ++ tail)))) /\
            (!F gs tail n u.
              N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
              LENGTH Mcut < n /\
              mem_inv (\ctx src_fn src_inst src_state.
                gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
                  static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
                (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
              rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
                (Ecut,OK u) ==>
              static_mem_ok cpl.cp_max_static_eom (stage 7) sf src_inst u /\
              ~in_revert_forward sf u /\
              (inv_memory_observation src_inst.inst_opcode ==>
                (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op visit_state) /\
                u.vs_initial_fmp = visit_state.vs_initial_fmp)))) /\
  ((?r r8. step_inst (N-d) (stage 8) inst8 s8 = r /\
      r8 = (case r of OK u => Halt u | other => other) /\
      ((?u. r = OK u /\ u.vs_halted) \/ (?u. r = Halt u) \/
       (?ex u. r = Abort ex u)) /\
      inst8.inst_opcode <> INVOKE /\
      run_blocks N (stage 8) root_tf root_entry = r8 /\
      (!F gs tail. N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
          raw_slots gs ==>
        ?extra. sites = gas_events_blocks F (stage 7) root_sf
          (root_entry with vs_gas_readings := gs ++ tail) ++ extra)) \/
    in_revert_forward fn9 s9 \/
    (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode /\
     (~source_memory_reads_disjoint cpl inst9 s9 \/
      ~context_source_memory_writes_disjoint cpl inst9 s9)) \/
    (fin = asm_opt_finalizer /\
      ?dst x sz src off. inst9.inst_opcode = CODECOPY /\
        inst9.inst_operands = [dst; Var x; sz] /\ code_end_var fn9 x /\
        eval_operand (Var x) s9 = SOME src /\
        FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off /\
        ~(w2n (src - n2w off) < dimword (:256) DIV 2)) \/
    (inst8.inst_opcode = GAS /\ inst9.inst_opcode = GAS /\ s8.vs_gas_readings = []) \/
    (inst9.inst_opcode = INVOKE /\
     ~(?callee_name ops callee args ent.
        decode_invoke inst9 = SOME (callee_name,ops) /\
        lookup_function callee_name (stage 9).ctx_functions = SOME callee /\
        eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent)) \/
    (inst9.inst_opcode <> INVOKE /\ ?err. step_inst 0 (stage 9) inst9 s9 = Error err))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then
    (qx_choosel_then [`root_sf`,`lbl7`,`schedules`] (map_every assume_tac o CONJUNCTS))
    focus_production_packet_cursor_static >>
  qpat_x_assum `!N. 0 < N ==> _` (qspec_then `1` mp_tac) >>
  simp_tac bool_ss [DECIDE ``0 < (1:num)``,LET_THM] >>
  disch_then (qx_choosel_then [`bb0`,`bt0`,`ps0`,`xs0`,`ys0`,`rho0`,`f90`,
      `current0`,`rooted_eval`] (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `root_tf = dft_fn root_sf` >>
  qabbrev_tac `root_entry = vs0 with
    <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|>` >>
  qabbrev_tac `i80 = HD bt0.bb_instructions` >>
  qabbrev_tac `i90 = HD (HD f90.fn_blocks).bb_instructions` >>
  qabbrev_tac `q80 = JointConfig [] [] FEMPTY entry_taint root_tf i80 root_entry [] FEMPTY []
    [OriginInitial root_entry;
     OriginObserve (OriginSnapshot root_tf [] FEMPTY FEMPTY i80 root_entry)]` >>
  qabbrev_tac `q90 = JointConfig [] [] FEMPTY entry_taint f90 i90 root_entry [] FEMPTY []
    [OriginInitial root_entry;
     OriginObserve (OriginSnapshot f90 [] FEMPTY FEMPTY i90 root_entry)]` >>
  `joint_initial vs0 out.po_unit.cu_context q90` by
    simp[Abbr `q90`,Abbr `i90`,Abbr `root_entry`] >>
  drule_all_then assume_tac focus_false_codegen_context >>
  `(fin = K SOME ==>
      normal_frame_plan rpolicy out.po_unit cpl prog
        (vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
                    vs_return_pc_token := 0w; vs_inst_idx := 0|>)
        es0 q90 (entry_asm_state vs0 es0))` by
    (disch_tac >>
     `prog' = prog` by fs[combinTheory.K_THM] >>
     `(entry_asm_state vs0 es0 with as_code := assemble prog ++ vs0.vs_data_section) =
       entry_asm_state vs0 es0` by simp[entry_asm_state_def] >>
     `asm_frame_rel_tail [] prog vs0.vs_data_section es0 (entry_asm_state vs0 es0) es0` by fs[] >>
     irule gasFocusPlainFrameInitialStaticTheory.focus_plain_frame_initial_static >> simp[]) >>
  `(fin = asm_opt_finalizer ==>
      normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code)
        rpolicy out.po_unit cpl prog vs0 es0 q90 (entry_asm_state vs0 es0)
        (sym_init (entry_asm_state vs0 es0)))` by
    (disch_tac >>
     qpat_assum `fin = asm_opt_finalizer ==> label_flow_ok _ /\ _` (fn th =>
       mp_tac th >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac) >>
     drule_all_then assume_tac focus_opt_label_flow >>
     drule_all_then strip_assume_tac focus_opt_static_assembly >>
     irule normal_frame_symbolic_initial >> simp[focus_s7_symbolic_context_def]) >>
  `fin = asm_opt_finalizer ==>
     label_flow_ok unit.cu_context /\
     (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                ~MEM (Label "code_end") inst.inst_operands) /\
     EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                       ds.ds_items) unit.cu_data_segment /\
     ((?fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
                 MEM (Label "runtime_begin") inst.inst_operands) ==>
      EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment)` by
    (disch_tac >> qpat_assum `fin = asm_opt_finalizer ==> label_flow_ok _ /\ _`
       (fn th => mp_tac th >> asm_rewrite_tac [] >> metis_tac[])) >>
  drule_all_then (qx_choose_then `B` assume_tac) focus_stop_run_budget >>
  qpat_assum `stage 9 = out.po_unit.cu_context` (fn th =>
    map_every (fn pat => qpat_assum pat (assume_tac o ONCE_REWRITE_RULE [GSYM th]))
      [`joint_initial vs0 out.po_unit.cu_context _`,
       `joint_trace vs0 out.po_unit.cu_context _ _ _ _`,
       `cfg_norm_joint_cursors (stage 8) out.po_unit.cu_context _ _ _`]) >>
  (* State the invariant directly from the frozen conclusion, removing only
     the selected cut and the stop disjunction. The root data stay parameters. *)
  (fn (asl, goal) =>
    let
      val (ws, body) = strip_exists goal
      val fixed = ["root_sf","root_tf","lbl7","q80","q90","schedules","rooted_eval"]
      fun name v = fst (dest_var v)
      fun find n = valOf (List.find (fn v => name v = n orelse name v = n ^ "'") ws)
      val shared = map (fn n =>
        let val v = find n in v |-> mk_var (n,type_of v) end) fixed
      val entry = Parse.parse_in_context (free_vars (list_mk_conj asl))
        `vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|>`
      val use_entry = [entry |-> mk_var ("root_entry",type_of entry)]
      val f = find "asm_fuel"
      val r = genvar numSyntax.num
      val rank = Parse.parse_in_context [find "fn9",find "s9"]
        `case lookup_block s9.vs_current_bb fn9.fn_blocks of
           NONE => 0 | SOME bb => LENGTH bb.bb_instructions - s9.vs_inst_idx`
      val fields = strip_conj body
      val cert = list_mk_conj (List.take (fields, length fields - 3) @
        [List.nth (fields,length fields - 2), mk_eq (r,rank)])
      val keep = filter (fn v =>
        not (aconv v f orelse List.exists (fn {redex,...} => aconv v redex) shared)) ws
      val pred = mk_abs (f,mk_abs (r,list_mk_exists (keep,subst use_entry (subst shared cert))))
    in
      markerLib.ABBREV_TAC (mk_eq (mk_var ("Prefix",type_of pred),pred)) (asl,goal)
    end) >>
  suspend "search"
QED

Resume focus_uniform_frontier[search]:
  `vs0.vs_gas_readings = gas_readings es0` by
    (qpat_assum `asm_frame_rel_tail [] prog' _ _ _ _`
       (mp_tac o CONJUNCT2 o REWRITE_RULE [asm_frame_rel_tail_def]) >>
     simp[entry_asm_state_def]) >>
  `?r. Prefix 0 r` by
    (qpat_assum `marker$Abbrev (Prefix = _)`
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     CONV_TAC (QUANT_CONV (TRY_CONV (RATOR_CONV BETA_CONV THENC BETA_CONV))) >>
     qabbrev_tac `b0 = if phi_prefix_length bt0.bb_instructions < LENGTH ps0
                       then NONE else SOME (root_entry,0)` >>
     qabbrev_tac `ms0 = if IS_SOME b0 then
                      MAP (\i. if i.inst_opcode = GAS then [NONE:bytes32 option] else []) xs0
                    else []` >>
     qabbrev_tac `es00 = if IS_SOME b0 then
                      MAP (\i. if i.inst_opcode = GAS then [(root_sf.fn_name,i.inst_id)] else []) xs0
                    else []` >>
     qabbrev_tac `ks0 = if IS_SOME b0 then
                      MAP (\i. if i.inst_opcode = GAS then [([]:(num # num) list,1:num,i.inst_id)] else []) xs0
                    else []` >>
     qexistsl [`(case lookup_block root_entry.vs_current_bb f90.fn_blocks of
                   NONE => 0 | SOME bb => LENGTH bb.bb_instructions - root_entry.vs_inst_idx)`,
       `FLAT ms0`,`FLAT es00`,`root_entry.vs_gas_readings`,`1`,
       `[]`,`[]`,`[]`,`[]`,`current0`,`[]`,`entry_asm_state vs0 es0`,
       `sym_init (entry_asm_state vs0 es0)`,
       `FEMPTY |+ ([],(root_sf,root_tf,0:num,root_entry,[1:num],NONE,NONE))`,
       `FEMPTY |+ (([],1:num),(bb0,bt0,ps0,xs0,ys0,rho0,root_entry,0:num,b0,0:num,OK root_entry,F,NONE))`,
       `FEMPTY`,`FEMPTY |+ (([],1),ms0)`,`FEMPTY |+ (([],1),es00)`,
       `FEMPTY |+ (([],1),ks0)`,`[]`,`1`,
       `[]`,`[]`,`FEMPTY`,`entry_taint`,`root_tf`,`i80`,`root_entry`,`[]`,`FEMPTY`,`[]`,
       `[OriginInitial root_entry;
         OriginObserve (OriginSnapshot root_tf [] FEMPTY FEMPTY i80 root_entry)]`,
       `[]`,`[]`,`FEMPTY`,`entry_taint`,`f90`,`i90`,`root_entry`,`[]`,`FEMPTY`,`[]`,
       `[OriginInitial root_entry;
         OriginObserve (OriginSnapshot f90 [] FEMPTY FEMPTY i90 root_entry)]`] >>
     simp[asmSpliceTheory.sym_steps_def,Abbr `q80`,Abbr `q90`,Abbr `ks0`] >>
     conj_tac >-
       (qpat_assum `?tail. trace_blocks _ _ _ _ _ _ = _::tail`
          (strip_assume_tac) >> simp[]) >>
     conj_tac >-
       (simp[Abbr `ms0`,Abbr `es00`] >> IF_CASES_TAC >> simp[] >>
        qid_spec_tac `xs0` >> Induct >> simp[] >>
        gen_tac >> IF_CASES_TAC >> simp[]) >>
     conj_tac >-
       (`FILTER IS_SOME (FLAT ms0) = []` by
          (simp[Abbr `ms0`] >> IF_CASES_TAC >> simp[] >>
           qid_spec_tac `xs0` >> Induct >> simp[FILTER_APPEND] >>
           gen_tac >> IF_CASES_TAC >> simp[]) >>
        simp[Abbr `root_entry`]) >>
     qexistsl [`K 0`,`[]`] >> simp[combinTheory.K_THM]) >>
  `!f r. Prefix f r ==> f <= B` by
    (rpt gen_tac >>
     qpat_assum `marker$Abbrev (Prefix = _)`
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     CONV_TAC (LAND_CONV (RATOR_CONV BETA_CONV THENC BETA_CONV)) >>
     disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
     first_x_assum irule >>
     simp[]) >>
  qabbrev_tac `loss = \i. ?f r. Prefix f r /\ i = B - f` >>
  qspec_then `loss` mp_tac WhileTheory.LEAST_EXISTS_IMP >>
  (impl_tac >- (qexists `B` >> simp[Abbr `loss`] >> qexists `0` >> simp[] >>
                qexists `r` >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN2 mp_tac (mk_asm "fuel_min")) >>
  simp_tac bool_ss [Abbr `loss`] >>
  disch_then (qx_choose_then `f` (qx_choose_then `r_initial` strip_assume_tac)) >>
  `!f' r'. Prefix f' r' ==> f' <= f` by
    (rpt strip_tac >> spose_not_then assume_tac >>
     `f' <= B` by (qpat_assum `!a b. Prefix a b ==> a <= B` irule >>
                   qexists `r'` >> simp[]) >>
     `B - f' < B - f` by decide_tac >>
     asm "fuel_min" (qspec_then `B - f'` mp_tac) >>
     BETA_TAC >>
     `B - f' < (LEAST i. ?a b. Prefix a b /\ i = B - a)` by simp[] >>
     simp[] >> qexistsl [`f'`,`r'`] >> simp[]) >>
  qspec_then `Prefix f` mp_tac WhileTheory.LEAST_EXISTS_IMP >>
  (impl_tac >- (qexists `r_initial` >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qabbrev_tac `best_rank = $LEAST (Prefix f)` >>
  `!r'. Prefix f r' ==> best_rank <= r'` by
    (rpt strip_tac >> simp[GSYM arithmeticTheory.NOT_LESS] >>
     disch_tac >> qpat_assum `!n. n < best_rank ==> _` (qspec_then `r'` mp_tac) >> simp[]) >>
  qpat_x_assum `Prefix f best_rank` mp_tac >>
  qpat_assum `marker$Abbrev (Prefix = _)`
    (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  CONV_TAC (LAND_CONV (RATOR_CONV BETA_CONV THENC BETA_CONV)) >>
  disch_then (qx_choosel_then
    [`raw_slots`,`sites`,`unused`,`N`,`evs8`,`qs8`,`evs9`,`qs9`,`current`,`saved`,
     `ast`,`ss`,`acts`,`blocks`,`calls`,`ms_tab`,`es_tab`,`ks_tab`,`p`,`d`,
     `stk8`,`PG8`,`G8`,`tn8`,`fn8`,`inst8`,`s8`,`oms8`,`om8`,`hs8`,`hist8`,
     `stk9`,`PG9`,`G9`,`tn9`,`fn9`,`inst9`,`s9`,`oms9`,`om9`,`hs9`,`hist9`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?align old_cursors old_asm old_sym costs. _`
    (qx_choosel_then [`align`,`old_cursors`,`old_asm`,`old_sym`,`costs`]
       (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `j = LENGTH evs8` >>
  qabbrev_tac `obs = trace_gas (TAKE j (trace_blocks [] 0 N (stage 8) root_tf root_entry))` >>
  drule_then (map_every assume_tac o CONJUNCTS) focus_current_instruction >>
  drule_then (map_every assume_tac o CONJUNCTS) focus_cursor_ready_context >>
  `o1_fn_shape out.po_unit.cu_context fn9` by
    (qpat_x_assum `o1_ctx_shape (stage 9)` (mp_tac o REWRITE_RULE [o1_ctx_shape_def,EVERY_MEM]) >>
     qpat_assum `stage 9 = out.po_unit.cu_context` (fn eq =>
       qpat_assum `MEM fn9 (stage 9).ctx_functions` (assume_tac o REWRITE_RULE [eq])) >>
     asm_rewrite_tac [] >> strip_tac >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `(fin = asm_opt_finalizer ==>
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rpolicy out.po_unit cpl prog vs0 es0
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast ss)` by
    (disch_tac >> qpat_assum `fin = asm_opt_finalizer ==> sym_steps _ _ f _ = _ /\ _`
      (mp_tac o REWRITE_RULE [IMP_CONJ_THM]) >> asm_rewrite_tac [] >> simp[]) >>
  drule_all focus_frame_cursor_phase >>
  disch_then (qspec_then `0` (fn th =>
    qpat_assum `stage 9 = out.po_unit.cu_context`
      (fn eq => assume_tac (ONCE_REWRITE_RULE [GSYM eq] th)))) >>
  drule_all (Q.INST [`cpl` |-> `cpl`, `fin` |-> `fin`, `prog` |-> `prog`,
    `fuel` |-> `N-d`] focus_joint_selectable_stop_or_guards) >>
  disch_then (qspecl_then [`prog`,`fin`,`d`,`cpl`,`N`]
    (DISJ_CASES_THEN2 (map_every assume_tac o CONJUNCTS)
      (CONJUNCTS_THEN2 assume_tac assume_tac)))
  >- suspend "advance" >>
  suspend "stop"
QED

Resume focus_uniform_frontier[stop]:
  qpat_assum `dft_focus_packet_rel N _ _ _ _ _ (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d _ raw_slots sites unused`
    (mp_then Any mp_tac focus_current_row_cut) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then
    [`cut_sf`,`cut_inc`,`cut_entry`,`cut_order`,`cut_bb`,`cut_bt`,`cut_ps`,`cut_xs`,`cut_ys`,
     `cut_rho`,`cut_state`,`cut_h`,`cut_body`,`cut_ix`,`cut_q`,`cut_z`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `FLOOKUP blocks (p,d) = SOME (cut_bb,cut_bt,_,_,_,_,_,_,_,_,OK s8,F,NONE)`
    (mp_then Any mp_tac focus_selected_endpoint_cut) >>
  disch_then (fn rule =>
    qpat_assum `dft_focus_packet_rel N _ _ _ _ _ (j,obs)
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d _ raw_slots sites unused`
      (mp_then Any mp_tac rule)) >>
  disch_then (fn rule =>
    qpat_assum `FLOOKUP acts p = SOME (cut_sf,fn8,cut_inc,cut_entry,cut_order,NONE,NONE)`
      (mp_then Any mp_tac rule)) >>
  disch_then (qspecl_then [`cut_z`,`cut_q`,`cpl`] mp_tac) >>
  (impl_tac >- (disj1_tac >> asm_rewrite_tac [])) >>
  disch_then (CONJUNCTS_THEN2 (K ALL_TAC) assume_tac) >>
  qexistsl [`raw_slots`,`sites`,`unused`,`N`,`root_sf`,`root_tf`,`lbl7`,`q80`,`q90`,
    `evs8`,`qs8`,`evs9`,`qs9`,`schedules`,`current`,`saved`,`f`,`ast`,`ss`,
    `acts`,`blocks`,`calls`,`ms_tab`,`es_tab`,`ks_tab`,`rooted_eval`,`p`,`d`,
    `stk8`,`PG8`,`G8`,`tn8`,`fn8`,`inst8`,`s8`,`oms8`,`om8`,`hs8`,`hist8`,
    `stk9`,`PG9`,`G9`,`tn9`,`fn9`,`inst9`,`s9`,`oms9`,`om9`,`hs9`,`hist9`] >>
  qpat_assum `Abbrev (root_entry = _)`
    (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (j = _)`
    (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (obs = _)`
    (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  (* Keep the indexed conjuncts intact when discharging the flat certificate. *)
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexistsl [`align`,`old_cursors`,`old_asm`,`old_sym`,`costs`] >>
               asm_rewrite_tac []) >>
  conj_tac >-
    (qexistsl [`cut_sf`,`cut_inc`,`cut_entry`,`cut_order`,`NONE`,`NONE`,
       `cut_bb`,`cut_bt`,`cut_ps`,`cut_xs`,`cut_ys`,`cut_rho`,`cut_state`,`cut_h`,
       `cut_body`,`cut_ix`,`OK s8`,`F`,`NONE`] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`cut_q`,`cut_z`] >>
     simp_tac bool_ss [CONJ_ASSOC] >>
     qpat_assum `?src_inst cuts levels Mcut Ecut Kcut mr er kr. _`
       (ACCEPT_TAC o SIMP_RULE bool_ss [CONJ_ASSOC])) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `inst9 = inst8 /\ _ \/ _`
    (DISJ_CASES_THEN2 (map_every assume_tac o CONJUNCTS) mp_tac)
  >- (disj1_tac >>
      `~s8.vs_halted` by
        (PairCases_on `current` >>
         qpat_assum `cfg_norm_joint_cursors (stage 8) (stage 9) _ _ _`
           (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [cfg_norm_joint_cursors_def]) >>
         qmatch_asmsub_rename_tac `cfg_norm_cursors (stage 8) cur_rounds cur_cells` >>
         qpat_assum `cfg_norm_cursors (stage 8) cur_rounds cur_cells` mp_tac >>
         qpat_assum `?pending. HD cur_cells = ((inst8,s8),pending)` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         drule_then strip_assume_tac cfg_norm_cursors_lengths >>
         Cases_on `cur_rounds` >> Cases_on `cur_cells` >> fs[] >>
         rename1 `cfg_norm_cursors _ (row::rs) (cell::cs)` >>
         PairCases_on `row` >> PairCases_on `cell` >> fs[] >>
         drule cfg_norm_cursors_head >> simp[]) >>
      qpat_assum `dft_focus_packet_rel N _ _ _ _ _ (j,obs)
        acts blocks calls ms_tab es_tab ks_tab rooted_eval p d _ raw_slots sites unused`
        (mp_then Any mp_tac focus_same_inventory_terminal_stop) >>
      (impl_tac >- (conj_tac >> (simp[]))) >> simp_tac bool_ss []) >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [] >> metis_tac[]
QED

Resume focus_uniform_frontier[advance]:
  `root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|>` by
    simp[Abbr `root_entry`] >>
  `j = LENGTH evs8` by simp[Abbr `j`] >>
  `obs = trace_gas (TAKE j (trace_blocks [] 0 N (stage 8) root_tf root_entry))` by
    simp[Abbr `obs`] >>
  qpat_assum `dft_focus_packet_rel N _ _ _ _ _ (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d _ raw_slots sites unused`
    (mp_then Any mp_tac focus_joint_progress) >>
  (* Progress uses the names of the selected certificate, with fuel named f here. *)
  disch_then (fn th =>
    let
      fun specialize th =
        if is_forall (concl th) then
          let val (v,_) = dest_forall (concl th) in
            specialize (if fst (dest_var v) = "asm_fuel" then Q.SPEC `f` th else SPEC v th)
          end
        else th
    in mp_tac (specialize th) end) >>
  (impl_tac >- (rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE
     (qpat_assum `j = LENGTH evs8` (rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC)))) >>
  disch_then (qx_choosel_then
    [`ev9`,`q9'`,`n`,`ast'`,`ss'`,`N'`,`raw_slots'`,`sites'`,`unused'`,
     `evs8'`,`qs8'`,`evs9'`,`qs9'`,`current'`,`saved'`,`asm_fuel'`,`j'`,`obs'`,
     `acts'`,`blocks'`,`calls'`,`ms_tab'`,`es_tab'`,`ks_tab'`,`p'`,`d'`,
     `stk8'`,`PG8'`,`G8'`,`tn8'`,`fn8'`,`inst8'`,`s8'`,`oms8'`,`om8'`,`hs8'`,`hist8'`,
     `stk9'`,`PG9'`,`G9'`,`tn9'`,`fn9'`,`inst9'`,`s9'`,`oms9'`,`om9'`,`hs9'`,`hist9'`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `joint_trace vs0 (stage 8) q80 evs8 qs8 _`
    (mp_then Any assume_tac joint_trace_endpoint) >>
  qpat_assum `joint_trace vs0 (stage 9) q90 evs9 qs9 _`
    (mp_then Any assume_tac joint_trace_endpoint) >>
  `LENGTH qs8 = LENGTH evs8 /\ LENGTH qs9 = LENGTH evs9` by
    (conj_tac >> first_assum (fn th =>
       let val chain = CONJUNCT2 (REWRITE_RULE [joint_trace_def] th)
       in ACCEPT_TAC (SYM (MATCH_MP joint_chain_length chain)) end)) >>
  qmatch_asmsub_abbrev_tac `EL (LENGTH evs8) (q80::qs8) = q8` >>
  qmatch_asmsub_abbrev_tac `EL (LENGTH evs9) (q90::qs9) = q9` >>
  `?add8. qs8' = qs8 ++ add8 /\ j' = j + LENGTH add8 /\ LENGTH add8 <= 1 /\
     (j' = SUC j /\ inst8.inst_opcode = GAS ==> s8.vs_gas_readings <> [])` by
    (qpat_assum `_ /\ _ \/ (?ev8. joint_transition (stage 8) _ ev8 _ /\ _)`
       (DISJ_CASES_THEN2 (map_every assume_tac o CONJUNCTS)
          (qx_choose_then `ev8` (map_every assume_tac o CONJUNCTS)))
     >- (qexists `[]` >> qpat_assum `qs8' = qs8` (fn qs_eq =>
         qpat_assum `j' = j` (fn j_eq => simp[NoAsms,qs_eq,j_eq])))
     >> qexists `[JointConfig stk8' PG8' G8' tn8' fn8' inst8' s8' oms8' om8' hs8' hist8']` >>
     map_every (fn p => qpat_assum p mp_tac)
       [`qs8' = qs8 ++ [_]`,`j' = SUC j`, `inst8.inst_opcode = GAS ==> _ /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ADD1]) >>
  rename1 `qs8' = qs8 ++ add8` >>
  suspend "ledger"
QED

Resume focus_uniform_frontier[ledger]:
  qabbrev_tac `m = LENGTH evs9` >>
  qabbrev_tac `rank = \q. case q of JointConfig stk PG G tn fn inst s oms om hs h =>
     case lookup_block s.vs_current_bb fn.fn_blocks of
       NONE => 0 | SOME bb => LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  (Q.SUBGOAL_THEN `0 < n \/ rank q9' < rank q9` assume_tac >-
    (qpat_assum `q9' = JointConfig _ _ _ _ _ _ _ _ _ _ _` SUBST1_TAC >>
     simp_tac bool_ss [Abbr `q9`, Abbr `rank`] >>
     irule (BETA_RULE focus_ledger_rank_step) >>
     qpat_assum `0 < n \/ n = 0 /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])) >>
  (let
     val rule = focus_stop_aligned_ledger_snoc
     val vars = free_vars (concl rule)
     fun find s = valOf (List.find (fn v => fst (dest_var v) = s) vars)
     val params = ["j'","q9'","current","a0","s0","opt","cursors","asm_edge","sym_edge",
                   "cost_ok","edge_ok","fuel"]
   in
     qspecl_then
       [`j'`,`q9'`,`(schedules,current,saved)`,`entry_asm_state vs0 es0`,
        `sym_init (entry_asm_state vs0 es0)`,`fin = asm_opt_finalizer`,
        `cfg_norm_joint_cursors (stage 8) (stage 9)`,
        `\k a b. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
                    prog k a = AsmOK b`,
        `\k a b. sym_steps prog (asm_data_env prog vs0.vs_code) k a = SymOK b`,
        `\cost edge. 0 < cost \/ rank (SND edge) < rank (FST edge)`,
        `\moved q8 q9. case (q8,q9) of
          (JointConfig frames8 p8 g8 t8 f8 i8 u8 o8 m8 sh8 oh8,
           JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) =>
           (~in_revert_forward fn9 s9 /\
            (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode ==>
             source_memory_reads_disjoint cpl inst9 s9 /\
             context_source_memory_writes_disjoint cpl inst9 s9) /\
            (fin = asm_opt_finalizer ==>
             !dst x sz src off.
               inst9.inst_opcode = CODECOPY /\ inst9.inst_operands = [dst; Var x; sz] /\
               code_end_var fn9 x /\ eval_operand (Var x) s9 = SOME src /\
               FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off ==>
               w2n (src - n2w off) < dimword (:256) DIV 2)) /\
           (active_inst fn9 inst9 s9 /\
            (inst9.inst_opcode = INVOKE ==>
             ?nm' ops callee args ent.
               decode_invoke inst9 = SOME (nm',ops) /\
               lookup_function nm' (stage 9).ctx_functions = SOME callee /\
               eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent) /\
            (inst9.inst_opcode <> INVOKE ==>
             (?u. step_inst 0 (stage 9) inst9 s9 = OK u /\ ~u.vs_halted) \/
             (stk9 <> [] /\ ?ir u. step_inst 0 (stage 9) inst9 s9 = IntRet ir u))) /\
           (moved /\ i8.inst_opcode = GAS ==> u8.vs_gas_readings <> [])`,
        `f`] mp_tac (GENL (map find params) rule)
   end) >>
  BETA_TAC >>
  (impl_tac >-
    (rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
            qpat_assum `j = LENGTH evs8` (rewrite_tac o single) >> first_assum ACCEPT_TAC,
            simp_tac bool_ss [pairTheory.FST,pairTheory.SND] >> first_assum ACCEPT_TAC,
            simp_tac bool_ss [Abbr `rank`] >> first_assum ACCEPT_TAC,
            simp_tac (srw_ss()) [Abbr `q8`, Abbr `q9`] >>
              rpt conj_tac >> first_assum ACCEPT_TAC])) >>
  `SUC m = LENGTH evs9'` by
    (qpat_assum `evs9' = evs9 ++ [_]` (fn th =>
       simp[NoAsms, th, Abbr `m`, ADD1])) >>
  disch_then (fn th =>
    qpat_assum `qs8' = qs8 ++ add8` (fn q8s =>
    qpat_assum `qs9' = qs9 ++ [q9']` (fn q9s =>
    qpat_assum `SUC m = LENGTH evs9'` (fn len =>
    qpat_assum `asm_fuel' = f + n` (fn fuel =>
    qpat_assum `Abbrev (rank = _)` (fn rk =>
      mp_tac (BETA_RULE (PURE_REWRITE_RULE [GSYM q8s, GSYM q9s, len, GSYM fuel,
        REWRITE_RULE [markerTheory.Abbrev_def] rk] th)))))))) >>
  disch_then (qx_choosel_then [`align'`,`old_cursors'`] assume_tac) >>
  `j' <= LENGTH evs9'` by
    (qpat_assum `j' = LENGTH evs8'` (rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  `Prefix asm_fuel' (rank q9')` by
    (qpat_assum `marker$Abbrev (Prefix = _)`
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     CONV_TAC (RATOR_CONV BETA_CONV THENC BETA_CONV) >>
     qexistsl [`raw_slots'`,`sites'`,`unused'`,`N'`,`evs8'`,`qs8'`,`evs9'`,`qs9'`,
       `current'`,`saved'`,`ast'`,`ss'`,`acts'`,`blocks'`,`calls'`,`ms_tab'`,`es_tab'`,`ks_tab'`,`p'`,`d'`,
       `stk8'`,`PG8'`,`G8'`,`tn8'`,`fn8'`,`inst8'`,`s8'`,`oms8'`,`om8'`,`hs8'`,`hist8'`,
       `stk9'`,`PG9'`,`G9'`,`tn9'`,`fn9'`,`inst9'`,`s9'`,`oms9'`,`om9'`,`hs9'`,`hist9'`] >>
     qpat_assum `j' = LENGTH evs8'` (SUBST1_TAC o SYM) >>
     qpat_assum `obs' = trace_gas _` (SUBST1_TAC o SYM) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (qexistsl [`align'`,`old_cursors'`,`old_asm ++ [ast']`,`old_sym ++ [ss']`,`costs ++ [n]`] >>
        first_assum ACCEPT_TAC) >>
     conj_tac >-
       (qpat_assum `!h. h < j' ==> _` mp_tac >>
        simp_tac bool_ss []) >>
     qpat_assum `q9' = JointConfig _ _ _ _ _ _ _ _ _ _ _` SUBST1_TAC >>
     simp_tac (srw_ss()) [Abbr `rank`]) >>
  `asm_fuel' <= f` by
    (qpat_assum `!a b. Prefix a b ==> a <= f` irule >>
     qexists `rank q9'` >> first_assum ACCEPT_TAC) >>
  `asm_fuel' = f` by
    (qpat_assum `asm_fuel' <= f` mp_tac >> qpat_assum `asm_fuel' = f + n` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `best_rank <= rank q9'` by
    (qpat_assum `!r. Prefix f r ==> best_rank <= r` irule >>
     qpat_assum `asm_fuel' = f` (rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  `best_rank = rank q9` by
    (simp_tac (srw_ss()) [Abbr `rank`,Abbr `q9`] >> first_assum ACCEPT_TAC) >>
  (qsuff_tac `F` >- simp_tac bool_ss []) >>
  map_every (fn p => qpat_assum p mp_tac)
    [`0 < n \/ rank q9' < rank q9`, `asm_fuel' = f + n`, `asm_fuel' = f`,
     `best_rank <= rank q9'`, `best_rank = rank q9`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac
QED

Finalise focus_uniform_frontier
