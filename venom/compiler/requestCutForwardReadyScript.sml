Theory requestCutForwardReady
Ancestors
  requestCutInvokeReady cfgNormSupplySim fnBlockBodySteps
  contextCodegenRel unitShapeDefs o1PassContract venomExecSemantics venomExecProofs venomInstProps
  venomWf venomInst venomState stackPlanTypes finite_map rich_list list

Theorem forward_suffix_operand_defined[local]:
  wf_ssa fn /\ wf_function fn /\ supply_prefix_defined fn s /\
  active_inst fn inst s /\ inst.inst_opcode <> PHI /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands ==>
  !op. MEM op inst.inst_operands ==> IS_SOME (eval_operand op s)
Proof
  strip_tac >> Cases >> simp[eval_operand_def, lookup_var_def, FLOOKUP_DEF] >>
  strip_tac
  >- (IF_CASES_TAC >> simp[] >>
      drule_all supply_cursor_use_defined >> simp[]) >>
  fs[EVERY_MEM] >>
  qpat_x_assum `!op. MEM op inst.inst_operands ==> _` drule >>
  simp[is_label_operand_def]
QED

Theorem every_drop_next[local]:
  EVERY P (DROP n xs) ==> EVERY P (DROP (SUC n) xs)
Proof
  `DROP 1 (DROP n xs) = DROP (SUC n) xs` by simp[DROP_DROP_T, arithmeticTheory.ADD1] >>
  pop_assum (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
  metis_tac[EVERY_DROP]
QED

Theorem forward_suffix_inst_ready[local]:
  fn_inst_wf fn /\ MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  active_inst fn inst s /\ inst_wf inst /\ MEM inst (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >> fs[get_instruction_def] >> conj_tac
  >- (simp[active_inst_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[fn_inst_wf_def] >> metis_tac[EL_MEM]) >>
  simp[MEM_EL] >> qexists_tac `0` >> simp[EL_DROP]
QED

Theorem forward_suffix_no_labels[local]:
  EVERY (\i. EVERY (\op. ~is_label_operand op) i.inst_operands) insts /\
  MEM inst insts ==> EVERY (\op. ~is_label_operand op) inst.inst_operands
Proof
  simp_tac std_ss [EVERY_MEM] >> metis_tac[]
QED

Theorem assign_revert_suffix_total[local]:
  !n s.
    wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    supply_prefix_defined fn s /\ s.vs_inst_idx + n = j /\
    get_instruction bb j = SOME ri /\ ri.inst_opcode = REVERT /\
    (!k inst. s.vs_inst_idx <= k /\ k < j /\ get_instruction bb k = SOME inst ==>
              inst.inst_opcode = ASSIGN) /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?r u. exec_block fuel C bb s = Abort r u
Proof
  Induct
  >- (simp[] >> rpt strip_tac >>
      `get_instruction bb s.vs_inst_idx = SOME ri` by simp[] >>
      drule_all forward_suffix_inst_ready >> strip_tac >>
      drule_all forward_suffix_no_labels >> strip_tac >>
      `ri.inst_opcode <> PHI` by simp[] >>
      mp_tac (Q.INST [`inst` |-> `ri`, `fn` |-> `fn`, `s` |-> `s`]
        forward_suffix_operand_defined) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac >>
      fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      gvs[MEM, DISJ_IMP_THM, FORALL_AND_THM, optionTheory.IS_SOME_EXISTS] >>
      simp[Once exec_block_def, step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
  rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx < j /\ j < LENGTH bb.bb_instructions` by
    fs[get_instruction_def] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  qabbrev_tac `inst = EL s.vs_inst_idx bb.bb_instructions` >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by simp[get_instruction_def, Abbr `inst`] >>
  `inst.inst_opcode = ASSIGN` by
    (qpat_assum `!k inst. s.vs_inst_idx <= k /\ k < j /\ _ ==> _`
       (qspecl_then [`s.vs_inst_idx`, `inst`] mp_tac) >> simp[]) >>
  drule_all forward_suffix_inst_ready >> strip_tac >>
  drule_all forward_suffix_no_labels >> strip_tac >>
  `inst.inst_opcode <> PHI` by simp[] >>
  mp_tac (Q.INST [`inst` |-> `inst`, `fn` |-> `fn`, `s` |-> `s`]
    forward_suffix_operand_defined) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `?u. step_inst fuel C inst s = OK u` by
    (fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
     gvs[MEM, DISJ_IMP_THM, FORALL_AND_THM, optionTheory.IS_SOME_EXISTS] >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `u.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
  `EL s.vs_inst_idx bb.bb_instructions = inst` by simp[Abbr `inst`] >>
  drule_all supply_prefix_defined_step >>
  strip_tac >>
  qpat_x_assum `!s. _ ==> ?r u. exec_block _ _ _ _ = _`
    (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >>
  (impl_tac >-
    (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE all_tac)
     >- (rpt strip_tac >> first_x_assum irule >> qexists_tac `k` >> simp[])
     >- metis_tac[every_drop_next])) >>
  strip_tac >> simp[Once exec_block_def]
QED

Theorem forward_copy_suffix_total[local]:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  bb_well_formed bb /\ (!inst. MEM inst bb.bb_instructions ==> inst_shape_ok inst) /\
  supply_prefix_defined fn s /\ revert_forward_pair bb s.vs_inst_idx j ==>
  ?r u. exec_block fuel C bb s = Abort r u
Proof
  strip_tac >> drule_all rf_pair_no_labels >> strip_tac >>
  qpat_x_assum `revert_forward_pair bb s.vs_inst_idx j`
    (mp_tac o REWRITE_RULE [revert_forward_pair_def]) >> strip_tac >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\ EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def] >>
  drule_all forward_suffix_inst_ready >> strip_tac >>
  drule_all forward_suffix_no_labels >> strip_tac >>
  `inst.inst_opcode <> PHI` by simp[] >>
  mp_tac (Q.INST [`inst` |-> `inst`, `fn` |-> `fn`, `s` |-> `s`]
    forward_suffix_operand_defined) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `(?t. step_inst fuel C inst s = OK t) \/
   (?r t. step_inst fuel C inst s = Abort r t)` by
    (gvs[MEM, DISJ_IMP_THM, FORALL_AND_THM, optionTheory.IS_SOME_EXISTS] >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >> IF_CASES_TAC >> simp[])
  >~ [`step_inst fuel C inst s = Abort _ _`]
  >- simp[Once exec_block_def] >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `t.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
  drule_all supply_prefix_defined_step >>
  strip_tac >>
  rename1 `get_instruction bb j = SOME ri` >>
  `!k i. SUC s.vs_inst_idx <= k /\ k < j /\ get_instruction bb k = SOME i ==>
      i.inst_opcode = ASSIGN` by
    (rpt gen_tac >> strip_tac >>
     `s.vs_inst_idx < k` by decide_tac >>
     qpat_assum `!k i. s.vs_inst_idx < k /\ k < j /\ _ ==> _`
       (qspecl_then [`k`, `i`] mp_tac) >> simp[]) >>
  `EVERY (\i. EVERY (\op. ~is_label_operand op) i.inst_operands)
      (DROP (SUC s.vs_inst_idx) bb.bb_instructions)` by
    (irule every_drop_next >> first_assum ACCEPT_TAC) >>
  `SUC s.vs_inst_idx + (j - SUC s.vs_inst_idx) = j` by decide_tac >>
  qspec_then `j - SUC s.vs_inst_idx` mp_tac
    (Q.INST [`fn` |-> `fn`, `bb` |-> `bb`, `j` |-> `j`, `fuel` |-> `fuel`, `C` |-> `C`,
              `ri` |-> `ri`] assign_revert_suffix_total) >>
  disch_then (qspec_then `t with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> simp[Once exec_block_def]
QED

Theorem request_cut_stopped_forward_ready:
  cfg_norm_joint_cursors C8 C9 (schedules,(rounds,cells),saved) q8
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  o1_ctx_shape C9 /\ in_revert_forward fn s ==>
  ?bb r u. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
           exec_block fuel C9 bb s = Abort r u
Proof
  strip_tac >> drule cfg_norm_joint_cursor_supply >> strip_tac >>
  `o1_fn_shape C9 fn` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `fn_inst_wf fn /\ EVERY inst_shape_ok (fn_insts fn)` by
    fs[o1_fn_shape_def, fn_shape_ok_def] >>
  fs[in_revert_forward_def, revert_forward_at_def] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `!i. MEM i bb.bb_instructions ==> inst_shape_ok i` by
    (fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  TRY (drule_all (Q.INST [`fuel` |-> `fuel`, `C` |-> `C9`]
        forward_copy_suffix_total) >> simp[] >> NO_TAC) >>
  drule_all rf_pair_no_labels >> strip_tac >>
  `j < s.vs_inst_idx /\ ?ri. get_instruction bb s.vs_inst_idx = SOME ri /\
                               ri.inst_opcode = REVERT` by fs[revert_forward_pair_def] >>
  `DROP (s.vs_inst_idx - j) (DROP j bb.bb_instructions) = DROP s.vs_inst_idx bb.bb_instructions` by
    (`j + (s.vs_inst_idx - j) = s.vs_inst_idx` by decide_tac >> simp[DROP_DROP_T]) >>
  `EVERY (\i. EVERY (\op. ~is_label_operand op) i.inst_operands)
      (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[EVERY_DROP] >>
  `!k i. s.vs_inst_idx <= k /\ k < s.vs_inst_idx /\
    get_instruction bb k = SOME i ==> i.inst_opcode = ASSIGN` by
    (rpt gen_tac >> strip_tac >> qsuff_tac `F` >- simp[] >> decide_tac) >>
  mp_tac (Q.SPECL [`0`, `s`]
    (Q.INST [`fn` |-> `fn`, `bb` |-> `bb`, `j` |-> `s.vs_inst_idx`,
       `fuel` |-> `fuel`, `C` |-> `C9`, `ri` |-> `ri`] assign_revert_suffix_total)) >>
  simp[] >> disch_then match_mp_tac >> first_assum ACCEPT_TAC
QED
