Theory requestCutAssertCursor
Ancestors
  o1ContractCfgNormJointCursors o1ContractCfgNormCursors o1ContractCfgNorm
  cfgNormSupplySim ctxLookupAgreeHelpers venomExecProofs venomExecSemantics
  venomState venomInst opcodeClass stateEquiv stateFrame passSimulationProps words list
Theorem cfg_norm_terminal_body[local]:
  MEM bb fn.fn_blocks /\ EVERY label_positions_ok (fn_insts fn) /\
  a.vs_current_bb = v.vs_current_bb /\ a.vs_inst_idx = v.vs_inst_idx /\
  a.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL a.vs_inst_idx bb.bb_instructions /\
  ~MEM inst.inst_opcode [PHI; JMP; JNZ; INVOKE] /\
  supply_state_agree fn a v ==>
  EL v.vs_inst_idx (supply_block_image pred target split repls bb).bb_instructions = inst /\
  (!op. MEM op inst.inst_operands ==> eval_operand op a = eval_operand op v) /\
  lift_result (\s t. execution_frame s = execution_frame t)
              (\s t. execution_frame s = execution_frame t)
              (\s t. execution_frame s = execution_frame t)
              (step_inst 0 C inst a) (step_inst 0 C inst v)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY label_positions_ok bb.bb_instructions` by
    (qpat_x_assum `EVERY label_positions_ok _` mp_tac >>
     rewrite_tac[fn_insts_def, fn_insts_EVERY_block] >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (asm_rewrite_tac[] >> irule supply_block_image_index_unchanged >> fs[EVERY_EL] >> metis_tac[]) >>
  `!x. MEM (Var x) inst.inst_operands ==> MEM x (irSupply$fn_ir_vars fn)` by
    (rpt strip_tac >> irule supply_operand_in_fn >> qexistsl_tac [`bb`, `inst`] >>
     simp[] >> metis_tac[EL_MEM]) >>
  conj_tac >- metis_tac[supply_eval_operand_agree] >>
  qpat_x_assum `inst = _` kall_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (mp_tac (Q.INST [`st` |-> `a`, `st'` |-> `v`, `fuel` |-> `0`, `ctx` |-> `C`]
        supply_step_terminator) >>
      simp[] >> Cases_on `step_inst 0 C inst a` >> Cases_on `step_inst 0 C inst v` >>
      simp[lift_result_def, supply_state_agree_def]) >>
  mp_tac (Q.INST [`st` |-> `a`, `st'` |-> `v`, `fuel` |-> `0`, `ctx` |-> `C`]
    supply_step_nonterm) >>
  fs[] >> Cases_on `step_inst 0 C inst a` >> Cases_on `step_inst 0 C inst v` >>
  simp[lift_result_def, supply_state_agree_def]
QED

Theorem cfg_norm_cursors_terminal[local]:
  !C rounds cells. cfg_norm_cursors C rounds cells ==>
    !inst a.
    FST (HD cells) = (inst,a) /\ ~MEM inst.inst_opcode [PHI; JMP; JNZ; INVOKE] /\
    (!u. step_inst 0 C inst a = OK u ==> u.vs_halted) ==>
    FST (FST (LAST cells)) = inst /\
    (!op. MEM op inst.inst_operands ==>
      eval_operand op a = eval_operand op (SND (FST (LAST cells)))) /\
    lift_result (\s t. execution_frame s = execution_frame t)
                (\s t. execution_frame s = execution_frame t)
                (\s t. execution_frame s = execution_frame t)
                (step_inst 0 C inst a) (step_inst 0 C inst (SND (FST (LAST cells))))
Proof
  ho_match_mp_tac cfg_norm_cursors_ind >>
  simp[LAST_CONS_cond] >> rpt conj_tac
  >- (rpt strip_tac >> Cases_on `step_inst 0 C inst a` >> simp[lift_result_def])
  >- suspend "body" >>
  rpt strip_tac >> gvs[] >> metis_tac[step_inst_non_invoke]
QED

Resume cfg_norm_cursors_terminal[body]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> gvs[] >>
  rename1 `build_split_block_supply _ pred target = (split,repls,_)` >>
  rename1 `supply_state_agree fn a v` >>
  rename1 `v.vs_inst_idx < LENGTH bb.bb_instructions` >>
  mp_tac (Q.INST [`pred` |-> `pred`, `target` |-> `target`,
    `split` |-> `split`, `repls` |-> `repls`, `bb` |-> `bb`,
    `fn` |-> `fn`, `a` |-> `a`, `v` |-> `v`,
    `inst` |-> `EL v.vs_inst_idx bb.bb_instructions`] cfg_norm_terminal_body) >>
  simp[] >> strip_tac >> gvs[] >>
  `!u. step_inst 0 C (EL v.vs_inst_idx bb.bb_instructions) v = OK u ==> u.vs_halted` by
    (rpt strip_tac >> Cases_on `step_inst 0 C (EL v.vs_inst_idx bb.bb_instructions) a` >>
     gvs[lift_result_def] >> metis_tac[]) >>
  qpat_x_assum `(!u. step_inst 0 C _ v = OK u ==> u.vs_halted) ==> _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >> asm_rewrite_tac[] >>
  mp_tac (SIMP_RULE (srw_ss()) [] (Q.SPECL
    [`\s t. execution_frame s = execution_frame t`,
     `\s t. execution_frame s = execution_frame t`] lift_result_trans)) >>
  disch_then (qspecl_then [`step_inst 0 C (EL v.vs_inst_idx bb.bb_instructions) a`,
    `step_inst 0 C (EL v.vs_inst_idx bb.bb_instructions) v`,
    `step_inst 0 C (EL v.vs_inst_idx bb.bb_instructions)
      (SND (FST (if cursors = [] then ((EL v.vs_inst_idx bb.bb_instructions,v),pending)
                 else LAST cursors)))`] mp_tac) >>
  asm_rewrite_tac[]
QED

Finalise cfg_norm_cursors_terminal

Theorem cfg_norm_joint_terminal_operands:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  ~MEM inst8.inst_opcode [PHI; JMP; JNZ; INVOKE] /\
  (!u. step_inst 0 C8 inst8 s8 = OK u ==> u.vs_halted) ==>
  inst9 = inst8 /\
  (!op. MEM op inst8.inst_operands ==> eval_operand op s8 = eval_operand op s9) /\
  lift_result (\s t. execution_frame s = execution_frame t)
              (\s t. execution_frame s = execution_frame t)
              (\s t. execution_frame s = execution_frame t)
              (step_inst 0 C8 inst8 s8) (step_inst 0 C9 inst9 s9)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> PairCases_on `current` >>
  gvs[cfg_norm_joint_cursors_def] >>
  drule cfg_norm_cursors_terminal >> simp[step_inst_non_invoke] >> metis_tac[]
QED

Theorem cfg_norm_joint_terminal:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  ~MEM inst8.inst_opcode [PHI; JMP; JNZ; INVOKE] /\
  (!u. step_inst 0 C8 inst8 s8 = OK u ==> u.vs_halted) ==>
  inst9 = inst8 /\
  lift_result (\s t. execution_frame s = execution_frame t)
              (\s t. execution_frame s = execution_frame t)
              (\s t. execution_frame s = execution_frame t)
              (step_inst 0 C8 inst8 s8) (step_inst 0 C9 inst9 s9)
Proof
  strip_tac >> drule_all_then strip_assume_tac cfg_norm_joint_terminal_operands >> simp[]
QED

Theorem cfg_norm_joint_assert_abort:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  MEM inst8.inst_opcode [ASSERT; ASSERT_UNREACHABLE] /\
  step_inst fuel C8 inst8 s8 = Abort ab s8' ==>
  inst9 = inst8 /\ ?u. step_inst 0 C9 inst9 s9 = Abort ab u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~MEM inst8.inst_opcode [PHI; JMP; JNZ; INVOKE]` by fs[] >>
  `step_inst 0 C8 inst8 s8 = Abort ab s8'` by metis_tac[step_inst_non_invoke, MEM] >>
  drule cfg_norm_joint_terminal >> simp[] >> strip_tac >>
  Cases_on `step_inst 0 C9 inst8 s9` >> gvs[lift_result_def]
QED

Theorem cfg_norm_joint_primitive_abort:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  inst8.inst_opcode <> INVOKE /\ step_inst fuel C8 inst8 s8 = Abort ab post ==>
  inst9 = inst8 /\
  (!op. MEM op inst8.inst_operands ==> eval_operand op s8 = eval_operand op s9) /\
  ?u. step_inst 0 C9 inst9 s9 = Abort ab u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~MEM inst8.inst_opcode [PHI; JMP; JNZ; INVOKE]` by
    (drule step_inst_abort_opcodes >> rpt strip_tac >> gvs[]) >>
  `step_inst 0 C8 inst8 s8 = Abort ab post` by gvs[step_inst_non_invoke] >>
  drule cfg_norm_joint_terminal_operands >> simp[] >> strip_tac >>
  Cases_on `step_inst 0 C9 inst8 s9` >> gvs[lift_result_def]
QED

Theorem cfg_norm_joint_source_running:
  cfg_norm_joint_cursors C8 C9 (schedules,(rounds,cells),saved)
    (JointConfig stk PG G tn fn inst s oms om hs h) q9 ==>
  ~s.vs_halted
Proof
  Cases_on `q9` >> PURE_REWRITE_TAC [cfg_norm_joint_cursors_def] >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  qpat_assum `HD cells = _` mp_tac >>
  qpat_assum `cfg_norm_cursors C8 rounds cells` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  Cases_on `rounds` >> Cases_on `cells` >> simp[] >>
  rpt strip_tac >>
  TRY (drule cfg_norm_cursors_lengths >> simp[] >> NO_TAC) >>
  rename1 `cfg_norm_cursors _ (row::rs) (cell::cs)` >>
  PairCases_on `row` >> PairCases_on `cell` >> gvs[] >>
  drule cfg_norm_cursors_head >> simp[]
QED

Theorem cfg_norm_joint_primitive_halt:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  inst8.inst_opcode <> INVOKE /\ step_inst fuel C8 inst8 s8 = Halt post ==>
  inst9 = inst8 /\ ?u. step_inst 0 C9 inst9 s9 = Halt u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~MEM inst8.inst_opcode [PHI; JMP; JNZ; INVOKE]` by
    (drule step_inst_halt_opcodes >> rpt strip_tac >> gvs[]) >>
  `step_inst 0 C8 inst8 s8 = Halt post` by gvs[step_inst_non_invoke] >>
  drule cfg_norm_joint_terminal >> simp[] >> strip_tac >>
  Cases_on `step_inst 0 C9 inst8 s9` >> gvs[lift_result_def]
QED
