Theory requestCutCfgCodeEnd
Ancestors
  o1CodeEndCfgNormTransport o1ContractCfgNormJointCursors
  o1ContractCfgNormCursors o1ContractCfgNorm cfgNormSupplySim cfgNormDefs irSupply
  codegenSymRel lowerDloadPtrStatic unitShapeDefs frameJointTransition venomInst venomState list pair

Theorem cfg_norm_cursors_codecopy[local]:
  !C rounds cells. cfg_norm_cursors C rounds cells ==>
  !x. (FST (FST (LAST cells))).inst_opcode = CODECOPY /\
    MEM (Var x) (FST (FST (LAST cells))).inst_operands /\
    code_end_var (FST (SND (LAST rounds))) x ==>
    FST (FST (HD cells)) = FST (FST (LAST cells)) /\
    code_end_var (FST (SND (HD rounds))) x /\
    eval_operand (Var x) (SND (FST (HD cells))) =
      eval_operand (Var x) (SND (FST (LAST cells)))
Proof
  ho_match_mp_tac cfg_norm_cursors_ind >> simp[LAST_CONS_cond] >>
  rpt conj_tac >> rpt (gen_tac ORELSE disch_then strip_assume_tac) >> gvs[]
  >- suspend "body"
  >> suspend "split"
QED

Resume cfg_norm_cursors_codecopy[body]:
  rename1 `supply_state_agree fn a v` >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[] >> strip_tac >>
  `wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    gvs[supply_norm_inv_def] >>
  `EVERY label_positions_ok bb.bb_instructions` by
    (gvs[fn_insts_def, EVERY_MEM] >> metis_tac[MEM_fn_insts_blocks]) >>
  `(EL v.vs_inst_idx (supply_block_image pred target split repls bb).bb_instructions).inst_opcode = CODECOPY` by
    metis_tac[] >>
  `(EL v.vs_inst_idx bb.bb_instructions).inst_opcode = CODECOPY` by
    (mp_tac (Q.INST [`i` |-> `v.vs_inst_idx`, `bb` |-> `bb`, `pred` |-> `pred`,
       `target` |-> `target`, `split` |-> `split`, `repls` |-> `repls`]
       supply_block_image_index) >> simp[]) >>
  `EL v.vs_inst_idx (supply_block_image pred target split repls bb).bb_instructions =
     EL v.vs_inst_idx bb.bb_instructions` by
    (irule supply_block_image_index_unchanged >> simp[EVERY_EL] >> metis_tac[EVERY_EL]) >>
  `MEM (EL v.vs_inst_idx bb.bb_instructions) (fn_insts fn)` by
    metis_tac[fn_insts_def, MEM_fn_insts_blocks, MEM_EL] >>
  `MEM x (fn_ir_vars fn)` by metis_tac[fn_ir_vars_operand] >>
  `eval_operand (Var x) a = eval_operand (Var x) v` by
    (irule supply_eval_operand_agree >> qexists_tac `fn` >> simp[]) >>
  simp[] >>
  qpat_assum `code_end_var next_fn x`
    (mp_tac o Q.SPEC `fn` o MATCH_MP cfg_old_code_end_var) >>
  simp[] >> impl_tac >- metis_tac[cfg_split_old_definition] >>
  Cases_on `cursors = []` >> gvs[]
QED

Resume cfg_norm_cursors_codecopy[split]:
  first_x_assum (qspec_then `x` mp_tac) >> simp[] >> strip_tac >>
  `ir_supply_inst_ok s /\ ir_supply_covers_fn s fn` by gvs[supply_norm_inv_def] >>
  `(EL v.vs_inst_idx split.bb_instructions).inst_opcode = CODECOPY` by metis_tac[] >>
  drule_all supply_split_index_shape >> simp[]
QED

Finalise cfg_norm_cursors_codecopy

Theorem request_cut_cfg_codecopy:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  inst9.inst_opcode = CODECOPY /\ MEM (Var x) inst9.inst_operands /\
  code_end_var fn9 x ==>
  inst8 = inst9 /\ code_end_var fn8 x /\
  eval_operand (Var x) s8 = eval_operand (Var x) s9
Proof
  strip_tac >> PairCases_on `current` >> gvs[cfg_norm_joint_cursors_def] >>
  qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then drule >> simp[] >> strip_tac >>
  drule cfg_norm_cursors_codecopy >> disch_then (qspec_then `x` mp_tac) >> simp[]
QED
