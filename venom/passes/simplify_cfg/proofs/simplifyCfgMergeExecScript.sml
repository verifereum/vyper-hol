(* Instruction positions and the removed chain transfer. *)
Theory simplifyCfgMergeExec
Ancestors
  simplifyCfgShapeCore
  simplifyCfgMergeClosure simplifyCfgControlExec simplifyCfgAvailability
  simplifyCfgMergePaths venomExecSemantics venomInst venomWf venomState
  unitShapeDefs stackPlanTypes cfgTransform cfgHelpers simplifyCfgStaticInterface
  simplifyCfgDefs unitLabelMapIdentity list rich_list

Theorem scfg_chain_instruction_left:
  i < LENGTH (FRONT a.bb_instructions) ==>
  get_instruction (scfg_chain_block a b a) i =
    SOME (scfg_phi_image a b a.bb_label (EL i a.bb_instructions))
Proof
  strip_tac >>
  simp[scfg_chain_block_def, get_instruction_def, EL_MAP, EL_APPEND] >>
  AP_TERM_TAC >> irule EL_FRONT >>
  Cases_on `a.bb_instructions` >> gvs[LENGTH_FRONT, NULL_EQ]
QED

Theorem scfg_chain_instruction_right:
  j < LENGTH b.bb_instructions ==>
  get_instruction (scfg_chain_block a b a)
    (LENGTH (FRONT a.bb_instructions) + j) =
    SOME (scfg_phi_image a b a.bb_label (EL j b.bb_instructions))
Proof
  simp[scfg_chain_block_def, get_instruction_def, EL_MAP, EL_APPEND]
QED

Theorem scfg_chain_instruction_left_nonphi:
  i < LENGTH (FRONT a.bb_instructions) /\
  (EL i a.bb_instructions).inst_opcode <> PHI ==>
  get_instruction (scfg_chain_block a b a) i = SOME (EL i a.bb_instructions)
Proof
  simp[scfg_chain_instruction_left, scfg_phi_image_nonphi]
QED

Theorem scfg_chain_instruction_right_nonphi:
  scfg_chain_hyp fn a b /\ j < LENGTH b.bb_instructions ==>
  get_instruction (scfg_chain_block a b a)
    (LENGTH (FRONT a.bb_instructions) + j) = SOME (EL j b.bb_instructions)
Proof
  strip_tac >> simp[scfg_chain_instruction_right] >>
  irule scfg_phi_image_nonphi >>
  drule scfg_chain_no_phis >>
  simp[no_phis_def, EVERY_EL]
QED

Theorem scfg_chain_enter_right:
  scfg_chain_hyp fn a b ==>
  run_block fuel C b s = exec_block fuel C b (s with vs_inst_idx := 0)
Proof
  strip_tac >> irule venomExecProofsTheory.run_block_no_phis_eq_exec_block >>
  drule scfg_chain_no_phis >> simp[no_phis_def]
QED

Theorem scfg_nonlabel_get_label:
  ~is_label_operand op ==> get_label op = NONE
Proof
  Cases_on `op` >> simp[is_label_operand_def, get_label_def]
QED

Theorem scfg_nonlabel_successors:
  !ops. EVERY (\op. ~is_label_operand op) ops ==>
  FILTER IS_SOME (MAP get_label ops) = []
Proof
  Induct >> simp[] >> metis_tac[scfg_nonlabel_get_label, optionTheory.NOT_IS_SOME_EQ_NONE]
QED

Theorem scfg_single_successor_transfer:
  inst_wf i /\ scfg_inst_shape i /\
  nub (REVERSE (get_successors i)) = [l] ==>
  (i.inst_opcode = JMP /\ i.inst_operands = [Label l]) \/
  (?c. i.inst_opcode = JNZ /\ i.inst_operands = [c; Label l; Label l] /\
       ~is_label_operand c)
Proof
  strip_tac >>
  `!x. MEM x (get_successors i) <=> x = l` by
    (metis_tac[MEM_nub, MEM_REVERSE, MEM]) >>
  Cases_on `i.inst_opcode` >>
  gvs[get_successors_def, is_terminator_def, scfg_inst_shape_def] >>
  gvs[inst_wf_def, scfg_label_positions_def, label_positions_ok_def, get_label_def] >>
  gvs[scfg_nonlabel_get_label, scfg_nonlabel_successors] >>
  metis_tac[]
QED

Theorem scfg_chain_transfer_shape:
  scfg_chain_hyp fn a b ==>
  ((LAST a.bb_instructions).inst_opcode = JMP /\
   (LAST a.bb_instructions).inst_operands = [Label b.bb_label]) \/
  (?c. (LAST a.bb_instructions).inst_opcode = JNZ /\
       (LAST a.bb_instructions).inst_operands = [c; Label b.bb_label; Label b.bb_label] /\
       ~is_label_operand c)
Proof
  strip_tac >>
  `MEM a fn.fn_blocks` by
    metis_tac[scfg_chain_hyp_def, lookup_block_member_label] >>
  `MEM (LAST a.bb_instructions) a.bb_instructions` by
    metis_tac[scfg_chain_blocks_nonempty, LAST_MEM] >>
  `fn_inst_wf fn /\ scfg_shape fn` by
    metis_tac[scfg_chain_hyp_def, scfg_normalized_static,
      scfg_static_inst_wf, scfg_static_shape] >>
  `inst_wf (LAST a.bb_instructions) /\ scfg_inst_shape (LAST a.bb_instructions)` by
    (fs[fn_inst_wf_def, scfg_shape_def, EVERY_MEM] >>
     metis_tac[fn_insts_MEM]) >>
  irule scfg_single_successor_transfer >> simp[] >>
  fs[scfg_chain_hyp_def, can_merge_blocks_def, bb_succs_def] >>
  Cases_on `a.bb_instructions` >> gvs[]
QED

Theorem scfg_frame_eval_nonlabel:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_entry_state fn s0 /\ frame_reach C fn s0 i s /\
  i.inst_opcode <> PHI /\ MEM c i.inst_operands /\ ~is_label_operand c ==>
  IS_SOME (eval_operand c s)
Proof
  strip_tac >> Cases_on `c` >> gvs[eval_operand_def, is_label_operand_def] >>
  irule scfg_frame_operand_defined >> metis_tac[]
QED

Theorem scfg_chain_transfer_step:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  frame_reach C fn s0 (LAST a.bb_instructions) s ==>
  step_inst k C (LAST a.bb_instructions) s = OK (jump_to b.bb_label s)
Proof
  strip_tac >>
  drule scfg_chain_transfer_shape >> strip_tac
  >- (Cases_on `LAST a.bb_instructions` >> gvs[] >>
      simp[step_inst_def, step_inst_base_def]) >>
  `wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn` by
    metis_tac[scfg_chain_old_wf, scfg_chain_hyp_def, scfg_normalized_static,
      scfg_static_inst_wf, scfg_static_ok, simplify_cfg_fn_ok_def] >>
  `(LAST a.bb_instructions).inst_opcode <> PHI /\
   MEM c (LAST a.bb_instructions).inst_operands` by simp[] >>
  drule_all scfg_frame_eval_nonlabel >> strip_tac >>
  Cases_on `LAST a.bb_instructions` >>
  Cases_on `eval_operand c s` >> gvs[] >>
  simp[step_inst_def, step_inst_base_def]
QED
