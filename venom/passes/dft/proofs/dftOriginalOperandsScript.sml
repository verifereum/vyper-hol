Theory dftOriginalOperands
Ancestors
  dftOriginalRuntime dftOriginalScheduleRuntime dftOriginalCutLifecycle
  dftProtectedRuntime dftLocalOrdinaryClosure dftOccurrenceOrdinaryClosure
  dftOccurrenceAvailability venomInstProofs1 venomExecProofs venomWf venomInst
  list rich_list finite_map arithmetic

Theorem dft_original_first_operands:
  dft_original_cut f b q s /\ q.bb_instructions = (pp ++ done) ++ x::todo /\
  pp = FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions /\
  s.vs_inst_idx = LENGTH (pp ++ done) /\
  (!l. MEM (Label l) x.inst_operands ==> l IN FDOM s.vs_labels) ==>
  !op. MEM op x.inst_operands ==> ?v. eval_operand op s = SOME v
Proof
  rewrite_tac[APPEND_ASSOC] >>
  MATCH_ACCEPT_TAC (REWRITE_RULE [APPEND_ASSOC] dft_original_cut_eval_operand)
QED

Theorem dft_original_swap_cut:
  dft_original_block f b q /\ dft_original_cut f b q s /\
  q.bb_instructions = pre ++ [x;y] ++ post /\ s.vs_inst_idx = LENGTH pre /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  schedule_edges b.bb_instructions dft_must_order (pre ++ [y;x] ++ post) ==>
  dft_original_cut f b (q with bb_instructions := pre ++ [y;x] ++ post) s
Proof
  strip_tac >> drule_all dft_original_block_swap >> strip_tac >>
  simp[dft_original_cut_def] >> conj_tac
  >- fs[dft_original_block_def] >>
  fs[dft_original_cut_def, dft_activation_cut_def] >>
  fs[TAKE_APPEND1] >> metis_tac[]
QED

Theorem dft_original_before_operands:
  dft_original_block f b q /\ dft_original_cut f b q s /\
  q.bb_instructions = (pp ++ done) ++ [x;y] ++ post /\
  pp = FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions /\
  s.vs_inst_idx = LENGTH (pp ++ done) /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  schedule_edges b.bb_instructions dft_must_order ((pp ++ done) ++ [y;x] ++ post) /\
  (!l. MEM (Label l) y.inst_operands ==> l IN FDOM s.vs_labels) ==>
  !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v
Proof
  strip_tac >> drule_all dft_original_swap_cut >> strip_tac >>
  qpat_x_assum `dft_original_cut f b q s` kall_tac >>
  drule dft_original_cut_eval_operand >>
  disch_then (qspecl_then [`y`, `x::post`, `pp`, `done`] mp_tac) >>
  simp[APPEND_ASSOC]
QED

Theorem dft_original_step_cut:
  dft_original_cut f b q s /\ get_instruction q s.vs_inst_idx = SOME x /\
  inst_wf x /\ x.inst_opcode <> PHI /\ ~is_terminator x.inst_opcode /\
  step_inst_base x s = OK sx ==>
  dft_original_cut f b q (sx with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all venomExecProofsTheory.step_inst_base_fdom >> strip_tac >>
  `sx.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_inst_base_preserves_all] >>
  irule dft_original_cut_advance >> qexistsl_tac [`x`, `s`] >> simp[]
QED

Theorem dft_original_after_operands:
  dft_original_cut f b q s /\
  q.bb_instructions = (pp ++ done) ++ [x;y] ++ post /\
  pp = FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions /\
  s.vs_inst_idx = LENGTH (pp ++ done) /\
  inst_wf x /\ x.inst_opcode <> PHI /\ ~is_terminator x.inst_opcode /\
  (!l. MEM (Label l) y.inst_operands ==> l IN FDOM s.vs_labels) ==>
  !sx. step_inst_base x s = OK sx ==>
    !op. MEM op y.inst_operands ==>
      ?v. eval_operand op (sx with vs_inst_idx := SUC s.vs_inst_idx) = SOME v
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `get_instruction q s.vs_inst_idx = SOME x` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  drule_all dft_original_step_cut >> strip_tac >>
  `sx.vs_labels = s.vs_labels` by metis_tac[step_inst_base_preserves_all] >>
  qpat_x_assum `dft_original_cut f b q s` kall_tac >>
  drule dft_original_cut_eval_operand >>
  disch_then (qspecl_then [`y`, `post`, `pp`, `done ++ [x]`] mp_tac) >>
  simp[APPEND_ASSOC, ADD1]
QED
