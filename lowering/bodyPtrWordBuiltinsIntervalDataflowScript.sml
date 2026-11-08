Theory bodyPtrWordBuiltinsIntervalDataflow
Ancestors bodyPtrWordBuiltinsIntervalProbe bodyPtrWordBuiltinsScalar
  bodyPtrWordBuiltinsDataflow ptrDiscipline ptrSafeRun decoderGhostFramePtr
  venomExecProofs venomInst venomInstProps venomExecSemantics venomState
  list finite_map fragGasPathPtr fragExec
Libs finite_mapLib intReduce

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset

(* This set is a must-analysis certificate, not a runtime assumption. *)
Definition word_interval_scalars_def:
  word_interval_scalars s =
    if s.vs_current_bb = "@exit_2" \/
       ((s.vs_current_bb = "@then_0" \/ s.vs_current_bb = "@else_1") /\
         0 < s.vs_inst_idx)
    then {"%6"} else {}
End

Theorem word_interval_scalar_initial:
  s.vs_current_bb = (SND word_interval_start).cs_current_bb ==>
  word_interval_scalars s = {}
Proof
  CONV_TAC (LAND_CONV (RAND_CONV EVAL)) >>
  simp[word_interval_scalars_def]
QED

Theorem word_interval_operand_endpoint:
  !op sm.
  lower_value compile_expr (FST word_interval_start) (BaseT (IntT 256))
    (IfExp (BaseT (IntT 256)) (Name (BaseT BoolT) "b")
      (Literal (BaseT (IntT 256)) (IntL 1))
      (Literal (BaseT (IntT 256)) (IntL 2)))
    (SND word_interval_start) = (op,sm) ==>
  op = Var "%6" /\ sm.cs_current_bb = "@exit_2" /\
  LENGTH sm.cs_current_insts = 0
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem word_interval_instruction_shapes:
  !lbl bb inst.
  lookup_block lbl word_interval_function.fn_blocks = SOME bb /\
  MEM inst bb.bb_instructions ==>
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI /\
  ((MEM "%6" inst.inst_outputs) ==>
    inst.inst_opcode = ASSIGN /\
    ((inst.inst_operands = [Lit 1w]) \/ (inst.inst_operands = [Lit 2w])))
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[AllCaseEqs(), is_terminator_def]
QED

Theorem word_interval_entry_prov:
  entry_prov word_interval_function s G = G
Proof
  EVAL_TAC >> rpt IF_CASES_TAC >> simp[Once phis_prov_def]
QED

Theorem word_interval_branch_fetch:
  !lbl bb idx inst.
  (lbl = "@then_0" \/ lbl = "@else_1") /\
  lookup_block lbl word_interval_function.fn_blocks = SOME bb /\
  get_instruction bb idx = SOME inst ==>
  ((idx = 0 /\ inst.inst_opcode = ASSIGN /\
    inst.inst_outputs = ["%6"] /\
    (inst.inst_operands = [Lit 1w] \/ inst.inst_operands = [Lit 2w])) \/
   (idx = 1 /\ inst.inst_opcode = JMP /\
    inst.inst_operands = [Label "@exit_2"]))
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[] >>
  Cases_on `idx` >> gvs[] >> Cases_on `n` >> gvs[]
QED

Theorem word_interval_terminator_fetch:
  !lbl bb inst.
  lookup_block lbl word_interval_function.fn_blocks = SOME bb /\
  MEM inst bb.bb_instructions /\ is_terminator inst.inst_opcode ==>
  ((lbl = "entry" /\ inst.inst_opcode = JNZ /\
    inst.inst_operands = [Var "%5"; Label "@then_0"; Label "@else_1"]) \/
   ((lbl = "@then_0" \/ lbl = "@else_1") /\
    inst.inst_opcode = JMP /\ inst.inst_operands = [Label "@exit_2"]) \/
   (lbl = "@exit_2" /\ inst.inst_opcode = STOP))
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[AllCaseEqs(), is_terminator_def]
QED

Theorem word_interval_writers:
  !lbl bb inst.
  lookup_block lbl word_interval_function.fn_blocks = SOME bb /\
  MEM inst bb.bb_instructions /\ MEM "%6" inst.inst_outputs ==>
  lbl = "@then_0" \/ lbl = "@else_1"
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem word_interval_nonterm_scalar:
  lookup_block s.vs_current_bb word_interval_function.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst s = OK t /\
  (!x. x IN word_interval_scalars s ==> FLOOKUP G x = NONE) ==>
  !x. x IN word_interval_scalars (t with vs_inst_idx := SUC s.vs_inst_idx) ==>
    FLOOKUP (FST (ghost_step fuel ctx PG G tn inst s)) x = NONE
Proof
  strip_tac >>
  `MEM inst bb.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  drule_all word_interval_instruction_shapes >> strip_tac >>
  drule_all ghost_step_non_invoke >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] SUBST1_TAC) >>
  simp[] >>
  drule_all step_preserves_control_flow >> strip_tac >>
  Cases_on `s.vs_current_bb = "@then_0" \/ s.vs_current_bb = "@else_1"`
  >- (drule_all word_interval_branch_fetch >> strip_tac >>
      gvs[is_terminator_def] >>
      simp[word_interval_scalars_def, step_prov_def, out_prov_def,
           first_prov_def, op_prov_def, set_prov_def, FLOOKUP_DRESTRICT]) >>
  `~MEM "%6" inst.inst_outputs` by metis_tac[word_interval_writers] >>
  Cases_on `s.vs_current_bb = "@exit_2"` >>
  gvs[word_interval_scalars_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[step_prov_other_output]
QED

Theorem word_interval_terminator_successor:
  lookup_block s.vs_current_bb word_interval_function.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK t ==>
  (t = jump_to "@then_0" s \/ t = jump_to "@else_1" s) \/
  ((s.vs_current_bb = "@then_0" \/ s.vs_current_bb = "@else_1") /\
   s.vs_inst_idx = 1 /\ t = jump_to "@exit_2" s)
Proof
  strip_tac >>
  `MEM inst bb.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  drule_all word_interval_terminator_fetch >> strip_tac
  >- (gvs[step_inst_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
      metis_tac[]) 
  >- (drule_at (Pat `lookup_block _ _ = _`) word_interval_branch_fetch >>
      simp[] >> disch_then drule >> strip_tac >>
      gvs[step_inst_def, step_inst_base_opcode_eqs, is_terminator_def])
  >- (drule_at (Pat `lookup_block _ _ = _`) word_interval_branch_fetch >>
      simp[] >> disch_then drule >> strip_tac >>
      gvs[step_inst_def, step_inst_base_opcode_eqs, is_terminator_def]) >>
  gvs[step_inst_def, step_inst_base_opcode_eqs]
QED

Theorem word_interval_no_phis:
  !lbl bb s.
  lookup_block lbl word_interval_function.fn_blocks = SOME bb ==>
  eval_phis s bb.bb_instructions = OK s /\
  phi_prefix_length bb.bb_instructions = 0
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  simp[Once eval_phis_def, Once phi_prefix_length_def]
QED

Theorem word_interval_jump_scalars:
  ((t = jump_to "@then_0" s \/ t = jump_to "@else_1" s) \/
   ((s.vs_current_bb = "@then_0" \/ s.vs_current_bb = "@else_1") /\
     s.vs_inst_idx = 1 /\ t = jump_to "@exit_2" s)) /\
  (!x. x IN word_interval_scalars s ==> FLOOKUP G x = NONE) ==>
  !x. x IN word_interval_scalars t ==> FLOOKUP G x = NONE
Proof
  simp[word_interval_scalars_def, jump_to_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem word_interval_edge_scalar:
  gas_path_ptr_edge D lo ctx word_interval_function PG G tn s n G' tn' (OK t) /\
  (!x. x IN word_interval_scalars s ==> FLOOKUP G x = NONE) ==>
  !x. x IN word_interval_scalars t ==> FLOOKUP G' x = NONE
Proof
  simp[gas_path_ptr_edge_def] >> rpt strip_tac >> gvs[]
  >- (drule_all word_interval_nonterm_scalar >>
      disch_then (qspecl_then [`tn`, `PG`] mp_tac) >>
      Cases_on `ghost_step fuel ctx PG G tn inst s` >> gvs[])
  >- (drule_all word_interval_no_phis >> strip_tac >> gvs[] >>
      gvs[word_interval_entry_prov] >>
      drule_all word_interval_terminator_successor >> strip_tac >>
      gvs[word_interval_scalars_def, jump_to_def])
  >- (drule_all word_interval_terminator_successor >> strip_tac >>
      irule word_interval_jump_scalars >> metis_tac[]) >>
  qpat_x_assum `OK _ = _` (mp_tac o SYM) >>
  disch_then SUBST_ALL_TAC >> gvs[exit_result_def]
QED

Theorem word_interval_path_scalar:
  s0.vs_current_bb = (SND word_interval_start).cs_current_bb /\
  gas_path_ptr D lo ctx word_interval_function PG G0 tn0 s0 n G tn (OK t) /\
  t.vs_current_bb = "@exit_2" ==>
  FLOOKUP G "%6" = NONE
Proof
  strip_tac >> drule gas_path_ptr_normal_invariant >>
  disch_then (qspecl_then
    [`\H s. !x. x IN word_interval_scalars s ==> FLOOKUP H x = NONE`, `t`]
    mp_tac) >>
  (impl_tac
   >- (simp[] >> conj_tac
       >- (drule word_interval_scalar_initial >> simp[]) >>
       metis_tac[word_interval_edge_scalar])) >>
  simp[word_interval_scalars_def]
QED

Theorem word_interval_operand_path_scalar:
  !D lo ctx PG G0 tn0 s0 n G tn t op sm.
  lower_value compile_expr (FST word_interval_start) (BaseT (IntT 256))
    (IfExp (BaseT (IntT 256)) (Name (BaseT BoolT) "b")
      (Literal (BaseT (IntT 256)) (IntL 1))
      (Literal (BaseT (IntT 256)) (IntL 2)))
    (SND word_interval_start) = (op,sm) /\
  s0.vs_current_bb = (SND word_interval_start).cs_current_bb /\
  s0.vs_inst_idx = LENGTH (SND word_interval_start).cs_current_insts /\
  gas_path_ptr D lo ctx word_interval_function PG G0 tn0 s0 n G tn (OK t) /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  op_prov G op = NONE
Proof
  rpt strip_tac >> drule word_interval_operand_endpoint >> strip_tac >>
  gvs[op_prov_def] >> irule word_interval_path_scalar >> metis_tac[]
QED
