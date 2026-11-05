Theory bodyPtrTypeBuiltinsControlClosure
Ancestors
  bodyPtrTypeBuiltinsControlProbe bodyPtrTypeBuiltinsScalarCertificate
  fragGasPathPtr fragExec ptrSafeRun venomExecSemantics venomInstProofs
  venomState venomInst gasCount

(* A finite PC invariant is needed to distinguish execution before and after
   the producer.  It describes only the checked closed conditional, not a
   universal compiler certificate. *)
Definition literal_conditional_pc_inv_def:
  literal_conditional_pc_inv G s <=>
    (s.vs_current_bb = "entry" /\ s.vs_inst_idx = 0) \/
    (MEM s.vs_current_bb ["@then_0"; "@else_1"] /\
      (s.vs_inst_idx = 0 \/
       (s.vs_inst_idx = 1 /\ FLOOKUP G "%0" = NONE))) \/
    (s.vs_current_bb = "@exit_2" /\ s.vs_inst_idx = 0 /\
     FLOOKUP G "%0" = NONE)
End

Theorem no_phi_jump_edge_result:
  gas_path_ptr_edge D lo ctx fn PG G tn s n H ts (OK t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  MEM i.inst_opcode [JNZ; JMP] /\
  (!fuel. step_inst fuel ctx i s = OK (jump_to lbl s)) /\
  (!target. lookup_block lbl fn.fn_blocks = SOME target ==>
    eval_phis (jump_to lbl s) target.bb_instructions = OK (jump_to lbl s) /\
    phi_prefix_length target.bb_instructions = 0) /\
  entry_prov fn (jump_to lbl s) G = G ==>
  t = jump_to lbl s /\ H = G
Proof
  strip_tac >>
  gvs[gas_path_ptr_edge_def, is_terminator_def, exit_result_def] >>
  gvs[jump_to_def]
QED

Theorem literal_conditional_phi_prefix:
  compile_expr ce (BaseT (UintT 256))
    (IfExp (BaseT (UintT 256)) (Literal (BaseT BoolT) (BoolL b))
      (Literal (BaseT (UintT 256)) (IntL 7))
      (Literal (BaseT (UintT 256)) (IntL 9)))
    (initial_compile_state "entry") = (vv, st) /\
  fn.fn_blocks = REVERSE st.cs_blocks ++
    [<|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts|>] /\
  lookup_block lbl fn.fn_blocks = SOME target ==>
  eval_phis s target.bb_instructions = OK s /\
  phi_prefix_length target.bb_instructions = 0
Proof
  strip_tac >> drule compile_literal_conditional_probe >> strip_tac >>
  gvs[lookup_block_def, listTheory.FIND_thm] >>
  Cases_on `lbl = "entry"`
  >- gvs[eval_phis_def, phi_prefix_length_def] >>
  Cases_on `lbl = "@then_0"`
  >- gvs[eval_phis_def, phi_prefix_length_def] >>
  Cases_on `lbl = "@else_1"`
  >- gvs[eval_phis_def, phi_prefix_length_def] >>
  Cases_on `lbl = "@exit_2"` >>
  gvs[eval_phis_def, phi_prefix_length_def]
QED

Theorem literal_assign_edge_control:
  gas_path_ptr_edge D lo ctx fn PG G tn s n H ts (OK t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode = ASSIGN /\ i.inst_outputs = [x] /\
  i.inst_operands = [Lit w] ==>
  t.vs_current_bb = s.vs_current_bb /\
  t.vs_inst_idx = SUC s.vs_inst_idx /\ FLOOKUP H x = NONE
Proof
  strip_tac >>
  `FLOOKUP H x = NONE` by metis_tac[literal_assign_edge_none] >>
  gvs[gas_path_ptr_edge_def, is_terminator_def, exit_result_def] >>
  gvs[step_inst_non_invoke, step_inst_base_def, eval_operand_def,
      update_var_def, exit_result_def]
QED

Theorem gas_path_ptr_edge_fetch:
  gas_path_ptr_edge D lo ctx fn PG G tn s n H ts r ==>
  ?bb i. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
         get_instruction bb s.vs_inst_idx = SOME i
Proof
  simp[gas_path_ptr_edge_def] >> metis_tac[]
QED

Theorem literal_conditional_jump_edge:
  compile_expr ce (BaseT (UintT 256))
    (IfExp (BaseT (UintT 256)) (Literal (BaseT BoolT) (BoolL b))
      (Literal (BaseT (UintT 256)) (IntL 7))
      (Literal (BaseT (UintT 256)) (IntL 9)))
    (initial_compile_state "entry") = (vv, st) /\
  fn.fn_blocks = REVERSE st.cs_blocks ++
    [<|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts|>] /\
  gas_path_ptr_edge D lo ctx fn PG G tn s n H ts (OK t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  MEM i.inst_opcode [JNZ; JMP] /\
  (!fuel. step_inst fuel ctx i s = OK (jump_to lbl s)) ==>
  t = jump_to lbl s /\ H = G
Proof
  strip_tac >>
  drule_at (Pat `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _`)
    no_phi_jump_edge_result >> disch_then irule >>
  conj_tac
  >- metis_tac[literal_conditional_phi_prefix] >>
  conj_tac
  >- metis_tac[literal_conditional_entry_prov] >>
  qexistsl_tac [`bb`, `i`] >> simp[]
QED

Theorem literal_conditional_edge_inv:
  compile_expr ce (BaseT (UintT 256))
    (IfExp (BaseT (UintT 256)) (Literal (BaseT BoolT) (BoolL b))
      (Literal (BaseT (UintT 256)) (IntL 7))
      (Literal (BaseT (UintT 256)) (IntL 9)))
    (initial_compile_state "entry") = (vv, st) /\
  fn.fn_blocks = REVERSE st.cs_blocks ++
    [<|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts|>] /\
  gas_path_ptr_edge D lo ctx fn PG G tn s n H ts (OK t) /\
  literal_conditional_pc_inv G s ==>
  literal_conditional_pc_inv H t
Proof
  strip_tac >> drule gas_path_ptr_edge_fetch >> strip_tac >>
  gvs[literal_conditional_pc_inv_def]
  >~ [`gas_path_ptr_edge _ _ _ _ _ _ _ s _ _ _ _`,
       `s.vs_current_bb = "entry"`] >- suspend "entry"
  >~ [`gas_path_ptr_edge _ _ _ _ _ _ _ s _ _ _ _`,
       `s.vs_current_bb = "@exit_2"`]
  >- (drule compile_literal_conditional_probe >> strip_tac >>
      gvs[lookup_block_def, get_instruction_def, listTheory.FIND_thm]) >>
  all_tac
  >~ [`gas_path_ptr_edge _ _ _ _ _ _ _ s _ _ _ _`, `s.vs_inst_idx = 0`]
  >- suspend "assign"
  >~ [`gas_path_ptr_edge _ _ _ _ _ _ _ s _ _ _ _`, `s.vs_inst_idx = 0`]
  >- suspend "assign" >>
  suspend "jumps"
QED

Resume literal_conditional_edge_inv[entry]:
  `i = <|inst_id := 0; inst_opcode := JNZ;
      inst_operands := [Lit (if b then 1w else 0w);
        Label "@then_0"; Label "@else_1"]; inst_outputs := []|>` by
    (drule compile_literal_conditional_probe >> strip_tac >>
     gvs[lookup_block_def, get_instruction_def, listTheory.FIND_thm]) >>
  `t = jump_to (if b then "@then_0" else "@else_1") s /\ H = G` by
    (irule literal_conditional_jump_edge >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     gen_tac >> Cases_on `b` >>
     gvs[step_inst_non_invoke, step_inst_base_def, eval_operand_def]) >>
  Cases_on `b` >> gvs[jump_to_def]
QED

Resume literal_conditional_edge_inv[assign]:
  markerLib.RESUME_TAC >> (
  `?w. i.inst_opcode = ASSIGN /\ i.inst_outputs = ["%0"] /\
       i.inst_operands = [Lit w]` by
    (drule compile_literal_conditional_probe >> strip_tac >>
     gvs[lookup_block_def, get_instruction_def, listTheory.FIND_thm]) >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 1 /\
   FLOOKUP H "%0" = NONE` by
    (drule_at (Pat `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _`)
       literal_assign_edge_control >> simp[] >>
     disch_then irule >> metis_tac[]) >> gvs[])
QED

Resume literal_conditional_edge_inv[jumps]:
  markerLib.RESUME_TAC >> (
  `i.inst_opcode = JMP /\ i.inst_operands = [Label "@exit_2"]` by
    (drule compile_literal_conditional_probe >> strip_tac >>
     gvs[lookup_block_def, get_instruction_def, listTheory.FIND_thm]) >>
  `t = jump_to "@exit_2" s /\ H = G` by
    (irule literal_conditional_jump_edge >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     gvs[step_inst_non_invoke, step_inst_base_def]) >>
  gvs[jump_to_def])
QED

Finalise literal_conditional_edge_inv

Theorem literal_conditional_all_paths:
  compile_expr ce (BaseT (UintT 256))
    (IfExp (BaseT (UintT 256)) (Literal (BaseT BoolT) (BoolL b))
      (Literal (BaseT (UintT 256)) (IntL 7))
      (Literal (BaseT (UintT 256)) (IntL 9)))
    (initial_compile_state "entry") = (vv, st) /\
  fn.fn_blocks = REVERSE st.cs_blocks ++
    [<|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts|>] /\
  ~s.vs_halted /\ s.vs_current_bb = "entry" /\ s.vs_inst_idx = 0 /\
  gas_path_ptr D lo ctx fn PG G tn s n H ts (OK t) /\
  t.vs_current_bb = st.cs_current_bb /\
  t.vs_inst_idx = LENGTH st.cs_current_insts ==>
  FLOOKUP H "%0" = NONE
Proof
  strip_tac >>
  `literal_conditional_pc_inv H t` by
    (drule gas_path_ptr_prov_invariant >>
     disch_then (qspec_then `literal_conditional_pc_inv` irule) >>
     simp[] >> conj_tac
     >- metis_tac[literal_conditional_edge_inv] >>
     simp[literal_conditional_pc_inv_def]) >>
  drule compile_literal_conditional_probe >> strip_tac >>
  gvs[literal_conditional_pc_inv_def]
QED
