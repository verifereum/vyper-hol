Theory makeSsaRfAssign
Ancestors contextCodegenRel venomInst list

Definition rf_map_operand_def:
  (rf_map_operand f (Var v) = Var (f v)) /\
  (rf_map_operand f (Lit n) = Lit n) /\
  (rf_map_operand f (Label l) = Label l)
End

Definition rf_operand_in_def:
  (rf_operand_in V (Var v) <=> MEM v V) /\
  (rf_operand_in V (Lit n) <=> T) /\
  (rf_operand_in V (Label l) <=> T)
End

(* Only non-outputs need separation. PHI operands are deliberately opaque. *)
Definition rf_local_step_def:
  rf_local_step V f g inst inst' <=>
    inst'.inst_opcode = inst.inst_opcode /\
    (ALL_DISTINCT inst.inst_outputs ==>
      inst'.inst_outputs = MAP g inst.inst_outputs) /\
    (inst.inst_opcode <> PHI ==>
      inst'.inst_operands = MAP (rf_map_operand f) inst.inst_operands) /\
    (!v. MEM v V /\ ~MEM v inst.inst_outputs ==>
      g v = f v /\ ~MEM (g v) inst'.inst_outputs)
End

Theorem rf_step_back_assign_success:
  rf_local_step V f g inst inst' /\ rf_operand_in V op /\
  step_back_assign inst op = SOME q ==>
  step_back_assign inst' (rf_map_operand g op) =
    SOME (rf_map_operand f q)
Proof
  Cases_on `op` >>
  simp[rf_operand_in_def, rf_map_operand_def, step_back_assign_def] >>
  rpt strip_tac >> gvs[rf_local_step_def, rf_map_operand_def] >>
  Cases_on `MEM s inst.inst_outputs` >> gvs[]
  >- (gvs[AllCaseEqs()] >> Cases_on `inst.inst_operands` >> gvs[]) >>
  first_x_assum drule_all >> simp[rf_map_operand_def]
QED

Theorem rf_resolve_assign_cons:
  inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [v] /\
  inst.inst_operands = [src] ==>
  resolve_block_assigns (inst::rest) op =
    resolve_block_assigns rest (if op = Var v then src else op)
Proof
  strip_tac >> Cases_on `op`
  >- (Cases_on `rest` >> simp[resolve_block_assigns_def])
  >- (Cases_on `s = v` >> simp[Once resolve_block_assigns_def]) >>
  Cases_on `rest` >> simp[resolve_block_assigns_def]
QED

(* A fresh output on a self-copy must step back to the OLD spelling. *)
Theorem rf_self_copy_probe:
  step_back_assign (mk_inst 0 ASSIGN [Var "x"] ["x"]) (Var "x") =
    SOME (Var "x") /\
  step_back_assign (mk_inst 0 ASSIGN [Var "old_x"] ["fresh_x"])
    (Var "fresh_x") = SOME (Var "old_x")
Proof
  EVAL_TAC
QED

Theorem rf_distinct_copy_probe:
  step_back_assign (mk_inst 0 ASSIGN [Var "x"] ["y"]) (Var "y") =
    SOME (Var "x") /\
  step_back_assign (mk_inst 0 ASSIGN [Var "renamed_x"] ["fresh_y"])
    (Var "fresh_y") = SOME (Var "renamed_x") /\
  step_back_assign (mk_inst 0 ASSIGN [Var "renamed_x"] ["fresh_y"])
    (Var "renamed_x") = SOME (Var "renamed_x")
Proof
  EVAL_TAC
QED

Theorem rf_multi_output_barrier_probe:
  step_back_assign (mk_inst 0 INVOKE [] ["fresh_x"; "fresh_y"])
    (Var "fresh_x") = NONE /\
  step_back_assign (mk_inst 0 INVOKE [] ["fresh_x"; "fresh_y"])
    (Var "fresh_y") = NONE /\
  step_back_assign (mk_inst 0 INVOKE [] ["fresh_x"; "fresh_y"])
    (Var "old_z") = SOME (Var "old_z")
Proof
  EVAL_TAC
QED

Theorem rf_self_copy_interface_probe:
  rf_local_step [x] f g
    (mk_inst id ASSIGN [Var x] [x])
    (mk_inst id ASSIGN [Var (f x)] [g x])
Proof
  simp[rf_local_step_def, mk_inst_def, rf_map_operand_def]
QED

Theorem rf_distinct_copy_interface_probe:
  x <> y /\ g x = f x /\ g x <> g y ==>
  rf_local_step [x;y] f g
    (mk_inst id ASSIGN [Var x] [y])
    (mk_inst id ASSIGN [Var (f x)] [g y])
Proof
  simp[rf_local_step_def, mk_inst_def, rf_map_operand_def] >>
  metis_tac[]
QED

Theorem rf_duplicate_output_interface_probe:
  rf_local_step ["x";"z"] I (\v. if v = "x" then "b" else v)
    (mk_inst 0 INVOKE [] ["x";"x"])
    (mk_inst 0 INVOKE [] ["a";"b"]) /\
  step_back_assign (mk_inst 0 INVOKE [] ["a";"b"])
    (Var "z") = SOME (Var "z")
Proof
  simp[rf_local_step_def, mk_inst_def, step_back_assign_def] >>
  rpt strip_tac >> gvs[]
QED
