Theory makeSsaRfWitness
Ancestors makeSsaRfAssign contextCodegenRel venomInst list

Theorem rf_same_after_assigns_refl[simp]:
  !xs a. same_after_assigns xs a a
Proof
  Cases >> simp[same_after_assigns_def]
QED

Theorem rf_same_after_assigns_append:
  !xs a b older. same_after_assigns xs a b ==>
    same_after_assigns (xs ++ older) a b
Proof
  Induct >> simp[same_after_assigns_def] >> rpt gen_tac >>
  Cases_on `a = b` >> simp[same_after_assigns_def] >>
  Cases_on `step_back_assign h a` >> simp[] >>
  Cases_on `step_back_assign h b` >> simp[] >> metis_tac[]
QED

(* Identity fields and edge-specific PHI operands are irrelevant to copies. *)
Definition rf_copy_shape_def:
  rf_copy_shape inst inst' <=>
    inst'.inst_opcode = inst.inst_opcode /\
    inst'.inst_outputs = inst.inst_outputs /\
    (inst.inst_opcode <> PHI ==> inst'.inst_operands = inst.inst_operands)
End

Theorem rf_step_back_assign_shape:
  rf_copy_shape inst inst' ==>
  step_back_assign inst' op = step_back_assign inst op
Proof
  Cases_on `op` >> simp[step_back_assign_def, rf_copy_shape_def] >>
  rpt strip_tac >> Cases_on `inst.inst_opcode = PHI` >> gvs[]
QED

Theorem rf_same_after_assigns_shape:
  !xs ys a b. LIST_REL rf_copy_shape xs ys ==>
    same_after_assigns ys a b = same_after_assigns xs a b
Proof
  Induct >> Cases_on `ys` >> simp[same_after_assigns_def] >>
  rpt strip_tac >> drule rf_step_back_assign_shape >> strip_tac >>
  Cases_on `a = b` >> simp[same_after_assigns_def] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

(* Lists are latest first. f is the oldest entry, g the newest exit.
   Every source operand belongs to the fixed relevant variable universe. *)
Definition rf_back_trace_def:
  (rf_back_trace V f g [] ys <=> ys = [] /\ g = f) /\
  (rf_back_trace V f g (inst::xs) ys <=>
    ?h inst' rest. ys = inst'::rest /\
      rf_local_step V h g inst inst' /\
      EVERY (rf_operand_in V) inst.inst_operands /\
      rf_back_trace V f h xs rest)
End

Theorem rf_step_back_assign_in:
  EVERY (rf_operand_in V) inst.inst_operands /\
  rf_operand_in V op /\ step_back_assign inst op = SOME q ==>
  rf_operand_in V q
Proof
  Cases_on `op` >>
  simp[step_back_assign_def, rf_operand_in_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), rf_operand_in_def] >>
  Cases_on `inst.inst_operands` >> gvs[rf_operand_in_def]
QED

Theorem rf_back_trace_append:
  !xs xs' f h g ys ys'.
  rf_back_trace V h g xs xs' /\ rf_back_trace V f h ys ys' ==>
  rf_back_trace V f g (xs ++ ys) (xs' ++ ys')
Proof
  Induct >> simp[rf_back_trace_def] >> rpt strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem rf_same_after_assigns_transport:
  !xs ys f g a b.
  rf_back_trace V f g xs ys /\ rf_operand_in V a /\ rf_operand_in V b /\
  same_after_assigns xs a b ==>
  same_after_assigns ys (rf_map_operand g a) (rf_map_operand g b)
Proof
  Induct >> simp[rf_back_trace_def, same_after_assigns_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >> Cases_on `a = b` >> simp[] >>
  Cases_on `step_back_assign h a` >> gvs[] >>
  Cases_on `step_back_assign h b` >> gvs[] >>
  imp_res_tac rf_step_back_assign_success >>
  Cases_on `rf_map_operand g a = rf_map_operand g b` >>
  simp[same_after_assigns_def] >>
  first_x_assum irule >> metis_tac[rf_step_back_assign_in]
QED

Definition rf_assign_inst_def:
  rf_assign_inst inst <=>
    ?v src. inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [v] /\
      inst.inst_operands = [src]
End

Theorem rf_assign_step_total:
  rf_assign_inst inst ==> ?q. step_back_assign inst op = SOME q
Proof
  simp[rf_assign_inst_def] >> rpt strip_tac >> Cases_on `op` >>
  simp[step_back_assign_def] >> Cases_on `s = v` >> simp[]
QED

Theorem rf_assign_resolve_step:
  rf_assign_inst inst /\ step_back_assign inst op = SOME q ==>
  resolve_block_assigns (inst::xs) op = resolve_block_assigns xs q
Proof
  simp[rf_assign_inst_def] >> rpt strip_tac >>
  drule_all rf_resolve_assign_cons >> disch_then (qspec_then `xs` assume_tac) >>
  Cases_on `op` >> gvs[step_back_assign_def] >>
  Cases_on `s = v` >> gvs[]
QED

Theorem rf_local_step_assign:
  rf_local_step V f g inst inst' /\ rf_assign_inst inst ==>
  rf_assign_inst inst'
Proof
  simp[rf_local_step_def, rf_assign_inst_def] >> rpt strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem rf_resolve_assigns_transport:
  !xs ys f g op.
  rf_back_trace V f g xs ys /\ EVERY rf_assign_inst xs /\ rf_operand_in V op ==>
  resolve_block_assigns ys (rf_map_operand g op) =
    rf_map_operand f (resolve_block_assigns xs op)
Proof
  Induct
  >- simp[rf_back_trace_def, resolve_block_assigns_def] >>
  simp[rf_back_trace_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule rf_assign_step_total >> disch_then (qspec_then `op` strip_assume_tac) >>
  `rf_assign_inst inst'` by metis_tac[rf_local_step_assign] >>
  drule_all rf_step_back_assign_success >> strip_tac >>
  imp_res_tac rf_assign_resolve_step >> simp[] >>
  first_x_assum irule >> metis_tac[rf_step_back_assign_in]
QED

Theorem rf_back_trace_length:
  !xs ys f g. rf_back_trace V f g xs ys ==> LENGTH ys = LENGTH xs
Proof
  Induct >> simp[rf_back_trace_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem rf_back_trace_split:
  !xs ys f g n.
  rf_back_trace V f g xs ys ==>
  ?h. rf_back_trace V h g (TAKE n xs) (TAKE n ys) /\
      rf_back_trace V f h (DROP n xs) (DROP n ys)
Proof
  Induct >> simp[rf_back_trace_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `n` >> simp[rf_back_trace_def] >> gvs[] >>
  first_x_assum drule >> disch_then (qspec_then `n'` strip_assume_tac) >>
  metis_tac[]
QED

Theorem rf_copy_shape_id[simp]:
  rf_copy_shape inst (inst with inst_id := id)
Proof
  simp[rf_copy_shape_def]
QED

Theorem rf_copy_shape_phi_operands:
  inst.inst_opcode = PHI ==>
  rf_copy_shape inst (inst with inst_operands := ops)
Proof
  simp[rf_copy_shape_def]
QED
