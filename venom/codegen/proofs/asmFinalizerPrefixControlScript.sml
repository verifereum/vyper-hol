(* Quantitative source chunks for control-flow label renaming. *)
Theory asmFinalizerPrefixControl
Ancestors
  asmSplice asmSymPc asmSymSem asmSem

Theorem rename_label_prefix_chunk:
  !p k x y env ss.
    k+1<LENGTH p /\ EL k p=AsmLabel x /\
    EL (k+1) p=AsmLabel y /\ ss.sym_base.as_pc=k /\
    ss.sym_base.as_stack=[] ==>
    sym_steps p env 1 ss=SymOK(sym_with_pc (k+1) ss) /\
    (!i a. i<1 /\ sym_steps p env i ss=SymOK a ==>
      a.sym_base.as_pc<LENGTH p /\ EL a.sym_base.as_pc p<>AsmOp "GAS" /\
      a.sym_base.as_gas_readings=ss.sym_base.as_gas_readings)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[sym_steps_pos, sym_step_def, asm_step_def, sym_lift_def,
           asm_next_def, sym_steps_def, sym_with_pc_def] >>
      simp[sym_state_component_equality, asm_state_component_equality]) >>
  rpt strip_tac >> `i=0` by decide_tac >>
  gvs[sym_steps_def]
QED

Theorem rename_jump_prefix_chunk:
  !p k x y j env ss.
    k+2<LENGTH p /\ EL k p=AsmLabel x /\
    EL (k+1) p=AsmPushLabel y /\ EL (k+2) p=AsmOp "JUMP" /\
    INDEX_OF (AsmLabel y) p=SOME j /\ ss.sym_base.as_pc=k /\
    ss.sym_base.as_stack=[] ==>
    sym_steps p env 3 ss=SymOK(sym_with_pc j ss) /\
    (!i a. i<3 /\ sym_steps p env i ss=SymOK a ==>
      a.sym_base.as_pc<LENGTH p /\ EL a.sym_base.as_pc p<>AsmOp "GAS" /\
      a.sym_base.as_gas_readings=ss.sym_base.as_gas_readings)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[sym_steps_pos, sym_step_def, asm_step_def, sym_lift_def,
           asm_next_def, sym_steps_def, sym_with_pc_def,
           sym_set_stack_def, sym_step_op_def, sym_jump_def, sym_jump_dest_def] >>
      simp[sym_state_component_equality, asm_state_component_equality]) >>
  rpt strip_tac >> `i=0 \/ i=1 \/ i=2` by decide_tac >>
  gvs[sym_steps_pos, sym_steps_def, sym_step_def, asm_step_def,
      sym_lift_def, asm_next_def, sym_set_stack_def] >>
  gvs[sym_state_component_equality, asm_state_component_equality]
QED
