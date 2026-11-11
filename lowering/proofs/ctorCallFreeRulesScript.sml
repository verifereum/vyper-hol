(* Instruction-predicate boundaries for the compilation state monad. *)
Theory ctorCallFreeRules
Ancestors
  list compileEnv venomInst loweringShapeDefs emitHelper

Theorem every_state_insts_blocks:
  EVERY P (state_insts st) <=>
  EVERY (\bb. EVERY P bb.bb_instructions) (all_blocks st)
Proof
  simp[state_insts_def, EVERY_FLAT, EVERY_MAP]
QED

Theorem every_state_insts_return:
  EVERY P (state_insts st) ==>
  EVERY P (state_insts (SND (comp_return x st)))
Proof
  simp[comp_return_def]
QED

Theorem every_state_insts_get:
  EVERY P (state_insts st) ==>
  EVERY P (state_insts (SND (comp_get st)))
Proof
  simp[comp_get_def]
QED

Theorem every_state_insts_fresh_var:
  EVERY P (state_insts st) ==>
  EVERY P (state_insts (SND (fresh_var st)))
Proof
  simp[fresh_var_def, state_insts_def, all_blocks_def]
QED

Theorem every_state_insts_fresh_id:
  EVERY P (state_insts st) ==>
  EVERY P (state_insts (SND (fresh_id st)))
Proof
  simp[fresh_id_def, state_insts_def, all_blocks_def]
QED

Theorem every_state_insts_fresh_label:
  EVERY P (state_insts st) ==>
  EVERY P (state_insts (SND (fresh_label suffix st)))
Proof
  simp[fresh_label_def, state_insts_def, all_blocks_def]
QED

Theorem every_state_insts_emit:
  EVERY P (state_insts st) /\ P inst ==>
  EVERY P (state_insts (SND (emit inst st)))
Proof
  simp[emit_def, state_insts_def, all_blocks_def]
QED

Theorem every_state_insts_new_block:
  EVERY P (state_insts st) ==>
  EVERY P (state_insts (SND (new_block label st)))
Proof
  simp[new_block_def, state_insts_def, all_blocks_def]
QED

Theorem every_state_insts_bind:
  (!st. EVERY P (state_insts st) ==>
        EVERY P (state_insts (SND (m st)))) /\
  (!x st. EVERY P (state_insts st) ==>
          EVERY P (state_insts (SND (f x st)))) ==>
  !st. EVERY P (state_insts st) ==>
       EVERY P (state_insts (SND (comp_bind m f st)))
Proof
  rpt strip_tac >> Cases_on `m st` >> gvs[comp_bind_def] >>
  metis_tac[pairTheory.SND]
QED

Theorem every_state_insts_ignore_bind:
  (!st. EVERY P (state_insts st) ==>
        EVERY P (state_insts (SND (m st)))) /\
  (!st. EVERY P (state_insts st) ==>
        EVERY P (state_insts (SND (n st)))) ==>
  !st. EVERY P (state_insts st) ==>
       EVERY P (state_insts (SND (comp_ignore_bind m n st)))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  simp[every_state_insts_bind]
QED

Theorem every_state_insts_emit_inst:
  (!id. P (mk_inst id opc ops outs)) /\ EVERY P (state_insts st) ==>
  EVERY P (state_insts (SND (emit_inst opc ops outs st)))
Proof
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def,
       state_insts_def, all_blocks_def]
QED

Theorem every_state_insts_emit_void:
  (!id. P (mk_inst id opc ops [])) /\ EVERY P (state_insts st) ==>
  EVERY P (state_insts (SND (emit_void opc ops st)))
Proof
  simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
       state_insts_def, all_blocks_def]
QED

Theorem every_state_insts_emit_op:
  (!id out. P (mk_inst id opc ops [out])) /\ EVERY P (state_insts st) ==>
  EVERY P (state_insts (SND (emit_op opc ops st)))
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, state_insts_def, all_blocks_def]
QED

Theorem every_state_insts_fresh_vars:
  !n st. EVERY P (state_insts st) ==>
  EVERY P (state_insts (SND (fresh_vars n st)))
Proof
  Induct >> simp[fresh_vars_def, every_state_insts_return] >>
  simp[every_state_insts_bind, every_state_insts_fresh_var,
       every_state_insts_return]
QED

Theorem every_state_insts_empty:
  st.cs_blocks = [] /\ st.cs_current_insts = [] ==>
  EVERY P (state_insts st)
Proof
  simp[state_insts_def, all_blocks_def]
QED

Theorem call_free_emit_inst:
  opc <> RETURNDATACOPY /\ opc <> INVOKE /\
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
        (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
        (state_insts (SND (emit_inst opc ops outs st)))
Proof
  strip_tac >> irule every_state_insts_emit_inst >> simp[mk_inst_def]
QED

Theorem call_free_emit_void:
  opc <> RETURNDATACOPY /\ opc <> INVOKE /\
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
        (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
        (state_insts (SND (emit_void opc ops st)))
Proof
  strip_tac >> irule every_state_insts_emit_void >> simp[mk_inst_def]
QED

Theorem call_free_emit_op:
  opc <> RETURNDATACOPY /\ opc <> INVOKE /\
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
        (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
        (state_insts (SND (emit_op opc ops st)))
Proof
  strip_tac >> irule every_state_insts_emit_op >> simp[mk_inst_def]
QED
