Theory deployOutcomesFreeLowering
Ancestors
  loweringShapeDefs emitHelper compileEnv venomInst list pair

(* Instruction predicates are kept generic: the constructor application
   instantiates P with exclusion of the six oracle/call opcodes. *)
Theorem outcomes_free_all_blocks:
  EVERY P (state_insts s) <=>
  EVERY (\bb. EVERY P bb.bb_instructions) (all_blocks s)
Proof
  simp[state_insts_def, EVERY_FLAT, EVERY_MAP]
QED

Theorem outcomes_free_state_insts:
  EVERY P (state_insts s) <=>
  EVERY (\bb. EVERY P bb.bb_instructions) s.cs_blocks /\
  EVERY P s.cs_current_insts
Proof
  simp[state_insts_def, all_blocks_def, EVERY_FLAT, EVERY_MAP,
       EVERY_MEM, MEM_REVERSE, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem outcomes_free_bind:
  (!s. EVERY P (state_insts s) ==>
       EVERY P (state_insts (SND (m s)))) /\
  (!x s. EVERY P (state_insts s) ==>
       EVERY P (state_insts (SND (f x s)))) ==>
  !s. EVERY P (state_insts s) ==>
      EVERY P (state_insts (SND (comp_bind m f s)))
Proof
  rpt strip_tac >> Cases_on `m s` >> gvs[comp_bind_def] >>
  first_x_assum irule >>
  qpat_x_assum `!s. _` (qspec_then `s` mp_tac) >> simp[]
QED

Theorem outcomes_free_ignore_bind:
  (!s. EVERY P (state_insts s) ==>
       EVERY P (state_insts (SND (m s)))) /\
  (!s. EVERY P (state_insts s) ==>
       EVERY P (state_insts (SND (f s)))) ==>
  !s. EVERY P (state_insts s) ==>
      EVERY P (state_insts (SND (comp_ignore_bind m f s)))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >> rpt strip_tac >>
  irule outcomes_free_bind >> simp[]
QED

Theorem outcomes_free_return:
  EVERY P (state_insts (SND (comp_return x s))) = EVERY P (state_insts s)
Proof
  simp[comp_return_def]
QED

Theorem outcomes_free_get:
  EVERY P (state_insts (SND (comp_get s))) = EVERY P (state_insts s)
Proof
  simp[comp_get_def]
QED

Theorem outcomes_free_fresh:
  EVERY P (state_insts (SND (fresh_id s))) = EVERY P (state_insts s) /\
  EVERY P (state_insts (SND (fresh_var s))) = EVERY P (state_insts s) /\
  EVERY P (state_insts (SND (fresh_label lbl s))) = EVERY P (state_insts s)
Proof
  simp[fresh_id_def, fresh_var_def, fresh_label_def, outcomes_free_state_insts]
QED

Theorem outcomes_free_new_block:
  EVERY P (state_insts (SND (new_block lbl s))) = EVERY P (state_insts s)
Proof
  simp[new_block_def, outcomes_free_state_insts] >> metis_tac[]
QED

Theorem outcomes_free_emit:
  EVERY P (state_insts (SND (emit i s))) <=> EVERY P (state_insts s) /\ P i
Proof
  simp[emit_def, outcomes_free_state_insts, EVERY_APPEND] >> metis_tac[]
QED

Theorem outcomes_free_emit_ops:
  EVERY (\i. P i.inst_opcode) (state_insts s) /\ P opc ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (emit_op opc ops s))) /\
  EVERY (\i. P i.inst_opcode) (state_insts (SND (emit_void opc ops s))) /\
  EVERY (\i. P i.inst_opcode) (state_insts (SND (emit_inst opc ops outs s)))
Proof
  simp[emit_op_def, emit_void_def, emit_inst_def, comp_ignore_bind_def, comp_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def,
       outcomes_free_state_insts, mk_inst_def]
QED
