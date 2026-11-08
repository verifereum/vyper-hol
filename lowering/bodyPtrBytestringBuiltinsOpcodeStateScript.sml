Theory bodyPtrBytestringBuiltinsOpcodeState
Ancestors
  bodyPtrBytestringBuiltinsOpcodePrimitives bodyPtrBytestringBuiltinsImageBoundary
  exprCallBounds compileEnv emitHelper venomInst list

(* A single proof-interface abbreviation avoids repeating the two instruction
   streams in every callback contract. It adds no compiler semantics. *)
Definition compiler_no_extcode_def:
  compiler_no_extcode s <=>
    EVERY (\bb. EVERY (\i. i.inst_opcode <> EXTCODECOPY)
      bb.bb_instructions) s.cs_blocks /\
    EVERY (\i. i.inst_opcode <> EXTCODECOPY) s.cs_current_insts
End

Theorem no_extcode_emit_inst:
  opc <> EXTCODECOPY /\ compiler_no_extcode s ==>
  compiler_no_extcode (SND (emit_inst opc ops outs s))
Proof
  Cases_on `emit_inst opc ops outs s` >> Cases_on `q` >>
  simp[compiler_no_extcode_def] >> strip_tac >>
  irule instruction_predicate_emit_inst >>
  goal_assum (drule_at Any) >> simp[mk_inst_def] >> metis_tac[]
QED

Theorem no_extcode_emit_void:
  opc <> EXTCODECOPY /\ compiler_no_extcode s ==>
  compiler_no_extcode (SND (emit_void opc ops s))
Proof
  Cases_on `emit_void opc ops s` >> Cases_on `q` >>
  simp[compiler_no_extcode_def] >> strip_tac >>
  irule instruction_predicate_emit_void >>
  goal_assum (drule_at Any) >> simp[mk_inst_def] >> metis_tac[]
QED

Theorem no_extcode_emit_op:
  opc <> EXTCODECOPY /\ compiler_no_extcode s ==>
  compiler_no_extcode (SND (emit_op opc ops s))
Proof
  Cases_on `emit_op opc ops s` >>
  simp[compiler_no_extcode_def] >> strip_tac >>
  irule instruction_predicate_emit_op >>
  goal_assum (drule_at Any) >> simp[mk_inst_def] >> metis_tac[]
QED

Theorem no_extcode_new_block:
  compiler_no_extcode s ==>
  compiler_no_extcode (SND (new_block label s))
Proof
  Cases_on `new_block label s` >>
  drule new_block_per_block >>
  simp[compiler_no_extcode_def]
QED

Theorem no_extcode_fresh_ops:
  compiler_no_extcode s ==>
  compiler_no_extcode (SND (fresh_var s)) /\
  compiler_no_extcode (SND (fresh_label suffix s)) /\
  compiler_no_extcode (SND (fresh_id s)) /\
  compiler_no_extcode (SND (comp_return x s)) /\
  compiler_no_extcode (SND (comp_get s))
Proof
  simp[compiler_no_extcode_def, fresh_var_def, fresh_label_def,
       fresh_id_def, comp_return_def, comp_get_def]
QED

Theorem no_extcode_bind:
  (!s. compiler_no_extcode s ==> compiler_no_extcode (SND (m s))) /\
  (!x s. compiler_no_extcode s ==> compiler_no_extcode (SND (k x s))) ==>
  !s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (comp_bind m k s))
Proof
  simp[compiler_invariant_bind]
QED

Theorem no_extcode_ignore_bind:
  (!s. compiler_no_extcode s ==> compiler_no_extcode (SND (m s))) /\
  (!s. compiler_no_extcode s ==> compiler_no_extcode (SND (k s))) ==>
  !s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (comp_ignore_bind m k s))
Proof
  simp[compiler_invariant_ignore_bind]
QED

Theorem no_extcode_result:
  m s = (x,t) /\ compiler_no_extcode s /\
  (!s. compiler_no_extcode s ==> compiler_no_extcode (SND (m s))) ==>
  compiler_no_extcode t
Proof
  strip_tac >> first_x_assum (qspec_then `s` mp_tac) >> simp[]
QED

Theorem no_extcode_slice_bounds_copy:
  opc <> EXTCODECOPY /\ compiler_no_extcode s ==>
  compiler_no_extcode (SND
    (comp_ignore_bind (compile_assert_slice_bounds start len limit)
      (emit_void opc ops) s))
Proof
  Cases_on `comp_ignore_bind (compile_assert_slice_bounds start len limit)
    (emit_void opc ops) s` >> Cases_on `q` >>
  simp[compiler_no_extcode_def] >> strip_tac >>
  irule slice_bounds_copy_no_extcode >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem no_extcode_invalid_expr:
  compiler_no_extcode s ==>
  compiler_no_extcode (SND (invalid_expr_call ty s))
Proof
  simp[invalid_expr_call_def] >> pairarg_tac >> simp[] >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `s`, `opc` |-> `INVALID`, `ops` |-> `[]`,
    `outs` |-> `[]`] no_extcode_emit_inst) >> simp[]
QED
