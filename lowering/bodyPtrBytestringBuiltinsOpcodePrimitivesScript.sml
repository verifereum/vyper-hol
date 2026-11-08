(* Instruction predicates compose without source or runtime assumptions.
   new_block_per_block already provides the block-finalization boundary. *)
Theory bodyPtrBytestringBuiltinsOpcodePrimitives
Ancestors
  bodyPtrBytestringBuiltinsImageBoundary compileEnv emitHelper builtinBytes
  venomInst list

Theorem instruction_predicate_emit:
  emit inst sa = (out,sb) /\ P inst /\
  EVERY (\bb. EVERY P bb.bb_instructions) sa.cs_blocks /\
  EVERY P sa.cs_current_insts ==>
  EVERY (\bb. EVERY P bb.bb_instructions) sb.cs_blocks /\
  EVERY P sb.cs_current_insts
Proof
  simp[emit_def] >> rpt strip_tac >> gvs[]
QED

Theorem instruction_predicate_emit_inst:
  emit_inst opc ops outs sa = (out,sb) /\
  P (mk_inst sa.cs_next_id opc ops outs) /\
  EVERY (\bb. EVERY P bb.bb_instructions) sa.cs_blocks /\
  EVERY P sa.cs_current_insts ==>
  EVERY (\bb. EVERY P bb.bb_instructions) sb.cs_blocks /\
  EVERY P sb.cs_current_insts
Proof
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem instruction_predicate_emit_void:
  emit_void opc ops sa = (out,sb) /\
  P (mk_inst sa.cs_next_id opc ops []) /\
  EVERY (\bb. EVERY P bb.bb_instructions) sa.cs_blocks /\
  EVERY P sa.cs_current_insts ==>
  EVERY (\bb. EVERY P bb.bb_instructions) sb.cs_blocks /\
  EVERY P sb.cs_current_insts
Proof
  simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem instruction_predicate_emit_op:
  emit_op opc ops sa = (out,sb) /\
  (!x. P (mk_inst sa.cs_next_id opc ops [x])) /\
  EVERY (\bb. EVERY P bb.bb_instructions) sa.cs_blocks /\
  EVERY P sa.cs_current_insts ==>
  EVERY (\bb. EVERY P bb.bb_instructions) sb.cs_blocks /\
  EVERY P sb.cs_current_insts
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem compiler_invariant_bind:
  (!s. R s ==> R (SND (m s))) /\
  (!x s. R s ==> R (SND (k x s))) ==>
  !s. R s ==> R (SND (comp_bind m k s))
Proof
  simp[comp_bind_def] >> rpt strip_tac >>
  pairarg_tac >>
  `R cs'` by (first_x_assum (qspec_then `s` mp_tac) >> simp[]) >>
  simp[]
QED

Theorem compiler_invariant_ignore_bind:
  (!s. R s ==> R (SND (m s))) /\
  (!s. R s ==> R (SND (k s))) ==>
  !s. R s ==> R (SND (comp_ignore_bind m k s))
Proof
  simp[comp_ignore_bind_def, compiler_invariant_bind]
QED

(* A first client: the dynamic copy opcode must satisfy the exclusion.
   Both the arithmetic bounds and the copy preserve the entire block stream. *)
Theorem slice_bounds_copy_no_extcode:
  opc <> EXTCODECOPY /\
  comp_ignore_bind (compile_assert_slice_bounds start len limit)
    (emit_void opc ops) sa = (out,sb) /\
  EVERY (\bb. EVERY (\i. i.inst_opcode <> EXTCODECOPY)
    bb.bb_instructions) sa.cs_blocks /\
  EVERY (\i. i.inst_opcode <> EXTCODECOPY) sa.cs_current_insts ==>
  EVERY (\bb. EVERY (\i. i.inst_opcode <> EXTCODECOPY)
    bb.bb_instructions) sb.cs_blocks /\
  EVERY (\i. i.inst_opcode <> EXTCODECOPY) sb.cs_current_insts
Proof
  simp[compile_assert_slice_bounds_def, comp_ignore_bind_def, comp_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def, mk_inst_def] >>
  rpt strip_tac >> gvs[]
QED
