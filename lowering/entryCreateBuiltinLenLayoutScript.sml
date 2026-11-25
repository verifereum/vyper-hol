(* Only the length-load suffix is administrative; the child may contain calls. *)
Theory entryCreateBuiltinLenLayout
Ancestors
  builtinSimple context emitHelper compileEnv exprLoweringProps abiEncoderProps
  venomInst list rich_list

Theorem compile_len_admin_facts[local]:
  compile_builtin_len ctor imm operand loc sm = (op,sb) ==>
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  EVERY (\i. i.inst_id IN frag_ids sm sb /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (emitted_insts sm sb) /\
  sm.cs_next_id < sb.cs_next_id /\
  LENGTH sm.cs_current_insts < LENGTH sb.cs_current_insts
Proof
  Cases_on `loc` >> Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_builtin_len_def, compile_ptr_load_def, compile_imm_load_word_def,
       emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[is_terminator_def, mk_inst_def, frag_ids_def]
QED

Theorem compile_len_admin_layout:
  compile_builtin_len ctor imm operand loc sm = (op,sb) ==>
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  EVERY (\i. i.inst_id IN frag_ids sm sb /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (emitted_insts sm sb)
Proof
  disch_then (strip_assume_tac o MATCH_MP compile_len_admin_facts) >> simp[]
QED

Theorem compile_len_admin_nonempty:
  compile_builtin_len ctor imm operand loc sm = (op,sb) ==>
  sm.cs_next_id < sb.cs_next_id /\
  LENGTH sm.cs_current_insts < LENGTH sb.cs_current_insts
Proof
  disch_then (strip_assume_tac o MATCH_MP compile_len_admin_facts) >> simp[]
QED
