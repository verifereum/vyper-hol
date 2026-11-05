(* Local producer boundaries for the operand-linked Extract32 window. *)
Theory bodyMemTbExtract32Origin
Ancestors
  bodyMemTbExtract32Witness builtinBytes exprLowering context emitHelper compileEnv
  venomInst builtinMisc

Theorem extract32_slice_data_opcodes:
  compile_slice_data len data start amount outsz sa = (op,sb) ==>
  MAP (\i. i.inst_opcode) sb.cs_current_insts =
  MAP (\i. i.inst_opcode) sa.cs_current_insts ++
    [ADD; LT; GT; OR; ISZERO; ASSERT; ALLOCA; ADD; ADD; MCOPY; MSTORE]
Proof
  simp[compile_slice_data_def, compile_assert_slice_bounds_def,
       compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem extract32_mul_check_opcodes:
  compile_mul_overflow_check x y res signed bits sa = (u,sb) ==>
  MAP (\i. i.inst_opcode) sb.cs_current_insts =
  MAP (\i. i.inst_opcode) sa.cs_current_insts ++
    ([if signed then SDIV else Div; EQ; ISZERO; OR] ++
     (if signed /\ bits = 256 then [EQ; NOT; ISZERO; AND; ISZERO; AND] else []) ++
     [ASSERT])
Proof
  Cases_on `signed` >> Cases_on `bits = 256` >>
  simp[compile_mul_overflow_check_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem extract32_wei_int_opcodes:
  compile_as_wei_value_int valop scale signed sa = (u,sb) ==>
  MAP (\i. i.inst_opcode) sb.cs_current_insts =
  MAP (\i. i.inst_opcode) sa.cs_current_insts ++
    (if scale = 1 then [] else
     [MUL; Div; EQ; ISZERO; OR] ++
     (if signed then [SLT; ISZERO; AND] else []) ++ [ASSERT])
Proof
  Cases_on `scale = 1` >> Cases_on `signed` >>
  simp[compile_as_wei_value_int_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem extract32_array_subscript_opcodes:
  (if dynamic then loader baseop else comp_return (Lit (n2w n))) sa = (len,sm) /\
  compile_array_subscript baseop idx dynamic n stride elemsz signed loader sa = (u,sb) ==>
  MAP (\i. i.inst_opcode) sb.cs_current_insts =
  MAP (\i. i.inst_opcode) sm.cs_current_insts ++
    ((if signed then [SLT] else []) ++
     [LT; ISZERO; OR; ISZERO; ASSERT] ++
     (if dynamic then [ADD] else []) ++ [MUL; ADD])
Proof
  Cases_on `dynamic` >> Cases_on `signed` >>
  simp[compile_array_subscript_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem extract32_list_membership_opcodes:
  !needle args sa.
    ?ops. MAP (\i. i.inst_opcode)
             (SND (compile_list_membership_in needle args sa)).cs_current_insts =
          MAP (\i. i.inst_opcode) sa.cs_current_insts ++ ops /\
          EVERY (\opc. opc = EQ \/ opc = OR) ops
Proof
  recInduct compile_list_membership_in_ind >> rpt strip_tac >>
  simp[Once compile_list_membership_in_def, comp_return_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, fresh_id_def, fresh_var_def, emit_def,
       mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `compile_list_membership_in needle rest sm` >>
  pairarg_tac >> simp[] >>
  first_x_assum (qspec_then `sm` mp_tac) >>
  simp[Abbr `sm`] >> rpt strip_tac >>
  qexists_tac `[EQ] ++ ops ++ [OR]` >> simp[]
QED
