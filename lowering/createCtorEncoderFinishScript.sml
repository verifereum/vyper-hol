Theory createCtorEncoderFinish
Ancestors
  exprLowering compileEnv emitHelper fragExec venomInst rich_list list arithmetic
Libs pairLib

Theorem ctor_encoder_finish_position:
  compile_abi_encode_values_to_buf ce dst rows st = (alen,en) /\
  fn_has_code st en fn ==>
  ?bb k j.
    lookup_block en.cs_current_bb fn.fn_blocks = SOME bb /\
    LENGTH en.cs_current_insts = SUC k /\
    get_instruction bb k = SOME j /\
    j.inst_opcode = MLOAD /\ en.cs_next_id = SUC j.inst_id
Proof
  simp[compile_abi_encode_values_to_buf_def, comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  simp[emit_op_def, comp_ignore_bind_def, comp_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  rename1 `compile_abi_encode_value_rows _ _ _ _ _ _ = ((),pre)` >>
  qexists `LENGTH pre.cs_current_insts` >>
  fs[get_instruction_def, ADD1, el_append3, mk_inst_def]
QED
