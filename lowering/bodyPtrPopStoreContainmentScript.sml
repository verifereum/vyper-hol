Theory bodyPtrPopStoreContainment
Ancestors
  bodyPtrPopCallContainment context exprLowering emitHelper compileEnv venomInst

Theorem pop_compile_storage_pop_current_store:
  compile_dynarray_pop base_op ws elem_sz ctor imm LocStorage sa = (op,sb) ==>
  ?i. MEM i sb.cs_current_insts /\ i.inst_opcode = SSTORE
Proof
  simp[compile_dynarray_pop_def, compile_ptr_load_def, compile_ptr_store_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def, mk_inst_def] >>
  rpt strip_tac >> gvs[] >> dsimp[]
QED

Theorem pop_compile_storage_pop_fn_store:
  compile_dynarray_pop base_op ws elem_sz ctor imm LocStorage sa = (op,sb) /\
  fn_has_code sa sb fn ==>
  ?i. MEM i (fn_insts fn) /\ i.inst_opcode = SSTORE
Proof
  rpt strip_tac >> drule pop_compile_storage_pop_current_store >> strip_tac >>
  qexists_tac `i` >> simp[] >>
  metis_tac[pop_fn_has_code_current_member]
QED
