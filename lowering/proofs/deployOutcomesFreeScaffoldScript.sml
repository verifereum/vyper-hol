(* Constructor scaffolding never consumes the call-outcome oracle. *)
Theory deployOutcomesFreeScaffold
Ancestors
  moduleLowering loweringShapeDefs emitHelper context compileEnv venomInst list
Libs
  monadsyntax

Theorem compile_fixed_region_with_id_excludes_outcomes:
  compile_fixed_region_with_id sz st = (v,st') /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
    bb.bb_instructions) (all_blocks st) ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
    bb.bb_instructions) (all_blocks st')
Proof
  simp[compile_fixed_region_with_id_def, fresh_id_def, fresh_var_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[all_blocks_def, EVERY_APPEND, mk_inst_def]
QED

Theorem compile_nonreentrant_lock_excludes_outcomes:
  compile_nonreentrant_lock key trans view st = (v,st') /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
    bb.bb_instructions) (all_blocks st) ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
    bb.bb_instructions) (all_blocks st')
Proof
  Cases_on `trans` >> Cases_on `view` >>
  simp[compile_nonreentrant_lock_def, emit_op_def, emit_void_def,
       fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[all_blocks_def, EVERY_APPEND, mk_inst_def]
QED

Theorem compile_nonreentrant_unlock_excludes_outcomes:
  compile_nonreentrant_unlock key trans view st = (v,st') /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
    bb.bb_instructions) (all_blocks st) ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
    bb.bb_instructions) (all_blocks st')
Proof
  Cases_on `trans` >> Cases_on `view` >>
  simp[compile_nonreentrant_unlock_def, emit_void_def,
       fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[all_blocks_def, EVERY_APPEND, mk_inst_def]
QED

Theorem compile_constructor_epilogue_excludes_outcomes:
  compile_constructor_epilogue rt cap imm st = (v,st') /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
    bb.bb_instructions) (all_blocks st) ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
    bb.bb_instructions) (all_blocks st')
Proof
  Cases_on `cap > 0` >>
  simp[compile_constructor_epilogue_def, compile_alloc_buffer_def,
       emit_op_def, emit_void_def, emit_inst_def,
       fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[all_blocks_def, EVERY_APPEND, mk_inst_def]
QED

Theorem compile_simple_deploy_excludes_outcomes:
  compile_simple_deploy rt cap st = (v,st') /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
    bb.bb_instructions) (all_blocks st) ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
    bb.bb_instructions) (all_blocks st')
Proof
  simp[compile_simple_deploy_def, compile_alloc_buffer_def,
       emit_op_def, emit_void_def, emit_inst_def,
       fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[all_blocks_def, EVERY_APPEND, mk_inst_def]
QED

Theorem constructor_payable_check_excludes_outcomes:
  (if ~pay then
     do cv <- emit_op CALLVALUE [];
        nv <- emit_op ISZERO [cv]; emit_void ASSERT [nv] od
   else comp_return ()) st = (v,st') /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
    bb.bb_instructions) (all_blocks st) ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
    bb.bb_instructions) (all_blocks st')
Proof
  Cases_on `pay` >>
  simp[emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[all_blocks_def, EVERY_APPEND, mk_inst_def]
QED

Theorem constructor_exit_block_excludes_outcomes:
  (do cs <- comp_get;
      (if block_is_terminated cs then comp_return ()
       else emit_inst JMP [Label exit_lbl] []);
      new_block exit_lbl od) st = (v,st') /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
    bb.bb_instructions) (all_blocks st) ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
    bb.bb_instructions) (all_blocks st')
Proof
  Cases_on `block_is_terminated st` >>
  simp[comp_get_def, emit_inst_def, fresh_id_def, emit_def, new_block_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[all_blocks_def, EVERY_APPEND, mk_inst_def]
QED
