(* The administrative instructions emitted by a delayed positional snapshot. *)
Theory entryCreatePosSnapshotCode
Ancestors
  typedCopyGasOps exprSimAbiEncodeObliviousCode exprSimAbiGasBridge
  exprLowering compileEnv context emitHelper venomInst list

val admin_op = ``\opc. opc <> GAS /\ opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE``;

fun admin_actions ths =
  let val rules = ths @ [LET_THM, code_action_return, code_action_emit_inst,
       code_action_emit_op, code_action_emit_void, code_action_new_block,
       code_action_fresh_var, code_action_fresh_label]
  in rpt (FIRST [CHANGED_TAC (simp rules), irule code_action_bind,
                  irule code_action_ignore_bind, conj_tac, gen_tac])
  end;

Theorem admin_ptr_actions[local,simp]:
  code_action ^admin_op (compile_ptr_load ctor imm loc p) /\
  code_action ^admin_op (compile_ptr_store ctor imm loc p v) /\
  code_action ^admin_op (compile_imm_load_word ctor imm p)
Proof
  Cases_on `loc` >> Cases_on `imm` >>
  simp[compile_ptr_load_def, compile_ptr_store_def, compile_imm_load_word_def,
       compile_imm_store_word_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >> rpt conj_tac >> admin_actions []
QED

Theorem admin_word_copy_action[local,simp]:
  code_action ^admin_op (compile_word_copy_loop_base src dst n ll sl ctor imm)
Proof
  Cases_on `word_scale ll = 1` >> Cases_on `word_scale sl = 1` >>
  simp[compile_word_copy_loop_base_def, comp_ignore_bind_def] >>
  admin_actions [admin_ptr_actions]
QED

Theorem admin_imm_copy_action[local,simp]:
  !n off. code_action ^admin_op (compile_imm_copy_to_memory ctor imm src dst n off)
Proof
  `!p off. code_action ^admin_op (compile_lit_byte_offset p off)` by
    (rpt gen_tac >> Cases_on `off = 0` >> Cases_on `p` >>
     simp[compile_lit_byte_offset_def] >> admin_actions []) >>
  pop_assum (fn th => Induct >> simp[compile_imm_copy_to_memory_def] >>
      admin_actions [th, admin_ptr_actions])
QED

Theorem admin_ensure_action[local,simp]:
  code_action ^admin_op (compile_ensure_in_memory src loc bytes n ctor imm)
Proof
  Cases_on `loc` >> Cases_on `n = 1` >>
  simp[compile_ensure_in_memory_def, compile_alloc_buffer_def,
       compile_storage_to_memory_def, compile_transient_to_memory_def,
       compile_slot_to_memory_def, compile_word_copy_loop_def,
       compile_word_copy_loop_op_def, comp_ignore_bind_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  admin_actions [admin_ptr_actions, admin_word_copy_action, admin_imm_copy_action,
                 code_action_alloc_buffer]
QED

Theorem admin_unwrap_code_action:
  code_action ^admin_op (unwrap_value ce vv)
Proof
  Cases_on `vv` >> simp[unwrap_value_def, code_action_return, admin_ptr_actions] >>
  rename1 `is_word_type ty` >> Cases_on `is_word_type ty` >> simp[admin_ptr_actions] >>
  Cases_on `p.ptr_location` >>
  simp[code_action_return, admin_ensure_action]
QED

Theorem admin_store_code_action:
  code_action ^admin_op (compile_store_memory ce src dst dt st)
Proof
  `!ce dst dt src st. code_action ^admin_op (compile_store_memory_typed ce dst dt src st)` by
    (qspec_then `^admin_op` mp_tac typed_copy_code_family >> simp[]) >>
  `!n. code_action ^admin_op (compile_copy_memory dst src n)` by
    (Cases >> simp[compile_copy_memory_def, code_action_return, code_action_emit_void]) >>
  `code_action ^admin_op (compile_store_bytestring src dst)` by
    (simp[compile_store_bytestring_def, compile_bytestring_copy_len_def] >> admin_actions []) >>
  simp[compile_store_memory_def] >> rpt IF_CASES_TAC >>
  simp[code_action_emit_void]
QED

Theorem pos_snapshot_code_action[local]:
  code_action ^admin_op (compile_snapshot_vv ce copy input)
Proof
  `!ty. code_action ^admin_op (compile_materialize_vv ce ty input)` by
    (simp[compile_materialize_vv_def] >>
     admin_actions [code_action_alloc_buffer, admin_unwrap_code_action, admin_store_code_action]) >>
  rw[compile_snapshot_vv_def, code_action_return] >>
  irule code_action_bind >> simp[code_action_return, admin_unwrap_code_action]
QED

Theorem pos_snapshot_opcode_inventory:
  compile_snapshot_vv ce copy input a = (saved,b) ==>
  EVERY (\i. ~MEM i.inst_opcode [GAS; CREATE; CREATE2; INVOKE]) (frag_code a b)
Proof
  strip_tac >>
  drule (REWRITE_RULE [code_action_def] pos_snapshot_code_action) >>
  simp[code_step_def]
QED
