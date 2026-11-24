(* The post-VV administrative interval of one buffered internal argument. *)
Theory entryIntCallStageBuffer
Ancestors
  entryCreateEffectFocus entryCreatePathScope entryCreateAdminSequence
  createSizeCutCode createSizeCutOpens createSizeLocationCode createSizeTypedCopyCode
  typedCopyGasOps exprSimAbiEncodeObliviousCode exprSimAbiGasBridge
  exprLowering compileEnv context emitHelper venomInst fragExec list pair

val buffer_safe = ``\opc. opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2``;

fun buffer_actions ths =
  let val rules = ths @ [LET_THM, code_action_return, code_action_emit_inst,
       code_action_emit_op, code_action_emit_void, code_action_new_block,
       code_action_fresh_var, code_action_fresh_label]
  in rpt (FIRST [CHANGED_TAC (simp rules), irule code_action_bind,
                  irule code_action_ignore_bind, conj_tac, gen_tac])
  end;

Theorem buffer_ptr_actions[local,simp]:
  code_action ^buffer_safe (compile_ptr_load ctor imm loc p) /\
  code_action ^buffer_safe (compile_ptr_store ctor imm loc p v) /\
  code_action ^buffer_safe (compile_imm_load_word ctor imm p)
Proof
  Cases_on `loc` >> Cases_on `imm` >>
  simp[compile_ptr_load_def, compile_ptr_store_def, compile_imm_load_word_def,
       compile_imm_store_word_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >> rpt conj_tac >> buffer_actions []
QED

Theorem buffer_word_copy_action[local,simp]:
  code_action ^buffer_safe (compile_word_copy_loop_base src dst n ll sl ctor imm)
Proof
  Cases_on `word_scale ll = 1` >> Cases_on `word_scale sl = 1` >>
  simp[compile_word_copy_loop_base_def, comp_ignore_bind_def] >> buffer_actions [buffer_ptr_actions]
QED

Theorem buffer_imm_copy_action[local,simp]:
  !n off. code_action ^buffer_safe (compile_imm_copy_to_memory ctor imm src dst n off)
Proof
  `!p off. code_action ^buffer_safe (compile_lit_byte_offset p off)` by
    (rpt gen_tac >> Cases_on `off = 0` >> Cases_on `p` >>
     simp[compile_lit_byte_offset_def] >> buffer_actions []) >>
  pop_assum (fn th => Induct >> simp[compile_imm_copy_to_memory_def] >>
      buffer_actions [th, buffer_ptr_actions])
QED

Theorem buffer_ensure_action[local,simp]:
  code_action ^buffer_safe (compile_ensure_in_memory src loc bytes n ctor imm)
Proof
  Cases_on `loc` >> Cases_on `n = 1` >>
  simp[compile_ensure_in_memory_def, compile_alloc_buffer_def,
       compile_storage_to_memory_def, compile_transient_to_memory_def,
       compile_slot_to_memory_def, compile_word_copy_loop_def,
       compile_word_copy_loop_op_def, comp_ignore_bind_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  buffer_actions [buffer_ptr_actions, buffer_word_copy_action, buffer_imm_copy_action,
                  code_action_alloc_buffer]
QED

Theorem buffer_unwrap_action:
  code_action ^buffer_safe (unwrap_value ce vv)
Proof
  Cases_on `vv` >> simp[unwrap_value_def, code_action_return, buffer_ptr_actions] >>
  rename1 `is_word_type ty` >> Cases_on `is_word_type ty` >> simp[buffer_ptr_actions] >>
  Cases_on `p.ptr_location` >>
  simp[code_action_return, buffer_ensure_action]
QED

Theorem buffer_store_action:
  code_action ^buffer_safe (compile_store_memory ce src dst dt st)
Proof
  `!ce dst dt src st. code_action ^buffer_safe (compile_store_memory_typed ce dst dt src st)` by
    (qspec_then `^buffer_safe` mp_tac typed_copy_code_family >> simp[]) >>
  `!n. code_action ^buffer_safe (compile_copy_memory dst src n)` by
    (Cases >> simp[compile_copy_memory_def, code_action_return, code_action_emit_void]) >>
  `code_action ^buffer_safe (compile_store_bytestring src dst)` by
    (simp[compile_store_bytestring_def, compile_bytestring_copy_len_def] >> buffer_actions [buffer_ptr_actions]) >>
  simp[compile_store_memory_def] >> rpt IF_CASES_TAC >>
  simp[code_action_emit_void]
QED

(* These actions are also used after a saved external-call argument. *)
Theorem saved_value_admin_actions:
  code_action ^buffer_safe (unwrap_value ce vv) /\
  code_action ^buffer_safe (compile_store_memory ce src dst dt st)
Proof
  simp[buffer_unwrap_action, buffer_store_action]
QED

Theorem intcall_stage_buffer_admin_safe:
  compile_alloc_buffer n a = (buf,b) /\
  unwrap_value ce vv b = (op,c) /\
  compile_store_memory ce op buf.buf_operand dt (vv_type vv) c = ((),d) /\
  fn_has_code a d fn /\ body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions ==>
  create_operand_cut a d explicit ctx fn tops cx st0 source (es,s)
Proof
  strip_tac >>
  `create_cut_code {} a d` by
    (irule create_cut_code_join >> qexists_tac `b` >> conj_tac
     >- metis_tac[create_alloc_buffer_cut_code, SND] >>
     irule create_cut_code_join >> qexists_tac `c` >>
     metis_tac[create_unwrap_cut_code, create_store_memory_cut_code, SND]) >>
  `code_step ^buffer_safe a b` by
    (qpat_assum `compile_alloc_buffer _ _ = _`
       (mp_then (Pat `compile_alloc_buffer _ _ = _`) irule
         (REWRITE_RULE [code_action_def] (Q.SPECL [`^buffer_safe`, `n`] code_action_alloc_buffer))) >> simp[]) >>
  `code_step ^buffer_safe b c` by
    (irule (REWRITE_RULE [code_action_def] buffer_unwrap_action) >> metis_tac[]) >>
  `code_step ^buffer_safe c d` by
    (irule (REWRITE_RULE [code_action_def] buffer_store_action) >> metis_tac[]) >>
  `code_step ^buffer_safe a d` by
    (irule code_step_trans >> qexists_tac `b` >> simp[] >>
     irule code_step_trans >> qexists_tac `c` >> simp[]) >>
  irule create_effect_suffix_cut >> fs[code_step_def] >> metis_tac[]
QED
