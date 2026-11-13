Theory runtimeSymSrcSystemCreate
Ancestors
  runtimeSymSrcContext runtimeSymSrcContextTypedBase runtimeSymSrcEmission
  runtimeSymSrcInterfaces
  builtinSystem builtinCreate builtinSimple compileEnv emitHelper
  loweringShapeDefs venomInst list stackPlanTypes

(* Equation-first versions support forward composition in emission order. *)
Theorem runtime_sym_sc_op[local]:
  emit_op opc ops s = (v,s') ==>
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  metis_tac[runtime_sym_emit_op]
QED

Theorem runtime_sym_sc_void[local]:
  emit_void opc ops s = (u,s') ==>
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  metis_tac[runtime_sym_emit_void]
QED

Theorem runtime_sym_sc_inst[local]:
  emit_inst opc ops outs s = (u,s') ==>
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `u` >> rpt strip_tac >> irule runtime_sym_emit_inst >>
  qexistsl [`s.cs_next_id`, `opc`, `ops`, `outs`, `s`] >>
  simp[runtime_sym_ordinary_inst]
QED

Theorem runtime_sym_sc_alloc[local]:
  compile_alloc_buffer n s = (b,s') ==>
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand b.buf_operand
Proof
  metis_tac[runtime_sym_alloc_buffer]
QED

Theorem runtime_sym_select:
  ~is_label_operand c /\ ~is_label_operand a /\ ~is_label_operand b /\
  EVERY runtime_sym_inst (state_insts s) /\ compile_select c a b s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_select_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  ntac 3 (rev_dxrule runtime_sym_sc_op >> simp[] >> strip_tac) >> simp[]
QED

Theorem runtime_sym_send:
  ~is_label_operand to_op /\ ~is_label_operand value /\ ~is_label_operand gas /\
  EVERY runtime_sym_inst (state_insts s) /\ compile_send to_op value gas s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_send_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rev_dxrule runtime_sym_sc_op >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_sc_void >> simp[]
QED

Theorem runtime_sym_raw_revert:
  ~is_label_operand p_op /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_raw_revert p_op s = (u,s') ==> EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_raw_revert_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  ntac 2 (rev_dxrule runtime_sym_sc_op >> simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_sc_inst >> simp[]
QED

Theorem runtime_sym_selfdestruct:
  ~is_label_operand to_op /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_selfdestruct to_op s = (u,s') ==> EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_selfdestruct_def] >> strip_tac >>
  rev_dxrule runtime_sym_sc_void >> simp[]
QED

Theorem runtime_sym_msg_data_to_memory:
  EVERY runtime_sym_inst (state_insts s) /\
  compile_msg_data_to_memory s = ((p_op,len),s') ==>
  EVERY runtime_sym_inst (state_insts s') /\
  ~is_label_operand p_op /\ ~is_label_operand len
Proof
  simp[compile_msg_data_to_memory_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >> gvs[comp_return_def] >>
  rev_dxrule runtime_sym_sc_op >> simp[] >> strip_tac >>
  drule_all runtime_sym_alloc_dynamic >> strip_tac >>
  rev_dxrule runtime_sym_sc_void >> simp[is_label_operand_def]
QED

Theorem runtime_sym_raw_call_outbuf:
  EVERY runtime_sym_inst (state_insts s) /\
  compile_raw_call_outbuf n s = ((v,p),s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v /\ ~is_label_operand p
Proof
  Cases_on `n > 0` >>
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >> gvs[comp_return_def] >>
  rev_dxrule runtime_sym_sc_alloc >> strip_tac >> simp[] >>
  rev_dxrule runtime_sym_sc_op >> simp[is_label_operand_def]
QED

Theorem runtime_sym_sc_block[local]:
  new_block l s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[new_block_def, state_insts_def, all_blocks_def, MAP_APPEND,
       FLAT_APPEND, EVERY_APPEND] >> rpt strip_tac >> gvs[]
QED

Theorem runtime_sym_check_create_result:
  ~is_label_operand result /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_check_create_result result revert_flag s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `revert_flag` >>
  simp[compile_check_create_result_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >>
  gvs[comp_return_def] >>
  imp_res_tac runtime_sym_fresh_label >> gvs[] >>
  drule_at (Pat `emit_inst JNZ _ _ _ = _`) runtime_sym_jnz >>
  simp[] >> strip_tac >>
  rev_dxrule runtime_sym_sc_block >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_sc_op >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_sc_alloc >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_sc_void >> simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_inst REVERT _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_sc_inst) >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_sc_block >> simp[]
QED

Theorem runtime_sym_create_dispatch:
  ~is_label_operand p_op /\ ~is_label_operand len /\ ~is_label_operand value /\
  (!op. salt = SOME op ==> ~is_label_operand op) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_create_dispatch p_op len value salt revert_flag s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `salt` >> simp[compile_create_dispatch_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rev_dxrule runtime_sym_sc_op >> simp[] >> strip_tac >>
  drule_all runtime_sym_check_create_result >> simp[]
QED

Theorem runtime_sym_create_proxy_buf:
  ~is_label_operand target /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_create_proxy_buf target s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_create_proxy_buf_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >>
  gvs[comp_return_def] >>
  rev_dxrule runtime_sym_sc_alloc >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_sc_void >> simp[is_label_operand_def] >> strip_tac >>
  ntac 2 (rev_dxrule runtime_sym_sc_op >> simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_sc_void >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_sc_op >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_sc_void >> simp[is_label_operand_def]
QED

Theorem runtime_sym_create_proxy:
  ~is_label_operand target /\ ~is_label_operand value /\
  (!op. salt = SOME op ==> ~is_label_operand op) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_create_proxy target value salt revert_flag s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_create_proxy_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule_all runtime_sym_create_proxy_buf >> strip_tac >>
  drule_at (Pat `compile_create_dispatch _ _ _ _ _ _ = _`)
    runtime_sym_create_dispatch >> simp[is_label_operand_def]
QED

Theorem runtime_sym_create_copy:
  ~is_label_operand target /\ ~is_label_operand value /\
  (!op. salt = SOME op ==> ~is_label_operand op) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_create_copy target value salt revert_flag s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `salt` >>
  simp[compile_create_copy_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rev_dxrule runtime_sym_sc_op >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_sc_void >> simp[] >> strip_tac >>
  ntac 3 (rev_dxrule runtime_sym_sc_op >> simp[is_label_operand_def] >> strip_tac) >>
  drule_all runtime_sym_alloc_dynamic >> strip_tac >>
  rev_dxrule runtime_sym_sc_void >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_sc_op >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_sc_void >> simp[is_label_operand_def] >> strip_tac >>
  ntac 3 (rev_dxrule runtime_sym_sc_op >> simp[is_label_operand_def] >> strip_tac) >>
  drule_all runtime_sym_check_create_result >> simp[]
QED

Theorem runtime_sym_create_blueprint_check:
  ~is_label_operand target /\ ~is_label_operand off /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_create_blueprint_check target off s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_create_blueprint_check_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >>
  gvs[comp_return_def] >>
  ntac 3 (rev_dxrule runtime_sym_sc_op >> simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_sc_void >> simp[]
QED

(* Memory copy safety is supplied by the integrated context boundary. *)
Theorem runtime_sym_create_blueprint_append:
  ~is_label_operand target /\ ~is_label_operand value /\
  ~is_label_operand off /\ ~is_label_operand sz /\
  ~is_label_operand args /\ ~is_label_operand len /\
  (!op. salt = SOME op ==> ~is_label_operand op) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_create_blueprint_append target value salt off sz args len revert_flag s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  strip_tac >>
  qpat_x_assum `compile_create_blueprint_append _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_create_blueprint_append_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >>
  rev_dxrule runtime_sym_sc_op >> simp[] >> strip_tac >>
  pairarg_tac >> simp[] >>
  drule_all runtime_sym_alloc_dynamic >> strip_tac >>
  pairarg_tac >> simp[] >>
  rev_dxrule runtime_sym_sc_void >> simp[] >> strip_tac >>
  Cases_on `len = Lit 0w` >> simp[comp_return_def]
  >- (Cases_on `salt` >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
      rev_dxrule runtime_sym_sc_op >> simp[] >> strip_tac >>
      drule_all runtime_sym_check_create_result >> simp[]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_sc_op >> simp[] >> strip_tac >>
  drule_all runtime_sym_copy_memory_dynamic >> strip_tac >>
  Cases_on `salt` >> gvs[] >>
  rev_dxrule runtime_sym_sc_op >> simp[] >> strip_tac >>
  drule_all runtime_sym_check_create_result >> simp[]
QED

Theorem runtime_sym_create_blueprint:
  ~is_label_operand target /\ ~is_label_operand value /\ ~is_label_operand off /\
  (!op. salt = SOME op ==> ~is_label_operand op) /\
  (!p n. args_info = SOME (p,n) ==> ~is_label_operand p /\ ~is_label_operand n) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_create_blueprint target value salt off args_info revert_flag s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `args_info` >>
  simp[compile_create_blueprint_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac
  >- (drule_all runtime_sym_create_blueprint_check >> strip_tac >>
      drule_at (Pat `compile_create_blueprint_append _ _ _ _ _ _ _ _ _ = _`)
        runtime_sym_create_blueprint_append >> simp[is_label_operand_def]) >>
  PairCases_on `x` >> gvs[] >>
  drule_all runtime_sym_create_blueprint_check >> strip_tac >>
  drule_at (Pat `compile_create_blueprint_append _ _ _ _ _ _ _ _ _ = _`)
    runtime_sym_create_blueprint_append >> simp[]
QED

Theorem runtime_sym_raw_call_finish:
  ~is_label_operand to_op /\ ~is_label_operand data_ptr /\
  ~is_label_operand data_len /\ ~is_label_operand gas_op /\
  ~is_label_operand value_op /\ ~is_label_operand out_val /\
  ~is_label_operand out_ptr /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_raw_call_finish to_op data_ptr data_len gas_op value_op
    call_ty max_outsize revert_on_failure out_val out_ptr s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  strip_tac >>
  qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_raw_call_finish_def, comp_bind_def] >>
  pairarg_tac >> simp[] >>
  `EVERY runtime_sym_inst (state_insts cs') /\ ~is_label_operand success` by
    (Cases_on `call_ty` >> gvs[] >> rev_dxrule runtime_sym_sc_op >>
     simp[is_label_operand_def]) >>
  reverse (Cases_on `revert_on_failure`) >> simp[comp_bind_def, comp_ignore_bind_def]
  >- (Cases_on `max_outsize > 0` >> simp[comp_return_def, comp_bind_def, comp_ignore_bind_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[comp_return_def] >>
      rev_dxrule runtime_sym_sc_op >> simp[] >> strip_tac >>
      rev_dxrule runtime_sym_sc_op >> simp[is_label_operand_def] >> strip_tac >>
      drule_at (Pat `compile_select _ _ _ _ = _`) runtime_sym_select >>
      simp[is_label_operand_def] >> strip_tac >>
      rev_dxrule runtime_sym_sc_void >> simp[] >> strip_tac >>
      rev_dxrule runtime_sym_sc_alloc >> strip_tac >>
      rev_dxrule runtime_sym_sc_void >> simp[] >> strip_tac >>
      rev_dxrule runtime_sym_sc_op >> simp[is_label_operand_def] >> strip_tac >>
      rev_dxrule runtime_sym_sc_void >> simp[is_label_operand_def]) >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  imp_res_tac runtime_sym_fresh_label >> gvs[] >>
  drule_at (Pat `emit_inst JNZ _ _ _ = _`) runtime_sym_jnz >>
  simp[] >> strip_tac >>
  rev_dxrule runtime_sym_sc_block >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_sc_op >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_sc_alloc >> strip_tac >>
  rev_dxrule runtime_sym_sc_void >> simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_inst REVERT _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_sc_inst) >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_sc_block >> simp[] >> strip_tac >>
  Cases_on `max_outsize > 0` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, is_label_operand_def] >>
  qpat_x_assum `(\(a,b). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rev_dxrule runtime_sym_sc_op >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_sc_op >> simp[is_label_operand_def] >> strip_tac >>
  drule_at (Pat `compile_select _ _ _ _ = _`) runtime_sym_select >>
  simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_sc_void >> simp[]
QED
