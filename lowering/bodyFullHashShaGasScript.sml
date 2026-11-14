(* The only gas instruction in either generated SHA suffix. *)
Theory bodyFullHashShaGas
Ancestors
  builtinHashing context emitHelper compileEnv exprLoweringProps
  venomInst list rich_list arithmetic
  exprSimHash gasExplicitSites gasShadowState gasShadowUnit
  gasShadowUnitObservations pred_set

Theorem sha_fixed_gas_emitted:
  compile_sha256_bytesm value m sa = (op,sb) ==>
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) =
    [mk_inst (sa.cs_next_id+3) GAS []
      [STRING #"%" (toString (sa.cs_next_var+2))]]
Proof
  simp[compile_sha256_bytesm_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, DROP_LENGTH_APPEND,
    APPEND_ASSOC, mk_inst_def]
QED

Theorem sha_fixed_gas_classified:
  compile_sha256_bytesm value m sa = (op,sb) /\
  compile_sha256_bytesm value m shadow_sa = (shadow_op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function fn shadow_fn /\
  MEM fn ctx.ctx_functions /\ MEM shadow_fn shadow_ctx.ctx_functions /\
  fn_has_code sa sb fn /\ fn_has_code shadow_sa shadow_sb shadow_fn ==>
  MAP (\i. (fn.fn_name,i.inst_id) IN gas_explicit_sites ctx shadow_ctx)
    (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = [F]
Proof
  strip_tac >>
  `sa.cs_next_id = shadow_sa.cs_next_id /\
   sa.cs_next_var = shadow_sa.cs_next_var` by fs[gas_shadow_state_def] >>
  qabbrev_tac `i = mk_inst (sa.cs_next_id+3) GAS []
    [STRING #"%" (toString (sa.cs_next_var+2))]` >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = [i] /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts shadow_sa shadow_sb) = [i]` by
    metis_tac[sha_fixed_gas_emitted] >>
  `MEM i (fn_insts fn) /\ MEM i (fn_insts shadow_fn)` by
    (conj_tac >> irule hash_emitted_inst_mem >> goal_assum (drule_at Any) >>
     metis_tac[MEM_FILTER, MEM]) >>
  `gas_shadow_inst i i /\ i.inst_opcode = GAS` by
    simp[Abbr `i`, gas_shadow_inst_def, mk_inst_def] >>
  drule_all gas_explicit_sites_classify >> simp[Abbr `i`, mk_inst_def]
QED

Theorem sha_bytes_gas_emitted:
  compile_sha256_bytes value sa = (op,sb) ==>
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) =
    [mk_inst (sa.cs_next_id+3) GAS []
      [STRING #"%" (toString (sa.cs_next_var+3))]]
Proof
  simp[compile_sha256_bytes_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, DROP_LENGTH_APPEND,
    APPEND_ASSOC, mk_inst_def]
QED

Theorem sha_bytes_gas_classified:
  compile_sha256_bytes value sa = (op,sb) /\
  compile_sha256_bytes value shadow_sa = (shadow_op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function fn shadow_fn /\
  MEM fn ctx.ctx_functions /\ MEM shadow_fn shadow_ctx.ctx_functions /\
  fn_has_code sa sb fn /\ fn_has_code shadow_sa shadow_sb shadow_fn ==>
  MAP (\i. (fn.fn_name,i.inst_id) IN gas_explicit_sites ctx shadow_ctx)
    (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = [F]
Proof
  strip_tac >>
  `sa.cs_next_id = shadow_sa.cs_next_id /\
   sa.cs_next_var = shadow_sa.cs_next_var` by fs[gas_shadow_state_def] >>
  qabbrev_tac `i = mk_inst (sa.cs_next_id+3) GAS []
    [STRING #"%" (toString (sa.cs_next_var+3))]` >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = [i] /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts shadow_sa shadow_sb) = [i]` by
    metis_tac[sha_bytes_gas_emitted] >>
  `MEM i (fn_insts fn) /\ MEM i (fn_insts shadow_fn)` by
    (conj_tac >> irule hash_emitted_inst_mem >> goal_assum (drule_at Any) >>
     metis_tac[MEM_FILTER, MEM]) >>
  `gas_shadow_inst i i /\ i.inst_opcode = GAS` by
    simp[Abbr `i`, gas_shadow_inst_def, mk_inst_def] >>
  drule_all gas_explicit_sites_classify >> simp[Abbr `i`, mk_inst_def]
QED
