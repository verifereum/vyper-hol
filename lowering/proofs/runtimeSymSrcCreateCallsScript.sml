Theory runtimeSymSrcCreateCalls
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission runtimeSymSrcInterfaces
  runtimeSymSrcCallStaging runtimeSymSrcAbiEncode
  runtimeSymSrcContext runtimeSymSrcContextTypedBase
  runtimeSymSrcBlockEmission runtimeSymSrcSimpleCalls runtimeSymSrcOpenValues
  runtimeSymSrcContextComplete runtimeSymSrcContextCopy
  builtinCreate context loweringShapeDefs exprLowering compileEnv emitHelper list
  stackPlanTypes supportedExprs supportedExprTraverse venomInst exprOracleStorageInterfaces rich_list

fun create_emit_tac pat lemma =
  qpat_assum pat (mp_then Any mp_tac lemma) >>
  simp[is_label_operand_def] >> strip_tac;

Theorem runtime_sym_create_result[local]:
  ~is_label_operand result /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_check_create_result result rof s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `rof` >> simp[compile_check_create_result_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  qpat_assum `fresh_label "create_fail" _ = _`
    (mp_then Any strip_assume_tac runtime_sym_fresh_label) >>
  qpat_assum `fresh_label "create_ok" _ = _`
    (mp_then Any strip_assume_tac runtime_sym_fresh_label) >>
  create_emit_tac `emit_inst JNZ _ _ _ = _` runtime_sym_jnz >>
  imp_res_tac runtime_sym_new_block_result >>
  create_emit_tac `emit_op RETURNDATASIZE _ _ = _` runtime_sym_emit_op >>
  create_emit_tac `compile_alloc_buffer _ _ = _` runtime_sym_alloc_buffer >>
  create_emit_tac `emit_void RETURNDATACOPY _ _ = _` runtime_sym_emit_void >>
  qpat_assum `emit_inst REVERT _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_inst) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[runtime_sym_inst_def, mk_inst_def, runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_create_dispatch[local]:
  ~is_label_operand code_ptr /\ ~is_label_operand len /\ ~is_label_operand value /\
  (!op. salt = SOME op ==> ~is_label_operand op) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_create_dispatch code_ptr len value salt rof s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `salt` >> simp[compile_create_dispatch_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  create_emit_tac `emit_op _ _ _ = _` runtime_sym_emit_op >>
  qpat_assum `compile_check_create_result _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_create_result) >> simp[]
QED

Theorem runtime_sym_create_proxy_buf[local]:
  ~is_label_operand target /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_create_proxy_buf target s = (buf,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand buf
Proof
  simp[compile_create_proxy_buf_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  create_emit_tac `compile_alloc_buffer _ _ = _` runtime_sym_alloc_buffer >>
  qpat_x_assum `emit_void MSTORE [buf_alloc.buf_operand;Lit _] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >>
  simp[is_label_operand_def] >> strip_tac >>
  create_emit_tac `emit_op SHL _ _ = _` runtime_sym_emit_op >>
  create_emit_tac `emit_op ADD [_;Lit 19w] _ = _` runtime_sym_emit_op >>
  create_emit_tac `emit_void MSTORE [buf_preamble;_] _ = _` runtime_sym_emit_void >>
  create_emit_tac `emit_op ADD [_;Lit 39w] _ = _` runtime_sym_emit_op >>
  qpat_assum `emit_void MSTORE _ _ = _` (mp_then Any mp_tac runtime_sym_emit_void) >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_create_copy[local]:
  ~is_label_operand target /\ ~is_label_operand value /\
  (!op. salt = SOME op ==> ~is_label_operand op) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_create_copy target value salt rof s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `salt` >>
  simp[compile_create_copy_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  create_emit_tac `emit_op EXTCODESIZE _ _ = _` runtime_sym_emit_op >>
  create_emit_tac `emit_void ASSERT _ _ = _` runtime_sym_emit_void >>
  create_emit_tac `emit_op SHL _ _ = _` runtime_sym_emit_op >>
  create_emit_tac `emit_op OR _ _ = _` runtime_sym_emit_op >>
  create_emit_tac `emit_op ADD [code_size;Lit 32w] _ = _` runtime_sym_emit_op >>
  create_emit_tac `compile_alloc_dynamic _ _ = _` runtime_sym_alloc_dynamic >>
  create_emit_tac `emit_void MSTORE _ _ = _` runtime_sym_emit_void >>
  create_emit_tac `emit_op ADD [mem_ofst;Lit 32w] _ = _` runtime_sym_emit_op >>
  create_emit_tac `emit_void EXTCODECOPY _ _ = _` runtime_sym_emit_void >>
  create_emit_tac `emit_op ADD [mem_ofst;Lit 21w] _ = _` runtime_sym_emit_op >>
  create_emit_tac `emit_op ADD [code_size;Lit 11w] _ = _` runtime_sym_emit_op >>
  create_emit_tac `emit_op _ (_::_::_::_) _ = (result,_)` runtime_sym_emit_op >>
  qpat_assum `compile_check_create_result _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_create_result) >> simp[]
QED

Theorem runtime_sym_create_blueprint_check[local]:
  ~is_label_operand target /\ ~is_label_operand code_offset /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_create_blueprint_check lit target code_offset s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `lit` >>
  simp[compile_create_blueprint_check_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  create_emit_tac `emit_op EXTCODESIZE _ _ = _` runtime_sym_emit_op >>
  TRY (create_emit_tac `emit_op GT _ _ = _` runtime_sym_emit_op) >>
  create_emit_tac `emit_op SUB _ _ = _` runtime_sym_emit_op >>
  TRY (create_emit_tac `emit_op SGT _ _ = _` runtime_sym_emit_op) >>
  qpat_assum `emit_void ASSERT _ _ = _` (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]
QED

Theorem runtime_sym_create_salt[local]:
  (!e t s op s'. salt = SOME e /\ EVERY runtime_sym_inst (state_insts s) /\
    lower_value cfn ce t e s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_create_salt cfn ce salt s = (out,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ (!op. out = SOME op ==> ~is_label_operand op)
Proof
  Cases_on `salt` >> simp[compile_create_salt_def, comp_return_def, comp_bind_def]
  >- (strip_tac >> gvs[]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >> simp[]
QED

Theorem runtime_sym_create_ctor_args[local]:
  !args s vs s'.
    (!e t. MEM e args ==> runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env tops ce /\ EVERY (supported_pure_expr tops) args /\
    ~supported_exprs_exists is_self_code args /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_create_ctor_args cfn ce args s = (vs,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ EVERY runtime_sym_value vs /\
    LENGTH vs = LENGTH args
Proof
  Induct >> simp[Once compile_create_ctor_args_def, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `cfn ce (expr_type e) e s = _` >>
  `runtime_sym_expr_contract tops cfn ce (expr_type e) e` by metis_tac[] >>
  fs[supported_expr_exists_def] >>
  qpat_x_assum `runtime_sym_expr_contract _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[runtime_sym_expr_contract_def] >>
  disch_then (drule_at (Pat `cfn _ _ _ _ = _`)) >>
  simp[] >> (impl_tac >- gvs[supported_expr_def]) >> strip_tac >>
  qpat_assum `compile_snapshot_vv _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_snapshot_vv) >>
  disch_then (qspec_then `tops` mp_tac) >> simp[] >> strip_tac >>
  qpat_assum `!s vs s'. _ ==> _` (drule_at (Pat `compile_create_ctor_args _ _ _ _ = _`)) >>
  gvs[]
QED

Theorem runtime_sym_create_ctor_tuple[local]:
  (!e t. MEM e args ==> runtime_sym_expr_contract tops cfn ce t e) /\
  runtime_sym_env tops ce /\ EVERY (supported_pure_expr tops) args /\
  ~supported_exprs_exists is_self_code args /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_create_ctor_tuple cfn ce args s = (p,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand p
Proof
  simp[compile_create_ctor_tuple_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  qpat_assum `compile_create_ctor_args _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_create_ctor_args) >>
  disch_then (qspec_then `tops` mp_tac) >> simp[] >> strip_tac >>
  create_emit_tac `compile_alloc_buffer _ _ = _` runtime_sym_alloc_buffer >>
  qpat_assum `compile_extcall_store_values _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_extcall_store_values) >>
  disch_then (qspec_then `tops` mp_tac) >> simp[GSYM EVERY_MAP, MAP_ZIP]
QED

Theorem runtime_sym_create_snapshot[local]:
  runtime_sym_env tops ce /\ runtime_sym_value vv /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_create_snapshot ce vv ty s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `vv_location vv` >> TRY (Cases_on `x`) >>
  simp[compile_create_snapshot_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, compile_copy_memory_dynamic_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  TRY (pairarg_tac >> simp[]) >> TRY (pairarg_tac >> simp[]) >>
  TRY (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  imp_res_tac runtime_sym_value_operand >>
  create_emit_tac `compile_alloc_buffer _ _ = _` runtime_sym_alloc_buffer
  >>~- ([`compile_slot_to_memory _ _ _ _ _ = _`],
    create_emit_tac `compile_slot_to_memory _ _ _ _ _ = _` runtime_sym_slot_to_memory)
  >>~- ([`compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`],
    qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_imm_copy_to_memory) >>
    fs[runtime_sym_env_def] >> strip_tac) >>
  simp[] >>
  create_emit_tac `emit_op MLOAD _ _ = _` runtime_sym_emit_op >>
  qpat_x_assum `_ (emit_op ADD _ _) = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  create_emit_tac `emit_op ADD _ _ = _` runtime_sym_emit_op >>
  qpat_assum `emit_void MCOPY _ _ = _` (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]
QED

Theorem runtime_sym_create_blueprint_append[local]:
  ~is_label_operand target /\ ~is_label_operand value /\ ~is_label_operand offset /\
  ~is_label_operand codsz /\ ~is_label_operand args_ptr /\ ~is_label_operand args_len /\
  (!op. salt = SOME op ==> ~is_label_operand op) /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_create_blueprint_append target value salt offset codsz args_ptr args_len rof s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `salt` >> Cases_on `args_len = Lit 0w` >>
  simp[compile_create_blueprint_append_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, compile_copy_memory_dynamic_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  TRY (pairarg_tac >> simp[]) >> TRY (pairarg_tac >> simp[]) >>
  strip_tac >> gvs[] >>
  TRY (qpat_x_assum `_ (emit_op ADD [mem_ofst;codsz] _) = _` mp_tac >>
       pairarg_tac >> simp[] >> strip_tac) >>
  create_emit_tac `emit_op ADD [codsz;_] _ = _` runtime_sym_emit_op >>
  create_emit_tac `compile_alloc_dynamic _ _ = _` runtime_sym_alloc_dynamic >>
  create_emit_tac `emit_void EXTCODECOPY _ _ = _` runtime_sym_emit_void >>
  TRY (create_emit_tac `emit_op ADD [mem_ofst;codsz] _ = _` runtime_sym_emit_op >>
       create_emit_tac `emit_void MCOPY _ _ = _` runtime_sym_emit_void) >>
  create_emit_tac `emit_op _ (_::_::_::_) _ = (result,_)` runtime_sym_emit_op >>
  qpat_assum `compile_check_create_result _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_create_result) >> simp[]
QED

Theorem runtime_sym_create_blueprint_args[local]:
  (!e t. MEM e args ==> runtime_sym_expr_contract tops cfn ce t e) /\
  runtime_sym_env tops ce /\ EVERY (supported_pure_expr tops) args /\
  ~supported_exprs_exists is_self_code args /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_create_blueprint_args cfn ce raw later args s = ((p,n),s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand p /\ ~is_label_operand n
Proof
  Cases_on `raw` >>
  namedCases_on `args` ["", "arg tail_args"] >>
  TRY (Cases_on `tail_args`) >>
  simp[compile_create_blueprint_args_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[is_label_operand_def] >>
  TRY (drule_all runtime_sym_call_invalid >> simp[]) >>
  TRY (qpat_assum `compile_create_ctor_tuple _ _ _ _ = _`
     (mp_then Any mp_tac runtime_sym_create_ctor_tuple) >>
   disch_then (qspec_then `tops` mp_tac) >> simp[] >>
   (TRY (impl_tac >- first_assum ACCEPT_TAC)) >> strip_tac >>
   create_emit_tac `compile_alloc_buffer _ _ = _` runtime_sym_alloc_buffer >>
   qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _`
     (mp_then Any mp_tac runtime_sym_abi_encode_to_buf) >> simp[]) >>
  `runtime_sym_expr_contract tops cfn ce (expr_type arg) arg` by metis_tac[] >>
  fs[supported_expr_exists_def] >>
  qpat_x_assum `runtime_sym_expr_contract _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[runtime_sym_expr_contract_def] >>
  disch_then (drule_at (Pat `cfn _ _ _ _ = _`)) >>
  simp[] >> (impl_tac >- gvs[supported_expr_def]) >> strip_tac >>
  qpat_assum `compile_snapshot_vv _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_snapshot_vv) >>
  disch_then (qspec_then `tops` mp_tac) >> simp[] >> strip_tac >>
  drule_all runtime_sym_unwrap_value >> strip_tac >>
  create_emit_tac `emit_op MLOAD _ _ = _` runtime_sym_emit_op >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_raw_create[local]:
  (!e t. MEM e args ==> runtime_sym_expr_contract tops cfn ce t e) /\
  runtime_sym_env tops ce /\ EVERY (supported_pure_expr tops) args /\
  ~supported_exprs_exists is_self_code args /\
  MEM bytecode args /\ MEM value args /\
  (!e. MEM e ctor_args ==> MEM e args) /\
  (!e. salt = SOME e ==> MEM e args) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_raw_create cfn ce bytecode value ctor_args salt rof s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  strip_tac >>
  `runtime_sym_lower_value_clause tops` by
    (irule runtime_sym_lower_value >> metis_tac[runtime_sym_unwrap_value]) >>
  `!e t st op st'. MEM e args /\ EVERY runtime_sym_inst (state_insts st) /\
      lower_value cfn ce t e st = (op,st') ==>
      EVERY runtime_sym_inst (state_insts st') /\ ~is_label_operand op` by
    (mp_tac (Q.INST [`args` |-> `args`] runtime_sym_call_lower_argument) >>
     simp[] >> metis_tac[]) >>
  `supported_expr tops bytecode` by metis_tac[runtime_sym_supported_argument] >>
  `~supported_expr_exists is_self_code bytecode` by
    fs[supported_exprs_exists_not_every, EVERY_MEM] >>
  `EVERY (supported_pure_expr tops) ctor_args /\
    ~supported_exprs_exists is_self_code ctor_args` by
    (fs[EVERY_MEM, supported_exprs_exists_not_every] >> metis_tac[]) >>
  qpat_x_assum `compile_raw_create _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `ctor_args = []` >>
  simp[compile_raw_create_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, compile_copy_memory_dynamic_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[comp_bind_def, comp_ignore_bind_def] >>
  TRY (qpat_x_assum `_ (compile_create_ctor_tuple _ _ _ _) = _` mp_tac >>
       pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
       pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
       pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
       strip_tac >> gvs[]) >>
  TRY (qpat_x_assum `_ (lower_value _ _ _ value _) = _` mp_tac >>
       pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac) >>
  `runtime_sym_expr_contract tops cfn ce (expr_type bytecode) bytecode` by metis_tac[] >>
  qpat_x_assum `runtime_sym_expr_contract _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[runtime_sym_expr_contract_def] >>
  disch_then (drule_at (Pat `cfn _ _ _ _ = _`)) >> simp[] >> strip_tac >>
  qpat_assum `compile_create_snapshot _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_create_snapshot) >>
  disch_then (qspec_then `tops` mp_tac) >> simp[] >> strip_tac >>
  create_emit_tac `emit_op MLOAD _ _ = _` runtime_sym_emit_op >>
  create_emit_tac `emit_op ADD [_;Lit 32w] _ = _` runtime_sym_emit_op >>
  TRY (qpat_assum `compile_create_ctor_tuple _ _ _ _ = _`
       (mp_then Any mp_tac runtime_sym_create_ctor_tuple) >>
    disch_then (qspec_then `tops` mp_tac) >> simp[] >>
    (TRY (impl_tac >- metis_tac[])) >> strip_tac >>
    create_emit_tac `compile_alloc_buffer _ _ = _` runtime_sym_alloc_buffer >>
    create_emit_tac `emit_void MCOPY _ _ = _` runtime_sym_emit_void >>
    create_emit_tac `emit_op ADD [buf.buf_operand;len] _ = _` runtime_sym_emit_op >>
    create_emit_tac `compile_abi_encode_to_buf _ _ _ _ = _` runtime_sym_abi_encode_to_buf >>
    create_emit_tac `emit_op ADD [len;args_len] _ = _` runtime_sym_emit_op) >>
  qpat_assum `!e t st op st'. _ ==> _`
    (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >> simp[] >> strip_tac >>
  qpat_assum `compile_create_salt _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_create_salt) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  qpat_assum `compile_create_dispatch _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_create_dispatch) >> simp[]
QED

Theorem runtime_sym_create_blueprint_offset[local]:
  (!t s op s'. EVERY runtime_sym_inst (state_insts s) /\
     lower_value cfn ce t e s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  EVERY runtime_sym_inst (state_insts s) /\
  (case origin_fold_value e of Literal _ (IntL i) => comp_return (Lit (i2w i))
    | _ => lower_value cfn ce (expr_type e) e) s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `origin_fold_value e` >> TRY (Cases_on `l`) >>
  simp[comp_return_def, is_label_operand_def] >> strip_tac >> gvs[is_label_operand_def] >>
  first_x_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >> simp[]
QED

Theorem runtime_sym_create_subset[local]:
  (!e t. MEM e args ==> runtime_sym_expr_contract tops cfn ce t e) /\
  EVERY (supported_pure_expr tops) args /\ ~supported_exprs_exists is_self_code args /\
  (!e. MEM e sub ==> MEM e args) ==>
  (!e t. MEM e sub ==> runtime_sym_expr_contract tops cfn ce t e) /\
  EVERY (supported_pure_expr tops) sub /\ ~supported_exprs_exists is_self_code sub
Proof
  simp[supported_exprs_exists_not_every, EVERY_MEM] >> metis_tac[]
QED

Theorem runtime_sym_create_blueprint_args_subset[local]:
  (!e t. MEM e all_args ==> runtime_sym_expr_contract tops cfn ce t e) /\
  runtime_sym_env tops ce /\ EVERY (supported_pure_expr tops) all_args /\
  ~supported_exprs_exists is_self_code all_args /\
  (!e. MEM e args ==> MEM e all_args) /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_create_blueprint_args cfn ce raw later args s = ((p,n),s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand p /\ ~is_label_operand n
Proof
  strip_tac >>
  `(!e t. MEM e args ==> runtime_sym_expr_contract tops cfn ce t e) /\
    EVERY (supported_pure_expr tops) args /\ ~supported_exprs_exists is_self_code args` by
    metis_tac[runtime_sym_create_subset] >>
  metis_tac[runtime_sym_create_blueprint_args]
QED

fun create_lower_tac pat =
  qpat_assum pat (fn step =>
    let
      val (lhs,rhs) = dest_eq (concl step)
      val (_,[_,_,ty,expr,state]) = strip_comb lhs
      val (operand,state') = pairSyntax.dest_pair rhs
    in
      qpat_assum `!e t st op st'. _ ==> _`
        (mp_tac o SPECL [expr,ty,state,operand,state']) >>
      simp[] >> (TRY (impl_tac >- metis_tac[])) >> strip_tac
    end);

Theorem runtime_sym_compile_create_call[local]:
  (!e t. MEM e all_args ==> runtime_sym_expr_contract tops cfn ce t e) /\
  runtime_sym_env tops ce /\ EVERY (supported_pure_expr tops) all_args /\
  ~supported_exprs_exists is_self_code all_args /\
  (!e. MEM e args ==> MEM e all_args) /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_create_call cfn ce ck has_salt rof args s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  strip_tac >>
  `runtime_sym_lower_value_clause tops` by
    (irule runtime_sym_lower_value >> metis_tac[runtime_sym_unwrap_value]) >>
  `!e t st op st'. MEM e all_args /\ EVERY runtime_sym_inst (state_insts st) /\
      lower_value cfn ce t e st = (op,st') ==>
      EVERY runtime_sym_inst (state_insts st') /\ ~is_label_operand op` by
    (mp_tac (Q.INST [`args` |-> `all_args`] runtime_sym_call_lower_argument) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `compile_create_call _ _ _ _ _ _ _ = _` mp_tac >>
  namedCases_on `args` ["", "target tail"] >>
  TRY (namedCases_on `tail` ["", "value rest"]) >>
  Cases_on `ck` >> Cases_on `has_salt` >>
  TRY (namedCases_on `rest` ["", "first rest_tail"]) >>
  TRY (namedCases_on `rest_tail` ["", "second more"]) >>
  simp[NoAsms, compile_create_call_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  TRY pairarg_tac >> simp[] >> TRY pairarg_tac >> simp[] >>
  TRY pairarg_tac >> simp[] >> TRY pairarg_tac >> simp[] >>
  TRY pairarg_tac >> simp[] >> TRY pairarg_tac >> simp[] >>
  TRY pairarg_tac >> simp[] >> TRY pairarg_tac >> simp[] >>
  strip_tac >> gvs[comp_bind_def, comp_ignore_bind_def] >>
  TRY (drule_all runtime_sym_call_invalid >> simp[is_label_operand_def])
  >>~- ([`compile_raw_create _ _ _ _ _ _ _ _ = _`],
    qpat_assum `compile_raw_create _ _ _ _ _ _ _ _ = _`
      (mp_then Any mp_tac (Q.INST [`args` |-> `all_args`] runtime_sym_raw_create)) >>
    disch_then (qspecl_then [`tops`, `all_args`] mp_tac) >> simp[] >>
    TRY (impl_tac >>
      TRY (rpt strip_tac >>
           qpat_assum `!e. _ ==> MEM e all_args` irule >> simp[] >>
           FIRST [qpat_assum `MEM _ (FRONT (_::_))` (mp_tac o MATCH_MP MEM_FRONT),
                  mp_tac (Q.ISPECL [`second:expr`, `more:expr list`] MEM_LAST)] >>
           simp[] >> tautLib.TAUT_TAC)) >> simp[]) >>
  create_lower_tac `lower_value _ _ _ target s = _` >>
  TRY (qpat_assum `compile_create_blueprint_args _ _ _ _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_create_blueprint_args_subset) >>
    disch_then (qspecl_then [`tops`, `all_args`] mp_tac) >> simp[] >>
    (TRY (impl_tac >- metis_tac[])) >> strip_tac) >>
  TRY (qpat_x_assum `_ (lower_value _ _ _ value _) = _` mp_tac >>
       pairarg_tac >> simp[] >> strip_tac) >>
  TRY (create_lower_tac `lower_value _ _ _ value _ = _`) >>
  TRY (create_emit_tac `compile_create_proxy_buf _ _ = _` runtime_sym_create_proxy_buf) >>
  TRY (qpat_x_assum `_ (compile_create_salt _ _ _ _) = _` mp_tac >>
       pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
       pairarg_tac >> simp[] >> strip_tac) >>
  TRY (qpat_assum `compile_create_salt _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_create_salt) >>
    simp[] >> (TRY (impl_tac >- metis_tac[])) >> strip_tac) >>
  TRY (qpat_assum `compile_create_dispatch _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_create_dispatch) >> simp[is_label_operand_def]) >>
  TRY (qpat_assum `compile_create_copy _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_create_copy) >> simp[]) >>
  qpat_assum `(case origin_fold_value _ of Literal _ (IntL i) => _ | _ => _) _ = _`
    (mp_then Any mp_tac runtime_sym_create_blueprint_offset) >>
  simp[] >> (TRY (impl_tac >- metis_tac[])) >> strip_tac >>
  create_emit_tac `compile_create_blueprint_check _ _ _ _ = _` runtime_sym_create_blueprint_check >>
  qpat_assum `compile_create_blueprint_append _ _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_create_blueprint_append) >> simp[]
QED

Theorem runtime_sym_call_create:
  !tops cfn ce rt ty ck has_salt rof metadata es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
           runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env tops ce /\
    supported_expr tops (Call rt (CreateTarget ck has_salt rof metadata) es default) /\
    ~supported_expr_exists is_self_code
       (Call rt (CreateTarget ck has_salt rof metadata) es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) (CreateTarget ck has_salt rof metadata)
      es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (supported_pure_expr tops) es` by
    (Cases_on `default` >> fs[supported_expr_def, supported_pure_expr_def,
      supported_effect_expr_def, supported_pure_exprs_every]) >>
  `~supported_exprs_exists is_self_code es` by fs[supported_expr_exists_def] >>
  gvs[compile_call_def] >>
  Cases_on `compile_create_call cfn ce ck has_salt rof es s` >>
  gvs[as_stack_val_def, runtime_sym_value_def] >>
  qpat_assum `compile_create_call _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac
      (Q.INST [`all_args` |-> `es`] runtime_sym_compile_create_call)) >>
  disch_then (qspec_then `tops` mp_tac) >> simp[] >> metis_tac[]
QED
