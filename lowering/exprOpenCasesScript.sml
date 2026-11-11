(*
 * compile_expr keeps its block open: names, module variables, calls
 *
 * TOP-LEVEL:
 *   compile_expr_name_open     — a local the typing knows is bound
 *   compile_expr_toplevel_open — a supported module variable that
 *                                evaluates is bound in ce_module_vars, by the
 *                                storage and transient relations
 *   compile_subscript_open, compile_call_open,
 *   compile_struct_literal_body_open — the other compound cases
 *)

Theory exprOpenCases
Ancestors
  exprSimHypsDefs
  exprOpenCopies exprOpenPrimitives exprOpenTerminals exprOpenBuiltins
  supportedExprs supportedExprForms
  exprLowering  vyperTypeSystem compileEnv loweringStateRelDefs finite_map
  supportedDecls vyperState vyperInterpreter list
  builtinSystem venomInst supportedExprTraverse whitelistCheckerDecls

Theorem compile_expr_name_open:
  !cenv cx env es ann id ty sa vv sb.
    expr_sim_inv cenv cx env es /\ well_typed_expr env (Name ann id) /\
    ~block_is_terminated sa /\
    compile_expr cenv ty (Name ann id) sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt strip_tac >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_inv_def, well_typed_expr_def] >>
  gvs[compile_expr_def, compile_name_vv_def, comp_return_def]
QED

Theorem supported_variable_decl_runtime_lookup:
  !tops src id vis mut ty slot.
    supported_variable_decl tops (src,id) = SOME (vis,mut,ty,slot) /\
    (mut = Storage \/ mut = Transient) ==>
    src = NONE /\ ?decl key. find_var_decl_by_name id tops = SOME (decl,key)
Proof
  Induct_on `tops` >- simp[supported_variable_decl_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[supported_variable_decl_def, find_var_decl_by_name_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[]
QED

Theorem eval_toplevel_decl_bound:
  !cenv cx ann src id es tv es1 tops decl key.
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    get_module_code cx src = SOME tops /\
    find_var_decl_by_name id tops = SOME (decl,key) /\
    eval_expr cx (TopLevelName ann (src,id)) es = (INL tv,es1) ==>
    ?slot. FLOOKUP cenv.ce_module_vars (src,id) = SOME (StorageLoc slot) \/
           FLOOKUP cenv.ce_module_vars (src,id) = SOME (TransientLoc slot)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  Cases_on `decl` >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, LET_THM] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
  qmatch_asmsub_rename_tac `lookup_var_slot_from_layout cx tr src key` >>
  Cases_on `lookup_var_slot_from_layout cx tr src key` >>
  gvs[return_def, raise_def] >>
  (Cases_on `tr`
   >- (fs[transient_vars_rel_def] >> qexists_tac `n2w slot` >>
       disj2_tac >> first_assum irule >>
       goal_assum (drule_at (Pat `find_var_decl_by_name _ _ = _`)) >>
       simp[var_decl_transient_def])) >>
  fs[storage_vars_rel_def] >> qexists_tac `n2w slot` >>
  disj1_tac >> first_assum irule >>
  goal_assum (drule_at (Pat `find_var_decl_by_name _ _ = _`)) >>
  simp[var_decl_transient_def]
QED

Theorem supported_storage_value_runtime_lookup:
  !tops src id ann.
    supported_storage_value tops (src,id) ann ==>
    src = NONE /\ ?decl key. find_var_decl_by_name id tops = SOME (decl,key)
Proof
  rpt gen_tac >> simp[supported_storage_value_def] >>
  strip_tac >>
  Cases_on `supported_variable_decl tops (src,id)` >> gvs[] >>
  rename1 `supported_variable_decl _ _ = SOME decl_info` >>
  PairCases_on `decl_info` >>
  rename1 `supported_variable_decl _ _ = SOME (vis,mut,declared,slot)` >>
  Cases_on `slot` >> Cases_on `vis` >> Cases_on `mut` >> gvs[] >>
  drule supported_variable_decl_runtime_lookup >> simp[]
QED

Theorem compile_expr_toplevel_open:
  !tops cenv cx ann src id es tv es1 ty sa vv sb.
    supported_storage_value tops (src,id) ann /\
    get_module_code cx NONE = SOME tops /\
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    eval_expr cx (TopLevelName ann (src,id)) es = (INL tv,es1) /\
    ~block_is_terminated sa /\
    compile_expr cenv ty (TopLevelName ann (src,id)) sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> strip_tac >>
  drule supported_storage_value_runtime_lookup >> strip_tac >> gvs[] >>
  drule_all eval_toplevel_decl_bound >> strip_tac >>
  gvs[compile_expr_def]
QED

Theorem compile_subscript_open:
  !cfn cenv ret_ty ty base_e idx sa vv sb.
    compile_subscript cfn cenv ret_ty ty base_e idx sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_subscript_def, comp_bind_def] >>
  pairarg_tac >> simp[] >>
  Cases_on `place_type cenv base_e`
  >- (simp[comp_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      drule compile_mapping_subscript_open >> simp[]) >>
  rename1 `ValPT base_ty` >> Cases_on `base_ty` >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  metis_tac[compile_tuple_subscript_open, compile_array_subscript_open]
QED

Theorem compile_raw_call_finish_open:
  !addr data len gas value kind size rof out ptr sa v sb.
    compile_raw_call_finish addr data len gas value kind size rof out ptr sa =
      (v,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_raw_call_finish_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> IF_CASES_TAC >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]
  >~ [`emit_void MCOPY _ _ = _`]
    >- (drule emit_void_terminated >> simp[is_terminator_def])
  >~ [`emit_void MSTORE _ _ = _`]
    >- (drule emit_void_terminated >> simp[is_terminator_def])
  >~ [`new_block _ _ = _`]
    >- (drule new_block_open >> simp[]) >>
  Cases_on `kind` >> gvs[] >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_raw_call_open:
  !cfn cenv rty ty flags addr data args default sa vv sb.
    ~flags.rcf_is_delegate /\
    compile_call cfn cenv rty ty (RawCallTarget flags) (addr::data::args)
      default sa = (vv,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_call_def] >>
  rpt (pairarg_tac >> simp[]) >> IF_CASES_TAC >>
  strip_tac >> gvs[] >> drule compile_raw_call_finish_open >> simp[]
QED

Theorem compile_raw_call_calldata_open:
  !cfn cenv rty ty flags addr args default sa vv sb.
    ~flags.rcf_is_delegate /\
    compile_call cfn cenv rty ty (RawCallCalldataTarget flags) (addr::args)
      default sa = (vv,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_call_def] >>
  rpt (pairarg_tac >> simp[]) >> IF_CASES_TAC >>
  strip_tac >> gvs[] >> drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_raw_log_open:
  !cfn cenv rty ty topics data default sa vv sb.
    compile_call cfn cenv rty ty RawLog [topics;data] default sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_call_def] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_inst_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_call_open:
  !cfn cenv rty ty ann target args default env cx es tv es1 sa vv sb.
    well_typed_expr env (Call ann target args default) /\
    ~expr_evm_run_root (Call ann target args default) /\
    eval_expr cx (Call ann target args default) es = (INL tv,es1) /\
    compile_call cfn cenv rty ty target args default sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `target` >> strip_tac >>
  fs[expr_evm_run_root_def]
  >~ [`IntCall`] >- metis_tac[compile_intcall_open]
  >~ [`ExtCall _ _ signature _`]
    >- (PairCases_on `signature` >>
        drule well_typed_ext_call_operand_count >>
        Cases_on `args` >> simp[] >> strip_tac >>
        drule compile_extcall_open >> simp[])
  >~ [`Send gas`]
    >- (drule well_typed_send_shape >> Cases_on `gas` >> simp[] >>
        strip_tac >> gvs[] >>
        drule_at (Pat `compile_call _ _ _ _ _ _ _ _ = _`) compile_send_open >> simp[])
  >~ [`RawCallTarget flags`]
    >- (fs[well_typed_expr_def] >> Cases_on `args` >> gvs[] >>
        rename1 `addr::rest` >> Cases_on `rest` >> gvs[] >>
        drule_all compile_raw_call_open >> simp[])
  >~ [`RawCallCalldataTarget flags`]
    >- (fs[well_typed_expr_def] >> Cases_on `args` >> gvs[] >>
        drule_all compile_raw_call_calldata_open >> simp[])
  >~ [`RawLog`]
    >- (fs[well_typed_expr_def, LENGTH_EQ_NUM_compute] >>
        gvs[] >> drule compile_raw_log_open >> simp[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> simp[Once evaluate_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[return_def, raise_def])
QED

Theorem compile_struct_literal_body_open:
  !cfn bfn tfn cenv cx env es ty ann nsid fields sa vv sb.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    expr_sim_inv cenv cx env es /\
    well_typed_expr env (StructLit ann nsid fields) /\
    compile_expr_body cfn bfn tfn cenv ty (StructLit ann nsid fields) sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_expr_body_def] >>
  ntac 2 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule compile_alloc_buffer_open >> disch_tac >>
  drule_at (Pat `compile_struct_lit _ _ _ _ _ _ _ = _`)
    compile_struct_lit_open >> simp[] >>
  impl_tac >- (fs[] >> rpt strip_tac >> drule_all struct_literal_store_paths >> simp[]) >>
  simp[]
QED

Theorem compile_addmod_names_open:
  !cenv rty aty a bty b mty m sa vv sb.
    compile_addmod_names cenv rty aty a bty b mty m sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_addmod_names_def, as_stack_val_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  gvs[oneline as_stack_val_def, AllCaseEqs()] >>
  drule compile_addmod_open >> simp[]
QED

Theorem compile_mulmod_names_open:
  !cenv rty aty a bty b mty m sa vv sb.
    compile_mulmod_names cenv rty aty a bty b mty m sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_mulmod_names_def, as_stack_val_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  gvs[oneline as_stack_val_def, AllCaseEqs()] >>
  drule compile_mulmod_open >> simp[]
QED

Theorem compile_powmod256_names_open:
  !cenv rty aty a bty b sa vv sb.
    compile_powmod256_names cenv rty aty a bty b sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_powmod256_names_def, as_stack_val_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  gvs[oneline as_stack_val_def, AllCaseEqs()] >>
  drule compile_pow_mod256_open >> simp[]
QED
