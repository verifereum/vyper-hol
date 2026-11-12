(* Compiler fields and counted control for actual internal-function entry. *)
Theory bodyIntCallActualEntryFields
Ancestors
  bodyIntCallActualEntryResource bodyIntCallJointInputs
  bodyIntCallSemanticEntry bodyIntCallJointEntry intCallCallee
  emitHelperProps compileEnv context moduleLowering compileVyper
  fragGasSeq entrySinkExtraction rich_list list
Libs
  monadsyntax

Theorem internal_entry_environment:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) ==>
  ?stage_ce caps sc sr sm.
    compile_internal_entry_prefix ce params has_rb st0 = ((stage_ce,caps,rpc),sc) /\
    materialize_internal_params stage_ce caps sr = (ce2,sm)
Proof
  simp[compile_internal_function_entry_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_internal_entry_prefix _ _ _ _ = (prefix,_)` >>
  PairCases_on `prefix` >> gvs[] >>
  Cases_on `rt` >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `ce.ce_returns_count > 0` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  metis_tac[]
QED

Theorem compile_internal_entry_fields:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) ==>
  ce2 with <| ce_vars := ce.ce_vars; ce_return_buf := ce.ce_return_buf;
              ce_return_pc := ce.ce_return_pc |> = ce
Proof
  strip_tac >> drule internal_entry_environment >> strip_tac >>
  drule internal_entry_prefix_stages >> strip_tac >>
  drule intCallCalleeTheory.materialize_internal_params_shape >>
  strip_tac >> gvs[] >> simp[compile_env_component_equality]
QED

Theorem internal_entry_return_pc:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) ==>
  ce2.ce_return_pc = SOME (PtrVar rpc 0)
Proof
  strip_tac >> drule internal_entry_environment >> strip_tac >>
  drule internal_entry_prefix_stages >> strip_tac >>
  drule intCallCalleeTheory.materialize_internal_params_shape >>
  strip_tac >> gvs[]
QED

Theorem internal_entry_no_return_buffer:
  compile_internal_function_entry ce params F ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) ==>
  ce2.ce_return_buf = ce.ce_return_buf
Proof
  strip_tac >> drule internal_entry_environment >> strip_tac >>
  drule internal_entry_prefix_stages >> strip_tac >>
  drule intCallCalleeTheory.materialize_internal_params_shape >>
  strip_tac >> gvs[comp_return_def]
QED

Theorem packaged_internal_entry_alloc_env_agree:
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys is_ctor imm_size
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,pc,imm),st1) ==>
  alloc_env_agree
    (build_compile_env tops Internal mut name args ret ss F)
    (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
Proof
  strip_tac >> drule compile_internal_entry_fields >>
  simp[compile_env_component_equality] >> strip_tac >>
  gvs[package_internal_fn_def, set_internal_package_target_def,
      update_cenv_nonreentrant_def] >>
  simp[allocLimitsPropsTheory.alloc_env_agree_def, build_compile_env_def, pairTheory.ELIM_UNCURRY]
QED

Theorem compile_internal_entry_shape:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) ==>
  st1.cs_blocks = st0.cs_blocks /\ st1.cs_current_bb = st0.cs_current_bb /\
  st0.cs_next_var <= st1.cs_next_var /\ st0.cs_next_id <= st1.cs_next_id /\
  ?new. st1.cs_current_insts = st0.cs_current_insts ++ new /\ new <> [] /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) new
Proof
  simp[compile_internal_function_entry_def, compile_internal_entry_prefix_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  dxrule compile_internal_param_decls_shape >> strip_tac >>
  dxrule intCallCalleeTheory.materialize_internal_params_shape >> strip_tac >>
  Cases_on `has_rb` >> Cases_on `rt` >> Cases_on `ce.ce_returns_count > 0` >>
  Cases_on `ctor /\ imm_len > 0` >>
  gvs[emitHelperTheory.emit_op_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def,
      compile_alloc_buffer_def, compile_fixed_region_with_id_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emitHelperTheory.emit_op_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[venomInstTheory.is_terminator_def, EVERY_GENLIST, venomInstTheory.mk_inst_def] >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i new ==> _` (qspec_then `i` mp_tac) >>
  simp[venomInstTheory.is_terminator_def] >> rpt strip_tac >>
  gvs[venomInstTheory.is_terminator_def]
QED

Theorem internal_entry_counted_landing:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\
  fn_has_code st0 st1 func /\ ~s.vs_halted /\
  s.vs_current_bb = st0.cs_current_bb /\
  s.vs_inst_idx = LENGTH st0.cs_current_insts /\
  run_inst_seq (emitted_insts st0 st1) s = OK u ==>
  gas_path ctx func s
    (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st0 st1)))
    (OK (u with vs_inst_idx := LENGTH st1.cs_current_insts)) /\
  ~u.vs_halted /\ u.vs_current_bb = st1.cs_current_bb
Proof
  strip_tac >> drule compile_internal_entry_shape >> strip_tac >>
  `emitted_insts st0 st1 = new` by
    simp[exprLoweringPropsTheory.emitted_insts_def, DROP_LENGTH_APPEND] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX st1.cs_current_insts bb.bb_instructions` by
    (fs[fragExecTheory.fn_has_code_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts st0 st1) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st1.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`,`func`,`bb`] mp_tac) >> simp[] >> strip_tac >>
  metis_tac[run_inst_seq_preserves_entry_control]
QED

Theorem internal_entry_buffer_shape:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) ==>
  ?rb stb caps next stp sc.
    (if has_rb then do p <- emit_op PARAM [Lit 0w]; return (SOME p) od
     else return NONE) st0 = (rb,stb) /\
    compile_internal_param_decls params (if has_rb then 1 else 0) stb =
      ((caps,next),stp) /\
    emit_op RETPC_PARAM [Lit (n2w next)] stp = (rpc,sc) /\
    ce2.ce_return_buf =
      (case (rb,ce.ce_return_buf) of
         (SOME p,SOME (MemLoc off sz)) => SOME (PtrVar p sz)
       | _ => ce.ce_return_buf)
Proof
  strip_tac >> drule internal_entry_environment >> strip_tac >>
  drule internal_entry_prefix_stages >> strip_tac >>
  drule intCallCalleeTheory.materialize_internal_params_shape >> strip_tac >>
  qexistsl_tac [`rb`,`stb`,`caps`,`next`,`stp`,`sc`] >> gvs[]
QED

Theorem packaged_internal_entry_param_type:
  supported_function_body tops Internal args ss /\ MEM (n,ty) args /\
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys is_ctor imm_size
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,pc,imm),st1) ==>
  ce2.ce_var_type n = SOME ty
Proof
  strip_tac >> drule compile_internal_entry_fields >>
  simp[compile_env_component_equality] >> strip_tac >>
  gvs[package_internal_fn_def, set_internal_package_target_def,
      update_cenv_nonreentrant_def] >>
  irule supported_build_internal_env_param_type >> metis_tac[]
QED

Theorem internal_entry_module_pins:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\ cenv_module_pins tops ce ==>
  cenv_module_pins tops (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
Proof
  strip_tac >> drule compile_internal_entry_fields >>
  simp[compile_env_component_equality] >> strip_tac >>
  fs[bodySimTheory.cenv_module_pins_def]
QED
