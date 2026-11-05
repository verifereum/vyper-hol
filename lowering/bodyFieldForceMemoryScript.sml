(* Counted forced field projection from a local Name. *)
Theory bodyFieldForceMemory
Ancestors
  bodyFieldValueMemory
  bodyFieldMemoryProps bodyNameValueMemory bodyNameMemoryFacts
  exprSimFieldLayout exprSimAttributeProps exprSimVVFrame exprSimProps
  exprSimSource exprSimHypsDefs exprSimMemDefs exprSimDefs loweringPosts
  exprSimMemoryStack exprSimMemoryValues exprSimMemoryPath exprSimUnwrapProps exprSimUnwrap
  gasNormalPrefix gasSummary gasSummaryCompose gasContext gasCount fragGasMode
  fragGasPathMem fragGasSeqMem gasExemptCert
  bodyMemoryDefs emitHelperProps fragExecMem instMemFrontier allocaHistoryFragment
  exprLoweringProps emitHelper venomInst venomState words list rich_list finite_map
  compileEnv fragExec valueEncoding vyperValue vyperAST venomExecSemantics
  loweringSlice exprLowering vyperState vyperExprNoControl
  freshWrites varsExt vyperTyping vyperTypeSystem vyperTypeInvariants
  allocLimits context vyperInterpreter vyperTypeExprSoundness

Theorem compile_attribute_name_body_sim_mem:
  !ctx func cenv cx env ty ann sid id fld es.
    expr_body_pre cenv cx env (Attribute ann (Name (StructT sid) id) fld) es ==>
    expr_sim_mem ctx func cenv cx ty (Attribute ann (Name (StructT sid) id) fld) es
Proof
  rpt gen_tac >> strip_tac >>
  irule expr_sim_mem_values >> rpt gen_tac >> strip_tac >>
  Cases_on `compile_expr cenv ty (Attribute ann (Name (StructT sid) id) fld) sa` >>
  rename1 `_ = (vv,sm)` >>
  `unwrap_value cenv vv sm = (op,sb)` by
    fs[lower_value_def, comp_bind_def] >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all body_attribute_name_counted_prefix >> strip_tac >> gvs[] >>
  `is_word_type ann ==> ?w. eval_operand (mk_ptr p LocMemory).ptr_operand t = SOME w /\
      w2n w + 32 <= t.vs_alloca_next` by
    (strip_tac >> drule_all word_tv_memory_size >> strip_tac >>
     qexists_tac `fw` >> simp[mk_ptr_def]) >>
  `read_result cx tv (es with gas_obs := []) = (INL v, es with gas_obs := [])` by simp[] >>
  `(mk_ptr p LocMemory).ptr_location = LocMemory` by simp[mk_ptr_def] >>
  drule_all body_unwrap_memory_counted_read >>
  disch_then (qspec_then `ann` strip_assume_tac) >>
  qexistsl_tac [`[]`, `v`, `es`, `u`] >>
  reverse conj_tac
  >- (simp[expr_type_def] >> first_x_assum irule >> fs[]) >>
  simp[gas_value_prefix_def] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
  conj_tac
  >- (gen_tac >> simp[bind_def]) >>
  drule_all gas_path_mem_then >> simp[]
QED
