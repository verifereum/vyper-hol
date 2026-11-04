(* Counted forced field projection from a local Name. *)
Theory bodyFieldForceMemory
Ancestors
  bodyFieldValueMemory
  bodyFieldMemoryProps bodyNameValueMemory bodyNameMemoryFacts
  exprSimFieldLayout exprSimAttributeProps exprSimVVFrame exprSimProps
  exprSimSource exprSimHypsDefs exprSimMemDefs exprSimDefs loweringPosts
  exprSimMemoryStack exprSimMemoryValues exprSimMemoryPath exprSimUnwrapProps
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
  rpt gen_tac >> strip_tac >> simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty (Attribute ann (Name (StructT sid) id) fld) sa` >>
  rename1 `_ = (vv,sm)` >> simp[] >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  drule body_attribute_name_compile >> strip_tac >> gvs[] >>
  Cases_on `eval_expr cx (Attribute ann (Name (StructT sid) id) fld) es` >>
  rename1 `_ = (raw,est)` >>
  qpat_x_assum `(do result <- _; _ od) _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `raw`
  >- (rename1 `eval_expr _ _ _ = (INL r,est)` >> simp[] >> strip_tac >>
      drule read_result_state >> strip_tac >> gvs[] >>
      `expr_vv_res_ok (INL r)` by
        (Cases_on `r` >> gvs[expr_vv_res_ok_def, read_result_def,
                             raise_def, expr_res_ok_def]) >>
      `INL r <> INR (Error (RuntimeError "convert empty bytes to signed"))` by simp[] >>
      drule_all compile_attribute_name_body_capacity_mem >>
      disch_then (qspecl_then [`s0`, `ctx`] assume_tac) >>
      irule frag_exec_mem_seq_pointwise >>
      qexistsl [`\s. vv_post ctx func cenv cx
          (Attribute ann (Name (StructT sid) id) fld) es sa sm s0 es' r
          (LocatedValue ann (mk_ptr p (vv_loc bvv))) s /\
        vv_loc (LocatedValue ann (mk_ptr p (vv_loc bvv))) = LocMemory /\
        (?ftv w. evaluate_type (get_tenv cx) ann = SOME ftv /\
          eval_operand p s = SOME w /\
          w2n w + type_memory_size ftv <= s.vs_alloca_next) /\
        s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s`, `sm`] >>
      simp[] >> reverse conj_tac
      >- (irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >>
          simp[vv_operand_def, mk_ptr_def, expr_exit_def]) >>
      gen_tac >> strip_tac >>
      Cases_on `res`
      >- (rename1 `read_result cx r es' = (INL v,es')` >>
          `is_word_type ann ==> ?w. eval_operand p t = SOME w /\
               w2n w + 32 <= t.vs_alloca_next` by
            (strip_tac >> drule_all exprSimPropsTheory.word_tv_memory_size >>
             strip_tac >> qexists_tac `w` >> simp[]) >>
          `(mk_ptr p (vv_loc bvv)).ptr_location = LocMemory` by
            fs[vv_loc_def, vv_location_def] >>
          drule_all body_unwrap_memory_read_mem >>
          disch_then (qspecl_then [`s0`, `es`,
            `Attribute ann (Name (StructT sid) id) fld`, `ctx`, `expr_exit (INL v)`]
            assume_tac) >>
          irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >>
          gvs[mk_ptr_def, vv_loc_def, vv_location_def]) >>
      drule vv_post_failed_read >> metis_tac[]) >>
  rename1 `eval_expr _ _ _ = (INR exc,est)` >> strip_tac >> gvs[] >>
  `expr_vv_res_ok (INR exc)` by gvs[expr_vv_res_ok_def, expr_res_ok_def] >>
  `(INR exc : eval_result + exception) <>
     INR (Error (RuntimeError "convert empty bytes to signed"))` by simp[] >>
  drule_all compile_attribute_name_body_capacity_mem >>
  disch_then (qspecl_then [`s0`, `ctx`] assume_tac) >>
  `expr_exit (INR exc : eval_result + exception) =
   expr_exit (INR exc : value + exception)` by
    simp[FUN_EQ_THM, expr_exit_exception_transport] >>
  fs[] >>
  irule frag_exec_mem_exit_prefix >> goal_assum (drule_at Any) >> simp[]
QED
