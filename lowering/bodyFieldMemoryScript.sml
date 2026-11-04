(* Contained field capacity for actual memory projections. *)
Theory bodyFieldMemory
Ancestors
  loweringPosts
  bodyFieldMemoryProps bodyFieldValueMemory bodyFieldForceMemory
  exprSimAttributeProps exprSimFieldLayout exprSimProps exprSimVVFrame
  bodyNameValueMemory
  bodyNameMemoryFacts
  exprSimSource
  exprSimAttributeFields bodyAllocMemory
  valueEncoding compileEnv venomState words list rich_list finite_map
  exprSimAttribute exprSimHash exprSimLiteralBuffer exprOperandVar
  exprSimBuffer exprSimAggregateChildren exprSimDefs context
  exprLowering exprLoweringProps emitHelper emitHelperProps fragExec fragExecMem instMemFrontier
  allocaHistoryFragment venomInst vyperAST vyperTyping vyperInterpreter
  exprSimHyps vyperTypeSystem vyperTypeInvariants allocLimits
  bodyMemoryDefs exprSimUnwrap vyperState exprSimLen vyperTypeExprSoundness

Theorem compile_attribute_name_body_capacity_mem:
  expr_body_pre cenv cx env (Attribute ann (Name (StructT sid) id) fld) es /\
  compile_expr cenv ty (Attribute ann (Name (StructT sid) id) fld) sa = (vv,sb) /\
  eval_expr cx (Attribute ann (Name (StructT sid) id) fld) es = (res,es') /\
  expr_vv_res_ok res /\
  res <> INR (Error (RuntimeError "convert empty bytes to signed")) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa ==>
  frag_exec_mem ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s)
    (\s. (?tv. res = INL tv /\
               vv_post ctx func cenv cx (Attribute ann (Name (StructT sid) id) fld)
                 es sa sb s0 es' tv vv s) /\
         vv_loc vv = LocMemory /\
         (?ftv w. evaluate_type (get_tenv cx) ann = SOME ftv /\
                  eval_operand (vv_operand vv) s = SOME w /\
                  w2n w + type_memory_size ftv <= s.vs_alloca_next) /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (expr_exit res)
Proof
  strip_tac >> drule body_attribute_name_pre >> strip_tac >>
  `expr_sim_pre cenv cx env (Name (StructT sid) id) es` by
    simp[expr_sim_pre_body, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  drule compile_name_body_vv_sim_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `ty`] assume_tac) >>
  drule body_attribute_name_compile >> strip_tac >> gvs[] >>
  rename1 `compile_expr cenv ty (Name (StructT sid) id) sa = (bvv, sm)` >>
  drule attr_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  gvs[body_attribute_name_eval, bind_def] >>
  Cases_on `eval_expr cx (Name (StructT sid) id) es` >>
  rename1 `_ = (er, es1)` >>
  `expr_vv_res_ok er` by
    (drule_all expr_body_pre_vv_res_ok >> simp[]) >>
  `er <> INR (Error (RuntimeError "convert empty bytes to signed"))` by
    (Cases_on `er` >> gvs[]) >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ (Name _ _) _` mp_tac >>
  simp[expr_vv_sim_mem_def] >>
  disch_then drule_all >> disch_then (qspec_then `s0` assume_tac) >>
  Cases_on `er` >> gvs[]
  >- (rename1 `eval_expr cx (Name (StructT sid) id) es = (INL btv, es1)` >>
      `?entry. lookup_scopes id es.scopes = SOME entry` by
        (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
         drule_all vyperTypeEnvTheory.well_typed_Name_lookup >> metis_tac[]) >>
      `es1 = es` by (drule_all body_name_eval_state >> simp[]) >> gvs[] >>
      drule_all expr_body_pre_runtime_typed >> strip_tac >> gvs[expr_type_def] >>
      `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
      drule_all struct_fields_layout >> strip_tac >> gvs[] >>
      drule_all attribute_type_evaluates >> strip_tac >>
      `~popped_at_field btv fld es` by
        (irule popped_keys_indexed_not_at_field >>
         fs[expr_sim_inv_def, expr_type_def]) >>
      `!m. res <> INR (Error (TypeError m))` by
        (rpt strip_tac >> gvs[expr_vv_res_ok_def]) >>
      `vv_loc bvv = LocMemory` by
        (`?ptr sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var ptr) sz)` by
           gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
         gvs[compile_expr_def, compile_name_vv_def, comp_return_def,
             vv_loc_def, vv_location_def, mk_ptr_def]) >>
      irule frag_exec_mem_seq_pointwise >>
      qexistsl [`\s. vv_post ctx func cenv cx (Name (StructT sid) id)
                   es sa sm s0 es btv bvv s /\
                   s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s`,
                `sm`] >> simp[] >> reverse conj_tac
      >- (irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >>
          simp[expr_exit_def]) >>
      gen_tac >> strip_tac >>
      qmatch_asmsub_abbrev_tac `emit_op ADD [_; Lit (n2w off)] sm = _` >>
      drule_all attr_add_frag_mem_at >>
      disch_then (qspecl_then [`btv`, `s0`, `es`, `es`] mp_tac) >>
      disch_then (qspecl_then [`t`, `cx`, `ctx`, `expr_exit res`] assume_tac) >>
      qpat_x_assum `frag_exec_mem ctx sa sm _ _ _` kall_tac >>
      qpat_x_assum `compile_expr _ _ (Attribute _ _ _) _ = _` kall_tac >>
      irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >> simp[] >>
      rpt strip_tac
      >- (qpat_x_assum `frag_exec_mem _ _ _ _ _ _` kall_tac >>
          `?v. read_result cx btv es = (INL v, es)` by
            (drule body_base_memory_post_read_struct >> simp[expr_type_def] >>
             disch_then drule_all >> simp[]) >>
          `value_has_type (StructTV fs) v` by metis_tac[] >>
          `?vals. v = StructV vals /\ struct_has_type fs vals` by
            (Cases_on `v` >> gvs[value_has_type_def] >>
             rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def]) >>
          gvs[] >> drule_all select_attr_read >> strip_tac >> gvs[] >>
          qpat_assum `vv_loc bvv = LocMemory`
            (fn th => pure_once_rewrite_tac[GSYM th]) >>
          irule body_attr_memory_vv_post >> simp[expr_type_def, Abbr `off`] >>
          goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >> gvs[])
      >- simp[vv_loc_def, vv_location_def, mk_ptr_def] >>
      `stmt_state_rel ctx func cenv cx es s` by fs[vv_post_def] >>
      `eval_operand p s = SOME (w + n2w
        (struct_field_offset (get_struct_fields cenv.ce_struct_fields
          (nsid_to_string sid)) fld))` by fs[Abbr `off`, attr_offset_def] >>
      drule_all body_attribute_name_capacity >>
      simp[vv_operand_def, mk_ptr_def, Abbr `off`, attr_offset_def]) >>
  irule frag_exec_mem_exit_prefix >> goal_assum (drule_at Any) >> simp[]
QED

