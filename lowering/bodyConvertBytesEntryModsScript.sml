(* Source typing and paired compiler cuts for Convert to bytes/string. *)
Theory bodyConvertBytesEntryMods
Ancestors
  bodyFullPredsMods bodyTypeBuiltinAbiMods exprBodyPreProps bodyFullShared
  exprSimConvertBytes exprSimConvert exprLowering exprLoweringProps
  exprBopLowering gasShadowCompileStmtHelpers gasShadowCompilePure gasShadowState
  gasShadow externalEntryShape fragExec
  compileEnv vyperTypeSystem vyperContext vyperInterpreter vyperState vyperAST

Theorem bytes_convert_entry_mods:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann Convert dst [e]) es /\
  is_bytestring_type dst ==>
  ann = dst /\ is_bytestring_type (expr_type e) /\
  valid_conversion (expr_type e) dst /\ well_formed_type env.type_defs dst /\
  expr_body_pre_mods mods ce cx env e es
Proof
  strip_tac >>
  drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def, well_typed_type_builtin_args_def,
       type_builtin_result_ok_def] >> strip_tac >> gvs[] >>
  drule_all_then assume_tac valid_conversion_to_bytestring >> simp[] >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  irule type_builtin_body_arg_pre_mods >>
  simp[] >> qexistsl_tac [`ann`,`[e]`,`es`,`Convert`,`ann`] >> simp[]
QED

Theorem bytes_convert_compile_cut[local]:
  is_bytestring_type dst /\ is_bytestring_type (expr_type e) /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) ==>
  compile_expr ce ty (TypeBuiltin dst Convert dst [e]) sa =
    as_ptr_val dst LocMemory
      (if type_memory_bytes ce (lowered_value_type ce e) < type_memory_bytes ce dst
       then compile_bytestring_widen_copy (type_memory_bytes ce dst) op
         (type_memory_bytes ce (lowered_value_type ce e)) sm
       else compile_type_convert op (mk_convert_op (expr_type e) dst) sm)
Proof
  strip_tac >>
  simp[Once (cj 1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (cj 3 compile_expr_raw_def), compile_type_builtin_dispatch_body_def,
       exprCallBoundsTheory.expr_child_callback_def] >>
  simp[lower_value_child_call, SF ETA_ss, expr_type_def,
       valueCopyBytesTheory.is_bytestring_word_type] >>
  Cases_on `dst` >> gvs[is_bytestring_type_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem bytes_convert_memory_shape_mods:
  is_bytestring_type dst /\ is_bytestring_type (expr_type e) ==>
  !sa. ?out sb. compile_expr ce ty (TypeBuiltin dst Convert dst [e]) sa =
    (LocatedValue dst (mk_ptr out LocMemory),sb)
Proof
  strip_tac >> gen_tac >>
  Cases_on `lower_value compile_expr ce (expr_type e) e sa` >>
  rename1 `_ = (op,sm)` >>
  `compile_expr ce ty (TypeBuiltin dst Convert dst [e]) sa =
    as_ptr_val dst LocMemory
      (if type_memory_bytes ce (lowered_value_type ce e) < type_memory_bytes ce dst
       then compile_bytestring_widen_copy (type_memory_bytes ce dst) op
         (type_memory_bytes ce (lowered_value_type ce e)) sm
       else compile_type_convert op (mk_convert_op (expr_type e) dst) sm)` by
    (irule bytes_convert_compile_cut >> simp[]) >>
  Cases_on `type_memory_bytes ce (lowered_value_type ce e) < type_memory_bytes ce dst`
  >- (Cases_on `compile_bytestring_widen_copy (type_memory_bytes ce dst) op
          (type_memory_bytes ce (lowered_value_type ce e)) sm` >>
      gvs[as_ptr_val_def, contextTheory.mk_ptr_def])
  >- (Cases_on `compile_type_convert op (mk_convert_op (expr_type e) dst) sm` >>
      gvs[as_ptr_val_def, contextTheory.mk_ptr_def])
QED

Theorem bytes_convert_paired_cut_mods:
  is_bytestring_type dst /\ is_bytestring_type (expr_type e) /\
  compile_expr ce ty (TypeBuiltin dst Convert dst [e]) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (TypeBuiltin dst Convert dst [e])) sha = (vv,shb) /\
  gas_shadow_state sa sha /\
  fn_has_code sa sb func /\ fn_has_code sha shb shadow_func ==>
  ?op sm shm out.
    lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
      (gas_shadow_expr e) sha = (op,shm) /\
    gas_shadow_state sm shm /\ vv = LocatedValue dst (mk_ptr out LocMemory) /\
    fn_has_code sa sm func /\ fn_has_code sha shm shadow_func /\
    fn_has_code sm sb func /\ fn_has_code shm shb shadow_func /\
    cs_extends sa sm /\ cs_extends sha shm /\ cs_extends sm sb /\ cs_extends shm shb /\
    (if type_memory_bytes ce (lowered_value_type ce e) < type_memory_bytes ce dst then
       compile_bytestring_widen_copy (type_memory_bytes ce dst) op
         (type_memory_bytes ce (lowered_value_type ce e)) sm = (out,sb) /\
       compile_bytestring_widen_copy (type_memory_bytes ce dst) op
         (type_memory_bytes ce (lowered_value_type ce e)) shm = (out,shb)
     else
       compile_type_convert op (mk_convert_op (expr_type e) dst) sm = (out,sb) /\
       compile_type_convert op (mk_convert_op (expr_type e) dst) shm = (out,shb))
Proof
  strip_tac >>
  Cases_on `lower_value compile_expr ce (expr_type e) e sa` >>
  rename1 `_ = (op,sm)` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
    (gas_shadow_expr e) sha` >> rename1 `_ = (sop,shm)` >>
  `sop = op /\ gas_shadow_state sm shm` by
    (irule gas_shadow_step >> simp[] >>
     qexistsl_tac [`lower_value compile_expr ce (expr_type e) e`,
       `lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e)`,
       `sa`,`sha`] >> simp[gas_shadow_stmt_lower_value_env]) >>
  gvs[] >>
  `cs_extends sa sm /\ cs_extends sha shm` by
    metis_tac[cj 2 compile_expr_grows] >>
  `compile_expr ce ty (TypeBuiltin dst Convert dst [e]) sa =
    as_ptr_val dst LocMemory
      (if type_memory_bytes ce (lowered_value_type ce e) < type_memory_bytes ce dst
       then compile_bytestring_widen_copy (type_memory_bytes ce dst) op
         (type_memory_bytes ce (lowered_value_type ce e)) sm
       else compile_type_convert op (mk_convert_op (expr_type e) dst) sm)` by
    (irule bytes_convert_compile_cut >> simp[]) >>
  `compile_expr (gas_shadow_env T ce) ty (TypeBuiltin dst Convert dst [gas_shadow_expr e]) sha =
    as_ptr_val dst LocMemory
      (if type_memory_bytes ce (lowered_value_type ce e) < type_memory_bytes ce dst
       then compile_bytestring_widen_copy (type_memory_bytes ce dst) op
         (type_memory_bytes ce (lowered_value_type ce e)) shm
       else compile_type_convert op (mk_convert_op (expr_type e) dst) shm)` by
    (mp_tac (Q.INST [`ce` |-> `gas_shadow_env T ce`, `e` |-> `gas_shadow_expr e`,
       `sa` |-> `sha`, `sm` |-> `shm`] bytes_convert_compile_cut) >> simp[]) >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gas_shadow_expr_def] >> strip_tac >>
  Cases_on `type_memory_bytes ce (lowered_value_type ce e) < type_memory_bytes ce dst` >>
  fs[as_ptr_val_pair, contextTheory.mk_ptr_def] >>
  `cs_extends sm sb /\ cs_extends shm shb` by
    (qpat_assum `SND _ = sb` (once_rewrite_tac o single o GSYM) >>
     qpat_assum `SND _ = shb` (once_rewrite_tac o single o GSYM) >>
     simp[NoAsms, cj 1 compile_type_convert_labels, cj 1 compile_bytestring_widen_copy_labels]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sha shm shadow_func /\ fn_has_code shm shb shadow_func` by
    (irule fn_has_code_split >> simp[]) >>
  gvs[] >>
  qpat_assum `FST _ = FST _` (once_rewrite_tac o single o GSYM) >>
  simp[pairTheory.PAIR]
QED
