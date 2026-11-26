(* Linked inputs for the checked calldata window. *)
Theory bodyCalldataSliceInputsMods
Ancestors
  bodyFullPredsMods exprBodyPreProps exprSimCalldataSlice exprSimSource list
  supportedExprTraverse allocLimits vyperTypeSystem vyperTypeCallGraph
  exprSimHypsDefs exprLoweringProps gasShadow gasShadowState
  gasShadowCompileStmtHelpers exprLowering compileEnv fragExec
  bodyPtrBytestringBuiltinsExternalSlice
  vyperAST vyperContext vyperInterpreter
Libs monadsyntax

Theorem calldata_slice_operand_pre_mods[local]:
  expr_body_pre_mods mods ce cx env (Builtin ann (CalldataSlice n) [e]) es ==>
  expr_body_pre_mods mods ce cx env e es
Proof
  rw[expr_body_pre_mods_def, Once well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def, supported_expr_exists_def,
     supported_exprs_exists_every, expr_has_evm_run_thm,
     code_slice_source_def, expr_type_def, EXISTS_MEM] >>
  fs[int_calls_expr_def, constSubstCorrectTheory.frame_well_typed_exprs_every]
QED

Theorem calldata_slice_operand_mods:
  (builtin_args_length_ok (CalldataSlice n) (LENGTH args) ==>
    body_exprs_full_ok_mods mods exps cx args) /\
  expr_body_pre_mods mods ce cx env (Builtin ann (CalldataSlice n) args) es ==>
  ?e m. args = [e] /\ expr_type e = BaseT (UintT 256) /\
    ann = BaseT (BytesT (Dynamic m)) /\ 0 < n /\ n <= m /\ m < 2 ** 256 /\
    expr_body_pre_mods mods ce cx env e es /\ body_expr_full_ok_mods mods exps cx e
Proof
  strip_tac >>
  drule_then (strip_assume_tac o MATCH_MP calldata_slice_typing)
    expr_body_pre_mods_well_typed >>
  qpat_x_assum `args = [e]` SUBST_ALL_TAC >>
  `body_exprs_full_ok_mods mods exps cx [e]` by
    (first_x_assum irule >> simp[builtin_args_length_ok_def]) >>
  drule_then assume_tac calldata_slice_operand_pre_mods >>
  qexistsl_tac [`e`,`m`] >> fs[body_exprs_full_ok_mods_def]
QED

(* The real/shadow cuts agree on the input operand.  The slice suffix
   itself contains no recursively lowered expression. *)
Theorem calldata_slice_compile_mods:
  compile_expr ce ty (Builtin ann (CalldataSlice n) [e]) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (Builtin ann (CalldataSlice n) [e])) sha = (vv,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\
  fn_has_code sha shb shadow_func ==>
  ?x sm shm out.
    lower_value compile_expr ce (expr_type e) e sa = (x,sm) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
      (gas_shadow_expr e) sha = (x,shm) /\
    compile_slice_calldata x (Lit (n2w n)) (type_memory_bytes ce ann) sm = (out,sb) /\
    compile_slice_calldata x (Lit (n2w n)) (type_memory_bytes ce ann) shm = (out,shb) /\
    vv = LocatedValue ann (mk_ptr out LocMemory) /\ gas_shadow_state sm shm /\
    cs_extends sa sm /\ cs_extends sha shm /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code sha shm shadow_func
Proof
  strip_tac >> Cases_on `lower_value compile_expr ce (expr_type e) e sa` >>
  rename1 `lower_value _ _ _ _ _ = (x,sm)` >>
  Cases_on `compile_slice_calldata x (Lit (n2w n)) (type_memory_bytes ce ann) sm` >>
  rename1 `compile_slice_calldata _ _ _ sm = (out,bb)` >>
  qpat_x_assum `compile_expr ce _ _ _ = _` mp_tac >>
  simp[compile_calldata_slice_parts, as_ptr_val_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  `gas_shadow_compiles (lower_value compile_expr ce (expr_type e) e)
     (lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
       (gas_shadow_expr e))` by irule gas_shadow_stmt_lower_value_env >>
  Cases_on `lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
      (gas_shadow_expr e) sha` >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`sha`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[] >> strip_tac >> gvs[] >> rename1 `gas_shadow_state sm shm` >>
  qmatch_assum_rename_tac `lower_value compile_expr ce _ e sa = (x,sm)` >>
  rename1 `fn_has_code sa sb func` >>
  Cases_on `compile_slice_calldata x (Lit (n2w n)) (type_memory_bytes ce ann) shm` >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gas_shadow_expr_def, gas_shadow_builtin_def, compile_calldata_slice_parts,
       as_ptr_val_def, comp_return_def, contextTheory.mk_ptr_def] >> strip_tac >> gvs[] >>
  `cs_extends sa sm /\ cs_extends sha shm` by
    (conj_tac >> metis_tac[cj 2 compile_expr_grows]) >>
  rename1 `fn_has_code sha shb shadow_func` >>
  `cs_extends sm sb` by
    (qpat_assum `compile_slice_calldata _ _ _ sm = _`
       (strip_assume_tac o MATCH_MP compile_slice_calldata_stages) >>
     irule cs_extends_trans >> qexists_tac `s4` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s3` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s2` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s1` >> simp[]) >>
  `cs_extends shm shb` by
    (qpat_assum `compile_slice_calldata _ _ _ shm = _`
       (strip_assume_tac o MATCH_MP compile_slice_calldata_stages) >>
     irule cs_extends_trans >> qexists_tac `s4` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s3` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s2` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s1` >> simp[]) >>
  simp[] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sha shm shadow_func /\ fn_has_code shm shb shadow_func` by
    (irule fn_has_code_split >> simp[]) >>
  simp[]
QED
