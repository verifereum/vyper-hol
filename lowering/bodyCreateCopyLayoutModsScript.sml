(* CreateCopyOf: static argument shape and paired compiler cuts. *)
Theory bodyCreateCopyLayoutMods
Ancestors
  exprBodyPreProps vyperTypeInvariants vyperTypeSystem vyperInterpreter vyperCreate
  vyperAST vyperState vyperValue vfmState list
  exprLowering exprLoweringProps builtinCreate compileEnv
  gasShadow gasShadowState gasShadowCompile gasShadowCompileHelpers
  gasShadowCompileStmtHelpers gasShadowCompileBuiltinCreate
  fragExec externalEntryShape exprSimSend
Libs pairLib

Theorem create_copy_args_mods:
  expr_body_pre_mods mods cenv cx env
    (Call ann (CreateTarget CreateCopyOf salted rof ks) args dflt) es ==>
  ann = BaseT AddressT /\
  ?target amount salts.
    args = target :: amount :: salts /\
    expr_type target = BaseT AddressT /\
    expr_type amount = BaseT (UintT 256) /\
    (if salted then
       ?salt. salts = [salt] /\ expr_type salt = BaseT (BytesT (Fixed 32))
     else salts = []) /\
    LENGTH salts = (if salted then 1 else 0)
Proof
  disch_then (mp_tac o MATCH_MP expr_body_pre_mods_well_typed) >>
  Cases_on `salted` >>
  simp[Once well_typed_expr_def, create_arg_types_ok_def, MAP_EQ_CONS] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem create_copy_operand_order[local]:
  create_operand_order CreateCopyOf salted args = args
Proof
  Cases_on `args` >> simp[create_operand_order_def]
QED

Theorem create_copy_eval_read_mods:
  bind (eval_expr cx (Call ann (CreateTarget CreateCopyOf salted rof ks) args dflt))
    (read_result cx) =
  bind (eval_exprs cx args)
    (\values. bind (eval_create_operands cx CreateCopyOf salted rof
       (MAP expr_type args) (blueprint_literal_offset cx salted args) values)
       (read_result cx))
Proof
  simp[Once evaluate_def, create_copy_operand_order, bind_assoc]
QED

(* The subcall after the operands have been read, including the empty-code exit. *)
Theorem create_copy_read_prepared_mods:
  IS_SOME es.outcomes /\ dest_AddressV target = SOME addr /\
  dest_NumV amount = SOME value /\ dest_optional_salt salt = SOME sw /\
  LENGTH ts = (if IS_SOME salt then 3 else 2) /\
  code = (lookup_account addr es.accounts).code ==>
  bind (eval_create_operands cx CreateCopyOf (IS_SOME salt) rof ts off
        (target::amount::(case salt of NONE => [] | SOME v => [v])))
    (read_result cx) es =
  if code = [] then (INR (Error (RuntimeError "create source has no deployable code")),es)
  else bind (ignore_bind (check_not_static cx)
        (create_oracle_result sw value (create_copy_initcode code) rof))
    (read_result cx) es
Proof
  Cases_on `salt` >>
  simp[eval_create_operands_def, create_operand_layout_def, eval_create_def,
       dest_create_args_def, make_create_operands_def, dest_optional_num_def,
       dest_optional_salt_def, build_create_code_def] >>
  rpt strip_tac >>
  qpat_x_assum `LENGTH ts = _` mp_tac >>
  simp[LENGTH_EQ_NUM_compute] >> strip_tac >> gvs[] >>
  simp[dest_create_args_def, make_create_operands_def, dest_optional_num_def,
       dest_optional_salt_def, create_arg_ctor_types_def, build_create_code_def,
       bind_def, ignore_bind_def, lift_option_type_def, lift_option_def,
       get_accounts_def, check_def, check_not_static_def, assert_def, return_def, raise_def] >>
  Cases_on `(lookup_account addr es.accounts).code = []` >>
  Cases_on `cx.txn.is_static` >> simp[]
QED

Theorem create_copy_lower_call[local]:
  lower_value compile_expr cenv ty
    (Call ann (CreateTarget CreateCopyOf salted rof ks) args dflt) =
  compile_create_call compile_expr cenv CreateCopyOf salted rof args
Proof
  simp[FUN_EQ_THM, lower_value_def, compile_expr_call, compile_call_def,
       as_stack_val_def, unwrap_value_def, comp_bind_def, comp_return_def] >>
  gen_tac >>
  Cases_on `compile_create_call compile_expr cenv CreateCopyOf salted rof args x` >>
  simp[as_stack_val_def, unwrap_value_def, comp_return_def]
QED

(* Expose the sequencing once; shadow states are paired by transport below. *)
Theorem create_copy_lower_sequence[local]:
  LENGTH salts = (if salted then 1 else 0) ==>
  lower_value compile_expr cenv ty
    (Call ann (CreateTarget CreateCopyOf salted rof ks)
      (target::amount::salts) dflt) =
  comp_bind (lower_value compile_expr cenv (expr_type target) target) (\x.
  comp_bind (lower_value compile_expr cenv (expr_type amount) amount) (\y.
  comp_bind (compile_create_salt compile_expr cenv
      (if salted then SOME (HD salts) else NONE)) (\sop.
    compile_create_copy x y sop rof)))
Proof
  simp[create_copy_lower_call, compile_create_call_def]
QED

Theorem create_copy_compile_parts[local]:
  LENGTH salts = (if salted then 1 else 0) /\
  lower_value compile_expr cenv ty
    (Call ann (CreateTarget CreateCopyOf salted rof ks)
      (target::amount::salts) dflt) sa = (result,sb) ==>
  ?x y sop a b c.
    lower_value compile_expr cenv (expr_type target) target sa = (x,a) /\
    lower_value compile_expr cenv (expr_type amount) amount a = (y,b) /\
    compile_create_salt compile_expr cenv
      (if salted then SOME (HD salts) else NONE) b = (sop,c) /\
    compile_create_copy x y sop rof c = (result,sb)
Proof
  strip_tac >> drule create_copy_lower_sequence >>
  disch_then (fn th => fs[th, comp_bind_def]) >>
  qpat_x_assum `_ = (result,sb)` mp_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem create_copy_shadow_result[local]:
  gas_shadow_compiles f g ==> f s = (op,u) /\ gas_shadow_state s h ==>
  ?hu. g h = (op,hu) /\ gas_shadow_state u hu
Proof
  rewrite_tac[gas_shadow_compiles_def] >> strip_tac >> strip_tac >>
  first_x_assum drule >> Cases_on `g h` >> simp[]
QED

Theorem create_copy_shadow_salt[local]:
  gas_shadow_compiles (compile_create_salt compile_expr cenv salt)
    (compile_create_salt compile_expr (gas_shadow_env T cenv)
       (OPTION_MAP gas_shadow_expr salt))
Proof
  mp_tac (MATCH_MP gas_shadow_compiles_create_salt
    (cj 1 gas_shadow_compile_expr_env) |>
    Q.INST [`sd` |-> `T`, `sh` |-> `T`, `salt_e` |-> `salt`]) >>
  simp[]
QED

Theorem create_copy_compile_cuts[local]:
  gas_shadow_state sa sha /\
  lower_value compile_expr cenv ty
    (Call ann (CreateTarget CreateCopyOf salted rof ks)
      (target::amount::salts) dflt) sa = (result,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann (CreateTarget CreateCopyOf salted rof ks)
      (target::amount::salts) dflt)) sha = (result,shb) /\
  LENGTH salts = (if salted then 1 else 0) ==>
  ?x y sop a b c ha hb hc.
    lower_value compile_expr cenv (expr_type target) target sa = (x,a) /\
    lower_value compile_expr cenv (expr_type amount) amount a = (y,b) /\
    compile_create_salt compile_expr cenv
      (if salted then SOME (HD salts) else NONE) b = (sop,c) /\
    compile_create_copy x y sop rof c = (result,sb) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type target)
      (gas_shadow_expr target) sha = (x,ha) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type amount)
      (gas_shadow_expr amount) ha = (y,hb) /\
    compile_create_salt compile_expr (gas_shadow_env T cenv)
      (OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)) hb = (sop,hc) /\
    compile_create_copy x y sop rof hc = (result,shb) /\
    gas_shadow_state a ha /\ gas_shadow_state b hb /\ gas_shadow_state c hc
Proof
  strip_tac >> drule_all create_copy_compile_parts >> strip_tac >>
  qpat_assum `lower_value _ _ _ target sa = _`
    (mp_then Any (drule_then (qx_choose_then `ha` strip_assume_tac))
       (MATCH_MP create_copy_shadow_result
          (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env))) >>
  qpat_assum `lower_value _ _ _ amount a = _`
    (mp_then Any (drule_then (qx_choose_then `hb` strip_assume_tac))
       (MATCH_MP create_copy_shadow_result
          (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env))) >>
  qpat_assum `compile_create_salt _ _ _ b = _`
    (mp_then Any (drule_then (qx_choose_then `hc` strip_assume_tac))
       (MATCH_MP create_copy_shadow_result create_copy_shadow_salt)) >>
  `compile_create_copy x y sop rof hc = (result,shb)` by
    (`LENGTH (MAP gas_shadow_expr salts) = (if salted then 1 else 0)` by simp[] >>
     `(if salted then SOME (HD (MAP gas_shadow_expr salts)) else NONE) =
        OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)` by
       (Cases_on `salted` >> Cases_on `salts` >> gvs[]) >>
     fs[Once gas_shadow_expr_def, create_copy_lower_sequence,
        comp_bind_def, gas_shadow_expr_type]) >>
  qexistsl [`x`,`y`,`sop`,`a`,`b`,`c`,`ha`,`hb`,`hc`] >> simp[]
QED

Theorem create_copy_cut_code[local]:
  lower_value compile_expr cenv ty e sa = (x,a) /\
  lower_value compile_expr cenv ty' e' a = (y,b) /\
  compile_create_salt compile_expr cenv salt b = (sop,c) /\
  compile_create_copy x y sop rof c = (out,sb) /\
  fn_has_code sa sb fn ==>
  ci_mono sa a /\ ci_mono a b /\ ci_mono b c /\ cs_extends c sb /\
  fn_has_code sa a fn /\ fn_has_code a b fn /\ fn_has_code b c fn /\ fn_has_code c sb fn
Proof
  strip_tac >>
  `ci_mono sa a` by metis_tac[ci_mono_lower_value_compile_expr, pairTheory.SND] >>
  `ci_mono a b` by metis_tac[ci_mono_lower_value_compile_expr, pairTheory.SND] >>
  `ci_mono b c` by metis_tac[ci_mono_compile_create_salt, cj 1 compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends c sb` by metis_tac[compile_create_copy_labels, pairTheory.SND] >>
  `cs_extends sa a /\ cs_extends a b /\ cs_extends b c` by fs[ci_mono_def] >>
  `cs_extends b sb` by metis_tac[cs_extends_trans] >>
  `cs_extends a sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa a fn /\ fn_has_code a sb fn` by metis_tac[fn_has_code_split] >>
  `fn_has_code a b fn /\ fn_has_code b sb fn` by metis_tac[fn_has_code_split] >>
  simp[] >> metis_tac[fn_has_code_split]
QED

Theorem create_copy_layout_mods:
  expr_body_pre_mods mods cenv cx env
    (Call ann (CreateTarget CreateCopyOf salted rof ks) args dflt) es /\
  lower_value compile_expr cenv ty
    (Call ann (CreateTarget CreateCopyOf salted rof ks) args dflt) sa = (result,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann (CreateTarget CreateCopyOf salted rof ks) args dflt))
      sha = (result,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb fn /\ fn_has_code sha shb hfn ==>
  ann = BaseT AddressT /\
  ?target amount salts x y sop a b c ha hb hc.
    args = target :: amount :: salts /\
    expr_type target = BaseT AddressT /\ expr_type amount = BaseT (UintT 256) /\
    (if salted then
       ?salt. salts = [salt] /\ expr_type salt = BaseT (BytesT (Fixed 32))
     else salts = []) /\
    LENGTH salts = (if salted then 1 else 0) /\
    create_operand_order CreateCopyOf salted args = target :: amount :: salts /\
    lower_value compile_expr cenv (expr_type target) target sa = (x,a) /\
    lower_value compile_expr cenv (expr_type amount) amount a = (y,b) /\
    compile_create_salt compile_expr cenv
      (if salted then SOME (HD salts) else NONE) b = (sop,c) /\
    compile_create_copy x y sop rof c = (result,sb) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type target)
      (gas_shadow_expr target) sha = (x,ha) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type amount)
      (gas_shadow_expr amount) ha = (y,hb) /\
    compile_create_salt compile_expr (gas_shadow_env T cenv)
      (OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)) hb = (sop,hc) /\
    compile_create_copy x y sop rof hc = (result,shb) /\
    gas_shadow_state a ha /\ gas_shadow_state b hb /\ gas_shadow_state c hc /\
    ci_mono sa a /\ ci_mono a b /\ ci_mono b c /\ cs_extends c sb /\
    ci_mono sha ha /\ ci_mono ha hb /\ ci_mono hb hc /\ cs_extends hc shb /\
    fn_has_code sa a fn /\ fn_has_code a b fn /\ fn_has_code b c fn /\ fn_has_code c sb fn /\
    fn_has_code sha ha hfn /\ fn_has_code ha hb hfn /\
    fn_has_code hb hc hfn /\ fn_has_code hc shb hfn
Proof
  strip_tac >> drule_then strip_assume_tac create_copy_args_mods >> gvs[] >>
  drule_all create_copy_compile_cuts >> strip_tac >>
  qpat_assum `lower_value _ _ _ target sa = _`
    (mp_then Any (drule_all_then strip_assume_tac) create_copy_cut_code) >>
  qpat_assum `fn_has_code sha shb hfn`
    (mp_then Any (drule_all_then strip_assume_tac) create_copy_cut_code) >>
  qexistsl [`x`,`y`,`sop`,`a`,`b`,`c`,`ha`,`hb`,`hc`] >>
  gs[create_copy_operand_order]
QED
