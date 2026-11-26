Theory bodyCreateProxyLayoutMods
Ancestors
  exprBodyPreProps vyperCreate vyperInterpreter vyperTypeSystem
  exprLowering exprLoweringProps builtinCreate compileEnv fragExec
  gasShadowCompileStmtHelpers gasShadowCompileBuiltinCreate gasShadowState
  externalEntryShape vyperState gasShadow gasShadowCompile
  gasShadowCompileHelpers words vyperAST codegenRel
Libs
  pairLib

Theorem create_proxy_args_mods:
  expr_body_pre_mods mods cenv cx env
    (Call ann (CreateTarget CreateMinimalProxy salted rof ks) args dflt) es ==>
  ann = BaseT AddressT /\
  ?target amount salts.
    args = target::amount::salts /\
    expr_type target = BaseT AddressT /\
    expr_type amount = BaseT (UintT 256) /\
    (if salted then
       ?salt. salts = [salt] /\ expr_type salt = BaseT (BytesT (Fixed 32))
     else salts = [])
Proof
  disch_then (mp_tac o MATCH_MP expr_body_pre_mods_well_typed) >>
  Cases_on `salted` >>
  simp[Once well_typed_expr_def, create_arg_types_ok_def, listTheory.MAP_EQ_CONS] >>
  metis_tac[]
QED

Theorem create_proxy_read_order_mods:
  create_operand_order CreateMinimalProxy salted args = args /\
  bind (eval_expr cx (Call ann (CreateTarget CreateMinimalProxy salted rof ks) args dflt))
       (read_result cx) =
  bind (eval_exprs cx args)
       (\values. bind (eval_create_operands cx CreateMinimalProxy salted rof
                         (MAP expr_type args) (blueprint_literal_offset cx salted args) values)
                     (read_result cx))
Proof
  Cases_on `args` >> simp[Once evaluate_def, create_operand_order_def, bind_assoc] >>
  rename1 `create_operand_order _ _ (_::rest)` >>
  Cases_on `rest` >> simp[create_operand_order_def]
QED

Theorem proxy_lower_call[local]:
  lower_value compile_expr cenv ty
    (Call ann (CreateTarget CreateMinimalProxy salted rof ks) args dflt) =
  compile_create_call compile_expr cenv CreateMinimalProxy salted rof args
Proof
  simp[FUN_EQ_THM, lower_value_def, comp_bind_def] >> gen_tac >>
  simp[exprSimSendTheory.compile_expr_call, compile_call_def] >>
  Cases_on `compile_create_call compile_expr cenv CreateMinimalProxy salted rof args x` >>
  simp[as_stack_val_def, unwrap_value_def, comp_bind_def, comp_return_def]
QED

(* A single decomposition equation serves both compilation environments. *)
Theorem proxy_lower_layout[local]:
  LENGTH salts = (if salted then 1 else 0) ==>
  lower_value compile_expr cenv ty
    (Call ann (CreateTarget CreateMinimalProxy salted rof ks) (target::amount::salts) dflt) =
  comp_bind (lower_value compile_expr cenv (expr_type target) target) (\x.
    comp_bind (lower_value compile_expr cenv (expr_type amount) amount) (\y.
      comp_bind (compile_create_proxy_buf x) (\buf.
        comp_bind (compile_create_salt compile_expr cenv
          (if salted then SOME (HD salts) else NONE)) (\sop.
            compile_create_dispatch buf (Lit 54w) y sop rof))))
Proof
  strip_tac >> simp[proxy_lower_call, compile_create_call_def]
QED

Theorem proxy_compile_parts[local]:
  LENGTH salts = (if salted then 1 else 0) /\
  lower_value compile_expr cenv ty
    (Call ann (CreateTarget CreateMinimalProxy salted rof ks) (target::amount::salts) dflt)
    sa = (result,sb) ==>
  ?x y buf sop a b c d.
    lower_value compile_expr cenv (expr_type target) target sa = (x,a) /\
    lower_value compile_expr cenv (expr_type amount) amount a = (y,b) /\
    compile_create_proxy_buf x b = (buf,c) /\
    compile_create_salt compile_expr cenv
      (if salted then SOME (HD salts) else NONE) c = (sop,d) /\
    compile_create_dispatch buf (Lit 54w) y sop rof d = (result,sb)
Proof
  strip_tac >> qpat_x_assum `lower_value _ _ _ (Call _ _ _ _) _ = _` mp_tac >>
  simp[proxy_lower_layout, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem proxy_shadow_result[local]:
  gas_shadow_compiles f g ==>
  gas_shadow_state s sh /\ f s = (x,t) ==>
  ?th. g sh = (x,th) /\ gas_shadow_state t th
Proof
  rw[gas_shadow_compiles_def] >>
  qpat_x_assum `!s t. _` drule >> simp[] >>
  Cases_on `g sh` >> simp[]
QED

Theorem proxy_shadow_salt[local]:
  gas_shadow_compiles (compile_create_salt compile_expr cenv salt)
    (compile_create_salt compile_expr (gas_shadow_env T cenv) (OPTION_MAP gas_shadow_expr salt))
Proof
  mp_tac (MATCH_MP gasShadowCompileHelpersTheory.gas_shadow_compiles_create_salt
    (cj 1 gasShadowCompileTheory.gas_shadow_compile_expr_env) |>
    Q.INST [`sd` |-> `T`, `sh` |-> `T`, `salt_e` |-> `salt`]) >>
  simp[]
QED

Theorem proxy_interval_code[local]:
  lower_value compile_expr cenv ty e sa = (x,a) /\
  lower_value compile_expr cenv ty' e' a = (y,b) /\
  compile_create_proxy_buf x b = (buf,c) /\
  compile_create_salt compile_expr cenv salt c = (sop,d) /\
  compile_create_dispatch buf (Lit 54w) y sop rof d = (out,sb) /\
  fn_has_code sa sb fn ==>
  ci_mono sa a /\ ci_mono a b /\ ci_mono b c /\ ci_mono c d /\
  fn_has_code sa a fn /\ fn_has_code a b fn /\ fn_has_code b c fn /\
  fn_has_code c d fn /\ fn_has_code d sb fn
Proof
  strip_tac >>
  `ci_mono sa a` by metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND] >>
  `ci_mono a b` by metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND] >>
  `ci_mono b c` by metis_tac[ci_mono_compile_create_proxy_buf,pairTheory.SND] >>
  `ci_mono c d` by metis_tac[ci_mono_compile_create_salt,compile_expr_ci_mono,pairTheory.SND] >>
  `cs_extends d sb` by
    metis_tac[compile_create_dispatch_labels,pairTheory.SND] >>
  simp[] >> fs[ci_mono_def] >>
  `cs_extends c sb` by metis_tac[cs_extends_trans] >>
  `cs_extends b sb` by metis_tac[cs_extends_trans] >>
  `cs_extends a sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa a fn /\ fn_has_code a sb fn` by metis_tac[fn_has_code_split] >>
  `fn_has_code a b fn /\ fn_has_code b sb fn` by metis_tac[fn_has_code_split] >>
  `fn_has_code b c fn /\ fn_has_code c sb fn` by metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED

Theorem create_proxy_layout_mods:
  expr_body_pre_mods mods cenv cx env
    (Call ann (CreateTarget CreateMinimalProxy salted rof ks) args dflt) es /\
  lower_value compile_expr cenv ty
    (Call ann (CreateTarget CreateMinimalProxy salted rof ks) args dflt) sa = (result,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Call ann (CreateTarget CreateMinimalProxy salted rof ks) args dflt))
    sha = (result,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shfunc ==>
  ann = BaseT AddressT /\
  create_operand_order CreateMinimalProxy salted args = args /\
  ?target amount salts x y buf sop a b c d ah bh ch dh.
    args = target::amount::salts /\
    expr_type target = BaseT AddressT /\ expr_type amount = BaseT (UintT 256) /\
    (if salted then
       ?salt. salts = [salt] /\ expr_type salt = BaseT (BytesT (Fixed 32))
     else salts = []) /\
    lower_value compile_expr cenv (expr_type target) target sa = (x,a) /\
    lower_value compile_expr cenv (expr_type amount) amount a = (y,b) /\
    compile_create_proxy_buf x b = (buf,c) /\
    compile_create_salt compile_expr cenv
      (if salted then SOME (HD salts) else NONE) c = (sop,d) /\
    compile_create_dispatch buf (Lit 54w) y sop rof d = (result,sb) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type target)
      (gas_shadow_expr target) sha = (x,ah) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type amount)
      (gas_shadow_expr amount) ah = (y,bh) /\
    compile_create_proxy_buf x bh = (buf,ch) /\
    compile_create_salt compile_expr (gas_shadow_env T cenv)
      (OPTION_MAP gas_shadow_expr (if salted then SOME (HD salts) else NONE)) ch = (sop,dh) /\
    compile_create_dispatch buf (Lit 54w) y sop rof dh = (result,shb) /\
    gas_shadow_state a ah /\ gas_shadow_state b bh /\
    gas_shadow_state c ch /\ gas_shadow_state d dh /\ gas_shadow_state sb shb /\
    ci_mono sa a /\ ci_mono a b /\ ci_mono b c /\ ci_mono c d /\
    ci_mono sha ah /\ ci_mono ah bh /\ ci_mono bh ch /\ ci_mono ch dh /\
    fn_has_code sa a func /\ fn_has_code a b func /\ fn_has_code b c func /\
    fn_has_code c d func /\ fn_has_code d sb func /\
    fn_has_code sha ah shfunc /\ fn_has_code ah bh shfunc /\
    fn_has_code bh ch shfunc /\ fn_has_code ch dh shfunc /\ fn_has_code dh shb shfunc
Proof
  strip_tac >> drule_then strip_assume_tac create_proxy_args_mods >> gvs[] >>
  `LENGTH salts = (if salted then 1 else 0)` by (Cases_on `salted` >> gvs[]) >>
  drule_all_then strip_assume_tac proxy_compile_parts >>
  qpat_assum `lower_value compile_expr _ _ target sa = _`
    (mp_then Any (drule_all_then strip_assume_tac)
       (MATCH_MP proxy_shadow_result (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env))) >>
  qpat_assum `lower_value compile_expr _ _ amount a = _`
    (mp_then Any (drule_all_then strip_assume_tac)
       (MATCH_MP proxy_shadow_result (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env))) >>
  drule_all_then strip_assume_tac
    (MATCH_MP proxy_shadow_result gas_shadow_compiles_create_proxy_buf) >>
  drule_all_then strip_assume_tac (MATCH_MP proxy_shadow_result proxy_shadow_salt) >>
  drule_all_then strip_assume_tac
    (MATCH_MP proxy_shadow_result gas_shadow_compiles_create_dispatch) >>
  rename1 `compile_create_dispatch buf (Lit 54w) y sop rof dh = (result,z)` >>
  `z = shb` by
    (qpat_x_assum `lower_value compile_expr _ _ (gas_shadow_expr _) _ = (result,shb)` mp_tac >>
     simp[Once gas_shadow_expr_def, proxy_lower_layout,
          gas_shadow_expr_type, comp_bind_def] >>
     Cases_on `salted` >> gvs[]) >>
  qpat_x_assum `z = shb` SUBST_ALL_TAC >>
  qpat_assum `lower_value compile_expr cenv _ target sa = _`
    (mp_then Any (drule_all_then strip_assume_tac) proxy_interval_code) >>
  qpat_assum `lower_value compile_expr _ _ (gas_shadow_expr target) sha = _`
    (mp_then Any (drule_all_then strip_assume_tac) proxy_interval_code) >>
  rename1 `gas_shadow_state a ah` >>
  rename1 `gas_shadow_state b bh` >>
  rename1 `gas_shadow_state c ch` >>
  simp[create_operand_order_def] >>
  qexistsl [`x`,`y`,`buf`,`sop`,`a`,`b`,`c`,`d`,`ah`,`bh`,`ch`,`dh`] >>
  gvs[]
QED
