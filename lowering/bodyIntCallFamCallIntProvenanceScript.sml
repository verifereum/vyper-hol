(* Syntactic annotation provenance, independent of semantic post-value types. *)
Theory bodyIntCallFamCallIntProvenance
Ancestors
  bodyIntCallFamCallIntTags supportedExprs exprCallBounds exprLowering context

Theorem intcall_builtin_dispatch_tag[local]:
  vv_type (FST (compile_builtin_dispatch ce ann ty bi args st)) = ann
Proof
  once_rewrite_tac[compile_expr_raw_def] >> simp[intcall_builtin_tag]
QED

Theorem intcall_type_dispatch_tag[local]:
  vv_type (FST (compile_type_builtin_dispatch ce ann ty tb target args st)) = ann
Proof
  once_rewrite_tac[compile_expr_raw_def] >> simp[intcall_type_builtin_tag]
QED

Theorem intcall_builtin_callback_tag[local]:
  vv_type (FST (builtin_child_callback n compile_builtin_dispatch ce ann ty bi args st)) = ann
Proof
  simp[builtin_child_callback_def] >> IF_CASES_TAC >>
  simp[intcall_builtin_dispatch_tag, invalid_expr_call_def,
       pairTheory.ELIM_UNCURRY, vv_type_def]
QED

Theorem intcall_builtin_two_tag[local]:
  (!a t b xs s. vv_type (FST (bcb ce a t b xs s)) = a) ==>
  vv_type (FST (compile_expr_body cb bcb tcb ce ty
    (Builtin ann bi [x;y]) st)) = ann
Proof
  strip_tac >> Cases_on `x`
  >~ [`[Name a nm; y]`] >- (
    Cases_on `y` >> Cases_on `bi` >>
    simp[vyperASTTheory.expr_type_def, compile_expr_body_def, intcall_powmod_names_tag]) >>
  simp[vyperASTTheory.expr_type_def, compile_expr_body_def]
QED

Theorem intcall_builtin_three_tag[local]:
  (!a t b xs s. vv_type (FST (bcb ce a t b xs s)) = a) ==>
  vv_type (FST (compile_expr_body cb bcb tcb ce ty
    (Builtin ann bi [x;y;z]) st)) = ann
Proof
  strip_tac >> Cases_on `x`
  >~ [`[Name a nm; y; z]`] >- (
    Cases_on `y`
    >~ [`[Name a nm; Name b nn; z]`] >- (
      Cases_on `z` >> Cases_on `bi` >>
      simp[vyperASTTheory.expr_type_def, compile_expr_body_def, intcall_addmod_names_tag,
           intcall_mulmod_names_tag]) >>
    simp[vyperASTTheory.expr_type_def, compile_expr_body_def]) >>
  simp[vyperASTTheory.expr_type_def, compile_expr_body_def]
QED

Theorem intcall_builtin_outer_tag[local]:
  (!a t b xs s. vv_type (FST (bcb ce a t b xs s)) = a) ==>
  vv_type (FST (compile_expr_body cb bcb tcb ce ty
    (Builtin ann bi args) st)) = ann
Proof
  strip_tac >> Cases_on `args` >- simp[vyperASTTheory.expr_type_def, compile_expr_body_def] >>
  rename1 `x::xs` >> Cases_on `xs`
  >- (Cases_on `x` >> simp[vyperASTTheory.expr_type_def, compile_expr_body_def]) >>
  rename1 `x::y::ys` >> Cases_on `ys`
  >- (irule intcall_builtin_two_tag >> simp[]) >>
  rename1 `x::y::z::zs` >> Cases_on `zs`
  >- (irule intcall_builtin_three_tag >> simp[]) >>
  rename1 `x::y::z::w::rest` >>
  Cases_on `x`
  >~ [`Name a nm::y::z::w::rest`] >- (
    Cases_on `y`
    >~ [`Name a nm::Name b nn::z::w::rest`] >- (
      Cases_on `z` >> simp[vyperASTTheory.expr_type_def, compile_expr_body_def]) >>
    simp[vyperASTTheory.expr_type_def, compile_expr_body_def]) >>
  simp[vyperASTTheory.expr_type_def, compile_expr_body_def]
QED

Theorem intcall_pure_expr_tag:
  supported_pure_expr tops e /\ compile_expr ce ty e c = (vv,d) ==>
  vv_type vv = expr_type e
Proof
  strip_tac >>
  `vv_type (FST (compile_expr ce ty e c)) = expr_type e` suffices_by simp[] >>
  once_rewrite_tac[compile_expr_raw_def] >>
  Cases_on `e` >>
  fs[supported_pure_expr_def]
  >~ [`compile_expr_body _ _ _ _ _ (Builtin _ _ _) _`] >- (
    simp[vyperASTTheory.expr_type_def] >>
    irule intcall_builtin_outer_tag >> rpt gen_tac >>
    simp[builtin_child_callback_def] >> IF_CASES_TAC >> simp[intcall_builtin_dispatch_tag,
      invalid_expr_call_def, pairTheory.ELIM_UNCURRY, vv_type_def]) >>
  simp[vyperASTTheory.expr_type_def, compile_expr_body_def, intcall_literal_tag, intcall_name_tag,
       intcall_attribute_tag, intcall_subscript_tag,
       pairTheory.ELIM_UNCURRY, vv_type_def] 
  >~ [`FLOOKUP ce.ce_module_vars`] >- (
    rpt (BasicProvers.TOP_CASE_TAC >> simp[vv_type_def]))
  >~ [`FLOOKUP ce.ce_module_vars`] >- (
    rpt (BasicProvers.TOP_CASE_TAC >> simp[vv_type_def]))
  >~ [`is_word_type`] >- (IF_CASES_TAC >> simp[vv_type_def])
  >~ [`compile_type_builtin_dispatch`] >- (
    simp[intcall_type_dispatch_tag,
      invalid_expr_call_def, pairTheory.ELIM_UNCURRY, vv_type_def])
QED

Theorem intcall_pure_multi_vvs_tags:
  !es c vs d.
    supported_pure_exprs tops es /\
    compile_multi_vvs compile_expr ce es c = (vs,d) ==>
    MAP vv_type vs = MAP expr_type es
Proof
  Induct_on `es` >>
  simp[compile_multi_vvs_def, compileEnvTheory.comp_return_def,
       compileEnvTheory.comp_bind_def, supported_pure_expr_def]
  >> rpt gen_tac >> pairarg_tac >> pairarg_tac >>
  strip_tac >>
  rename1 `compile_expr ce (expr_type h) h c = (vv,b)` >>
  Cases_on `compile_multi_vvs compile_expr ce es b` >> gvs[] >> conj_tac
  >- (drule_all intcall_pure_expr_tag >> simp[]) >>
  first_x_assum irule >> goal_assum drule
QED
