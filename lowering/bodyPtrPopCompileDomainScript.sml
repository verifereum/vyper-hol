Theory bodyPtrPopCompileDomain
Ancestors supportedExprs supportedExprForms list pair

(* Shared callback domain for the three open compiler contracts. Place
   traversal admits annotations excluded by supported_expr, so consumers need
   this union rather than an invalid place-to-supported_expr coercion. *)
Definition pop_compile_domain_def:
  pop_compile_domain tops e <=>
    supported_pure_expr tops e \/ supported_effect_expr tops e \/
    supported_place_expr tops e \/ supported_effect_place_expr tops e
End

Theorem pop_domain_pure:
  supported_pure_expr tops e ==> pop_compile_domain tops e
Proof
  simp[pop_compile_domain_def]
QED

Theorem pop_domain_effect:
  supported_effect_expr tops e ==> pop_compile_domain tops e
Proof
  simp[pop_compile_domain_def]
QED

Theorem pop_domain_place:
  supported_place_expr tops e ==> pop_compile_domain tops e
Proof
  simp[pop_compile_domain_def]
QED

Theorem pop_domain_effect_place:
  supported_effect_place_expr tops e ==> pop_compile_domain tops e
Proof
  simp[pop_compile_domain_def]
QED

Theorem pop_domain_supported:
  supportedExprs$supported_expr tops e ==> pop_compile_domain tops e
Proof
  simp[supportedExprsTheory.supported_expr_def, pop_compile_domain_def] >> metis_tac[]
QED

Theorem pop_domain_subscript_children:
  pop_compile_domain tops (Subscript ty base_e key) ==>
  pop_compile_domain tops base_e /\ pop_compile_domain tops key
Proof
  simp[pop_compile_domain_def, supported_pure_expr_def, supported_effect_expr_def] >>
  metis_tac[]
QED

Theorem pop_domain_attribute_child:
  pop_compile_domain tops (Attribute ty base_e fld) ==> pop_compile_domain tops base_e
Proof
  simp[pop_compile_domain_def, supported_pure_expr_def, supported_effect_expr_def] >>
  metis_tac[]
QED

Theorem pop_domain_ifexp_children:
  pop_compile_domain tops (IfExp ty cond a b) ==>
  pop_compile_domain tops cond /\ pop_compile_domain tops a /\ pop_compile_domain tops b
Proof
  simp[pop_compile_domain_def, supported_pure_expr_def, supported_effect_expr_def] >>
  metis_tac[]
QED

Theorem pop_domain_struct_fields:
  pop_compile_domain tops (StructLit ty id fields) ==>
  EVERY (supported_pure_expr tops o SND) fields
Proof
  simp[pop_compile_domain_def, supported_pure_expr_def, supported_effect_expr_def,
       GSYM supported_pure_fields_every]
QED

Theorem pop_domain_builtin_form:
  pop_compile_domain tops (Builtin ty bi args) ==>
  supported_builtin_form tops ty bi args /\ EVERY (supported_pure_expr tops) args
Proof
  simp[pop_compile_domain_def, supported_pure_expr_def, supported_effect_expr_def,
       GSYM supported_pure_exprs_every]
QED

Theorem pop_domain_type_builtin_form:
  pop_compile_domain tops (TypeBuiltin ty tb rt args) ==>
  supported_type_builtin_form tops ty tb rt args /\ EVERY (supported_pure_expr tops) args
Proof
  simp[pop_compile_domain_def, supported_pure_expr_def, supported_effect_expr_def,
       GSYM supported_pure_exprs_every]
QED

Theorem pop_domain_pop_target:
  pop_compile_domain tops (Pop ty bt) ==>
  ?id. bt = TopLevelNameTarget id /\ supported_storage_dynamic_array tops id
Proof
  Cases_on `bt` >>
  simp[pop_compile_domain_def, supported_pure_expr_def, supported_effect_expr_def]
QED

Theorem pop_domain_call_support:
  pop_compile_domain tops (Call ty target args default_ret) ==>
  supported_effect_expr tops (Call ty target args default_ret)
Proof
  simp[pop_compile_domain_def, supported_pure_expr_def, supported_effect_expr_def]
QED

Theorem pop_domain_pure_argument:
  EVERY (supported_pure_expr tops) args /\ MEM a args ==> pop_compile_domain tops a
Proof
  simp[EVERY_MEM] >> metis_tac[pop_domain_pure]
QED

Theorem pop_domain_struct_child:
  pop_compile_domain tops (StructLit ty id fields) /\ MEM (fname,a) fields ==>
  pop_compile_domain tops a
Proof
  strip_tac >> drule pop_domain_struct_fields >>
  simp[EVERY_MEM] >> metis_tac[pop_domain_pure, SND]
QED

Theorem pop_domain_call_default:
  pop_compile_domain tops (Call ty target args default_ret) ==> default_ret = NONE
Proof
  Cases_on `default_ret` >> simp[] >> strip_tac >>
  drule pop_domain_call_support >>
  metis_tac[supported_call_default_rejected, supportedExprsTheory.supported_expr_def]
QED

Theorem pop_domain_call_args:
  pop_compile_domain tops (Call ty target args default_ret) ==>
  EVERY (supported_pure_expr tops) args
Proof
  strip_tac >>
  `default_ret = NONE` by metis_tac[pop_domain_call_default] >> gvs[] >>
  drule pop_domain_call_support >> Cases_on `target` >>
  simp[supported_effect_expr_def, supported_pure_exprs_every]
  >- (PairCases_on `p` >> simp[supported_effect_expr_def, supported_pure_exprs_every]) >>
  Cases_on `b`
  >- (namedCases_on `args` ["", "a xs"] >> simp[supported_effect_expr_def] >>
      namedCases_on `xs` ["", "v ys"] >> simp[supported_effect_expr_def] >>
      namedCases_on `ys` ["", "g zs"] >> simp[supported_effect_expr_def] >>
      Cases_on `zs` >> Cases_on `ty` >> simp[supported_effect_expr_def]) >>
  namedCases_on `args` ["", "a xs"] >> simp[supported_effect_expr_def] >>
  namedCases_on `xs` ["", "v ys"] >> simp[supported_effect_expr_def] >>
  Cases_on `ys` >> Cases_on `ty` >> simp[supported_effect_expr_def] >>
  simp[oneline supported_effect_expr_def] >> Cases_on `t` >> simp[]
QED
