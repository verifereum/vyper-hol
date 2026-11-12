Theory runtimeSymSrcBuiltinBody
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission supportedTypes
  runtimeSymSrcInterfaces exprCallBounds list supportedExprTraverse exprLowering
  supportedExprs supportedExprForms context compileEnv venomInst vyperAST
  memoryValueDefs typedCopyDomain builtinMisc builtinBytes builtinSimple

Theorem runtime_sym_builtin_child:
  (!e ty. expr_size e < list_size expr_size args ==>
     runtime_sym_expr_contract tops cfn ce ty e) /\
  EVERY (supported_pure_expr tops) args /\
  ~supported_exprs_exists is_self_code args /\ MEM e args ==>
  (!ty. runtime_sym_expr_contract tops cfn ce ty e) /\
  supported_expr tops e /\ ~supported_expr_exists is_self_code e
Proof
  rpt strip_tac
  >- (first_x_assum irule >> metis_tac[expr_list_member_bound])
  >- metis_tac[runtime_sym_supported_argument]
  >> gvs[supported_exprs_exists_every, EVERY_MEM]
QED

Theorem runtime_sym_builtin_env[local]:
  runtime_sym_generator_contracts tops ==>
  runtime_sym_builtin_contract tops (compile_builtin_dispatch_body cfn) ce rt ty (Env item) args
Proof
  strip_tac >> drule runtime_sym_generators_expr_primitive >>
  disch_then (assume_tac o cj 2 o SRULE [runtime_sym_expr_primitive_clauses_def]) >>
  pure_rewrite_tac[runtime_sym_builtin_contract_def] >> rpt strip_tac >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_builtin_dispatch_body_def, as_stack_val_def] >>
  Cases_on `compile_env_var item s` >>
  simp[NoAsms, as_stack_val_def] >> strip_tac >> gvs[] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  simp[runtime_sym_value_def]
QED
Theorem runtime_sym_builtin_lower_value:
  runtime_sym_generator_contracts tops /\
  (!e t. expr_size e < list_size expr_size args ==>
     runtime_sym_expr_contract tops cfn ce t e) /\
  runtime_sym_env ce /\ EVERY (supported_pure_expr tops) args /\
  ~supported_exprs_exists is_self_code args ==>
  !e t s op s'. MEM e args /\ EVERY runtime_sym_inst (state_insts s) /\
    lower_value cfn ce t e s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  strip_tac >> drule runtime_sym_generators_lower_value >>
  pure_rewrite_tac[runtime_sym_lower_value_clause_def] >> strip_tac >>
  rpt strip_tac >> drule_all runtime_sym_builtin_child >> strip_tac >>
  qpat_x_assum `!cfn ce ty e s op s'. _` (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[]
QED

Theorem runtime_sym_builtin_callback[local]:
  (!e t. expr_size e < list_size expr_size args ==>
     runtime_sym_expr_contract tops cfn ce t e) /\
  runtime_sym_env ce /\ EVERY (supported_pure_expr tops) args /\
  ~supported_exprs_exists is_self_code args ==>
  !e t s v s'. MEM e args /\ EVERY runtime_sym_inst (state_insts s) /\
     cfn ce t e s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all runtime_sym_builtin_child >> strip_tac >>
  qpat_x_assum `!ty. runtime_sym_expr_contract _ _ _ _ _`
    (mp_tac o Q.SPEC `t`) >>
  pure_rewrite_tac[runtime_sym_expr_contract_def] >>
  disch_then (drule_at_then (Pat `cfn _ _ _ _ = _`) mp_tac) >> simp[]
QED

Theorem runtime_sym_binop_guards[local]:
  supported_binop bop ty rhs bl el ==>
  bop <> In /\ bop <> NotIn /\
  ~(is_bytestring_type ty /\ (bop = Eq \/ bop = NotEq))
Proof
  Cases_on `bop` >> simp[supported_binop_def] >>
  Cases_on `ty` >> simp[supported_word_type_def, is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[supported_word_type_def, is_bytestring_type_def]
QED


Theorem runtime_sym_builtin_body:
  runtime_sym_generator_contracts tops /\
  (!e t. expr_size e < list_size expr_size args ==>
     runtime_sym_expr_contract tops cfn ce t e) ==>
  runtime_sym_builtin_contract tops (compile_builtin_dispatch_body cfn) ce rt ty bi args
Proof
  strip_tac >> pure_rewrite_tac[runtime_sym_builtin_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `EVERY (supported_pure_expr tops) args /\
   ~supported_exprs_exists is_self_code args` by
    gvs[runtime_sym_builtin_domain, supported_expr_exists_def] >>
  `!e t s op s'. MEM e args /\ EVERY runtime_sym_inst (state_insts s) /\
     lower_value cfn ce t e s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op` by
    (rpt gen_tac >> strip_tac >>
     drule_all runtime_sym_builtin_lower_value >> simp[]) >>
  Cases_on `bi`
  >~ [`Bop bop`] >- suspend "bop"
  >~ [`Env item`] >- (irule (runtime_sym_builtin_env |> SRULE [runtime_sym_builtin_contract_def]) >> simp[] >> metis_tac[])
  >~ [`Neg`] >- suspend "neg"
  >~ [`Abs`] >- suspend "abs"
  >~ [`Not`] >- suspend "not"
  >~ [`Acc item`] >- suspend "acc"
  >~ [`MakeArray elem bound`] >- suspend "array"
  >~ [`AsWeiValue d`] >- suspend "wei"
  >~ [`AddMod`] >- suspend "addmod"
  >~ [`MulMod`] >- suspend "mulmod"
  >~ [`PowMod256`] >- suspend "powmod"
  >~ [`BlockHash`] >- suspend "blockhash"
  >~ [`BlobHash`] >- suspend "blobhash"
  >~ [`ECRecover`] >- suspend "ecrecover"
  >~ [`ECAdd`] >- suspend "ecadd"
  >~ [`ECMul`] >- suspend "ecmul"
  >~ [`Uint2Str n`] >- suspend "uint2str"
  >~ [`CalldataSlice n`] >- suspend "calldataslice"
  >> gvs[supported_expr_def, supported_pure_expr_def,
         supported_effect_expr_def, supported_builtin_form_def]
QED
Resume runtime_sym_builtin_body[bop]:
  drule runtime_sym_bop_selections >> strip_tac >>
  namedCases_on `args` ["", "a tail"] >> gnvs[] >>
  namedCases_on `tail` ["", "b rest"] >> gnvs[] >>
  `supported_binop bop (expr_type a) (expr_type b)
     (supported_integer_literal a) (supported_nonnegative_literal b)` by
    gvs[supported_expr_def, supported_pure_expr_def,
        supported_effect_expr_def, supported_builtin_form_def] >>
  drule runtime_sym_binop_guards >> strip_tac >>
  drule runtime_sym_generators_expr_primitive >>
  disch_then (assume_tac o cj 3 o SRULE [runtime_sym_expr_primitive_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `compile_binop bop v1 v2 (expr_type a)
    (if bop = Exp then expr_int_literal a else NONE)
    (if bop = Exp then expr_int_literal b else NONE) st2` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  `EVERY runtime_sym_inst (state_insts st1) /\ ~is_label_operand v1` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st2) /\ ~is_label_operand v2` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  simp[runtime_sym_value_def] >>
  qpat_x_assum `!bop x y ty bl el s op s'. _` (drule_at_then (Pat `compile_binop _ _ _ _ _ _ _ = _`) mp_tac) >>
  simp[]
QED
Resume runtime_sym_builtin_body[neg]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_expr_primitive >>
  disch_then (assume_tac o cj 5 o SRULE [runtime_sym_expr_primitive_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  Cases_on `compile_neg v' (expr_type a) st1` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  qpat_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!v ty s op s'. _` (drule_at_then (Pat `compile_neg _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[abs]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_simple >>
  disch_then (assume_tac o cj 1 o SRULE [runtime_sym_simple_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  Cases_on `compile_builtin_abs v' st1` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  qpat_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!v s op s'. _` (drule_at_then (Pat `compile_builtin_abs _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[not]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_expr_primitive >>
  disch_then (assume_tac o cj 4 o SRULE [runtime_sym_expr_primitive_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  qpat_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `expr_type a = BaseT BoolT` >> simp[]
  >- (Cases_on `emit_op ISZERO [v'] st1` >>
      simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
      drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
      simp[runtime_sym_value_def]) >>
  Cases_on `compile_invert v' (expr_type a) ce st1` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  qpat_assum `!ce v ty s op s'. _`
    (drule_at_then (Pat `compile_invert _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[acc]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_acc >>
  pure_rewrite_tac[runtime_sym_acc_clause_def] >> strip_tac >>
  `runtime_sym_expr_contract tops cfn ce (BaseT AddressT) a` by
    (first_x_assum irule >> simp[]) >>
  `supported_expr tops a /\ ~supported_expr_exists is_self_code a` by
    (conj_tac >- (irule runtime_sym_supported_argument >> qexists `[a]` >> simp[]) >>
     qpat_x_assum `~supported_exprs_exists _ _` mp_tac >>
     simp[supported_exprs_exists_every]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  Cases_on `compile_acc cfn ce a item s` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  qpat_x_assum `!cfn ce e item s op s'. _`
    (drule_at_then (Pat `compile_acc _ _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[array]:
  `!e t. MEM e args ==> runtime_sym_expr_contract tops cfn ce t e` by
    (rpt strip_tac >> first_x_assum irule >> metis_tac[expr_list_member_bound]) >>
  qpat_x_assum `!e t. expr_size e < _ ==> _` kall_tac >>
  qpat_x_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` kall_tac >>
  drule runtime_sym_generators_context >>
  disch_then (assume_tac o cj 3 o SRULE [runtime_sym_context_clauses_def]) >>
  drule runtime_sym_generators_make_tuple >>
  pure_rewrite_tac[runtime_sym_make_tuple_clause_def] >> strip_tac >>
  drule runtime_sym_generators_make_array >>
  pure_rewrite_tac[runtime_sym_make_array_clause_def] >> strip_tac >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `elem` >> simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >>
  qpat_assum `!n s b s'. _` (drule_at_then (Pat `compile_alloc_buffer _ _ = _`) mp_tac) >>
  simp[] >> strip_tac
  >~ [`compile_make_tuple _ _ _ _ _ _`]
  >- (Cases_on `compile_make_tuple cfn ce args buf_op_alloc.buf_operand 0 st2` >>
      simp[as_ptr_val_def] >> strip_tac >> gnvs[] >>
      qpat_x_assum `!cfn ce es buf off s op s'. _`
        (drule_at_then (Pat `compile_make_tuple _ _ _ _ _ _ = _`) mp_tac) >>
      simp[runtime_sym_value_def, mk_ptr_def]) >>
  Cases_on `compile_make_array cfn ce args x (type_memory_bytes ce x)
    (case bound of Fixed v2 => F | Dynamic v3 => T) buf_op_alloc.buf_operand st2` >>
  simp[as_ptr_val_def] >> strip_tac >> gnvs[] >>
  qpat_x_assum `!cfn ce es ety stride lw buf s op s'. _`
    (drule_at_then (Pat `compile_make_array _ _ _ _ _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def, mk_ptr_def]
QED
Resume runtime_sym_builtin_body[wei]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_misc >>
  disch_then (fn th => map_every assume_tac
    [cj 6 (SRULE [runtime_sym_misc_clauses_def] th),
     cj 7 (SRULE [runtime_sym_misc_clauses_def] th)]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  qpat_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `is_decimal_type (expr_type a)` >> simp[]
  >- (Cases_on `compile_as_wei_value_decimal v' (denomination_multiplier d)
        (decimal_divisor (expr_type a)) st1` >>
      simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
      qpat_assum `!v scale divisor s op s'. _`
        (drule_at_then (Pat `compile_as_wei_value_decimal _ _ _ _ = _`) mp_tac) >>
      simp[runtime_sym_value_def]) >>
  Cases_on `compile_as_wei_value_int v' (denomination_multiplier d)
    (is_signed_type (expr_type a)) st1` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  qpat_assum `!v scale signed s op s'. _`
    (drule_at_then (Pat `compile_as_wei_value_int _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[addmod]:
  `LENGTH args = 3` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[] >>
     namedCases_on `ys` ["", "c zs"] >> simp[] >>
     namedCases_on `zs` ["", "d rest"] >> simp[]) >>
  namedCases_on `args` ["", "a xs"] >> gnvs[] >>
  namedCases_on `xs` ["", "b ys"] >> gnvs[] >>
  namedCases_on `ys` ["", "c zs"] >> gnvs[] >>
  `LENGTH zs = 0` by decide_tac >> gnvs[] >>
  drule runtime_sym_generators_math >>
  disch_then (assume_tac o cj 1 o SRULE [runtime_sym_math_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `compile_addmod va vb vc st3` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  `EVERY runtime_sym_inst (state_insts st1) /\ ~is_label_operand va` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st2) /\ ~is_label_operand vb` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st3) /\ ~is_label_operand vc` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  qpat_assum `!a b m s op s'. _` (drule_at_then (Pat `compile_addmod _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[mulmod]:
  `LENGTH args = 3` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[] >>
     namedCases_on `ys` ["", "c zs"] >> simp[] >>
     namedCases_on `zs` ["", "d rest"] >> simp[]) >>
  namedCases_on `args` ["", "a xs"] >> gnvs[] >>
  namedCases_on `xs` ["", "b ys"] >> gnvs[] >>
  namedCases_on `ys` ["", "c zs"] >> gnvs[] >>
  `LENGTH zs = 0` by decide_tac >> gnvs[] >>
  drule runtime_sym_generators_math >>
  disch_then (assume_tac o cj 2 o SRULE [runtime_sym_math_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `compile_mulmod va vb vc st3` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  `EVERY runtime_sym_inst (state_insts st1) /\ ~is_label_operand va` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st2) /\ ~is_label_operand vb` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st3) /\ ~is_label_operand vc` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  qpat_assum `!a b m s op s'. _` (drule_at_then (Pat `compile_mulmod _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[powmod]:
  `LENGTH args = 2` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[] >>
     namedCases_on `ys` ["", "c zs"] >> simp[]) >>
  namedCases_on `args` ["", "a xs"] >> gnvs[] >>
  namedCases_on `xs` ["", "b ys"] >> gnvs[] >>
  drule runtime_sym_generators_math >>
  disch_then (assume_tac o cj 3 o SRULE [runtime_sym_math_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `compile_pow_mod256 v1 v2 st2` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  `EVERY runtime_sym_inst (state_insts st1) /\ ~is_label_operand v1` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st2) /\ ~is_label_operand v2` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  qpat_assum `!a b s op s'. _` (drule_at_then (Pat `compile_pow_mod256 _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[blockhash]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_misc >>
  disch_then (assume_tac o cj 1 o SRULE [runtime_sym_misc_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  Cases_on `compile_blockhash v' st1` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  qpat_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!v s op s'. _` (drule_at_then (Pat `compile_blockhash _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[blobhash]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_misc >>
  disch_then (assume_tac o cj 2 o SRULE [runtime_sym_misc_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  Cases_on `compile_blobhash v' st1` >>
  simp[as_stack_val_def] >> strip_tac >> gnvs[] >>
  qpat_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!v s op s'. _` (drule_at_then (Pat `compile_blobhash _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[ecrecover]:
  `LENGTH args = 4` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[] >>
     namedCases_on `ys` ["", "c zs"] >> simp[] >>
     namedCases_on `zs` ["", "d ws"] >> simp[] >>
     namedCases_on `ws` ["", "e rest"] >> simp[]) >>
  namedCases_on `args` ["", "a xs"] >> gnvs[] >>
  namedCases_on `xs` ["", "b ys"] >> gnvs[] >>
  namedCases_on `ys` ["", "c zs"] >> gnvs[] >>
  namedCases_on `zs` ["", "d ws"] >> gnvs[] >>
  `LENGTH ws = 0` by decide_tac >> gnvs[] >>
  drule runtime_sym_generators_misc >>
  disch_then (assume_tac o cj 3 o SRULE [runtime_sym_misc_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `compile_ecrecover vh vv vr vs' st4` >>
  simp[as_stack_val_def] >> strip_tac >>
  qpat_x_assum `StackValue _ _ = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `r = s'` (SUBST_ALL_TAC o SYM) >>
  `EVERY runtime_sym_inst (state_insts st1) /\ ~is_label_operand vh` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st2) /\ ~is_label_operand vv` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st3) /\ ~is_label_operand vr` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st4) /\ ~is_label_operand vs'` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!e t. expr_size e < _ ==> _` kall_tac >>
  qpat_x_assum `!h v r x s op s'. _` (drule_at_then (Pat `compile_ecrecover _ _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def]
QED
Resume runtime_sym_builtin_body[ecadd]:
  drule runtime_sym_builtin_callback >> simp[] >> strip_tac >>
  `LENGTH args = 2` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[] >>
     namedCases_on `ys` ["", "c zs"] >> simp[]) >>
  namedCases_on `args` ["", "a xs"] >> gnvs[] >>
  namedCases_on `xs` ["", "b ys"] >> gnvs[] >>
  drule runtime_sym_generators_context >>
  disch_then (assume_tac o cj 1 o SRULE [runtime_sym_context_clauses_def]) >>
  drule runtime_sym_generators_misc >>
  disch_then (assume_tac o cj 4 o SRULE [runtime_sym_misc_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `compile_ecadd_points p1 p2 st2a` >>
  simp[as_ptr_val_def] >> strip_tac >>
  qpat_x_assum `LocatedValue _ _ = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `r = s'` (SUBST_ALL_TAC o SYM) >>
  `EVERY runtime_sym_inst (state_insts st1) /\ runtime_sym_value p1_vv` by
    (qpat_assum `!e t s v s'. _ /\ _ /\ cfn _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st1a) /\ ~is_label_operand p1` by
    (qpat_assum `!ce v s op s'. runtime_sym_env ce /\ _ ==> _` (mp_tac o Q.SPECL [`ce`, `p1_vv`]) >>
     disch_then (drule_at_then (Pat `unwrap_value _ _ _ = _`) mp_tac) >>
     disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `EVERY runtime_sym_inst (state_insts st2) /\ runtime_sym_value p2_vv` by
    (qpat_assum `!e t s v s'. _ /\ _ /\ cfn _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st2a) /\ ~is_label_operand p2` by
    (qpat_assum `!ce v s op s'. _` (drule_at_then (Pat `unwrap_value _ _ _ = _`) mp_tac) >>
     disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!e t s v s'. _ /\ _ /\ cfn _ _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!e t. expr_size e < _ ==> _` kall_tac >>
  qpat_assum `!p q s op s'. _` (drule_at_then (Pat `compile_ecadd_points _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def, mk_ptr_def]
QED
Resume runtime_sym_builtin_body[ecmul]:
  drule runtime_sym_builtin_callback >> simp[] >> strip_tac >>
  `LENGTH args = 2` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[] >>
     namedCases_on `ys` ["", "c zs"] >> simp[]) >>
  namedCases_on `args` ["", "a xs"] >> gnvs[] >>
  namedCases_on `xs` ["", "b ys"] >> gnvs[] >>
  drule runtime_sym_generators_context >>
  disch_then (assume_tac o cj 1 o SRULE [runtime_sym_context_clauses_def]) >>
  drule runtime_sym_generators_misc >>
  disch_then (assume_tac o cj 5 o SRULE [runtime_sym_misc_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `compile_ecmul_point p s'' st2` >>
  simp[as_ptr_val_def] >> strip_tac >>
  qpat_x_assum `LocatedValue _ _ = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `r = s'` (SUBST_ALL_TAC o SYM) >>
  `EVERY runtime_sym_inst (state_insts st1) /\ runtime_sym_value p_vv` by
    (qpat_assum `!e t s v s'. _ /\ _ /\ cfn _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st1a) /\ ~is_label_operand p` by
    (qpat_assum `!ce v s op s'. _` (drule_at_then (Pat `unwrap_value _ _ _ = _`) mp_tac) >>
     disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `EVERY runtime_sym_inst (state_insts st2) /\ ~is_label_operand s''` by
    (qpat_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` irule >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!e t s v s'. _ /\ _ /\ cfn _ _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!e t s op s'. _ /\ _ /\ lower_value _ _ _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!e t. expr_size e < _ ==> _` kall_tac >>
  qpat_assum `!p q s op s'. _` (drule_at_then (Pat `compile_ecmul_point _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def, mk_ptr_def]
QED
Resume runtime_sym_builtin_body[uint2str]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_simple >>
  disch_then (assume_tac o cj 4 o SRULE [runtime_sym_simple_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  Cases_on `compile_uint2str v' n (type_memory_bytes ce rt) st1` >>
  simp[as_ptr_val_def] >> strip_tac >> gnvs[] >>
  qpat_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!v digits size s op s'. _`
    (drule_at_then (Pat `compile_uint2str _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def, mk_ptr_def]
QED
Resume runtime_sym_builtin_body[calldataslice]:
  `LENGTH args = 1` by
    (qpat_x_assum `supported_expr _ _` mp_tac >>
     namedCases_on `args` ["", "a xs"] >>
     simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
          supported_builtin_form_def] >>
     namedCases_on `xs` ["", "b ys"] >> simp[]) >>
  namedCases_on `args` ["", "a rest"] >> gnvs[] >>
  drule runtime_sym_generators_simple >>
  disch_then (assume_tac o cj 3 o SRULE [runtime_sym_simple_clauses_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> pairarg_tac >> simp[] >>
  Cases_on `compile_slice_calldata start_op (Lit (n2w n)) (type_memory_bytes ce rt) st1` >>
  simp[as_ptr_val_def] >> strip_tac >> gnvs[] >>
  qpat_assum `!t s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _`
    (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!start len n s op s'. _`
    (drule_at_then (Pat `compile_slice_calldata _ _ _ _ = _`) mp_tac) >>
  simp[runtime_sym_value_def, mk_ptr_def, stackPlanTypesTheory.is_label_operand_def]
QED
Finalise runtime_sym_builtin_body
