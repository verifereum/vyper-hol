Theory bodyPtrPopBuiltinBoundary
Ancestors bodyPtrPopCompileDomain bodyPtrPopMathIntegration bodyPtrPopSliceIntegration
  bodyPtrPopMaterialization bodyPtrPopArithmeticBoundary bodyPtrPopAllocationBoundary
  bodyPtrPopScalarAccessorBoundary bodyPtrPopMiscGuardBoundary
  bodyPtrPopPrecompileBoundary bodyPtrPopAggregateBoundary
  bodyPtrPopUint2StrBoundary bodyPtrPopBinopBoundary
  bodyPtrPopFiniteProducerBoundary
  exprLowering supportedTypes supportedExprForms supportedExprs compileEnv emitHelper list

Theorem pop_builtin_callback_boundary:
  (!cenv ty e sa r sb. pop_compile_domain tops e /\ pop_comp_boundary sa /\
    cfn cenv ty e sa = (r,sb) ==> pop_comp_boundary sb) /\
  EVERY (supported_pure_expr tops) args ==>
  !a aty s v t. MEM a args /\ pop_comp_boundary s /\
    cfn cenv aty a s = (v,t) ==> pop_comp_boundary t
Proof
  rpt strip_tac >> drule_all pop_domain_pure_argument >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem pop_env_dispatch_boundary:
  pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv rt ty (Env item) args sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
  Cases_on `compile_env_var item sa` >> gvs[as_stack_val_def] >>
  drule_all pop_compile_env_var_boundary >> simp[]
QED

Theorem pop_acc_dispatch_boundary:
  (!aty s v t. pop_comp_boundary s /\ cfn cenv aty a s = (v,t) ==>
    pop_comp_boundary t) /\ pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv rt ty (Acc item) [a] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
  Cases_on `compile_acc cfn cenv a item sa` >> gvs[as_stack_val_def] >>
  drule_at (Pat `compile_acc _ _ _ _ _ = _`) pop_compile_acc_boundary >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem pop_not_dispatch_boundary:
  (!aty s v t. pop_comp_boundary s /\ cfn cenv aty a s = (v,t) ==>
    pop_comp_boundary t) /\ pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv rt ty Not [a] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st1` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >>
     first_x_assum drule_all >> simp[]) >>
  Cases_on `expr_type a = BaseT BoolT` >> gvs[]
  >- (Cases_on `emit_op ISZERO [v] st1` >> gvs[as_stack_val_def] >>
      drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]) >>
  Cases_on `compile_invert v (expr_type a) cenv st1` >> gvs[as_stack_val_def] >>
  drule_all pop_compile_invert_boundary >> simp[]
QED

Theorem pop_uint2str_dispatch_boundary:
  (!aty s v t. pop_comp_boundary s /\ cfn cenv aty a s = (v,t) ==>
    pop_comp_boundary t) /\ pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv rt ty (Uint2Str n) [a] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st1` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >>
     first_x_assum drule_all >> simp[]) >>
  Cases_on `compile_uint2str v n (type_memory_bytes cenv rt) st1` >>
  gvs[as_ptr_val_def] >> drule_all pop_compile_uint2str_boundary >> simp[]
QED

Theorem pop_make_array_dispatch_boundary:
  (!a aty s v t. MEM a args /\ pop_comp_boundary s /\
    cfn cenv aty a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv rt ty (MakeArray opt bd) args sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `opt` >> simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st2` by (drule_all pop_compile_alloc_buffer_boundary >> simp[])
  >- (Cases_on `compile_make_tuple cfn cenv args buf_op_alloc.buf_operand 0 st2` >>
      gvs[as_ptr_val_def] >>
      drule_at (Pat `compile_make_tuple _ _ _ _ _ _ = _`)
        pop_compile_make_tuple_boundary >> simp[] >>
      disch_then irule >> first_assum ACCEPT_TAC) >>
  Cases_on `compile_make_array cfn cenv args x (type_memory_bytes cenv x)
    (case bd of Dynamic _ => T | _ => F) buf_op_alloc.buf_operand st2` >>
  gvs[as_ptr_val_def] >>
  drule_at (Pat `compile_make_array _ _ _ _ _ _ _ _ = _`)
    pop_compile_make_array_boundary >> simp[] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Theorem pop_hash_dispatch_boundary:
  (bi = BlockHash \/ bi = BlobHash) /\
  (!aty s v t. pop_comp_boundary s /\ cfn cenv aty a s = (v,t) ==>
    pop_comp_boundary t) /\ pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv rt ty bi [a] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  strip_tac >> gvs[] >> gvs[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st1` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >>
     first_x_assum drule_all >> simp[]) >>
  Cases_on `compile_blockhash v st1` >> Cases_on `compile_blobhash v st1` >>
  gvs[as_stack_val_def] >>
  metis_tac[pop_compile_blockhash_boundary, pop_compile_blobhash_boundary]
QED

Theorem pop_powmod_dispatch_boundary:
  (!a aty s v t. MEM a [a1;a2] /\ pop_comp_boundary s /\
    cfn cenv aty a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv rt ty PowMod256 [a1;a2] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st1` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >> metis_tac[]) >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st2` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >> metis_tac[]) >>
  Cases_on `compile_pow_mod256 v1 v2 st2` >> gvs[as_stack_val_def] >>
  drule_all pop_compile_pow_mod256_boundary >> simp[]
QED

Theorem pop_wei_dispatch_boundary:
  supported_unsigned_type (expr_type a) /\
  (!aty s v t. pop_comp_boundary s /\ cfn cenv aty a s = (v,t) ==>
    pop_comp_boundary t) /\ pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv rt ty (AsWeiValue d) [a] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  strip_tac >>
  `~is_decimal_type (expr_type a)` by
    (Cases_on `expr_type a` >> gvs[supported_unsigned_type_def] >>
     rename1 `supported_unsigned_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[supported_unsigned_type_def, is_decimal_type_def]) >>
  gvs[compile_builtin_dispatch_body_def] >> pairarg_tac >> gvs[] >>
  `pop_comp_boundary st1` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >>
     first_x_assum drule_all >> simp[]) >>
  Cases_on `compile_as_wei_value_int v (denomination_multiplier d)
    (is_signed_type (expr_type a)) st1` >> gvs[as_stack_val_def] >>
  drule_all pop_compile_as_wei_value_int_boundary >> simp[]
QED

Theorem pop_ecrecover_dispatch_boundary:
  (!a aty s v t. MEM a [a1;a2;a3;a4] /\ pop_comp_boundary s /\
    cfn cenv aty a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv rt ty ECRecover [a1;a2;a3;a4] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st1` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >> metis_tac[]) >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st2` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >> metis_tac[]) >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st3` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >> metis_tac[]) >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st4` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >> metis_tac[]) >>
  qpat_x_assum `!a aty s v t. _` kall_tac >>
  Cases_on `compile_ecrecover vh vv vr vs' st4` >> gvs[as_stack_val_def] >>
  drule_all pop_compile_ecrecover_boundary >> simp[]
QED

Theorem pop_ecadd_dispatch_boundary:
  (!a aty s v t. MEM a [a1;a2] /\ pop_comp_boundary s /\
    cfn cenv aty a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv rt ty ECAdd [a1;a2] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st1` by metis_tac[] >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st1a` by (drule_all pop_unwrap_value_boundary >> simp[]) >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st2` by metis_tac[] >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st2a` by (drule_all pop_unwrap_value_boundary >> simp[]) >>
  Cases_on `compile_ecadd_points p1 p2 st2a` >> gvs[as_ptr_val_def] >>
  drule_all pop_compile_ecadd_points_boundary >> simp[]
QED

Theorem pop_ecmul_dispatch_boundary:
  (!a aty s v t. MEM a [a1;a2] /\ pop_comp_boundary s /\
    cfn cenv aty a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv rt ty ECMul [a1;a2] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_builtin_dispatch_body_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st1` by metis_tac[] >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st1a` by (drule_all pop_unwrap_value_boundary >> simp[]) >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st2` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >> metis_tac[]) >>
  rename1 `as_ptr_val rt LocMemory (compile_ecmul_point p scalar st2) = _` >>
  Cases_on `compile_ecmul_point p scalar st2` >> gvs[as_ptr_val_def] >>
  drule_all pop_compile_ecmul_point_boundary >> simp[]
QED

Theorem pop_supported_word_not_bytestring:
  supported_word_type ty ==> ~is_bytestring_type ty
Proof
  Cases_on `ty` >> simp[supported_word_type_def] >>
  rename1 `supported_word_type (BaseT bt)` >> Cases_on `bt` >>
  simp[supported_word_type_def, is_bytestring_type_def] >>
  rename1 `supported_word_type (BaseT (BytesT bd))` >> Cases_on `bd` >>
  simp[supported_word_type_def, is_bytestring_type_def]
QED

Theorem pop_supported_binop_dispatch_tests:
  supported_binop op ty rhs lit nonneg ==>
  op <> In /\ op <> NotIn /\
  ~(is_bytestring_type ty /\ (op = Eq \/ op = NotEq))
Proof
  Cases_on `op` >> simp[supported_binop_def] >>
  metis_tac[pop_supported_word_not_bytestring]
QED

Theorem pop_bop_dispatch_boundary:
  supported_binop op (expr_type a1) (expr_type a2) lit nonneg /\
  (!a aty s v t. MEM a [a1;a2] /\ pop_comp_boundary s /\
    cfn cenv aty a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv rt ty (Bop op) [a1;a2] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  strip_tac >> drule pop_supported_binop_dispatch_tests >> strip_tac >>
  gvs[compile_builtin_dispatch_body_def] >> pairarg_tac >> gvs[] >>
  `pop_comp_boundary st1` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >> metis_tac[]) >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st2` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >> metis_tac[]) >>
  Cases_on `compile_binop op v1 v2 (expr_type a1)
    (if op = Exp then expr_int_literal a1 else NONE)
    (if op = Exp then expr_int_literal a2 else NONE) st2` >>
  gvs[as_stack_val_def] >> drule_all pop_compile_binop_boundary >> simp[]
QED


Theorem pop_supported_builtin_bounded_arity:
  (!opt bd. bi <> MakeArray opt bd) /\ supported_builtin_form tops rt bi args ==>
  LENGTH args <= 4
Proof
  strip_tac >> Cases_on `args` >- simp[] >> rename1 `a::rest` >>
  Cases_on `rest` >- simp[] >> rename1 `a::b::rest` >>
  Cases_on `rest` >- simp[] >> rename1 `a::b::c::rest` >>
  Cases_on `rest` >- simp[] >> rename1 `a::b::c::d::rest` >>
  Cases_on `rest` >- simp[] >>
  Cases_on `bi` >> gvs[supported_builtin_form_def]
QED

Theorem pop_builtin_unary_dispatch_boundary:
  supported_builtin_form tops rt bi [a] /\
  (!aty s v t. pop_comp_boundary s /\ cfn cenv aty a s = (v,t) ==>
    pop_comp_boundary t) /\ pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv rt ty bi [a] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  strip_tac >> Cases_on `bi` >> gvs[supported_builtin_form_def]
  >~ [`compile_builtin_dispatch_body _ _ _ _ (MakeArray _ _) _ _ = _`]
  >- (drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
        pop_make_array_dispatch_boundary >> disch_then irule >> simp[] >>
      first_assum ACCEPT_TAC)
  >~ [`compile_builtin_dispatch_body _ _ _ _ (CalldataSlice _) _ _ = _`]
  >- (drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
        pop_slice_dispatch_boundary >> disch_then irule >> simp[] >>
      rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  FIRST [drule_all pop_not_dispatch_boundary,
         drule_all pop_acc_dispatch_boundary,
         drule_all pop_uint2str_dispatch_boundary,
         drule_all pop_wei_dispatch_boundary,
         (drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
            pop_single_math_dispatch_boundary >> disch_then irule >> simp[] >>
          first_assum ACCEPT_TAC),
         (drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
            pop_hash_dispatch_boundary >> disch_then irule >> simp[] >>
          first_assum ACCEPT_TAC)] >> simp[]
QED

Theorem pop_builtin_dispatch_boundary:
  supported_builtin_form tops rt bi args /\
  (!a aty s v t. MEM a args /\ pop_comp_boundary s /\
    cfn cenv aty a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv rt ty bi args sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  strip_tac >> Cases_on `?opt bd. bi = MakeArray opt bd`
  >- (gvs[] >> drule_all pop_make_array_dispatch_boundary >> simp[]) >>
  `!opt bd. bi <> MakeArray opt bd` by metis_tac[] >>
  drule_all pop_supported_builtin_bounded_arity >> strip_tac >>
  Cases_on `args`
  >- (Cases_on `bi` >> gvs[supported_builtin_form_def] >>
      drule_all pop_env_dispatch_boundary >> simp[]) >>
  rename1 `a::rest` >> Cases_on `rest`
  >- (gvs[] >> drule_all pop_builtin_unary_dispatch_boundary >> simp[]) >>
  rename1 `a::b::rest` >> Cases_on `rest`
  >- (Cases_on `bi` >> gvs[supported_builtin_form_def] >>
      FIRST [(drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
                pop_bop_dispatch_boundary >> disch_then irule >> simp[] >>
              conj_tac >- first_assum ACCEPT_TAC >>
              qexistsl [`supported_integer_literal a`, `supported_nonnegative_literal b`] >> simp[]),
             (drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
                pop_powmod_dispatch_boundary >> disch_then irule >> simp[] >> first_assum ACCEPT_TAC),
             (drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
                pop_ecadd_dispatch_boundary >> disch_then irule >> simp[] >> first_assum ACCEPT_TAC),
             (drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
                pop_ecmul_dispatch_boundary >> disch_then irule >> simp[] >> first_assum ACCEPT_TAC)] >> simp[]) >>
  rename1 `a::b::c::rest` >> Cases_on `rest`
  >- (Cases_on `bi` >> gvs[supported_builtin_form_def] >>
      drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
        pop_triple_math_dispatch_boundary >> disch_then irule >> simp[] >>
      first_assum ACCEPT_TAC) >>
  rename1 `a::b::c::d::rest` >> Cases_on `rest` >> gvs[] >>
  Cases_on `bi` >> gvs[supported_builtin_form_def] >>
  drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
    pop_ecrecover_dispatch_boundary >> disch_then irule >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem pop_builtin_open_boundary:
  !cfn.
  (!cenv ty e sa r sb. pop_compile_domain tops e /\ pop_comp_boundary sa /\
    cfn cenv ty e sa = (r,sb) ==> pop_comp_boundary sb) ==>
  !cenv rt ty bi args sa r sb.
  supported_builtin_form tops rt bi args /\
  EVERY (supported_pure_expr tops) args /\ pop_comp_boundary sa /\
  compile_builtin_dispatch_body cfn cenv rt ty bi args sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  rpt strip_tac >>
  drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
    pop_builtin_dispatch_boundary >> disch_then irule >> simp[] >>
  reverse conj_tac >- (qexists `tops` >> simp[]) >>
  rpt strip_tac >> drule_all pop_domain_pure_argument >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED
