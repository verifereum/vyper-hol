(*
 * compile_expr keeps its block open: builtin and type-builtin dispatch
 *
 * TOP-LEVEL:
 *   compile_dispatch_*_open, compile_type_dispatch_*_open — the
 *     supported builtin and type-builtin forms, one lemma per group
 *   compile_builtin_body_open, compile_pop_body_open — the bodies
 *     compile_expr gives them
 *)

Theory exprOpenDispatch
Ancestors
  exprOpenCases exprOpenBuiltins exprOpenConvert exprOpenPrimitives exprOpenTerminals
  exprOpenCopies supportedExprForms supportedTypes exprLowering compileEnv context
  builtinSimple builtinMath builtinMisc builtinBytes builtinStrings venomInst
  list pair

Theorem compile_dispatch_not_open:
  !cfn cenv rty ty args sa vv sb.
    compile_builtin_dispatch_body cfn cenv rty ty Not args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >>
  simp[oneline as_stack_val_def, AllCaseEqs()] >> strip_tac >> gvs[]
  >- (drule emit_op_nonterminator_open >> simp[is_terminator_def]) >>
  drule compile_invert_open >> simp[]
QED

Theorem compile_dispatch_bop_open:
  !cfn tops cenv rty ty op a b sa vv sb.
    supported_binop op (expr_type a) (expr_type b)
      (supported_integer_literal a) (supported_nonnegative_literal b) /\
    compile_builtin_dispatch_body cfn cenv rty ty (Bop op) [a;b] sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> strip_tac >>
  `op <> In /\ op <> NotIn /\ op <> ExpMod` by
    (Cases_on `op` >> gvs[supported_binop_def]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >> IF_CASES_TAC
  >- (rpt (pairarg_tac >> simp[]) >> IF_CASES_TAC >>
      simp[oneline as_stack_val_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      drule emit_op_nonterminator_open >> simp[is_terminator_def]) >>
  rpt (pairarg_tac >> simp[]) >>
  simp[oneline as_stack_val_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule compile_binop_open >> simp[] >> disch_then drule >> simp[]
QED

Theorem compile_dispatch_terminal_open:
  !cfn cenv rty ty bi args sa vv sb.
    (bi = Neg \/ bi = Abs \/ bi = AddMod \/ bi = MulMod \/ bi = PowMod256 \/
     bi = BlockHash \/ bi = BlobHash \/ bi = ECRecover \/ bi = ECAdd \/ bi = ECMul \/
     (?item. bi = Env item) \/ (?n. bi = Uint2Str n) \/ (?n. bi = CalldataSlice n)) /\
    compile_builtin_dispatch_body cfn cenv rty ty bi args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[]) >>
  simp[oneline as_stack_val_def, oneline as_ptr_val_def, AllCaseEqs()] >>
  strip_tac >> gvs[]
  >~ [`compile_neg _ _ _ = _`] >- (drule compile_neg_open >> simp[])
  >~ [`compile_builtin_abs _ _ = _`] >- (drule compile_builtin_abs_open >> simp[])
  >~ [`compile_addmod _ _ _ _ = _`] >- (drule compile_addmod_open >> simp[])
  >~ [`compile_mulmod _ _ _ _ = _`] >- (drule compile_mulmod_open >> simp[])
  >~ [`compile_pow_mod256 _ _ _ = _`] >- (drule compile_pow_mod256_open >> simp[])
  >~ [`compile_blockhash _ _ = _`] >- (drule compile_blockhash_open >> simp[])
  >~ [`compile_blobhash _ _ = _`] >- (drule compile_blobhash_open >> simp[])
  >~ [`compile_ecrecover _ _ _ _ _ = _`] >- (drule compile_ecrecover_open >> simp[])
  >~ [`compile_ecadd_points _ _ _ = _`] >- (drule compile_ecadd_points_open >> simp[])
  >~ [`compile_ecmul_point _ _ _ = _`] >- (drule compile_ecmul_point_open >> simp[])
  >~ [`compile_env_var _ _ = _`] >- (drule compile_env_var_open >> simp[])
  >~ [`compile_uint2str _ _ _ _ = _`] >- (drule compile_uint2str_open >> simp[]) >>
  drule compile_slice_calldata_open >> simp[]
QED

Theorem compile_dispatch_make_array_open:
  !cfn tops cenv rty ty elem bnd args sa vv sb.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    (case elem of NONE => T | SOME et =>
       supported_literal_elements tops (ArrayT et bnd) args) /\
    compile_builtin_dispatch_body cfn cenv rty ty (MakeArray elem bnd) args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `elem` >>
  simp[compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[]) >>
  simp[oneline as_ptr_val_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule compile_alloc_buffer_open >> disch_tac
  >- (drule_all compile_make_tuple_open >> simp[]) >>
  irule compile_make_array_open >>
  goal_assum (drule_at (Pat `compile_make_array _ _ _ _ _ _ _ _ = _`)) >>
  gvs[supported_literal_elements_def, EVERY_MEM] >>
  metis_tac[supported_copy_types_store_path]
QED

Theorem compile_as_wei_value_decimal_open:
  !v scale divisor sa r sb.
    compile_as_wei_value_decimal v scale divisor sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_as_wei_value_decimal_def,
    comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> IF_CASES_TAC >>
  simp[comp_bind_def] >> rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_dispatch_as_wei_value_open:
  !cfn cenv rty ty denom args sa vv sb.
    (!v st. lower_value cfn cenv (expr_type (HD args)) (HD args) sa = (v,st) ==>
      ~block_is_terminated st) /\
    compile_builtin_dispatch_body cfn cenv rty ty (AsWeiValue denom) args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >>
  simp[oneline as_stack_val_def, AllCaseEqs()] >> strip_tac >> gvs[]
  >- (drule compile_as_wei_value_decimal_open >> simp[]) >>
  drule_all compile_as_wei_value_int_open >> simp[]
QED

Theorem compile_bytestring_widen_copy_open[local]:
  !d v sz sa r sb.
    compile_bytestring_widen_copy d v sz sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_bytestring_widen_copy_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  Cases_on `sz` >> gvs[compile_copy_memory_def, comp_return_def]
  >- metis_tac[compile_alloc_buffer_open] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_type_dispatch_convert_open:
  !cfn cenv vty ty rty args sa vv sb.
    (!v st. lower_value cfn cenv (expr_type (HD args)) (HD args) sa = (v,st) ==>
      ~block_is_terminated st) /\
    compile_type_builtin_dispatch_body cfn cenv vty ty Convert rty args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_type_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC
  >- (rpt strip_tac >> gvs[] >> first_x_assum drule >> simp[]) >>
  IF_CASES_TAC
  >- (simp[oneline as_stack_val_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      drule compile_bytestring_widen_copy_open >> simp[]) >>
  Cases_on `rty` >>
  simp[oneline as_stack_val_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all compile_type_convert_open >> simp[]
QED

Theorem compile_type_dispatch_constant_open:
  !cfn cenv vty ty tb rty args sa vv sb.
    (tb = Empty \/ tb = MaxValue \/ tb = MinValue \/ tb = Epsilon) /\
    ~block_is_terminated sa /\
    compile_type_builtin_dispatch_body cfn cenv vty ty tb rty args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[]) >>
  rpt IF_CASES_TAC >> rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule compile_builtin_empty_complex_open >> simp[]
QED

Theorem compile_type_dispatch_abi_open:
  !cfn cenv vty ty tb rty args sa vv sb.
    ((?ensure mid. tb = AbiEncode ensure mid) \/ (?flag. tb = AbiDecode flag)) /\
    compile_type_builtin_dispatch_body cfn cenv vty ty tb rty args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_type_builtin_dispatch_body_def] >>
  rpt IF_CASES_TAC >> rpt (pairarg_tac >> simp[]) >>
  simp[oneline as_stack_val_def, oneline as_ptr_val_def, AllCaseEqs()] >>
  strip_tac >> gvs[]
  >~ [`lower_abi_encode _ _ _ _ _ _ = _`]
    >>~- ([`lower_abi_encode _ _ _ _ _ _ = _`],
      drule lower_abi_encode_open >> simp[]) >>
  drule lower_abi_decode_open >> simp[]
QED

Theorem compile_dispatch_acc_open:
  !cfn cenv rty ty item args sa vv sb.
    item <> Code /\
    (item = Address ==>
      !v st. lower_value cfn cenv (BaseT AddressT) (HD args) sa = (v,st) ==>
        ~block_is_terminated st) /\
    compile_builtin_dispatch_body cfn cenv rty ty (Acc item) args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_builtin_dispatch_body_def,
    oneline as_stack_val_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  Cases_on `item = Address`
  >- gvs[compile_acc_def] >>
  drule_all compile_acc_open >> simp[]
QED

Theorem compile_builtin_body_open:
  !cfn bfn tfn cenv ty ann bi args sa vv sb.
    (!v st. bfn cenv ann ty bi args sa = (v,st) ==> ~block_is_terminated st) /\
    compile_expr_body cfn bfn tfn cenv ty (Builtin ann bi args) sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `args`
  >- (simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >> metis_tac[]) >>
  rename1 `Builtin ann bi (a::rest)` >> Cases_on `a`
  >~ [`Builtin ann bi (Name aty an::rest)`]
  >- (Cases_on `rest`
      >- (simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >> metis_tac[]) >>
      rename1 `Name aty an::b::rest2` >> Cases_on `b`
      >~ [`Name aty an::Name bty bn::rest2`]
      >- (Cases_on `rest2`
          >- (Cases_on `bi` >>
              simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
              metis_tac[compile_powmod256_names_open]) >>
          rename1 `Name aty an::Name bty bn::m::rest3` >> Cases_on `m`
          >~ [`Name aty an::Name bty bn::Name mty mn::rest3`]
          >- (Cases_on `rest3` >> Cases_on `bi` >>
              simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
              metis_tac[compile_addmod_names_open, compile_mulmod_names_open]) >>
          simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >> metis_tac[]) >>
      simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >> metis_tac[]) >>
  simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >> metis_tac[]
QED

Theorem compile_pop_body_open:
  !cfn bfn tfn cenv ty ann target sa vv sb.
    compile_expr_body cfn bfn tfn cenv ty (Pop ann target) sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_expr_body_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule compile_dynarray_pop_open >> simp[]
QED
