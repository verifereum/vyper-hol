Theory bodyPtrTypeBuiltinsScalarDispatch
Ancestors bodyPtrTypeBuiltinsScalarSemantic bodyPtrTypeBuiltinsScalarContinue bodyPtrTypeBuiltinsIntegerContinue
  bodyPtrTypeBuiltinsIntegerBoolContinue bodyPtrTypeBuiltinsIntegerAddressContinue
  bodyPtrTypeBuiltinsIntegerBytesContinue bodyPtrTypeBuiltinsIntegerDecimalContinue
  bodyPtrTypeBuiltinsDecimalIntegerContinue bodyPtrTypeBuiltinsFixedAddressContinue
  bodyPtrTypeBuiltinsFixedBytesContinue bodyPtrTypeBuiltinsFixedBoolContinue
  bodyPtrTypeBuiltinsAddressUintContinue bodyPtrTypeBuiltinsAddressFixedContinue
  bodyPtrTypeBuiltinsFlagUintContinue bodyPtrTypeBuiltinsFlagFixedContinue
  exprLowering exprLoweringProps vyperAST vyperTypeSystem vyperValue
  bodyPtrDefs fragGasPathPtr exprSimDefs exprSimHyps exprSimConvert compileEnv

Theorem scalar_source_shapes:
  !src. is_word_type src /\ ~is_bytestring_type src ==>
  src = BaseT BoolT \/ src = BaseT AddressT \/ src = BaseT DecimalT \/
  (?n. src = BaseT (IntT n)) \/ (?n. src = BaseT (UintT n)) \/
  (?m. src = BaseT (BytesT (Fixed m))) \/ (?name. src = FlagT name)
Proof
  Cases_on `src` >> simp[is_word_type_def, is_bytestring_type_def] >>
  rename1 `is_word_type (BaseT b)` >> Cases_on `b` >>
  simp[is_word_type_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_bytestring_type_def]
QED

Theorem scalar_convert_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert typ [e]) es /\
  ~is_bytestring_type (expr_type e) /\
  compile_type_convert x
    (case typ of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
     | _ => mk_convert_op (expr_type e) typ) s1 = (op,sb) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v1 /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  fn_has_code s1 sb func /\ local_ptrs_reserved cenv s1 /\
  sa.cs_next_var <= s1.cs_next_var /\ ~ctx_has_dalloca ctx /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p) /\
  ptr_val_ok cx (expr_type e) v1 x G tn t0 /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (\vs. (convert_result cx (expr_type e) typ v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert typ [e])
        es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\ ptr_val_ok cx typ v op H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >> drule_all scalar_source_body_word_types >> strip_tac >>
  qspec_then `expr_type e` mp_tac scalar_source_shapes >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[]
  >- suspend "bool"
  >- suspend "address"
  >- suspend "decimal"
  >- suspend "int"
  >- suspend "uint"
  >- suspend "fixed"
  >> suspend "flag"
QED

Resume scalar_convert_continuation[bool]:
  Cases_on `ann` >> fs[valid_conversion_def] >>
  rename1 `valid_conversion (BaseT BoolT) (BaseT bt)` >>
  Cases_on `bt` >> fs[valid_conversion_def] >>
  qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
  irule scalar_identity_continuation >>
  fs[mk_convert_op_def, is_bytestring_type_def] >> metis_tac[]
QED

Resume scalar_convert_continuation[address]:
  Cases_on `ann` >> fs[valid_conversion_def] >>
  rename1 `valid_conversion (BaseT AddressT) (BaseT bt)` >>
  Cases_on `bt` >> fs[valid_conversion_def]
  >- (qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
      irule scalar_address_uint_continuation >> simp[] >> metis_tac[]) >>
  rename1 `valid_conversion (BaseT AddressT) (BaseT (BytesT bd))` >>
  Cases_on `bd` >> fs[valid_conversion_def] >>
  qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
  irule scalar_address_fixed_continuation >> simp[] >> metis_tac[]
QED

Resume scalar_convert_continuation[decimal]:
  Cases_on `ann` >> fs[valid_conversion_def] >>
  rename1 `valid_conversion (BaseT DecimalT) (BaseT bt)` >>
  Cases_on `bt` >> fs[valid_conversion_def]
  >- (irule (scalar_decimal_integer_continuation |> Q.INST [`so` |-> `F`] |> SRULE []) >>
      simp[] >> metis_tac[]) >>
  irule (scalar_decimal_integer_continuation |> Q.INST [`so` |-> `T`] |> SRULE []) >>
  simp[] >> metis_tac[]
QED

Resume scalar_convert_continuation[flag]:
  Cases_on `ann` >> fs[valid_conversion_def] >>
  rename1 `valid_conversion (FlagT name) (BaseT bt)` >>
  Cases_on `bt` >> fs[valid_conversion_def] >> gvs[]
  >- (qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
      irule scalar_flag_uint_continuation >> simp[] >> metis_tac[]) >>
  qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
  irule scalar_flag_fixed_continuation >> simp[] >> metis_tac[]
QED

Resume scalar_convert_continuation[int]:
  Cases_on `ann` >> fs[valid_conversion_def] >>
  rename1 `valid_conversion (BaseT (IntT n)) (BaseT bt)` >>
  Cases_on `bt` >> fs[valid_conversion_def]
  >- suspend "int_uint"
  >- suspend "int_int"
  >- suspend "int_bool"
  >- suspend "int_decimal"
  >- suspend "int_fixed"
  >> suspend "int_address"
QED

Resume scalar_convert_continuation[int_uint]:
  irule (scalar_integer_continuation |> Q.INST [`si` |-> `T`, `so` |-> `F`] |> SRULE []) >>
  simp[] >> metis_tac[]
QED
Resume scalar_convert_continuation[int_int]:
  irule (scalar_integer_continuation |> Q.INST [`si` |-> `T`, `so` |-> `T`] |> SRULE []) >>
  simp[] >> metis_tac[]
QED
Resume scalar_convert_continuation[int_bool]:
  irule (scalar_integer_bool_continuation |> Q.INST [`si` |-> `T`] |> SRULE []) >>
  simp[] >> metis_tac[]
QED
Resume scalar_convert_continuation[int_address]:
  irule (scalar_integer_address_continuation |> Q.INST [`si` |-> `T`] |> SRULE []) >>
  simp[] >> metis_tac[]
QED
Resume scalar_convert_continuation[int_fixed]:
  rename1 `valid_conversion (BaseT (IntT n)) (BaseT (BytesT bd))` >>
  Cases_on `bd` >> fs[valid_conversion_def] >>
  irule (scalar_integer_bytes_continuation |> Q.INST [`si` |-> `T`] |> SRULE []) >>
  simp[] >> metis_tac[]
QED
Resume scalar_convert_continuation[int_decimal]:
  irule (scalar_integer_decimal_continuation |> Q.INST [`si` |-> `T`] |> SRULE []) >>
  simp[] >> metis_tac[]
QED

Resume scalar_convert_continuation[uint]:
  Cases_on `ann` >> fs[valid_conversion_def]
  >- (rename1 `valid_conversion (BaseT (UintT n)) (BaseT bt)` >>
      Cases_on `bt` >> fs[valid_conversion_def]
      >- suspend "uint_uint"
      >- suspend "uint_int"
      >- suspend "uint_bool"
      >- suspend "uint_decimal"
      >- suspend "uint_fixed"
      >> suspend "uint_address") >>
  gvs[] >> qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
  irule scalar_flag_continuation >> simp[] >> metis_tac[]
QED

Resume scalar_convert_continuation[uint_uint]:
  irule (scalar_integer_continuation |> Q.INST [`si` |-> `F`, `so` |-> `F`] |> SRULE []) >>
  simp[] >> metis_tac[]
QED
Resume scalar_convert_continuation[uint_int]:
  irule (scalar_integer_continuation |> Q.INST [`si` |-> `F`, `so` |-> `T`] |> SRULE []) >>
  simp[] >> metis_tac[]
QED
Resume scalar_convert_continuation[uint_bool]:
  irule (scalar_integer_bool_continuation |> Q.INST [`si` |-> `F`] |> SRULE []) >>
  simp[] >> metis_tac[]
QED
Resume scalar_convert_continuation[uint_address]:
  irule (scalar_integer_address_continuation |> Q.INST [`si` |-> `F`] |> SRULE []) >>
  simp[] >> metis_tac[]
QED
Resume scalar_convert_continuation[uint_fixed]:
  rename1 `valid_conversion (BaseT (UintT n)) (BaseT (BytesT bd))` >>
  Cases_on `bd` >> fs[valid_conversion_def] >>
  irule (scalar_integer_bytes_continuation |> Q.INST [`si` |-> `F`] |> SRULE []) >>
  simp[] >> metis_tac[]
QED
Resume scalar_convert_continuation[uint_decimal]:
  irule (scalar_integer_decimal_continuation |> Q.INST [`si` |-> `F`] |> SRULE []) >>
  simp[] >> metis_tac[]
QED

Resume scalar_convert_continuation[fixed]:
  Cases_on `ann` >> fs[valid_conversion_def] >>
  rename1 `valid_conversion (BaseT (BytesT (Fixed m))) (BaseT bt)` >>
  Cases_on `bt` >> fs[valid_conversion_def]
  >- suspend "fixed_uint"
  >- suspend "fixed_int"
  >- suspend "fixed_bool"
  >- suspend "fixed_decimal"
  >- suspend "fixed_fixed"
  >> suspend "fixed_address"
QED

Resume scalar_convert_continuation[fixed_uint]:
  irule (scalar_fixed_int_continuation |> Q.INST [`sg` |-> `F`] |> SRULE []) >>
  simp[] >> metis_tac[]
QED
Resume scalar_convert_continuation[fixed_int]:
  irule (scalar_fixed_int_continuation |> Q.INST [`sg` |-> `T`] |> SRULE []) >>
  simp[] >> metis_tac[]
QED
Resume scalar_convert_continuation[fixed_bool]:
  qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
  irule scalar_fixed_bool_continuation >> simp[] >> metis_tac[]
QED
Resume scalar_convert_continuation[fixed_decimal]:
  qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
  irule scalar_fixed_decimal_continuation >> simp[] >> metis_tac[]
QED
Resume scalar_convert_continuation[fixed_fixed]:
  rename1 `valid_conversion (BaseT (BytesT (Fixed m))) (BaseT (BytesT bd))` >>
  Cases_on `bd` >> fs[valid_conversion_def] >>
  qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
  irule scalar_fixed_fixed_continuation >> simp[] >> metis_tac[]
QED
Resume scalar_convert_continuation[fixed_address]:
  qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
  irule scalar_fixed_address_continuation >> simp[] >> metis_tac[]
QED

Finalise scalar_convert_continuation
