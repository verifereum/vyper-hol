Theory convertScalarDispatch
Ancestors
  exprUnopStraight
  exprSimDefs exprSimProps exprSimStack loweringPosts
  convertScalarTyping convertScalarBytes convertScalarOutputs
  convertScalarDecimalFrag convertScalarFlags convertScalarProps
  exprSimUnop exprSimConvert exprSimHyps 
  exprLowering compileEnv vyperValue vyperTyping vyperTypeSystem
  valueEncoding words integer_word arithmeticProps list

Theorem scalar_fixed_decimal_mk_op:
  !m. mk_convert_op (BaseT (BytesT (Fixed m))) (BaseT DecimalT) =
    ConvBytesMToDecimal m 10000000000 (-&(2**167)) (&(2**167)-1)
Proof
  gen_tac >>
  qspec_then `167` (assume_tac o SRULE[]) w2i_i2w_neg_pow2 >>
  qspec_then `167` (assume_tac o SRULE[]) w2i_i2w_pow2_sub1 >>
  simp[mk_convert_op_def, is_bytestring_type_def, type_bounds_def,
       type_bits_def, is_signed_type_def] >> intLib.ARITH_TAC
QED

Theorem scalar_fixed_decimal_mk_frag[local]:
  !ctx func cenv cx m bs es0.
    LENGTH bs = m /\ 0 < m /\ m <= 32 ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x
        (mk_convert_op (BaseT (BytesT (Fixed m))) (BaseT DecimalT)))
      (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs))
      (BaseT DecimalT)
      (convert_result cx (BaseT (BytesT (Fixed m))) (BaseT DecimalT) (BytesV bs)) es0
Proof
  pure_rewrite_tac[scalar_fixed_decimal_mk_op] >>
  rpt strip_tac >> irule scalar_bytes_decimal_result_frag >> simp[]
QED

Theorem scalar_address_typed_dispatch:
  !ctx func cenv cx env es1 t tv v.
    valid_conversion (BaseT AddressT) t /\
    ~is_bytestring_type (BaseT AddressT) /\ ~is_bytestring_type t /\
    ~int_convert_pair (BaseT AddressT) t /\
    ~(BaseT AddressT = BaseT (BytesT (Fixed 0)) /\
      ((?k. t = BaseT (IntT k)) \/ t = BaseT DecimalT)) /\
    evaluate_type (get_tenv cx) (BaseT AddressT) = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v /\
    expr_sim_inv cenv cx env es1 ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x
        (case t of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
                 | _ => mk_convert_op (BaseT AddressT) t))
      (typed_val_to_w256 tv v) t
      (convert_result cx (BaseT AddressT) t v) es1
Proof
  rpt strip_tac >> drule_all scalar_conversion_from_address >> strip_tac >>
  gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
  simp[mk_convert_op_def, is_bytestring_type_def]
  >- (irule scalar_address_uint_result_frag >> simp[]) >>
  irule scalar_address_bytes_result_frag >> simp[]
QED

Theorem scalar_fixed_typed_dispatch:
  !ctx func cenv cx env es1 m t tv v.
    valid_conversion (BaseT (BytesT (Fixed m))) t /\
    ~is_bytestring_type (BaseT (BytesT (Fixed m))) /\ ~is_bytestring_type t /\
    ~int_convert_pair (BaseT (BytesT (Fixed m))) t /\
    evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v /\
    expr_sim_inv cenv cx env es1 ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x
        (case t of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
                 | _ => mk_convert_op (BaseT (BytesT (Fixed m))) t))
      (typed_val_to_w256 tv v) t
      (convert_result cx (BaseT (BytesT (Fixed m))) t v) es1
Proof
  rpt strip_tac >> drule_all scalar_conversion_from_fixed >> strip_tac >>
  gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
  simp[]
  >- suspend "bool"
  >- suspend "signed"
  >- suspend "unsigned"
  >- suspend "address"
  >- suspend "decimal" >>
  suspend "fixed"
QED

Resume scalar_fixed_typed_dispatch[bool]:
  simp[mk_convert_op_def, is_bytestring_type_def] >> irule scalar_bytes_bool_result_frag >> simp[]
QED
Resume scalar_fixed_typed_dispatch[signed]:
  rename1 `BytesV bs` >> Cases_on `bs = []`
  >- (gvs[] >> simp[mk_convert_op_def, is_bytestring_type_def] >>
      irule scalar_bytes0_int_result_frag >> simp[]) >>
  simp[mk_convert_op_def, is_bytestring_type_def] >>
  irule scalar_bytes_int_result_frag >> simp[] >> Cases_on `bs` >> gvs[]
QED
Resume scalar_fixed_typed_dispatch[unsigned]:
  simp[mk_convert_op_def, is_bytestring_type_def] >> irule scalar_bytes_uint_result_frag >> simp[]
QED
Resume scalar_fixed_typed_dispatch[address]:
  simp[mk_convert_op_def, is_bytestring_type_def] >> irule scalar_bytes_address_result_frag >> simp[]
QED
Resume scalar_fixed_typed_dispatch[decimal]:
  rename1 `BytesV bs` >> Cases_on `bs = []`
  >- (gvs[] >> pure_rewrite_tac[scalar_fixed_decimal_mk_op] >>
      irule scalar_bytes0_decimal_result_frag) >>
  irule scalar_fixed_decimal_mk_frag >> simp[] >> Cases_on `bs` >> gvs[]
QED
Resume scalar_fixed_typed_dispatch[fixed]:
  simp[mk_convert_op_def, is_bytestring_type_def] >> irule scalar_bytes_fixed_result_frag >> simp[]
QED
Finalise scalar_fixed_typed_dispatch

Theorem scalar_int_typed_dispatch:
  !ctx func cenv cx env es1 n t tv v.
    valid_conversion (BaseT (IntT n)) t /\
    ~is_bytestring_type (BaseT (IntT n)) /\ ~is_bytestring_type t /\
    ~int_convert_pair (BaseT (IntT n)) t /\
    ~(BaseT (IntT n) = BaseT (BytesT (Fixed 0)) /\
      ((?k. t = BaseT (IntT k)) \/ t = BaseT DecimalT)) /\
    evaluate_type (get_tenv cx) (BaseT (IntT n)) = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v /\
    expr_sim_inv cenv cx env es1 ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x
        (case t of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
                 | _ => mk_convert_op (BaseT (IntT n)) t))
      (typed_val_to_w256 tv v) t
      (convert_result cx (BaseT (IntT n)) t v) es1
Proof
  rpt strip_tac >> drule_all scalar_conversion_from_int >> strip_tac >>
  gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >> simp[]
  >- suspend "bytes"
  >- suspend "address" >>
  suspend "decimal"
QED
Resume scalar_int_typed_dispatch[bytes]:
  simp[mk_convert_op_def, is_bytestring_type_def, typed_val_to_w256_def,
       val_to_w256_def] >>
  irule (SRULE[] (Q.SPEC `T` (Q.GEN `sg` (SPEC_ALL scalar_int_bytes_result_frag)))) >> simp[]
QED
Resume scalar_int_typed_dispatch[address]:
  simp[mk_convert_op_def, is_bytestring_type_def, typed_val_to_w256_def,
       val_to_w256_def] >>
  irule scalar_int_address_result_frag >>
  drule_all vyperArithTheory.within_int_bound_in_word_range >>
  simp[integer_wordTheory.INT_MIN_def, integer_wordTheory.INT_MAX_def,
       wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def, dimword_def] >>
  intLib.ARITH_TAC
QED
Resume scalar_int_typed_dispatch[decimal]:
  simp[typed_val_to_w256_def, val_to_w256_def] >>
  irule (SRULE[] (Q.SPEC `T` (Q.GEN `sg` (SPEC_ALL scalar_int_decimal_mk_frag)))) >> simp[]
QED
Finalise scalar_int_typed_dispatch

Theorem scalar_uint_address_result_frag:
  !ctx func cenv cx n i es0.
    0 < n /\ n <= 256 /\ within_int_bound (Unsigned n) i ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x (ConvIntToInt F n F 160))
      (i2w i) (BaseT AddressT)
      (convert_result cx (BaseT (UintT n)) (BaseT AddressT) (IntV i)) es0
Proof
  rpt strip_tac >>
  simp[convert_result_def, vyperValueOperationTheory.evaluate_convert_from_def,
       vyperValueOperationTheory.evaluate_convert_def] >>
  irule unop_frag_straight >>
  simp[straight_fresh_convert, is_word_type_def] >>
  Cases_on `within_int_bound (Unsigned 160) i` >> simp[]
  >- (strip_tac >> qexists_tac `i2w i` >>
      `0 <= i /\ i < &(2**160)` by fs[within_int_bound_ineq] >>
      `i = &Num i` by intLib.ARITH_TAC >>
      `Num i < 2**160` by (fs[] >> intLib.ARITH_TAC) >>
      simp[evaluate_type_def, scalar_typed_address_word] >>
      conj_tac
      >- (qpat_x_assum `i = &Num i` SUBST1_TAC >>
          simp[i2w_pos, w2w_def, w2n_n2w, dimword_def,
               fcpLib.INDEX_CONV ``dimindex(:160)``] >> fs[]) >>
      rpt strip_tac >> drule convert_int_run >> simp[] >>
      disch_then drule_all >> simp[]) >>
  strip_tac >> rpt strip_tac >> drule convert_int_run >> simp[] >>
  disch_then drule_all >> simp[]
QED

Theorem scalar_uint_typed_dispatch:
  !ctx func cenv cx env es1 n t tv v.
    valid_conversion (BaseT (UintT n)) t /\
    ~is_bytestring_type (BaseT (UintT n)) /\ ~is_bytestring_type t /\
    ~int_convert_pair (BaseT (UintT n)) t /\
    ~(BaseT (UintT n) = BaseT (BytesT (Fixed 0)) /\
      ((?k. t = BaseT (IntT k)) \/ t = BaseT DecimalT)) /\
    evaluate_type (get_tenv cx) (BaseT (UintT n)) = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v /\
    expr_sim_inv cenv cx env es1 ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x
        (case t of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
                 | _ => mk_convert_op (BaseT (UintT n)) t))
      (typed_val_to_w256 tv v) t
      (convert_result cx (BaseT (UintT n)) t v) es1
Proof
  rpt strip_tac >> drule_all scalar_conversion_from_uint >> strip_tac >>
  gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >> simp[]
  >- suspend "bytes"
  >- suspend "address"
  >- suspend "decimal" >>
  suspend "flag"
QED
Resume scalar_uint_typed_dispatch[bytes]:
  simp[mk_convert_op_def, is_bytestring_type_def, typed_val_to_w256_def,
       val_to_w256_def] >>
  irule (SRULE[] (Q.SPEC `F` (Q.GEN `sg` (SPEC_ALL scalar_int_bytes_result_frag)))) >>
  simp[within_int_bound_ineq]
QED
Resume scalar_uint_typed_dispatch[address]:
  simp[mk_convert_op_def, is_bytestring_type_def, typed_val_to_w256_def,
       val_to_w256_def] >>
  irule scalar_uint_address_result_frag >> simp[within_int_bound_ineq] >>
  `i = &Num i` by intLib.ARITH_TAC >>
  qpat_x_assum `i = &Num i` (fn th => CONV_TAC (LAND_CONV (REWR_CONV th))) >>
  simp[]
QED
Resume scalar_uint_typed_dispatch[decimal]:
  simp[typed_val_to_w256_def, val_to_w256_def] >>
  irule (SRULE[] (Q.SPEC `F` (Q.GEN `sg` (SPEC_ALL scalar_int_decimal_mk_frag)))) >>
  simp[within_int_bound_ineq] >>
  `i = &Num i` by intLib.ARITH_TAC >>
  qpat_x_assum `i = &Num i` (fn th => CONV_TAC (LAND_CONV (REWR_CONV th))) >>
  simp[]
QED
Resume scalar_uint_typed_dispatch[flag]:
  Cases_on `FLOOKUP (get_tenv cx) name` >> gvs[] >>
  rename1 `FLOOKUP _ _ = SOME args` >> Cases_on `args` >> gvs[] >>
  drule_all scalar_flag_member_count >> disch_then SUBST1_TAC >>
  simp[typed_val_to_w256_def, val_to_w256_def] >>
  irule scalar_to_flag_result_frag >> simp[within_int_bound_ineq] >>
  `i = &Num i` by intLib.ARITH_TAC >>
  qpat_x_assum `i = &Num i` (fn th => CONV_TAC (LAND_CONV (REWR_CONV th))) >>
  simp[]
QED
Finalise scalar_uint_typed_dispatch

Theorem scalar_decimal_typed_dispatch:
  !ctx func cenv cx env es1 t tv v.
    valid_conversion (BaseT DecimalT) t /\
    ~is_bytestring_type (BaseT DecimalT) /\ ~is_bytestring_type t /\
    ~int_convert_pair (BaseT DecimalT) t /\
    ~(BaseT DecimalT = BaseT (BytesT (Fixed 0)) /\
      ((?k. t = BaseT (IntT k)) \/ t = BaseT DecimalT)) /\
    evaluate_type (get_tenv cx) (BaseT DecimalT) = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v /\
    expr_sim_inv cenv cx env es1 ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x
        (case t of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
                 | _ => mk_convert_op (BaseT DecimalT) t))
      (typed_val_to_w256 tv v) t
      (convert_result cx (BaseT DecimalT) t v) es1
Proof
  rpt strip_tac >> drule scalar_conversion_from_decimal >> strip_tac >>
  gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
  simp[typed_val_to_w256_def, val_to_w256_def]
  >- (irule scalar_decimal_signed_mk_frag >> simp[]) >>
  rename1 `mk_convert_op _ (BaseT (UintT bits))` >> Cases_on `bits = 256`
  >- (gvs[] >> irule scalar_decimal_uint256_mk_frag >> simp[]) >>
  irule scalar_decimal_unsigned_mk_frag >> simp[]
QED

Theorem scalar_flag_typed_dispatch:
  !ctx func cenv cx env es1 name t tv v.
    valid_conversion (FlagT name) t /\
    ~is_bytestring_type (FlagT name) /\ ~is_bytestring_type t /\
    ~int_convert_pair (FlagT name) t /\
    ~(FlagT name = BaseT (BytesT (Fixed 0)) /\
      ((?k. t = BaseT (IntT k)) \/ t = BaseT DecimalT)) /\
    evaluate_type (get_tenv cx) (FlagT name) = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v /\
    expr_sim_inv cenv cx env es1 ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x
        (case t of FlagT target => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string target))
                 | _ => mk_convert_op (FlagT name) t))
      (typed_val_to_w256 tv v) t
      (convert_result cx (FlagT name) t v) es1
Proof
  rpt strip_tac >> drule scalar_conversion_from_flag >> strip_tac >>
  gvs[evaluate_type_def] >>
  Cases_on `FLOOKUP (get_tenv cx) name` >> gvs[] >>
  rename1 `FLOOKUP _ _ = SOME args` >> Cases_on `args` >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  simp[mk_convert_op_def, is_bytestring_type_def, type_bits_def, is_signed_type_def]
  >- suspend "signed"
  >- suspend "unsigned" >>
  irule scalar_flag_bytes_result_frag
QED
Resume scalar_flag_typed_dispatch[signed]:
  irule (SRULE[] (Q.SPEC `T` (Q.GEN `sg` (SPEC_ALL scalar_flag_int_result_frag)))) >>
  simp[] >> rename1 `payload < 2 ** members` >>
  `2 ** members <= 2 ** 256` by (irule bitTheory.TWOEXP_MONO2 >> simp[]) >>
  qpat_x_assum `2 ** members <= _` (mp_tac o CONV_RULE (RAND_CONV EVAL)) >>
  decide_tac
QED
Resume scalar_flag_typed_dispatch[unsigned]:
  irule (SRULE[] (Q.SPEC `F` (Q.GEN `sg` (SPEC_ALL scalar_flag_int_result_frag)))) >>
  simp[] >> rename1 `payload < 2 ** members` >>
  `2 ** members <= 2 ** 256` by (irule bitTheory.TWOEXP_MONO2 >> simp[]) >>
  qpat_x_assum `2 ** members <= _` (mp_tac o CONV_RULE (RAND_CONV EVAL)) >>
  decide_tac
QED
Finalise scalar_flag_typed_dispatch

Theorem scalar_typed_dispatch:
  !ctx func cenv cx env es1 src t tv v.
    valid_conversion src t /\
    ~is_bytestring_type src /\ ~is_bytestring_type t /\
    ~int_convert_pair src t /\
    evaluate_type (get_tenv cx) src = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v /\
    expr_sim_inv cenv cx env es1 ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x
        (case t of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
                 | _ => mk_convert_op src t))
      (typed_val_to_w256 tv v) t (convert_result cx src t v) es1
Proof
  rpt strip_tac >> drule_all scalar_conversion_source >> strip_tac >> gvs[]
  >- (irule scalar_fixed_typed_dispatch >> simp[] >> metis_tac[])
  >- (irule scalar_address_typed_dispatch >> simp[] >> metis_tac[])
  >- (irule scalar_int_typed_dispatch >> simp[] >> metis_tac[])
  >- (irule scalar_uint_typed_dispatch >> simp[] >> metis_tac[])
  >- (irule scalar_decimal_typed_dispatch >> simp[] >> metis_tac[]) >>
  irule scalar_flag_typed_dispatch >> simp[] >> metis_tac[]
QED

Theorem scalar_conversion_word_types:
  !tenv src t. valid_conversion src t /\ ~is_bytestring_type src /\
    ~is_bytestring_type t /\ ~int_convert_pair src t /\
    IS_SOME (evaluate_type tenv src) /\ IS_SOME (evaluate_type tenv t) ==>
    is_word_type src /\ is_word_type t
Proof
  rpt gen_tac >> strip_tac >> drule_all scalar_conversion_source >> strip_tac >> gvs[]
  >- (drule_all scalar_conversion_from_fixed >> strip_tac >>
      gvs[evaluate_type_def, is_word_type_def])
  >- (drule_all scalar_conversion_from_address >> strip_tac >>
      gvs[evaluate_type_def, is_word_type_def])
  >- (drule_all scalar_conversion_from_int >> strip_tac >>
      gvs[evaluate_type_def, is_word_type_def])
  >- (drule_all scalar_conversion_from_uint >> strip_tac >>
      gvs[evaluate_type_def, is_word_type_def])
  >- (drule scalar_conversion_from_decimal >> strip_tac >>
      gvs[evaluate_type_def, is_word_type_def]) >>
  drule scalar_conversion_from_flag >> strip_tac >> gvs[evaluate_type_def, is_word_type_def]
QED

Theorem scalar_dispatch_extends:
  !src t cenv x sa op sb.
    valid_conversion src t /\ ~is_bytestring_type src /\
    ~is_bytestring_type t /\ ~int_convert_pair src t /\
    compile_type_convert x
      (case t of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
               | _ => mk_convert_op src t) sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `compile_type_convert x conv` >>
  irule (INST_TYPE [``:'a`` |-> ``:operand``] straight_fresh_extends) >> qexistsl_tac [`compile_type_convert x conv`, `op`] >>
  simp[] >> unabbrev_all_tac >>
  drule_all scalar_conversion_source >> strip_tac >> gvs[]
  >- (drule_all scalar_conversion_from_fixed >> strip_tac >> gvs[] >>
      simp[mk_convert_op_def, is_bytestring_type_def, type_bounds_def,
           type_bits_def, is_signed_type_def,
           straight_fresh_convert_scalar, straight_fresh_convert])
  >- (drule_all scalar_conversion_from_address >> strip_tac >> gvs[] >>
      simp[mk_convert_op_def, is_bytestring_type_def, type_bounds_def,
           type_bits_def, is_signed_type_def,
           straight_fresh_convert_scalar, straight_fresh_convert])
  >- (drule_all scalar_conversion_from_int >> strip_tac >> gvs[] >>
      simp[mk_convert_op_def, is_bytestring_type_def, type_bounds_def,
           type_bits_def, is_signed_type_def,
           straight_fresh_convert_scalar, straight_fresh_convert])
  >- (drule_all scalar_conversion_from_uint >> strip_tac >> gvs[] >>
      simp[mk_convert_op_def, is_bytestring_type_def, type_bounds_def,
           type_bits_def, is_signed_type_def,
           straight_fresh_convert_scalar, straight_fresh_convert])
  >- (drule scalar_conversion_from_decimal >> strip_tac >> gvs[] >>
      simp[mk_convert_op_def, is_bytestring_type_def, type_bounds_def,
           type_bits_def, is_signed_type_def,
           straight_fresh_convert_scalar, straight_fresh_convert] >>
      IF_CASES_TAC >> simp[straight_fresh_convert_scalar]) >>
  drule scalar_conversion_from_flag >> strip_tac >> gvs[] >>
  simp[mk_convert_op_def, is_bytestring_type_def,
       straight_fresh_convert_scalar, straight_fresh_convert]
QED
