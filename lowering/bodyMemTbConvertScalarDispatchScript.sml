(* Typed dispatch for the memory-checked scalar conversion suffixes. *)
Theory bodyMemTbConvertScalarDispatch
Ancestors
  bodyMemTbConvertScalarFlags bodyMemTbConvertScalarBytes
  bodyMemTbConvertScalarOutputs bodyMemTbConvertScalarDecimal
  convertScalarDispatch convertScalarTyping exprSimConvert compileEnv
  bodyUnopFragMemory exprUnopStraight convertScalarEncoding convertScalarBytes
  exprSimUnop valueEncoding vyperValueOperation integer_word words arithmeticProps
  exprSimHyps vyperTypeSystem vyperTyping vyperValue exprLowering
Libs intLib

Theorem scalar_fixed_typed_dispatch_mem:
  !ctx func cenv cx es1 m t tv v.
    valid_conversion (BaseT (BytesT (Fixed m))) t /\
    ~is_bytestring_type t /\
    evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (mk_convert_op (BaseT (BytesT (Fixed m))) t))
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

Resume scalar_fixed_typed_dispatch_mem[bool]:
  simp[mk_convert_op_def, is_bytestring_type_def, convert_result_def,
       vyperValueOperationTheory.evaluate_convert_from_def,
       vyperValueOperationTheory.evaluate_convert_def] >>
  irule scalar_bytes_bool_frag_mem >> simp[]
QED
Resume scalar_fixed_typed_dispatch_mem[signed]:
  simp[mk_convert_op_def, is_bytestring_type_def] >>
  irule (Q.INST [`sg` |-> `T`] (SPEC_ALL scalar_bytes_integer_result_frag_mem) |> SRULE []) >> simp[]
QED
Resume scalar_fixed_typed_dispatch_mem[unsigned]:
  simp[mk_convert_op_def, is_bytestring_type_def] >>
  irule (Q.INST [`sg` |-> `F`] (SPEC_ALL scalar_bytes_integer_result_frag_mem) |> SRULE []) >> simp[]
QED
Resume scalar_fixed_typed_dispatch_mem[address]:
  simp[mk_convert_op_def, is_bytestring_type_def] >>
  irule scalar_bytes_address_result_frag_mem >> simp[]
QED
Resume scalar_fixed_typed_dispatch_mem[decimal]:
  pure_rewrite_tac[scalar_fixed_decimal_mk_op] >>
  irule scalar_bytes_decimal_all_result_frag_mem >> simp[]
QED
Resume scalar_fixed_typed_dispatch_mem[fixed]:
  simp[mk_convert_op_def, is_bytestring_type_def] >>
  irule scalar_bytes_fixed_result_frag_mem >> simp[]
QED
Finalise scalar_fixed_typed_dispatch_mem

Theorem scalar_address_typed_dispatch_mem:
  !ctx func cenv cx es1 t tv v.
    valid_conversion (BaseT AddressT) t /\ ~is_bytestring_type t /\
    evaluate_type (get_tenv cx) (BaseT AddressT) = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (mk_convert_op (BaseT AddressT) t))
      (typed_val_to_w256 tv v) t
      (convert_result cx (BaseT AddressT) t v) es1
Proof
  rpt strip_tac >> drule_all scalar_conversion_from_address >> strip_tac >>
  gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
  simp[mk_convert_op_def, is_bytestring_type_def]
  >- (irule scalar_address_uint_result_frag_mem >> simp[]) >>
  irule scalar_address_bytes_result_frag_mem >> simp[]
QED

Theorem scalar_flag_typed_dispatch_mem:
  !ctx func cenv cx es1 name t tv v.
    valid_conversion (FlagT name) t /\
    evaluate_type (get_tenv cx) (FlagT name) = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (mk_convert_op (FlagT name) t))
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
  irule scalar_flag_bytes_result_frag_mem
QED
Resume scalar_flag_typed_dispatch_mem[signed]:
  irule (Q.INST [`sg` |-> `T`] (SPEC_ALL scalar_flag_int_result_frag_mem) |> SRULE []) >>
  simp[] >> rename1 `payload < 2 ** members` >>
  `2 ** members <= 2 ** 256` by (irule bitTheory.TWOEXP_MONO2 >> simp[]) >>
  qpat_x_assum `2 ** members <= _` (mp_tac o CONV_RULE (RAND_CONV EVAL)) >>
  decide_tac
QED
Resume scalar_flag_typed_dispatch_mem[unsigned]:
  irule (Q.INST [`sg` |-> `F`] (SPEC_ALL scalar_flag_int_result_frag_mem) |> SRULE []) >>
  simp[] >> rename1 `payload < 2 ** members` >>
  `2 ** members <= 2 ** 256` by (irule bitTheory.TWOEXP_MONO2 >> simp[]) >>
  qpat_x_assum `2 ** members <= _` (mp_tac o CONV_RULE (RAND_CONV EVAL)) >>
  decide_tac
QED
Finalise scalar_flag_typed_dispatch_mem

Theorem scalar_uint_address_result_frag_mem[local]:
  !ctx func cenv cx n i es0.
    0 < n /\ n <= 256 /\ within_int_bound (Unsigned n) i ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (ConvIntToInt F n F 160))
      (i2w i) (BaseT AddressT)
      (convert_result cx (BaseT (UintT n)) (BaseT AddressT) (IntV i)) es0
Proof
  rpt strip_tac >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  irule unop_frag_mem_straight >>
  simp[straight_fresh_convert, is_word_type_def] >>
  Cases_on `within_int_bound (Unsigned 160) i` >> simp[]
  >- (strip_tac >> qexists_tac `i2w i` >>
      `0 <= i /\ i < &(2**160)` by fs[within_int_bound_ineq] >>
      `i = &Num i` by intLib.ARITH_TAC >>
      `Num i < 2**160` by (fs[] >> intLib.ARITH_TAC) >>
      simp[evaluate_type_def, scalar_typed_address_word] >> conj_tac
      >- (qpat_x_assum `i = &Num i` SUBST1_TAC >>
          simp[i2w_pos, w2w_def, w2n_n2w, dimword_def,
               fcpLib.INDEX_CONV ``dimindex(:160)``] >> fs[]) >>
      rpt strip_tac >> drule convert_int_run >> simp[] >>
      disch_then drule_all >> simp[]) >>
  strip_tac >> rpt strip_tac >> drule convert_int_run >> simp[] >>
  disch_then drule_all >> simp[]
QED

Theorem scalar_int_typed_dispatch_mem[local]:
  !ctx func cenv cx env es1 n t tv v.
    valid_conversion (BaseT (IntT n)) t /\
    ~is_bytestring_type (BaseT (IntT n)) /\ ~is_bytestring_type t /\
    ~int_convert_pair (BaseT (IntT n)) t /\
    ~(BaseT (IntT n) = BaseT (BytesT (Fixed 0)) /\
      ((?k. t = BaseT (IntT k)) \/ t = BaseT DecimalT)) /\
    evaluate_type (get_tenv cx) (BaseT (IntT n)) = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v /\
    expr_sim_inv cenv cx env es1 ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x
        (case t of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
                 | _ => mk_convert_op (BaseT (IntT n)) t))
      (typed_val_to_w256 tv v) t
      (convert_result cx (BaseT (IntT n)) t v) es1
Proof
  rpt strip_tac >> drule_all scalar_conversion_from_int >> strip_tac >>
  gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >> simp[]
  >- suspend "bytes"
  >- suspend "address" >> suspend "decimal"
QED
Resume scalar_int_typed_dispatch_mem[bytes]:
  simp[mk_convert_op_def, is_bytestring_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  irule (SRULE[] (Q.INST [`sg` |-> `T`] (SPEC_ALL scalar_int_bytes_result_frag_mem))) >> simp[]
QED
Resume scalar_int_typed_dispatch_mem[address]:
  simp[mk_convert_op_def, is_bytestring_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  irule scalar_int_address_result_frag_mem >>
  drule_all vyperArithTheory.within_int_bound_in_word_range >>
  simp[integer_wordTheory.INT_MIN_def, integer_wordTheory.INT_MAX_def,
       wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def, dimword_def] >> intLib.ARITH_TAC
QED
Resume scalar_int_typed_dispatch_mem[decimal]:
  simp[typed_val_to_w256_def, val_to_w256_def] >>
  irule (SRULE[] (Q.INST [`sg` |-> `T`] (SPEC_ALL scalar_int_decimal_mk_frag_mem))) >> simp[]
QED
Finalise scalar_int_typed_dispatch_mem

Theorem scalar_uint_typed_dispatch_mem[local]:
  !ctx func cenv cx env es1 n t tv v.
    valid_conversion (BaseT (UintT n)) t /\
    ~is_bytestring_type (BaseT (UintT n)) /\ ~is_bytestring_type t /\
    ~int_convert_pair (BaseT (UintT n)) t /\
    ~(BaseT (UintT n) = BaseT (BytesT (Fixed 0)) /\
      ((?k. t = BaseT (IntT k)) \/ t = BaseT DecimalT)) /\
    evaluate_type (get_tenv cx) (BaseT (UintT n)) = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v /\
    expr_sim_inv cenv cx env es1 ==>
    unop_frag_mem ctx func cenv cx
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
  >- suspend "decimal" >> suspend "flag"
QED
Resume scalar_uint_typed_dispatch_mem[bytes]:
  simp[mk_convert_op_def, is_bytestring_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  irule (SRULE[] (Q.INST [`sg` |-> `F`] (SPEC_ALL scalar_int_bytes_result_frag_mem))) >>
  simp[within_int_bound_ineq]
QED
Resume scalar_uint_typed_dispatch_mem[address]:
  simp[mk_convert_op_def, is_bytestring_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  irule scalar_uint_address_result_frag_mem >> simp[within_int_bound_ineq] >>
  `i = &Num i` by intLib.ARITH_TAC >>
  qpat_x_assum `i = &Num i` (fn th => CONV_TAC (LAND_CONV (REWR_CONV th))) >> simp[]
QED
Resume scalar_uint_typed_dispatch_mem[decimal]:
  simp[typed_val_to_w256_def, val_to_w256_def] >>
  irule (SRULE[] (Q.INST [`sg` |-> `F`] (SPEC_ALL scalar_int_decimal_mk_frag_mem))) >>
  simp[within_int_bound_ineq] >> `i = &Num i` by intLib.ARITH_TAC >>
  qpat_x_assum `i = &Num i` (fn th => CONV_TAC (LAND_CONV (REWR_CONV th))) >> simp[]
QED
Resume scalar_uint_typed_dispatch_mem[flag]:
  Cases_on `FLOOKUP (get_tenv cx) name` >> gvs[] >>
  rename1 `FLOOKUP _ _ = SOME args` >> Cases_on `args` >> gvs[] >>
  drule_all scalar_flag_member_count >> disch_then SUBST1_TAC >>
  simp[typed_val_to_w256_def, val_to_w256_def] >>
  irule scalar_to_flag_result_frag_mem >> simp[within_int_bound_ineq] >>
  `i = &Num i` by intLib.ARITH_TAC >>
  qpat_x_assum `i = &Num i` (fn th => CONV_TAC (LAND_CONV (REWR_CONV th))) >> simp[]
QED
Finalise scalar_uint_typed_dispatch_mem

Theorem scalar_decimal_typed_dispatch_mem[local]:
  !ctx func cenv cx env es1 t tv v.
    valid_conversion (BaseT DecimalT) t /\
    ~is_bytestring_type (BaseT DecimalT) /\ ~is_bytestring_type t /\
    ~int_convert_pair (BaseT DecimalT) t /\
    ~(BaseT DecimalT = BaseT (BytesT (Fixed 0)) /\
      ((?k. t = BaseT (IntT k)) \/ t = BaseT DecimalT)) /\
    evaluate_type (get_tenv cx) (BaseT DecimalT) = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v /\
    expr_sim_inv cenv cx env es1 ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x
        (case t of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
                 | _ => mk_convert_op (BaseT DecimalT) t))
      (typed_val_to_w256 tv v) t
      (convert_result cx (BaseT DecimalT) t v) es1
Proof
  rpt strip_tac >> drule scalar_conversion_from_decimal >> strip_tac >>
  gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
  simp[typed_val_to_w256_def, val_to_w256_def]
  >- (irule scalar_decimal_signed_mk_frag_mem >> simp[]) >>
  rename1 `mk_convert_op _ (BaseT (UintT bits))` >> Cases_on `bits = 256`
  >- (gvs[] >> irule scalar_decimal_uint256_mk_frag_mem >> simp[]) >>
  irule scalar_decimal_unsigned_mk_frag_mem >> simp[]
QED

Theorem scalar_typed_dispatch_mem:
  !ctx func cenv cx env es1 src t tv v.
    valid_conversion src t /\
    ~is_bytestring_type src /\ ~is_bytestring_type t /\
    ~int_convert_pair src t /\
    ~(src = BaseT (BytesT (Fixed 0)) /\
      ((?k. t = BaseT (IntT k)) \/ t = BaseT DecimalT)) /\
    evaluate_type (get_tenv cx) src = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v /\
    expr_sim_inv cenv cx env es1 ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x
        (case t of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
                 | _ => mk_convert_op src t))
      (typed_val_to_w256 tv v) t (convert_result cx src t v) es1
Proof
  rpt strip_tac >> drule_all scalar_conversion_source >> strip_tac >> gvs[]
  >- (drule_all scalar_conversion_from_fixed >> strip_tac >> gvs[] >>
      irule scalar_fixed_typed_dispatch_mem >> simp[] >> metis_tac[])
  >- (drule_all scalar_conversion_from_address >> strip_tac >> gvs[] >>
      irule scalar_address_typed_dispatch_mem >> simp[] >> metis_tac[])
  >- (irule scalar_int_typed_dispatch_mem >> simp[] >> metis_tac[])
  >- (irule scalar_uint_typed_dispatch_mem >> simp[] >> metis_tac[])
  >- (irule scalar_decimal_typed_dispatch_mem >> simp[] >> metis_tac[]) >>
  drule scalar_conversion_from_flag >> strip_tac >> gvs[] >>
  irule scalar_flag_typed_dispatch_mem >> simp[] >> metis_tac[]
QED
