(* Concrete fixed-bytes conversion suffixes on memory-checked paths. *)
Theory bodyMemTbConvertScalarBytes
Ancestors
  bodyUnopFragMemory convertScalarBytesRun
  convertScalarEncoding convertScalarProps exprSimConvert exprUnopStraight
  valueEncodingProofs exprLowering compileEnv vyperValueOperation valueEncoding
  vyperValue venomExecSemantics list exprLoweringProps words integer_word
  builtinProps arithmeticProps

(* Empty fixed-bytes inputs are admitted by the conversion semantics. *)
Theorem convert_fixed0_int_result[local]:
  !cx b. 1 < b /\ b <= 256 ==>
    convert_result cx (BaseT (BytesT (Fixed 0))) (BaseT (IntT b))
      (BytesV []) = INL (IntV 0)
Proof
  `word_of_bytes_be (PAD_RIGHT (0w:word8) 32 []) = (0w:bytes32)` by
    (EVAL_TAC >> simp[]) >>
  `word_asr (0w:bytes32) 256 = 0w` by
    simp[fcpTheory.CART_EQ, word_asr_def, fcpTheory.FCP_BETA,
         word_msb_def, word_0] >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       within_int_bound_def, w2i_def]
QED

Theorem convert_fixed0_decimal_result[local]:
  !cx. convert_result cx (BaseT (BytesT (Fixed 0)))
    (BaseT DecimalT) (BytesV []) = INL (DecimalV 0)
Proof
  `word_of_bytes_be (PAD_RIGHT (0w:word8) 32 []) = (0w:bytes32)` by
    (EVAL_TAC >> simp[]) >>
  `word_asr (0w:bytes32) 256 = 0w` by
    simp[fcpTheory.CART_EQ, word_asr_def, fcpTheory.FCP_BETA,
         word_msb_def, word_0] >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       bounded_decimal_op_def, w2i_def] >> EVAL_TAC
QED

Theorem scalar_bytes_bool_frag_mem:
  !ctx func cenv cx m bs es0. LENGTH bs <= 32 ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x ConvToBool)
      (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs))
      (BaseT BoolT) (INL (BoolV (EXISTS (\b. b <> 0w) bs))) es0
Proof
  rpt strip_tac >> irule unop_frag_mem_straight >>
  simp[straight_fresh_convert, straight_fresh_convert_scalar, is_word_type_def] >> strip_tac >>
  qexists_tac `bool_to_word (EXISTS (\b. b <> 0w) bs)` >>
  simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def,
       bool_to_word_def] >>
  conj_tac >- (Cases_on `EXISTS (\b. b <> 0w) bs` >> simp[bool_to_word_def]) >>
  rpt strip_tac >> drule_all convert_bool_run >>
  simp[typed_val_to_w256_def, scalar_fixed_zero, EVERY_MEM, EXISTS_MEM,
       bool_to_word_def]
QED

Theorem scalar_bytes_widen_frag_mem:
  !ctx func cenv cx m n bs es0. m <= n /\ n <= 32 ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (ConvBytesMToBytesM m n))
      (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs))
      (BaseT (BytesT (Fixed n))) (INL (BytesV (PAD_RIGHT 0w n bs))) es0
Proof
  rpt strip_tac >> irule unop_frag_mem_straight >>
  simp[straight_fresh_convert, straight_fresh_convert_scalar, is_word_type_def] >> strip_tac >>
  qexists_tac `typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)` >>
  simp[evaluate_type_def, scalar_fixed_widen, typed_val_to_w256_def] >>
  rpt strip_tac >>
  gvs[compile_type_convert_def, comp_return_def, run_inst_seq_def,
      emitted_insts_def]
QED

Theorem scalar_bytes_uint_result_frag_mem:
  !ctx func cenv cx m b bs es0.
    LENGTH bs = m /\ m <= 32 /\ 0 < b /\ b <= 256 ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (ConvBytesToInt m F b))
      (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs))
      (BaseT (UintT b))
      (convert_result cx (BaseT (BytesT (Fixed m))) (BaseT (UintT b)) (BytesV bs)) es0
Proof
  rpt strip_tac >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes,
       evaluate_convert_def] >>
  qabbrev_tac `i:int = &(w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32))` >>
  irule unop_frag_mem_straight >>
  simp[straight_fresh_convert, straight_fresh_convert_scalar, is_word_type_def] >>
  Cases_on `within_int_bound (Unsigned b) i` >> simp[]
  >- (strip_tac >> qexists_tac `i2w i` >>
      simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
      rpt strip_tac >>
      irule (Q.SPEC `F` scalar_bytes_int_run_ok) >>
      simp[] >> qexistsl_tac [`b`, `bs`, `x`] >>
      simp[Abbr `i`, typed_val_to_w256_def]) >>
  strip_tac >> rpt strip_tac >>
  irule (Q.SPEC `F` scalar_bytes_int_run_abort) >>
  simp[] >> qexistsl_tac [`b`, `bs`, `op`, `x`] >> simp[Abbr `i`]
QED

Theorem scalar_bytes_int_result_frag_mem:
  !ctx func cenv cx m b bs es0.
    LENGTH bs = m /\ 0 < m /\ m <= 32 /\ 1 < b /\ b <= 256 ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (ConvBytesToInt m T b))
      (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs))
      (BaseT (IntT b))
      (convert_result cx (BaseT (BytesT (Fixed m))) (BaseT (IntT b)) (BytesV bs)) es0
Proof
  rpt strip_tac >>
  `bs <> []` by (Cases_on `bs` >> gvs[]) >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes,
       evaluate_convert_def] >>
  qabbrev_tac `i = w2i ((word_of_bytes_be (PAD_RIGHT 0w 32 bs):bytes32) >> (8*(32-m)))` >>
  irule unop_frag_mem_straight >>
  simp[straight_fresh_convert, straight_fresh_convert_scalar, is_word_type_def] >>
  Cases_on `within_int_bound (Signed b) i` >> simp[]
  >- (strip_tac >> qexists_tac `i2w i` >>
      simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
      rpt strip_tac >> irule (Q.SPEC `T` scalar_bytes_int_run_ok) >>
      simp[] >> qexistsl_tac [`b`, `bs`, `x`] >>
      simp[Abbr `i`, typed_val_to_w256_def]) >>
  strip_tac >> rpt strip_tac >> irule (Q.SPEC `T` scalar_bytes_int_run_abort) >>
  simp[] >> qexistsl_tac [`b`, `bs`, `op`, `x`] >>
  simp[Abbr `i`, typed_val_to_w256_def]
QED

Theorem scalar_bytes_decimal_result_frag_mem:
  !ctx func cenv cx m divisor bs es0.
    LENGTH bs = m /\ 0 < m /\ m <= 32 ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x
        (ConvBytesMToDecimal m divisor (-&(2**167)) (&(2**167)-1)))
      (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs))
      (BaseT DecimalT)
      (convert_result cx (BaseT (BytesT (Fixed m))) (BaseT DecimalT) (BytesV bs)) es0
Proof
  rpt strip_tac >>
  `bs <> []` by (Cases_on `bs` >> gvs[]) >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes,
       evaluate_convert_def, bounded_decimal_op_def] >>
  qabbrev_tac `i = w2i ((word_of_bytes_be (PAD_RIGHT 0w 32 bs):bytes32) >> (8*(32-m)))` >>
  irule unop_frag_mem_straight >>
  simp[straight_fresh_convert, straight_fresh_convert_scalar, is_word_type_def] >>
  Cases_on `within_int_bound decimal_bound i` >> fs[decimal_bits_def]
  >- (strip_tac >> qexists_tac `i2w i` >>
      simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
      rpt strip_tac >> irule scalar_bytes_decimal_run_ok >>
      simp[] >> qexistsl_tac [`bs`, `divisor`, `x`] >>
      simp[Abbr `i`, typed_val_to_w256_def]) >>
  strip_tac >> rpt strip_tac >> irule scalar_bytes_decimal_run_abort >>
  simp[] >> qexistsl_tac [`bs`, `divisor`, `op`, `x`] >>
  simp[Abbr `i`, typed_val_to_w256_def]
QED

Theorem scalar_bytes_narrow_result_frag_mem:
  !ctx func cenv cx m n bs es0.
    LENGTH bs = m /\ n < m /\ m <= 32 ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (ConvBytesMToBytesM m n))
      (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs))
      (BaseT (BytesT (Fixed n)))
      (convert_result cx (BaseT (BytesT (Fixed m)))
        (BaseT (BytesT (Fixed n))) (BytesV bs)) es0
Proof
  rpt strip_tac >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes,
       evaluate_convert_def] >>
  irule unop_frag_mem_straight >>
  simp[straight_fresh_convert, straight_fresh_convert_scalar, is_word_type_def] >>
  Cases_on `EVERY (\b. b = 0w) (DROP n bs)` >> simp[]
  >- (strip_tac >>
      qexists_tac `typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)` >>
      simp[evaluate_type_def, scalar_fixed_narrow] >>
      rpt strip_tac >> irule scalar_bytes_narrow_run_ok >>
      simp[] >> qexistsl_tac [`n`, `x`] >> simp[]) >>
  strip_tac >> rpt strip_tac >> irule scalar_bytes_narrow_run_abort >>
  simp[] >> qexistsl_tac [`bs`, `n`, `op`, `x`] >> simp[] >>
  gvs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

Theorem scalar_bytes_fixed_result_frag_mem:
  !ctx func cenv cx m n bs es0.
    LENGTH bs = m /\ m <= 32 /\ n <= 32 ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (ConvBytesMToBytesM m n))
      (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs))
      (BaseT (BytesT (Fixed n)))
      (convert_result cx (BaseT (BytesT (Fixed m)))
        (BaseT (BytesT (Fixed n))) (BytesV bs)) es0
Proof
  rpt strip_tac >> Cases_on `m <= n`
  >- (simp[convert_result_def, evaluate_convert_from_not_address_bytes,
           evaluate_convert_def] >>
      irule scalar_bytes_widen_frag_mem >> simp[]) >>
  irule scalar_bytes_narrow_result_frag_mem >> simp[]
QED

Theorem scalar_fixed0_int_result_frag_mem:
  !ctx func cenv cx b es0. 1 < b /\ b <= 256 ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (ConvBytesToInt 0 T b))
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 0))) (BytesV []))
      (BaseT (IntT b))
      (convert_result cx (BaseT (BytesT (Fixed 0))) (BaseT (IntT b)) (BytesV [])) es0
Proof
  rpt strip_tac >> simp[convert_fixed0_int_result] >>
  irule unop_frag_mem_straight >>
  simp[straight_fresh_convert, straight_fresh_convert_scalar, is_word_type_def] >>
  strip_tac >> qexists_tac `0w:bytes32` >>
  simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def, i2w_def] >>
  rpt strip_tac >>
  `word_asr (0w:bytes32) 256 = 0w` by
    simp[fcpTheory.CART_EQ, word_asr_def, fcpTheory.FCP_BETA,
         word_msb_def, word_0] >>
  drule (Q.SPEC `T` scalar_bytes_int_word_ok) >>
  disch_then (qspecl_then [`ss`, `0w:bytes32`] mp_tac) >>
  `word_of_bytes_be (PAD_RIGHT (0w:word8) 32 []) = (0w:bytes32)` by
    (EVAL_TAC >> simp[]) >>
  simp[typed_val_to_w256_def, val_to_w256_def, in_type_range_def,
       type_bounds_def, math_val_def, is_signed_type_def, type_bits_def,
       dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``, w2i_def]
QED

Theorem scalar_fixed0_decimal_result_frag_mem:
  !ctx func cenv cx divisor es0.
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x
        (ConvBytesMToDecimal 0 divisor (-&(2**167)) (&(2**167)-1)))
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 0))) (BytesV []))
      (BaseT DecimalT)
      (convert_result cx (BaseT (BytesT (Fixed 0))) (BaseT DecimalT) (BytesV [])) es0
Proof
  rpt strip_tac >> simp[convert_fixed0_decimal_result, scalar_bytes_decimal_eq] >>
  irule unop_frag_mem_straight >>
  simp[straight_fresh_convert, straight_fresh_convert_scalar, is_word_type_def] >>
  strip_tac >> qexists_tac `0w:bytes32` >>
  simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def, i2w_def] >>
  rpt strip_tac >>
  `word_asr (0w:bytes32) 256 = 0w` by
    simp[fcpTheory.CART_EQ, word_asr_def, fcpTheory.FCP_BETA,
         word_msb_def, word_0] >>
  drule (Q.SPEC `T` scalar_bytes_int_word_ok) >>
  disch_then (qspecl_then [`ss`, `0w:bytes32`] mp_tac) >>
  `word_of_bytes_be (PAD_RIGHT (0w:word8) 32 []) = (0w:bytes32)` by
    (EVAL_TAC >> simp[]) >>
  simp[typed_val_to_w256_def, val_to_w256_def, in_type_range_def,
       type_bounds_def, math_val_def, is_signed_type_def, type_bits_def,
       dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``, w2i_def]
QED

Theorem scalar_bytes_integer_result_frag_mem:
  !ctx func cenv cx sg m b bs es0.
    LENGTH bs = m /\ m <= 32 /\ 0 < b /\ b <= 256 /\
    (sg ==> 1 < b) ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (ConvBytesToInt m sg b))
      (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs))
      (BaseT (if sg then IntT b else UintT b))
      (convert_result cx (BaseT (BytesT (Fixed m)))
        (BaseT (if sg then IntT b else UintT b)) (BytesV bs)) es0
Proof
  rpt strip_tac >> Cases_on `sg` >> gvs[]
  >- (Cases_on `bs = []`
      >- (gvs[] >> irule scalar_fixed0_int_result_frag_mem >> simp[]) >>
      irule scalar_bytes_int_result_frag_mem >> Cases_on `bs` >> gvs[]) >>
  irule scalar_bytes_uint_result_frag_mem >> simp[]
QED

Theorem scalar_bytes_decimal_all_result_frag_mem:
  !ctx func cenv cx m divisor bs es0.
    LENGTH bs = m /\ m <= 32 ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x
        (ConvBytesMToDecimal m divisor (-&(2**167)) (&(2**167)-1)))
      (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs))
      (BaseT DecimalT)
      (convert_result cx (BaseT (BytesT (Fixed m))) (BaseT DecimalT) (BytesV bs)) es0
Proof
  rpt strip_tac >> Cases_on `bs = []`
  >- (gvs[] >> irule (SRULE [] scalar_fixed0_decimal_result_frag_mem)) >>
  irule scalar_bytes_decimal_result_frag_mem >> Cases_on `bs` >> gvs[]
QED

Theorem scalar_bytes_address_result_frag_mem:
  !ctx func cenv cx m bs es0.
    LENGTH bs = m /\ m <= 32 ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (ConvBytesToAddress m))
      (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs))
      (BaseT AddressT)
      (convert_result cx (BaseT (BytesT (Fixed m))) (BaseT AddressT) (BytesV bs)) es0
Proof
  rpt strip_tac >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes,
       evaluate_convert_def] >>
  qabbrev_tac `u = w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32)` >>
  irule unop_frag_mem_straight >>
  simp[straight_fresh_convert, straight_fresh_convert_scalar, is_word_type_def] >>
  Cases_on `u < 2**160` >> fs[]
  >- (strip_tac >> qexists_tac `n2w u` >>
      conj_tac
      >- (simp[evaluate_type_def] >>
          `LENGTH (word_to_bytes (n2w u:address) T) = 20` by
            simp[byteTheory.LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:160)``] >>
          mp_tac (Q.INST [`a` |-> `n2w u`] val_to_w256_address) >>
          simp[typed_val_to_w256_def, val_to_w256_def, w2w_def, w2n_n2w,
               dimword_def, fcpLib.INDEX_CONV ``dimindex(:160)``]) >>
      rpt strip_tac >> irule scalar_bytes_address_run_ok >>
      simp[] >> qexistsl_tac [`bs`, `x`] >> simp[Abbr `u`]) >>
  strip_tac >> rpt strip_tac >> irule scalar_bytes_address_run_abort >>
  simp[] >> qexistsl_tac [`bs`, `op`, `x`] >> simp[Abbr `u`]
QED
