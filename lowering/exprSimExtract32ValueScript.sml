(* Judgment-independent extract32 window and conversion facts. *)
Theory exprSimExtract32Value
Ancestors
  valueEncoding valueEncodingDefs valueEncodingProofs vyperInterpreter vyperContext vyperValue vyperTypeSystem
  arithmeticProps compileEnv vyperValueOperation byte words integer_word integer list rich_list
Libs
  wordsLib intLib

Theorem extract32_memory_slice:
  val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p mem /\
  n + 32 <= LENGTH bs ==>
  mem_word_at (p + 32 + n) mem =
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP n bs))
Proof
  simp[val_in_memory_def] >> strip_tac >>
  `mem_bytes_at 0 (LENGTH bs) bs = bs` by
    simp[mem_bytes_at_def, rich_listTheory.TAKE_APPEND] >>
  `mem_bytes_at (p + 32) (LENGTH bs) mem =
   mem_bytes_at 0 (LENGTH bs) bs` by simp[] >>
  drule valueEncodingProofsTheory.mem_bytes_at_translated_window >>
  disch_then (qspecl_then [`n`, `32`] mp_tac) >> simp[] >>
  `n + 32 - LENGTH bs = 0` by decide_tac >>
  simp[mem_word_at_def, mem_bytes_at_def,
       rich_listTheory.TAKE_APPEND, listTheory.LENGTH_DROP]
QED

Theorem extract32_convert_uint:
  !env win n.
    LENGTH win = 32 ==>
    evaluate_convert env (BytesV win) (BaseT (UintT n)) =
      if arithmeticProps$in_type_range (BaseT (UintT n))
           (&(w2n (word_of_bytes T (0w:bytes32) win)))
      then INL (IntV (&(w2n (word_of_bytes T (0w:bytes32) win))))
      else INR (RuntimeError "convert BytesV uint bound")
Proof
  rpt strip_tac >>
  simp[evaluate_convert_def, PAD_LEFT, PAD_RIGHT, byteTheory.word_of_bytes_be_def,
       arithmeticPropsTheory.in_type_range_def, type_bits_def, is_signed_type_def,
       within_int_bound_def]
QED

Theorem extract32_convert_int:
  !env win n.
    LENGTH win = 32 /\ 0 < n ==>
    evaluate_convert env (BytesV win) (BaseT (IntT n)) =
      if arithmeticProps$in_type_range (BaseT (IntT n))
           (w2i (word_of_bytes T (0w:bytes32) win))
      then INL (IntV (w2i (word_of_bytes T (0w:bytes32) win)))
      else INR (RuntimeError "convert BytesV int bound")
Proof
  rpt strip_tac >>
  simp[evaluate_convert_def, PAD_LEFT, PAD_RIGHT, byteTheory.word_of_bytes_be_def,
       arithmeticPropsTheory.in_type_range_def, type_bits_def, is_signed_type_def,
       within_int_bound_def] >>
  qmatch_goalsub_abbrev_tac `w2i w` >>
  `0 < 2 ** (n - 1)` by simp[] >>
  `&(2 ** (n - 1) - 1) = (&(2 ** (n - 1)):int) - 1` by
    simp[integerTheory.INT_SUB] >>
  `((if w2i w < 0 then Num (-w2i w) <= 2 ** (n - 1)
      else Num (w2i w) < 2 ** (n - 1)) =
    (-&(2 ** (n - 1)) <= w2i w /\
      w2i w <= &(2 ** (n - 1)) - 1))` suffices_by simp[] >>
  Cases_on `w2i w < 0` >> simp[]
  >- (once_rewrite_tac [GSYM integerTheory.INT_LE] >>
      `0 <= -w2i w` by intLib.ARITH_TAC >>
      pure_asm_rewrite_tac [integerTheory.INT_OF_NUM] >> intLib.ARITH_TAC) >>
  once_rewrite_tac [GSYM integerTheory.INT_LT] >>
  `0 <= w2i w` by intLib.ARITH_TAC >>
  pure_asm_rewrite_tac [integerTheory.INT_OF_NUM] >> intLib.ARITH_TAC
QED

Theorem extract32_numeric_encoding:
  (!n win. typed_val_to_w256 (BaseTV (UintT n))
      (IntV (&(w2n (word_of_bytes T (0w:bytes32) win)))) =
      word_of_bytes T (0w:bytes32) win) /\
  (!n win. typed_val_to_w256 (BaseTV (IntT n))
      (IntV (w2i (word_of_bytes T (0w:bytes32) win))) =
      word_of_bytes T (0w:bytes32) win)
Proof
  simp[typed_val_to_w256_def, val_to_w256_def,
       integer_wordTheory.i2w_pos, integer_wordTheory.i2w_w2i]
QED

Theorem extract32_convert_fixed:
  !env win m.
    LENGTH win = 32 /\ m <= 32 ==>
    evaluate_convert env (BytesV win) (BaseT (BytesT (Fixed m))) =
      if EVERY ($= 0w) (DROP m win)
      then INL (BytesV (TAKE m win))
      else INR (RuntimeError "convert BytesV bound")
Proof
  rpt strip_tac >> simp[evaluate_convert_def] >>
  Cases_on `m = 32`
  >- (gvs[PAD_RIGHT] >>
      `DROP 32 win = []` by (simp[GSYM LENGTH_NIL, LENGTH_DROP]) >> simp[]) >>
  `~(32 <= m)` by decide_tac >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem extract32_fixed_encoding:
  !win m.
    LENGTH win = 32 /\ m <= 32 /\ EVERY ($= 0w) (DROP m win) ==>
    typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV (TAKE m win)) =
      word_of_bytes T (0w:bytes32) win
Proof
  rpt strip_tac >>
  `!xs:byte list. EVERY ($= 0w) xs ==> xs = REPLICATE (LENGTH xs) 0w` by
    (Induct >> simp[] >> metis_tac[]) >>
  `DROP m win = REPLICATE (32 - m) 0w` by metis_tac[LENGTH_DROP] >>
  simp[typed_val_to_w256_def, byteTheory.word_of_bytes_be_def, PAD_RIGHT] >>
  gvs[GSYM REPLICATE_GENLIST] >> metis_tac[TAKE_DROP]
QED

Theorem extract32_convert_address:
  !env win.
    LENGTH win = 32 ==>
    evaluate_convert env (BytesV win) (BaseT AddressT) =
      if w2n (word_of_bytes T (0w:bytes32) win) < 2 ** 160
      then INL (AddressV (n2w (w2n (word_of_bytes T (0w:bytes32) win))))
      else INR (RuntimeError "convert bytes address")
Proof
  simp[evaluate_convert_def, PAD_LEFT, byteTheory.word_of_bytes_be_def]
QED

Theorem extract32_address_encoding:
  !w:bytes32. w2n w < 2 ** 160 ==>
    typed_val_to_w256 (BaseTV AddressT) (AddressV (n2w (w2n w))) = w
Proof
  rpt strip_tac >>
  simp[typed_val_to_w256_def, byteTheory.word_of_bytes_be_def,
       GSYM valueEncodingProofsTheory.word_to_bytes_w2w_address,
       byteTheory.word_of_bytes_word_to_bytes] >>
  simp[wordsTheory.w2w_def, wordsTheory.w2n_n2w,
       wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  fs[arithmeticTheory.MOD_LESS, EVAL ``2 ** 160``]
QED

Theorem extract32_shift_zero_bits:
  !w:bytes32. !k. k <= 256 ==>
    (w << k = 0w <=> !i. i < 256 - k ==> ~(w ' i))
Proof
  rpt strip_tac >>
  simp_tac (std_ss ++ fcpLib.FCP_ss ++ numSimps.ARITH_ss)
    [wordsTheory.word_lsl_def, wordsTheory.word_0,
     fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  eq_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `i + k` mp_tac) >> simp[]) >>
  rpt strip_tac >> Cases_on `k <= i` >> simp[]
QED

Theorem extract32_byte_zero_bits:
  !w:bytes32. !j. j < 32 ==>
    (get_byte (n2w j) w T = 0w <=>
     !r. r < 8 ==> ~(w ' (8 * (31 - j) + r)))
Proof
  rpt strip_tac >>
  `j < dimword (:256)` by (simp[wordsTheory.dimword_def] >> decide_tac) >>
  simp_tac (std_ss ++ fcpLib.FCP_ss ++ numSimps.ARITH_ss)
    [byteTheory.get_byte_def, byteTheory.byte_index_def,
     wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
     wordsTheory.w2w, wordsTheory.word_lsr_def, wordsTheory.word_0,
     fcpLib.INDEX_CONV ``dimindex(:256)``,
     fcpLib.INDEX_CONV ``dimindex(:8)``] >>
  simp[LET_THM, arithmeticTheory.LESS_MOD] >>
  `32 - (j + 1) = 31 - j` by decide_tac >> simp[]
QED

Theorem extract32_window_byte:
  !win j. LENGTH win = 32 /\ j < 32 ==>
    get_byte (n2w j) (word_of_bytes T (0w:bytes32) win) T = EL j win
Proof
  rpt strip_tac >>
  simp[byteTheory.get_byte_word_of_bytes_be,
       byteTheory.first_byte_at_0w, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem extract32_drop_zero:
  !win m. m <= LENGTH win ==>
    (EVERY ($= (0w:byte)) (DROP m win) <=>
     !j. m <= j /\ j < LENGTH win ==> EL j win = 0w)
Proof
  rpt strip_tac >> simp[EVERY_EL, LENGTH_DROP, EL_DROP] >>
  eq_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `j - m` mp_tac) >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem extract32_suffix_shift:
  !win m. LENGTH win = 32 /\ m <= 32 ==>
    (EVERY ($= 0w) (DROP m win) <=>
     ((word_of_bytes T (0w:bytes32) win) << (m * 8) = 0w))
Proof
  rpt strip_tac >>
  `m * 8 <= 256` by decide_tac >>
  simp[extract32_drop_zero, extract32_shift_zero_bits] >>
  eq_tac
  >- (rpt strip_tac >>
      `i DIV 8 < 32 /\ i MOD 8 < 8 /\
       i = 8 * (i DIV 8) + i MOD 8` by
        (mp_tac (Q.SPEC `8` arithmeticTheory.DIVISION) >> simp[] >>
         disch_then (qspec_then `i` mp_tac) >> decide_tac) >>
      `m <= 31 - i DIV 8 /\ 31 - i DIV 8 < 32 /\
       8 * (31 - (31 - i DIV 8)) + i MOD 8 = i` by decide_tac >>
      first_x_assum (qspec_then `31 - i DIV 8` mp_tac) >> simp[] >>
      drule_all extract32_window_byte >>
      drule_all extract32_byte_zero_bits >> metis_tac[]) >>
  rpt strip_tac >>
  `get_byte (n2w j) (word_of_bytes T (0w:bytes32) win) T = EL j win` by
    (irule extract32_window_byte >> simp[]) >>
  pop_assum (SUBST1_TAC o SYM) >>
  simp[extract32_byte_zero_bits] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem extract32_address_padding:
  !win. LENGTH win = 32 /\ EVERY ($= (0w:byte)) (TAKE 12 win) ==>
    PAD_LEFT 0w 32 (DROP 12 win) = win
Proof
  rpt strip_tac >>
  `!xs:byte list. EVERY ($= 0w) xs ==> xs = REPLICATE (LENGTH xs) 0w` by
    (Induct >> simp[] >> metis_tac[]) >>
  `LENGTH (TAKE 12 win) = 12` by simp[] >>
  `TAKE 12 win = REPLICATE 12 0w` by metis_tac[] >>
  simp[PAD_LEFT, GSYM REPLICATE_GENLIST] >> metis_tac[TAKE_DROP]
QED

Theorem extract32_address_bytes_encoding:
  !win. LENGTH win = 32 /\ EVERY ($= (0w:byte)) (TAKE 12 win) ==>
    typed_val_to_w256 (BaseTV AddressT) (BytesV (DROP 12 win)) =
      word_of_bytes T (0w:bytes32) win
Proof
  rpt strip_tac >>
  simp[typed_val_to_w256_def, byteTheory.word_of_bytes_be_def,
       extract32_address_padding]
QED

Theorem extract32_address_bound_bits:
  !w:bytes32. w2n w < 2 ** 160 <=>
    !i. 160 <= i /\ i < 256 ==> ~(w ' i)
Proof
  gen_tac >>
  `w2n w < 2 ** 160 <=> w >>> 160 = 0w` by
    (CONV_TAC (RAND_CONV (REWR_CONV (GSYM wordsTheory.w2n_11))) >>
     pure_rewrite_tac [wordsTheory.w2n_lsr, wordsTheory.w2n_n2w,
                       wordsTheory.word_0_n2w] >> simp[arithmeticTheory.DIV_EQ_X]) >>
  pop_assum SUBST1_TAC >>
  simp_tac (std_ss ++ fcpLib.FCP_ss ++ numSimps.ARITH_ss)
    [wordsTheory.word_lsr_def, wordsTheory.word_0,
     fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  eq_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `i - 160` mp_tac) >> simp[]) >>
  rpt strip_tac >> Cases_on `i + 160 < 256` >> simp[]
QED

Theorem extract32_address_prefix_bound:
  !win. LENGTH win = 32 ==>
    (EVERY ($= (0w:byte)) (TAKE 12 win) <=>
     w2n (word_of_bytes T (0w:bytes32) win) < 2 ** 160)
Proof
  rpt strip_tac >>
  simp[EVERY_EL, EL_TAKE, extract32_address_bound_bits] >>
  eq_tac
  >- (rpt strip_tac >>
      `i DIV 8 < 32 /\ i MOD 8 < 8 /\
       i = 8 * (i DIV 8) + i MOD 8` by
        (mp_tac (Q.SPEC `8` arithmeticTheory.DIVISION) >> simp[] >>
         disch_then (qspec_then `i` mp_tac) >> decide_tac) >>
      `31 - i DIV 8 < 12 /\
       8 * (31 - (31 - i DIV 8)) + i MOD 8 = i` by decide_tac >>
      first_x_assum (qspec_then `31 - i DIV 8` mp_tac) >> simp[] >>
      `31 - i DIV 8 < 32` by decide_tac >>
      drule_all extract32_window_byte >>
      drule_all extract32_byte_zero_bits >> metis_tac[]) >>
  rpt strip_tac >>
  `get_byte (n2w n) (word_of_bytes T (0w:bytes32) win) T = EL n win` by
    (irule extract32_window_byte >> simp[]) >>
  pop_assum (SUBST1_TAC o SYM) >>
  simp[extract32_byte_zero_bits] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem extract32_source_window:
  !bs n bt. n + 32 <= LENGTH bs ==>
    evaluate_extract32 bs n bt = evaluate_extract32 (TAKE 32 (DROP n bs)) 0 bt
Proof
  rpt strip_tac >>
  `LENGTH (TAKE 32 (DROP n bs)) = 32` by simp[LENGTH_TAKE] >>
  simp[evaluate_extract32_def, TAKE_LENGTH_ID_rwt]
QED

Theorem extract32_error_runtime:
  extract32_result_base_ok bt /\
  (case bt of IntT k => 0 < k | _ => T) /\
  evaluate_extract32 bs n bt = INR err ==>
  ?msg. err = RuntimeError msg
Proof
  strip_tac >>
  Cases_on `n + 32 <= LENGTH bs`
  >- (`LENGTH (TAKE 32 (DROP n bs)) = 32` by simp[] >>
      Cases_on `bt` >>
      gvs[extract32_result_base_ok_def, evaluate_extract32_def,
          extract32_convert_uint, extract32_convert_int, AllCaseEqs()] >>
      Cases_on `b` >>
      gvs[extract32_result_base_ok_def, AllCaseEqs()]) >>
  gvs[evaluate_extract32_def]
QED
