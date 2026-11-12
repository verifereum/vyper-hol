Theory calldataWordProps
Ancestors
  vyperCalldata vyperTyping exprLowering valueEncodingDefs valueEncodingProps
  vyperValue vyperArith compileEnv valueEncoding valueEncodingProofs
  venomMemProps abiValidStatic byte integer_word words list rich_list arithmetic

Theorem cd_word_value_encoding:
  !env ty tv w x. is_word_type ty /\ evaluate_type env ty = SOME tv ==>
  (cd_word_value tv w = SOME x <=>
   value_has_type tv x /\ typed_val_to_w256 tv x = w)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ty` >>
  gvs[is_word_type_def, evaluate_type_def, AllCaseEqs()]
  >> Cases_on `x` >>
  simp[cd_word_value_def, value_has_type_def, typed_val_to_w256_def,
       val_to_w256_def, SF boolSimps.COND_elim_ss]
  >- (eq_tac
      >- (strip_tac >> gvs[integer_wordTheory.i2w_def])
      >> strip_tac >>
      `Num i < 2 ** 256` by
        (irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** m'` >> simp[]) >>
      `~(i < 0)` by intLib.ARITH_TAC >>
      gvs[i2w_def, w2n_n2w, dimword_def, SF wordsLib.SIZES_ss])
  >- (eq_tac
      >- (strip_tac >> gvs[i2w_w2i])
      >> strip_tac >> drule_all w2i_i2w_within_signed >> gvs[])
  >- (`w2n w <= 1 <=> w = 0w \/ w = 1w` by
        (eq_tac
         >- (strip_tac >> `w2n w = 0 \/ w2n w = 1` by decide_tac >>
             metis_tac[n2w_w2n])
         >> strip_tac >> gvs[SF wordsLib.SIZES_ss]) >>
      Cases_on `w = 0w` >> Cases_on `w = 1w` >>
      gvs[SF wordsLib.SIZES_ss])
  >- (eq_tac
      >- (strip_tac >> gvs[i2w_w2i])
      >> strip_tac >>
      `168 <= 256` by simp[] >>
      drule_all w2i_i2w_within_signed >> gvs[])
  >> simp_tac bool_ss [EVERY_NOT_EXISTS, combinTheory.o_DEF]
  >- suspend "fixedbytes"
  >- suspend "address"
  >> suspend "flags"
QED

Resume cd_word_value_encoding[fixedbytes]:
  simp_tac bool_ss [GSYM EVERY_NOT_EXISTS] >>
  eq_tac
  >- (strip_tac >>
      gvs[EXISTS_MEM, EVERY_MEM] >>
      `LENGTH (word_to_bytes w T) = 32` by simp[] >>
      `DROP n (word_to_bytes w T) = REPLICATE (32-n) 0w` by
        (`DROP n (word_to_bytes w T) =
          REPLICATE (LENGTH (DROP n (word_to_bytes w T))) 0w` by
           (irule abi_zero_bytes_replicate >> simp[EVERY_MEM]) >> gvs[]) >>
      `PAD_RIGHT 0w 32 (TAKE n (word_to_bytes w T)) = word_to_bytes w T` by
        (simp[PAD_RIGHT, GSYM REPLICATE_GENLIST] >> metis_tac[TAKE_DROP]) >>
      simp[word_of_bytes_be_def]) >>
  strip_tac >>
  `word_to_bytes w T = PAD_RIGHT 0w 32 l` by
    (qpat_x_assum `word_of_bytes_be _ = w` (SUBST1_TAC o SYM) >>
     simp[word_of_bytes_be_def, word_bytes_roundtrip_256, bitstringTheory.length_pad_right]) >>
  gvs[PAD_RIGHT, GSYM REPLICATE_GENLIST, DROP_APPEND1, TAKE_APPEND1]
QED

Resume cd_word_value_encoding[address]:
  eq_tac
  >- (strip_tac >> gvs[] >>
      `((w2w ((w2w w):160 word)):256 word) = w` by
        (simp[w2w_def, w2n_n2w, dimword_def, SF wordsLib.SIZES_ss]) >>
      simp[GSYM word_to_bytes_w2w_address, word_of_bytes_be_def] >>
      metis_tac[vfmTypesTheory.word_to_bytes_word_of_bytes_256]) >>
  strip_tac >>
  `word_of_bytes_be (PAD_LEFT 0w 32 l):256 word =
   w2w (word_of_bytes_be l:160 word)` by
    (irule EQ_SYM >>
     irule (w2w_word_of_bytes_be_pad_left |> INST_TYPE [alpha |-> ``:160``, beta |-> ``:256``] |> SRULE [fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
     simp[SF wordsLib.SIZES_ss, dividesTheory.divides_def]) >>
  gvs[] >>
  `w2n (word_of_bytes_be l:160 word) < 2 ** 160` by
    (mp_tac (INST_TYPE [alpha |-> ``:160``] w2n_lt) >>
     simp[dimword_def, SF wordsLib.SIZES_ss]) >>
  `w2n (word_of_bytes_be l:160 word) < 2 ** 256` by gvs[] >>
  simp[w2w_def, w2n_n2w, dimword_def, SF wordsLib.SIZES_ss] >>
  `word_to_bytes (word_of_bytes_be l:160 word) T = l` by
    (simp[word_of_bytes_be_def] >> irule word_bytes_roundtrip >>
     simp[SF wordsLib.SIZES_ss, dividesTheory.divides_def]) >>
  gvs[]
QED

Resume cd_word_value_encoding[flags]:
  eq_tac
  >- (strip_tac >> gvs[]) >>
  strip_tac >>
  `n < 2 ** 256` by
    (irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** m` >> simp[]) >>
  gvs[w2n_n2w, dimword_def, SF wordsLib.SIZES_ss]
QED

Finalise cd_word_value_encoding
