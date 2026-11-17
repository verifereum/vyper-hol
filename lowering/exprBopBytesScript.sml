(* Fixed-byte operators use the typed, left-aligned word encoding. *)
Theory exprBopBytes
Ancestors
  exprBopBitwise exprBopShift exprBopStraight exprBopSimDefs exprBopSimProps
  exprSimProps exprSimBinopFrag loweringPosts exprLowering compileEnv
  vyperValueOperation vyperContext vyperValue vyperTyping
  valueEncoding valueEncodingProofs valueEncodingBitwise
  venomState venomExecSemantics list rich_list words byte integer integer_word
Libs
  wordsLib

Theorem bop_result_bytes_bitwise:
  (bop = And \/ bop = Or \/ bop = XOr) /\
  LENGTH xs = n /\ LENGTH ys = n /\ n <= 32 ==>
  ?bs. bop_result cx (BaseT (BytesT (Fixed n))) bop tys
         (BytesV xs) (BytesV ys) es = INL (BytesV bs) /\
       word_of_bytes_be bs =
         (if bop = And then word_and else if bop = Or then word_or
          else word_xor) (word_of_bytes_be xs : bytes32) (word_of_bytes_be ys)
Proof
  strip_tac >> gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def] >>
  metis_tac[word_of_bytes_be_bitwise]
QED

Theorem binop_frag_bytes_bitwise:
  (bop = And \/ bop = Or \/ bop = XOr) /\
  LENGTH xs = n /\ LENGTH ys = n /\ n <= 32 ==>
  binop_frag_post (expr_val_rel cx (BaseT (BytesT (Fixed n))))
    ctx func cenv cx bop ty (BaseT (BytesT (Fixed n))) bl el tys
    (BytesV xs) (BytesV ys) (word_of_bytes_be xs) (word_of_bytes_be ys) es
Proof
  strip_tac >> drule_all bop_result_bytes_bitwise >> strip_tac >>
  irule (Q.INST [`v` |-> `BytesV bs`, `w` |-> `word_of_bytes_be bs`]
    binop_frag_post_success) >>
  rpt conj_tac
  >- metis_tac[straight_fresh_compile_bitwise]
  >- first_assum ACCEPT_TAC
  >- simp[expr_val_rel_def, vyperValueTheory.evaluate_type_def,
          is_word_type_def, typed_bytes_word] >>
  rpt strip_tac >> drule_all compile_bitwise_run >> simp[]
QED

Theorem bop_result_bytes_shift:
  (bop = ShL \/ bop = ShR) /\ LENGTH bs = 32 /\
  within_int_bound (Unsigned 256) i ==>
  ?out. bop_result cx (BaseT (BytesT (Fixed 32))) bop tys
          (BytesV bs) (IntV i) es = INL (BytesV out) /\
    word_of_bytes_be out =
      (if bop = ShL then word_lsl else word_lsr)
        (word_of_bytes_be bs : bytes32) (w2n (i2w i : bytes32))
Proof
  strip_tac >>
  `~(i < 0) /\ w2n (i2w i : bytes32) = Num i` by
    (fs[within_int_bound_def] >>
     `?k. i = &k` by metis_tac[NUM_POSINT_EXISTS] >>
     gvs[i2w_pos, w2n_n2w, dimword_def]) >>
  gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def] >>
  simp[word_of_bytes_be_def, word_to_bytes_be_def,
       word_of_bytes_word_to_bytes, dividesTheory.compute_divides]
QED

Theorem binop_frag_bytes_shift:
  (bop = ShL \/ bop = ShR) /\ LENGTH bs = 32 /\
  within_int_bound (Unsigned 256) i ==>
  binop_frag_post (expr_val_rel cx (BaseT (BytesT (Fixed 32))))
    ctx func cenv cx bop (BaseT (BytesT (Fixed 32)))
    (BaseT (BytesT (Fixed 32))) bl el tys
    (BytesV bs) (IntV i) (word_of_bytes_be bs) (i2w i) es
Proof
  strip_tac >> drule_all bop_result_bytes_shift >> strip_tac >>
  irule (Q.INST [`v` |-> `BytesV out`, `w` |-> `word_of_bytes_be out`]
    binop_frag_post_success) >>
  rpt conj_tac
  >- metis_tac[straight_fresh_compile_shift]
  >- first_assum ACCEPT_TAC
  >- simp[expr_val_rel_def, vyperValueTheory.evaluate_type_def,
          is_word_type_def, typed_bytes_word] >>
  rpt strip_tac >> drule_all compile_shift_run >> simp[is_signed_type_def]
QED

Theorem binop_frag_bytes_typed:
  MEM bop [And;Or;XOr;ShL;ShR] /\
  well_typed_binop ann bop (BaseT (BytesT (Fixed m))) t2 /\
  evaluate_type tenv (BaseT (BytesT (Fixed m))) = SOME tv1 /\
  evaluate_type tenv t2 = SOME tv2 /\
  value_has_type tv1 v1 /\ value_has_type tv2 v2 /\
  (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) ==>
  binop_frag_post (expr_val_rel cx ann)
    ctx func cenv cx bop (BaseT (BytesT (Fixed m))) ann bl el tys
    v1 v2 (typed_val_to_w256 tv1 v1) (typed_val_to_w256 tv2 v2) es
Proof
  strip_tac >>
  Cases_on `bop = And \/ bop = Or \/ bop = XOr`
  >- (gvs[well_typed_binop_def, vyperValueTheory.evaluate_type_def] >>
      Cases_on `v1` >> Cases_on `v2` >> gvs[value_has_type_def] >>
      simp[typed_bytes_word] >> irule binop_frag_bytes_bitwise >> simp[]) >>
  `bop = ShL \/ bop = ShR` by gvs[] >>
  `ann = BaseT (BytesT (Fixed 32)) /\ m = 32 /\ is_int_type t2` by
    gvs[well_typed_binop_def] >>
  gvs[] >>
  drule_all int_type_value >> strip_tac >> gvs[] >>
  `within_int_bound (Unsigned 256) i` by
    (Cases_on `is_signed_type t2` >> gvs[] >>
     metis_tac[within_int_bound_unsigned_256]) >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  Cases_on `v1` >> gvs[value_has_type_def] >>
  simp[typed_bytes_word, typed_val_to_w256_word_value, word_value_def,
       val_to_w256_def] >>
  irule binop_frag_bytes_shift >> simp[]
QED

