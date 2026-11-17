(* Fixed-byte operators use the typed, left-aligned word encoding. *)
Theory exprBopBytes
Ancestors
  exprBopBitwise exprBopShift exprBopStraight exprBopSimDefs exprBopSimProps
  exprSimProps exprSimBinopFrag exprSimHypsDefs loweringPosts exprLowering compileEnv
  vyperValueOperation vyperContext vyperValue vyperTyping
  valueEncoding valueEncodingProofs valueEncodingBitwise
  fragGasFresh varsExt freshWrites
  venomState venomExecSemantics list rich_list words byte integer integer_word
Libs
  wordsLib

(* Fixed-byte widths are checked when their types are evaluated. *)
Theorem well_typed_binop_augassign_word:
  !ty bop t2.
    well_typed_binop ty bop ty t2 /\ bop <> In /\ bop <> NotIn ==>
    (word_value_type ty /\ word_value_type t2) \/
    ((?m. ty = BaseT (BytesT (Fixed m))) /\
     MEM bop [And; Or; XOr; ShL; ShR])
Proof
  Cases_on `bop` >> rw[well_typed_binop_def, word_value_type_def] >> gvs[]
QED

Theorem well_typed_binop_augassign_word_value:
  well_typed_binop ty bop ty t2 /\ bop <> In /\ bop <> NotIn /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv cur /\ word_value cur ==>
  word_value_type ty /\ word_value_type t2
Proof
  strip_tac >> drule_all well_typed_binop_augassign_word >> strip_tac
  >- simp[] >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `cur` >> gvs[value_has_type_def, loweringSliceTheory.word_value_def]
QED

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

Theorem compile_bytes_word_run:
  MEM bop [And;Or;XOr;ShL;ShR] /\
  compile_binop bop x y (BaseT (BytesT (Fixed m))) bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME w1 /\ eval_operand y s = SOME w2 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME
      (if bop = And then w1 && w2 else if bop = Or then w1 || w2
       else if bop = XOr then word_xor w1 w2
       else if bop = ShL then w1 << w2n w2 else w1 >>> w2n w2)
Proof
  strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand x (drop_fresh sa s) = SOME w1 /\
   eval_operand y (drop_fresh sa s) = SOME w2` by simp[eval_operand_drop_fresh] >>
  `?t. run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK t /\
    eval_operand op t = SOME
      (if bop = And then w1 && w2 else if bop = Or then w1 || w2
       else if bop = XOr then word_xor w1 w2
       else if bop = ShL then w1 << w2n w2 else w1 >>> w2n w2)` by
    (Cases_on `bop = And \/ bop = Or \/ bop = XOr`
     >- (drule_all compile_bitwise_run >> gvs[]) >>
     `bop = ShL \/ bop = ShR` by gvs[] >>
     drule_all compile_shift_run >> gvs[is_signed_type_def]) >>
  `straight_fresh (compile_binop bop x y (BaseT (BytesT (Fixed m))) bl el)` by
    (Cases_on `bop = And \/ bop = Or \/ bop = XOr`
     >- metis_tac[straight_fresh_compile_bitwise] >>
     `bop = ShL \/ bop = ShR` by gvs[] >>
     metis_tac[straight_fresh_compile_shift]) >>
  `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
                   (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     fs[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >> metis_tac[vars_ext_eval_operand]
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

Theorem bop_result_bytes_augshift:
  (bop = ShL \/ bop = ShR) /\ LENGTH bs = 32 /\ LENGTH amount = 32 ==>
  ?out. bop_result cx (BaseT (BytesT (Fixed 32))) bop tys
          (BytesV bs) (BytesV amount) es = INL (BytesV out) /\
    word_of_bytes_be out =
      (if bop = ShL then word_lsl else word_lsr)
        (word_of_bytes_be bs : bytes32) (w2n (word_of_bytes_be amount : bytes32))
Proof
  strip_tac >>
  gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def] >>
  simp[word_of_bytes_be_def, word_to_bytes_be_def,
       word_of_bytes_word_to_bytes, dividesTheory.compute_divides]
QED

Theorem binop_frag_bytes_augshift:
  (bop = ShL \/ bop = ShR) /\ LENGTH bs = 32 /\ LENGTH amount = 32 ==>
  binop_frag_post (expr_val_rel cx (BaseT (BytesT (Fixed 32))))
    ctx func cenv cx bop (BaseT (BytesT (Fixed 32)))
    (BaseT (BytesT (Fixed 32))) bl el tys
    (BytesV bs) (BytesV amount) (word_of_bytes_be bs) (word_of_bytes_be amount) es
Proof
  strip_tac >> drule_all bop_result_bytes_augshift >> strip_tac >>
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
  (bop = ShL \/ bop = ShR ==>
    (?i. v2 = IntV i /\ 0 <= i) \/ t2 = BaseT (BytesT (Fixed 32))) ==>
  binop_frag_post (expr_val_rel cx ann)
    ctx func cenv cx bop (BaseT (BytesT (Fixed m))) ann bl el tys
    v1 v2 (typed_val_to_w256 tv1 v1) (typed_val_to_w256 tv2 v2) es
Proof
  strip_tac >>
  Cases_on `bop = And \/ bop = Or \/ bop = XOr`
  >- (gvs[well_typed_binop_def, vyperValueTheory.evaluate_type_def,
          optionTheory.IF_EQUALS_OPTION] >>
      Cases_on `v1` >> Cases_on `v2` >> gvs[value_has_type_def] >>
      simp[typed_bytes_word] >> irule binop_frag_bytes_bitwise >> simp[]) >>
  `bop = ShL \/ bop = ShR` by gvs[] >>
  Cases_on `t2 = BaseT (BytesT (Fixed 32))`
  >- (gvs[well_typed_binop_def, vyperValueTheory.evaluate_type_def] >>
      Cases_on `v1` >> Cases_on `v2` >> gvs[value_has_type_def] >>
      simp[typed_bytes_word] >> irule binop_frag_bytes_augshift >> simp[]) >>
  `ann = BaseT (BytesT (Fixed 32)) /\ m = 32 /\ is_int_type t2` by
    gvs[well_typed_binop_def] >>
  gvs[] >>
  drule_all int_type_value >> strip_tac >> gvs[] >>
  `within_int_bound (Unsigned 256) i` by
    (Cases_on `is_signed_type t2` >> gvs[] >>
     metis_tac[within_int_bound_unsigned_256]) >>
  gvs[vyperValueTheory.evaluate_type_def, optionTheory.IF_EQUALS_OPTION] >>
  Cases_on `v1` >> gvs[value_has_type_def] >>
  simp[typed_bytes_word, typed_val_to_w256_word_value, word_value_def,
       val_to_w256_def] >>
  irule binop_frag_bytes_shift >> simp[]
QED

Theorem compile_bytes_binop_run:
  MEM bop [And;Or;XOr;ShL;ShR] /\
  well_typed_binop ann bop (BaseT (BytesT (Fixed m))) t2 /\
  evaluate_type tenv (BaseT (BytesT (Fixed m))) = SOME tv1 /\
  evaluate_type tenv t2 = SOME tv2 /\
  value_has_type tv1 v1 /\ value_has_type tv2 v2 /\
  (bop = ShL \/ bop = ShR ==>
    (?i. v2 = IntV i /\ 0 <= i) \/ t2 = BaseT (BytesT (Fixed 32))) /\
  compile_binop bop x y (BaseT (BytesT (Fixed m))) bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (typed_val_to_w256 tv1 v1) /\
  eval_operand y s = SOME (typed_val_to_w256 tv2 v2) ==>
  ?v t. bop_result cx ann bop tys v1 v2 es = INL v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\ expr_val_rel cx ann v op t
Proof
  strip_tac >>
  Cases_on `bop = And \/ bop = Or \/ bop = XOr`
  >- (gvs[well_typed_binop_def, vyperValueTheory.evaluate_type_def,
          optionTheory.IF_EQUALS_OPTION] >>
      Cases_on `v1` >> Cases_on `v2` >> gvs[value_has_type_def] >>
      fs[typed_bytes_word] >>
      drule_all bop_result_bytes_bitwise >> strip_tac >>
      qmatch_asmsub_rename_tac `bop_result _ _ _ _ _ _ _ = INL (BytesV result_bs)` >>
      drule_all compile_bytes_word_run >> strip_tac >>
      qexistsl_tac [`BytesV result_bs`, `t`] >>
      gvs[expr_val_rel_def, vyperValueTheory.evaluate_type_def,
          is_word_type_def, typed_bytes_word]) >>
  `bop = ShL \/ bop = ShR` by gvs[] >>
  Cases_on `t2 = BaseT (BytesT (Fixed 32))`
  >- (gvs[well_typed_binop_def, vyperValueTheory.evaluate_type_def] >>
      Cases_on `v1` >> Cases_on `v2` >> gvs[value_has_type_def] >>
      fs[typed_bytes_word] >>
      drule_all bop_result_bytes_augshift >> strip_tac >>
      drule_all compile_bytes_word_run >> strip_tac >>
      qexistsl_tac [`BytesV out`, `t`] >>
      gvs[expr_val_rel_def, vyperValueTheory.evaluate_type_def,
          is_word_type_def, typed_bytes_word]) >>
  `ann = BaseT (BytesT (Fixed 32)) /\ m = 32 /\ is_int_type t2` by
    gvs[well_typed_binop_def] >> gvs[] >>
  drule_all int_type_value >> strip_tac >> gvs[] >>
  `within_int_bound (Unsigned 256) i` by
    (Cases_on `is_signed_type t2` >> gvs[] >>
     metis_tac[within_int_bound_unsigned_256]) >>
  gvs[vyperValueTheory.evaluate_type_def, optionTheory.IF_EQUALS_OPTION] >>
  Cases_on `v1` >> gvs[value_has_type_def] >>
  fs[typed_bytes_word, typed_val_to_w256_word_value, word_value_def,
     val_to_w256_def] >>
  drule_all bop_result_bytes_shift >> strip_tac >>
  drule_all compile_bytes_word_run >> strip_tac >>
  qexistsl_tac [`BytesV out`, `t`] >>
  gvs[expr_val_rel_def, vyperValueTheory.evaluate_type_def,
      is_word_type_def, typed_bytes_word]
QED

