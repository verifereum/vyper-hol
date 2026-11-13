(* Concrete modular source values; independent of annotation and argument types. *)
Theory bodyPtrWordBuiltinsModularSource
Ancestors exprSimWordBuiltins exprSimWordArgs vyperContext
  vyperAST vyperState words venomExecSemantics integer_word vyperTypeBuiltins

Theorem word_pow_source_words:
  builtin_result cx ac ann PowMod256 ts [IntV (&w2n (a:bytes32)); IntV (&w2n (b:bytes32))] =
    INL (IntV (&w2n (word_exp a b)))
Proof
  simp[builtin_result_def, evaluate_builtin_def, word_exp_modexp, dimword_def, modexp_lt]
QED

Theorem word_modular_source_words:
  builtin_result cx ac ann (if is_mul then MulMod else AddMod) ts
    [IntV (&w2n (a:bytes32)); IntV (&w2n (b:bytes32)); IntV (&w2n (c:bytes32))] =
    if c = 0w then INR (Error (RuntimeError
      (if is_mul then "MulMod division by zero" else "AddMod division by zero")))
    else INL (IntV (&w2n ((if is_mul then mulmod else addmod) a b c)))
Proof
  Cases_on `is_mul` >> Cases_on `c = 0w` >>
  simp[builtin_result_def, evaluate_builtin_def, mulmod_def, addmod_def] >>
  irule arithmeticTheory.LESS_TRANS >> qexists_tac `w2n c` >>
  simp[arithmeticTheory.MOD_LESS, w2n_lt] >>
  irule arithmeticTheory.MOD_LESS >>
  `w2n c <> 0` by metis_tac[w2n_eq_0] >> decide_tac
QED

Theorem word_pow_source_typed:
  value_has_type (BaseTV (UintT 256)) v1 /\
  value_has_type (BaseTV (UintT 256)) v2 ==>
  builtin_result cx ac ann PowMod256 ts [v1;v2] =
    INL (IntV (&w2n (word_exp (val_to_w256 v1) (val_to_w256 v2))))
Proof
  strip_tac >>
  `v1 = IntV (&w2n (val_to_w256 v1)) /\
   v2 = IntV (&w2n (val_to_w256 v2))` by
    metis_tac[uint_value_word_rep, arithmeticTheory.LESS_EQ_REFL] >>
  metis_tac[word_pow_source_words]
QED

Theorem word_modular_source_typed:
  value_has_type (BaseTV (UintT 256)) v1 /\
  value_has_type (BaseTV (UintT 256)) v2 /\
  value_has_type (BaseTV (UintT 256)) v3 ==>
  builtin_result cx ac ann (if is_mul then MulMod else AddMod) ts [v1;v2;v3] =
    if val_to_w256 v3 = 0w then INR (Error (RuntimeError
      (if is_mul then "MulMod division by zero" else "AddMod division by zero")))
    else INL (IntV (&w2n ((if is_mul then mulmod else addmod)
      (val_to_w256 v1) (val_to_w256 v2) (val_to_w256 v3))))
Proof
  strip_tac >>
  `v1 = IntV (&w2n (val_to_w256 v1)) /\
   v2 = IntV (&w2n (val_to_w256 v2)) /\
   v3 = IntV (&w2n (val_to_w256 v3))` by
    metis_tac[uint_value_word_rep, arithmeticTheory.LESS_EQ_REFL] >>
  mp_tac (Q.INST [`a` |-> `val_to_w256 v1`, `b` |-> `val_to_w256 v2`,
    `c` |-> `val_to_w256 v3`] word_modular_source_words) >>
  metis_tac[]
QED
