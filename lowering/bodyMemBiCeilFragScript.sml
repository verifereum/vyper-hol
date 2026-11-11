(* Ceil's pure arithmetic suffix, on a memory-checked path. *)
Theory bodyMemBiCeilFrag
Ancestors
  bodyUnopFragMemory exprSimWordBuiltins exprUnopSimDefs
  exprSimUnopProps vyperContext compileEnv
  exprSimDefs valueEncoding vyperValue vyperInterpreter vyperValueOperation
  vyperAST builtinSimple builtinProps arithmeticProps words integer_word

Theorem compile_ceil_frag_mem:
  !ctx func cenv cx es i.
    within_int_bound (Signed 168) i ==>
    unop_frag_mem ctx func cenv cx (\x. compile_ceil x 10000000000)
      (typed_val_to_w256 (BaseTV DecimalT) (DecimalV i))
      (BaseT (IntT 256))
      (unop_result cx (BaseT (IntT 256)) Ceil [BaseT DecimalT] (DecimalV i) es) es
Proof
  rpt strip_tac >>
  simp[unop_result_def, evaluate_builtin_def] >>
  irule unop_frag_mem_straight >>
  simp[straight_fresh_ceil, is_word_type_def] >>
  strip_tac >>
  qexists_tac `i2w ((i + (10000000000 - 1)) / 10000000000):bytes32` >>
  simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  rpt strip_tac >>
  drule_all compile_ceil_correct >> strip_tac >>
  qexists_tac `ss'` >> simp[] >>
  drule decimal_ceil_word >> simp[WORD_LTi, word_0_w2i]
QED
