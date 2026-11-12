(* Typed integer and boolean conversion memory continuations. *)
Theory bodyMemTbConvertIntegerDispatch
Ancestors
  bodyMemTbConvertIntSuffix bodyUnopFragMemory exprSimConvert
  exprUnopStraight vyperTyping valueEncoding integer_word fragExec exprLoweringProps freshWrites
  compileEnv vyperTypeSystem exprSimArith exprLowering vyperValue venomState words venomExecSemantics
Libs intLib

Theorem convert_bool_frag_mem[local]:
  !ctx func cenv cx src v i es0 sg bits.
    val_to_w256 v = i2w i /\
    within_int_bound (if sg then Signed bits else Unsigned bits) i /\
    bits <= 256 /\
    convert_result cx src (BaseT BoolT) v = INL (BoolV (i <> 0)) ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x ConvToBool) (i2w i)
      (BaseT BoolT) (convert_result cx src (BaseT BoolT) v) es0
Proof
  rpt strip_tac >> irule unop_frag_mem_straight >>
  simp[straight_fresh_convert, is_word_type_def] >> strip_tac >>
  qexists_tac `bool_to_word (i <> 0)` >>
  simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def, bool_to_word_def] >>
  conj_tac >- (Cases_on `i = 0` >> simp[bool_to_word_def]) >>
  rpt strip_tac >> drule_all convert_bool_run >> strip_tac >>
  qexists_tac `ss'` >> simp[] >>
  Cases_on `(i2w i:bytes32) = 0w`
  >- (drule_all i2w_eq_0_within >> simp[]) >>
  Cases_on `i = 0` >> gvs[i2w_def]
QED

Theorem convert_bool_identity_frag_mem[local]:
  !ctx func cenv cx src t b es0.
    is_word_type t /\
    convert_result cx src t (BoolV b) = INL (IntV (if b then 1 else 0)) /\
    (!tv i. evaluate_type (get_tenv cx) t = SOME tv ==>
             typed_val_to_w256 tv (IntV i) = i2w i) ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x ConvIdentity) (if b then 1w else 0w)
      t (convert_result cx src t (BoolV b)) es0
Proof
  rpt strip_tac >> irule unop_frag_mem_straight >>
  simp[compile_type_convert_def, straight_fresh_return] >> strip_tac >>
  qexists_tac `i2w (if b then 1 else 0)` >> simp[] >>
  rpt strip_tac >>
  gvs[compile_type_convert_def, comp_return_def, emitted_insts_refl,
      run_inst_seq_nil, val_to_w256_def] >>
  Cases_on `b` >> simp[bool_to_word_def, i2w_def]
QED

Theorem integer_typed_dispatch_mem:
  !ctx func cenv cx src t tv v es0.
    int_convert_pair src t /\
    evaluate_type (get_tenv cx) src = SOME tv /\ value_has_type tv v /\
    IS_SOME (evaluate_type (get_tenv cx) t) ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (mk_convert_op src t))
      (typed_val_to_w256 tv v) t (convert_result cx src t v) es0
Proof
  rpt gen_tac >> simp[int_convert_pair_def] >> strip_tac >>
  gvs[evaluate_type_def, mk_convert_op_def, is_bytestring_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def, typed_val_to_w256_def, val_to_w256_def]
  >>~- ([`unop_frag_mem _ _ _ _ (\x. compile_type_convert x (ConvIntToInt _ _ _ _)) _ _ _ _`],
      irule (SRULE[val_to_w256_def] convert_int_frag_mem) >>
      simp[val_to_w256_def, is_word_type_def, evaluate_type_def,
           typed_val_to_w256_def, convert_result_def,
           vyperValueOperationTheory.evaluate_convert_from_def,
           vyperValueOperationTheory.evaluate_convert_def, within_int_bound_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()])
  >>~- ([`unop_frag_mem _ _ _ _ (\x. compile_type_convert x ConvIdentity) _ _ _ _`],
      irule convert_bool_identity_frag_mem >>
      simp[is_word_type_def, evaluate_type_def, typed_val_to_w256_def,
           val_to_w256_def, convert_result_def,
           vyperValueOperationTheory.evaluate_convert_from_def,
           vyperValueOperationTheory.evaluate_convert_def]) >>
  irule convert_bool_frag_mem >>
  simp[val_to_w256_def, convert_result_def,
       vyperValueOperationTheory.evaluate_convert_from_def,
       vyperValueOperationTheory.evaluate_convert_def] >>
  qexists_tac `n`
  >>~- ([`within_int_bound (Signed n) i`], qexists_tac `T` >> simp[]) >>
  qexists_tac `F` >> simp[within_int_bound_def]
QED
