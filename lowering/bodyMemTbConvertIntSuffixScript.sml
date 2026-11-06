(* Integer conversion's concrete straight-line memory certificate. *)
Theory bodyMemTbConvertIntSuffix
Ancestors
  bodyUnopFragMemory exprSimConvert exprUnopStraight
  exprLowering compileEnv vyperValue valueEncoding vyperAST
  integer_word

Theorem convert_int_frag_mem:
  !ctx func cenv cx in_s in_b out_s out_b src t v1 i es0.
    val_to_w256 v1 = i2w i /\ is_word_type t /\
    within_int_bound (if in_s then Signed in_b else Unsigned in_b) i /\
    0 < in_b /\ in_b <= 256 /\ 0 < out_b /\ (out_s ==> 1 < out_b) /\
    out_b <= 256 /\
    (within_int_bound (if out_s then Signed out_b else Unsigned out_b) i ==>
     convert_result cx src t v1 = INL (IntV i)) /\
    (~within_int_bound (if out_s then Signed out_b else Unsigned out_b) i ==>
     ?m. convert_result cx src t v1 = INR (Error (RuntimeError m))) /\
    (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
          typed_val_to_w256 tv (IntV i) = i2w i) ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (ConvIntToInt in_s in_b out_s out_b))
      (val_to_w256 v1) t (convert_result cx src t v1) es0
Proof
  rpt strip_tac >> irule unop_frag_mem_straight >>
  simp[straight_fresh_convert] >> strip_tac >>
  Cases_on `within_int_bound (if out_s then Signed out_b else Unsigned out_b) i`
  >- (gvs[] >> qexists_tac `i2w i` >> simp[] >>
      rpt strip_tac >> drule_all convert_int_run >> simp[]) >>
  gvs[] >> rpt strip_tac >>
  drule_all convert_int_run >> simp[]
QED
