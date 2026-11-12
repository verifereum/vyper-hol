(* Shared compiler certificates at the two clean scalar operand boundary. *)
Theory augAssignPtrCompiler
Ancestors
  augAssignPtrRemainingCertificate exprSimArith exprSimCompare
  exprBopBitwise exprBopShift exprBopFlag exprSimBinopFrag
  augAssignPtrScalarCertificate exprLowering freshWrites vyperTyping vyperTypeSystem ptrDiscipline compileEnv

Theorem compile_binop_straight_fresh_ptr:
  MEM bop [Add; Sub; Mul; Div; Mod; UnsafeAdd; UnsafeSub; UnsafeMul;
           UnsafeDiv; And; Or; XOr; ShL; ShR; Eq; NotEq; Lt; LtE; Gt;
           GtE; Exp; Min; Max; In; NotIn] ==>
  straight_fresh (compile_binop bop x y ty bl el)
Proof
  strip_tac >>
  Cases_on `bop` >> gvs[] >>
  TRY (irule straight_fresh_unsafe >> simp[] >> NO_TAC) >>
  TRY (irule straight_fresh_compare >> simp[] >> NO_TAC) >>
  TRY (irule straight_fresh_compile_bitwise >> simp[] >> NO_TAC) >>
  TRY (irule straight_fresh_compile_shift >> simp[] >> NO_TAC) >>
  simp[straight_fresh_minmax, straight_fresh_flag_in,
       compile_binop_def, straight_fresh_checked,
       straight_fresh_compile_safe_pow] >>
  Cases_on `is_decimal_type ty` >>
  simp[straight_fresh_checked, straight_fresh_decimal_div] >>
  Cases_on `ty` >> gvs[is_decimal_type_def] >>
  Cases_on `b` >> gvs[is_decimal_type_def, decimal_divisor_def,
                     straight_fresh_decimal_div]
QED

Theorem typed_binop_scalar_member_ptr:
  well_typed_binop ann bop t1 t2 /\ bop <> In /\ bop <> NotIn ==>
  MEM bop [Add; Sub; Mul; Div; Mod; UnsafeAdd; UnsafeSub; UnsafeMul;
           UnsafeDiv; And; Or; XOr; ShL; ShR; Eq; NotEq; Lt; LtE; Gt;
           GtE; Exp; Min; Max; In; NotIn]
Proof
  Cases_on `bop` >> simp[well_typed_binop_def]
QED

Theorem compile_binop_clean_certificate_ptr:
  MEM bop [Add; Sub; Mul; Div; Mod; UnsafeAdd; UnsafeSub; UnsafeMul;
           UnsafeDiv; And; Or; XOr; ShL; ShR; Eq; NotEq; Lt; LtE; Gt;
           GtE; Exp; Min; Max; In; NotIn] /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  (!l. x <> Label l /\ y <> Label l) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  op_prov G y = NONE /\ op_taint tn y = {} ==>
  ?A. scalar_code A (emitted_insts sa sb) /\
      (!z. z IN A ==> op_prov G (Var z) = NONE /\ op_taint tn (Var z) = {}) /\
      scalar_available
        (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                                   (emitted_insts sa sb)))) op
Proof
  strip_tac >>
  qexists_tac `{z | x = Var z \/ y = Var z}` >>
  `scalar_available {z | x = Var z \/ y = Var z} x /\
   scalar_available {z | x = Var z \/ y = Var z} y` by
    (Cases_on `x` >> Cases_on `y` >> gvs[scalar_available_def] >>
     metis_tac[]) >>
  drule_all compile_binop_scalar_code >> simp[] >> rpt strip_tac >>
  gvs[]
QED
