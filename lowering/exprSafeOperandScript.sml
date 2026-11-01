(*
 * The safe operands of the lowering's helpers (#636)
 *
 * The expression simulation reads the operand lower_value returns after
 * more code has run, so it must be a literal or a variable already handed
 * out (not_fresh_at), never a label: safe_operand.  word_result_ok is the
 * same for a value_vv: a StackValue's operand is safe, and a LocatedValue
 * has a word type, so unwrap_value loads it into a fresh variable.  This
 * theory proves safe_operand of the result of each helper compile_expr
 * uses for operators, conversions and arithmetic; exprSafeOperandBuiltins
 * does the builtins, calls and names, and exprWordOperand the induction.
 *
 * TOP-LEVEL:
 *   safe_operand_def, word_result_ok_def
 *   unwrap_value_safe_operand — unwrap_value of a word_result_ok value
 *   compile_type_convert_word_safe — a valid conversion to a word type
 *   well_typed_expr_type_well_formed — a well-typed expression's type is
 *                              well formed, given the local types are
 *   compile_binop_safe_operand
 *
 * Helpers: one *_safe_operand lemma per lowering helper.
 *)

Theory exprSafeOperand
Ancestors
  exprLoweringProps freshWrites compileEnv emitHelper context
  exprLowering exprCallBounds vyperTypeSystem vyperValue vyperAST vyperTypeBuiltins
  builtinSimple builtinMath builtinHashing builtinMisc builtinBytes builtinSystem

(* ===== The operand properties ===== *)

Definition safe_operand_def:
  safe_operand st op <=>
    (!z. op = Var z ==> not_fresh_at st z) /\ (!l. op <> Label l)
End

Definition word_result_ok_def:
  word_result_ok st (StackValue ty op) = safe_operand st op /\
  word_result_ok st (LocatedValue ty p) = is_word_type ty
End

Theorem safe_operand_Lit[simp]:
  safe_operand st (Lit n)
Proof
  simp[safe_operand_def]
QED

Theorem safe_operand_mono:
  sa.cs_next_var <= sb.cs_next_var /\ safe_operand sa op ==>
  safe_operand sb op
Proof
  rw[safe_operand_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem fresh_var_safe_operand:
  fresh_var sa = (z,sb) ==> safe_operand sb (Var z)
Proof
  simp[fresh_var_def] >> strip_tac >> gvs[] >>
  simp[safe_operand_def, not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem emit_op_safe_operand:
  emit_op opc args sa = (op,sb) ==> safe_operand sb op
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[safe_operand_def, not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem compile_ptr_load_safe_operand:
  compile_ptr_load is_ctor imm loc ptr_op sa = (op,sb) ==> safe_operand sb op
Proof
  Cases_on `is_ctor` >> Cases_on `imm` >> Cases_on `loc` >>
  simp[compile_ptr_load_def, compile_imm_load_word_def, comp_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[emit_op_safe_operand]
QED

Theorem unwrap_value_safe_operand:
  word_result_ok sa vv /\ unwrap_value cenv vv sa = (op,sb) ==>
  safe_operand sb op
Proof
  Cases_on `vv` >> simp[word_result_ok_def, unwrap_value_def,
                          comp_return_def] >>
  metis_tac[compile_ptr_load_safe_operand]
QED

(* ===== Conversions ===== *)

Theorem compile_type_convert_safe_input:
  safe_operand sa v /\ compile_type_convert v conv sa = (r,sb) ==>
  safe_operand sb r
Proof
  Cases_on `conv` >>
  simp[compile_type_convert_def, load_bytestring_as_word_def,
       compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt (IF_CASES_TAC >>
       simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
            fresh_id_def, fresh_var_def, emit_def]) >>
  strip_tac >> gvs[] >>
  gvs[safe_operand_def, not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem compile_type_convert_bytestring_safe:
  MEM conv [ConvBytestringToBool; ConvBytestringToInt s n;
            ConvBytestringToAddress; ConvBytestringToDecimal d lo hi;
            ConvBytestringToBytesM m] /\
  compile_type_convert v conv sa = (r,sb) ==> safe_operand sb r
Proof
  simp[] >> strip_tac >>
  qpat_x_assum `_ = (r,sb)` mp_tac >> gvs[] >>
  simp[compile_type_convert_def, load_bytestring_as_word_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def, LET_THM] >>
  rpt (IF_CASES_TAC >>
       simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
            fresh_id_def, fresh_var_def, emit_def]) >>
  strip_tac >> gvs[] >>
  gvs[safe_operand_def, not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem valid_conversion_nonword_source:
  well_formed_type tenv src /\ valid_conversion src dst /\
  ~is_word_type src ==> is_bytestring_type src
Proof
  Cases_on `src` >> simp[valid_conversion_def, is_word_type_def,
                         is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[valid_conversion_def, is_word_type_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[is_word_type_def, is_bytestring_type_def, well_formed_type_def,
       evaluate_type_def] >> rpt strip_tac >> gvs[]
QED

Theorem mk_convert_op_bytestring_word:
  is_bytestring_type src /\ valid_conversion src dst /\ is_word_type dst ==>
  ?s n d lo hi m.
    MEM (mk_convert_op src dst)
      [ConvBytestringToBool; ConvBytestringToInt s n;
       ConvBytestringToAddress; ConvBytestringToDecimal d lo hi;
       ConvBytestringToBytesM m]
Proof
  Cases_on `src` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def]
  >~ [`BytesT bd`]
  >- (Cases_on `bd` >> simp[is_bytestring_type_def] >>
      Cases_on `dst` >> simp[is_word_type_def, valid_conversion_def] >>
      rename1 `is_word_type (BaseT dbt)` >> Cases_on `dbt` >>
      simp[is_word_type_def, mk_convert_op_def, is_bytestring_type_def]
      >~ [`type_bounds (BaseT DecimalT)`]
      >- (Cases_on `type_bounds (BaseT DecimalT)` >> simp[]) >>
      rename1 `is_word_type (BaseT (BytesT dbd))` >> Cases_on `dbd` >>
      simp[is_word_type_def, mk_convert_op_def, is_bytestring_type_def]) >>
  Cases_on `dst` >> simp[is_word_type_def, valid_conversion_def] >>
  rename1 `is_word_type (BaseT dbt)` >> Cases_on `dbt` >>
  simp[is_word_type_def, valid_conversion_def, mk_convert_op_def,
       is_bytestring_type_def, type_bounds_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[is_word_type_def, valid_conversion_def, mk_convert_op_def,
       is_bytestring_type_def]
QED

Theorem compile_type_convert_word_safe:
  well_formed_type tenv src /\ valid_conversion src dst /\
  is_word_type dst /\ (is_word_type src ==> safe_operand sa v) /\
  compile_type_convert v (mk_convert_op src dst) sa = (r,sb) ==>
  safe_operand sb r
Proof
  rpt strip_tac >> Cases_on `is_word_type src`
  >- metis_tac[compile_type_convert_safe_input] >>
  `is_bytestring_type src` by metis_tac[valid_conversion_nonword_source] >>
  drule_all mk_convert_op_bytestring_word >> strip_tac >>
  drule_all compile_type_convert_bytestring_safe >> simp[]
QED

(* ===== Typing ===== *)

(* A well-typed expression's type is well formed, given that the local types
   are: the Name rule alone does not check it. *)
Theorem well_typed_expr_type_well_formed:
  well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t) ==>
  well_formed_type env.type_defs (expr_type e)
Proof
  strip_tac >> Cases_on `e` >> simp[expr_type_def]
  >~ [`Name _ _`]
  >- (gvs[well_typed_expr_def] >> metis_tac[])
  >~ [`TopLevelName _ nsid`]
  >- (PairCases_on `nsid` >> gvs[well_typed_expr_def])
  >~ [`Pop _ _`]
  >- (gvs[well_typed_expr_def, assignable_type_def] >>
      metis_tac[assignable_type_well_formed])
  >~ [`Call _ target _ _`]
  >- (Cases_on `target` >>
      gvs[well_typed_expr_def, well_formed_type_def, evaluate_type_def]
      >~ [`IntCall nsid`]
      >- (PairCases_on `nsid` >> gvs[well_typed_expr_def, well_formed_type_def])
      >~ [`ExtCall _ _ sig _`]
      >- (PairCases_on `sig` >> gvs[well_typed_expr_def, well_formed_type_def]) >>
      irule (REWRITE_RULE [well_formed_type_def]
               raw_call_return_type_well_formed) >> simp[]) >>
  gvs[well_typed_expr_def]
QED

(* ===== Operators and arithmetic ===== *)

Theorem compile_invert_safe_operand:
  compile_invert v ty cenv sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `ty` >> simp[compile_invert_def] >>
  metis_tac[emit_op_safe_operand]
QED

Theorem compile_neg_safe_operand:
  compile_neg v ty sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `type_bounds ty` >>
  simp[compile_neg_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_compare_safe_operand:
  compile_compare bop x y ty sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `bop` >> simp[compile_compare_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[emit_op_safe_operand, safe_operand_Lit]
QED

Theorem compile_select_safe_operand:
  compile_select c x y sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_select_def, comp_bind_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_pow_mod256_safe_operand:
  compile_pow_mod256 x y sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_pow_mod256_def] >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_addmod_safe_operand:
  compile_addmod x y z sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_addmod_def, comp_ignore_bind_def, comp_bind_def] >>
  strip_tac >> pairarg_tac >> gvs[] >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_mulmod_safe_operand:
  compile_mulmod x y z sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_mulmod_def, comp_ignore_bind_def, comp_bind_def] >>
  strip_tac >> pairarg_tac >> gvs[] >> metis_tac[emit_op_safe_operand]
QED

(* The compile monad's primitives, unfolded. *)
val monad_rws =
  [emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
   comp_return_def, fresh_id_def, fresh_var_def, emit_def];

(* A straight-line helper given by defs, whose result is a fresh variable or
   a literal on every path. *)
fun straight_safe_tac defs =
  simp (defs @ monad_rws) >>
  rpt (IF_CASES_TAC >> simp monad_rws) >>
  strip_tac >> gvs[] >>
  simp[safe_operand_def, not_fresh_at_def, ASCIInumbersTheory.toString_11];

Theorem compile_clamp_next_var:
  compile_clamp v ty sa = (u,sb) ==> sa.cs_next_var <= sb.cs_next_var
Proof
  Cases_on `type_bounds ty` >> Cases_on `is_signed_type ty` >>
  simp[compile_clamp_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[]
QED

Theorem clamp_and_return_safe_operand:
  safe_operand sa v /\ clamp_and_return v ty sa = (r,sb) ==>
  safe_operand sb r
Proof
  simp[clamp_and_return_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[compile_clamp_next_var, safe_operand_mono]
QED

Theorem wrap_truncate_safe_operand:
  safe_operand sa v /\ wrap_truncate v ty sa = (r,sb) ==>
  safe_operand sb r
Proof
  simp[wrap_truncate_def] >> rpt (IF_CASES_TAC >> simp[]) >>
  simp[comp_return_def] >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_safe_add_safe_operand:
  compile_safe_add x y ty sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `type_bounds ty` >>
  straight_safe_tac [compile_safe_add_def, clamp_and_return_def,
                     compile_clamp_def]
QED

Theorem compile_safe_sub_safe_operand:
  compile_safe_sub x y ty sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `type_bounds ty` >>
  straight_safe_tac [compile_safe_sub_def, clamp_and_return_def,
                     compile_clamp_def]
QED

Theorem compile_safe_decimal_div_safe_operand:
  compile_safe_decimal_div x y d ty sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_safe_decimal_div_def, comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[clamp_and_return_safe_operand, emit_op_safe_operand]
QED

Theorem compile_safe_mod_safe_operand:
  compile_safe_mod x y ty sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `is_signed_type ty` >>
  simp[compile_safe_mod_def, comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_safe_div_safe_operand:
  compile_safe_div x y ty sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `type_bounds ty` >>
  straight_safe_tac [compile_safe_div_def, clamp_and_return_def,
                     compile_clamp_def]
QED

Theorem compile_safe_mul_safe_operand:
  compile_safe_mul x y ty sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `type_bounds ty` >>
  straight_safe_tac [compile_safe_mul_def, compile_mul_overflow_check_def,
                     clamp_and_return_def, compile_clamp_def]
QED

Theorem compile_safe_pow_safe_operand:
  compile_safe_pow x y ty bl el sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `bl` >> Cases_on `el` >> Cases_on `type_bounds ty` >>
  straight_safe_tac [compile_safe_pow_def, compile_clamp_def]
QED

Theorem compile_binop_safe_operand:
  compile_binop bop x y ty bl el sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `bop` >> simp[compile_binop_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[emit_op_safe_operand, safe_operand_Lit,
    compile_safe_add_safe_operand, compile_safe_sub_safe_operand,
    compile_safe_mul_safe_operand, compile_safe_div_safe_operand,
    compile_safe_mod_safe_operand, compile_safe_decimal_div_safe_operand,
    compile_safe_pow_safe_operand, compile_compare_safe_operand,
    compile_select_safe_operand, wrap_truncate_safe_operand]
QED
