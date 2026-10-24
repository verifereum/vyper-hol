Theory vyperInvertTest
Ancestors
  jsonToVyperExpr jsonToVyperType jsonAST vyperAST vyperContext
  vyperState vyperInterpreter vyperSmallStep vyperTypeSystem
  vyperTypeContract vyperValueOperation
Libs
  vyperCheckContractLib

(* The frontend must preserve the operand's result type for bitwise inversion. *)
Theorem invert_frontend_test:
  translate_unary ctx JUop_Invert e (JT_Integer 256 F) =
    Builtin (BaseT (UintT 256)) Not [e] /\
  translate_unary ctx JUop_Invert e (JT_BytesM 32) =
    Builtin (BaseT (BytesT (Fixed 32))) Not [e] /\
  translate_unary ctx JUop_Invert e (JT_Named NONE "bool") =
    Builtin (BaseT BoolT) Not [e] /\
  translate_unary ctx JUop_Invert e (JT_Flag NONE "Permissions") =
    Builtin (FlagT (expr_current_nsid ctx, "Permissions")) Not [e] /\
  translate_unary ctx JUop_Not e (JT_Named NONE "bool") =
    Builtin (BaseT BoolT) Not [e]
Proof
  simp[translate_unary_def, translate_type_def, expr_type_ctx_def,
       tctx_current_nsid_def]
QED

(* Both supported directions and representative narrow-width rejections. *)
Theorem invert_checker_positive_test:
  well_typed_builtin_app (BaseT (UintT 256)) Not [BaseT (UintT 256)] /\
  well_typed_builtin_app (BaseT (BytesT (Fixed 32))) Not
    [BaseT (BytesT (Fixed 32))] /\
  well_typed_builtin_app (BaseT BoolT) Not [BaseT BoolT] /\
  well_typed_builtin_app (FlagT (NONE, "Permissions")) Not
    [FlagT (NONE, "Permissions")]
Proof
  simp[well_typed_builtin_app_def]
QED

Theorem invert_checker_narrow_rejection_test:
  ~well_typed_builtin_app (BaseT (UintT 8)) Not [BaseT (UintT 8)] /\
  ~well_typed_builtin_app (BaseT (UintT 128)) Not [BaseT (UintT 128)] /\
  ~well_typed_builtin_app (BaseT (UintT 255)) Not [BaseT (UintT 255)] /\
  ~well_typed_builtin_app (BaseT (BytesT (Fixed 1))) Not
    [BaseT (BytesT (Fixed 1))] /\
  ~well_typed_builtin_app (BaseT (BytesT (Fixed 16))) Not
    [BaseT (BytesT (Fixed 16))] /\
  ~well_typed_builtin_app (BaseT (BytesT (Fixed 31))) Not
    [BaseT (BytesT (Fixed 31))]
Proof
  simp[well_typed_builtin_app_def]
QED

(* The parameter is a well-typed expression, not a malformed literal.  A
   genuine flag declaration supplies the nominal type to the checker. *)
fun check_invert_contract ty declarations = let
  val modules = ``[(NONE, ^declarations ++
    [FunctionDecl External Pure F F "invert" [("x", ^ty)] [] ^ty
      [Return (SOME (Builtin ^ty Not [Name ^ty "x"]))]])]
    : (num option # toplevel list) list``
in
  vyperCheckContractLib.check_contract_conv
    (vyperCheckContractLib.mk_check_contract
      {in_deploy = false, address = ``0w : address``, modules = modules,
       layouts = ``[] : (address # (storage_layout # storage_layout)) list``})
end;

val ordinary_declarations = ``[] : toplevel list``;
val flag_declarations =
  ``[FlagDecl "Permissions" ["READ"; "WRITE"; "EXECUTE"]]``;
val () = app (fn (ty, declarations) =>
  if optionSyntax.is_some (rhs (concl (check_invert_contract ty declarations)))
  then () else raise Fail ("checker rejected supported inversion: " ^
                           term_to_string ty))
  [(``BaseT (UintT 256)``, ordinary_declarations),
   (``BaseT (BytesT (Fixed 32))``, ordinary_declarations),
   (``BaseT BoolT``, ordinary_declarations),
   (``FlagT (NONE, "Permissions")``, flag_declarations)];
val () = app (fn ty =>
  if optionSyntax.is_none (rhs (concl
    (check_invert_contract ty ordinary_declarations)))
  then () else raise Fail "checker accepted unsupported narrow inversion")
  [``BaseT (UintT 8)``, ``BaseT (UintT 128)``,
   ``BaseT (UintT 255)``, ``BaseT (BytesT (Fixed 1))``,
   ``BaseT (BytesT (Fixed 16))``, ``BaseT (BytesT (Fixed 31))``];

Theorem invert_zero_bytes_word[local]:
  !a n. word_of_bytes T a (REPLICATE n (0w:word8)) = (0w:bytes32)
Proof
  Induct_on `n` >> simp[byteTheory.word_of_bytes_def] >>
  simp[byteTheory.set_byte_def, LET_THM, byteTheory.word_slice_alt_zero]
QED

(* These are exact 32-byte results, not merely a successful BytesV result. *)
Theorem invert_bytes32_zero_test:
  evaluate_builtin cx acc (BaseT (BytesT (Fixed 32))) Not tys
    [BytesV (REPLICATE 32 (0w:word8))] =
    INL (BytesV (REPLICATE 32 (255w:word8)))
Proof
  simp[evaluate_builtin_def, byteTheory.word_of_bytes_be_def,
       invert_zero_bytes_word, wordsTheory.WORD_NOT_0] >>
  EVAL_TAC
QED

Theorem invert_ones_bytes_word[local]:
  word_of_bytes_be (REPLICATE 32 (255w:word8)) = ~(0w:bytes32)
Proof
  `word_to_bytes_be (~(0w:bytes32)) = REPLICATE 32 (255w:word8)` by
    (mp_tac invert_bytes32_zero_test >>
     simp[evaluate_builtin_def, byteTheory.word_of_bytes_be_def,
          invert_zero_bytes_word]) >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  simp[byteTheory.word_to_bytes_be_def, byteTheory.word_of_bytes_be_def,
       byteTheory.word_of_bytes_word_to_bytes]
QED


Theorem invert_bytes32_ones_test:
  evaluate_builtin cx acc (BaseT (BytesT (Fixed 32))) Not tys
    [BytesV (REPLICATE 32 (255w:word8))] =
    INL (BytesV (REPLICATE 32 (0w:word8)))
Proof
  simp[evaluate_builtin_def, invert_ones_bytes_word,
       wordsTheory.WORD_NOT_NOT] >> EVAL_TAC
QED

Theorem invert_mixed_bytes_word[local]:
  word_of_bytes_be (FLAT (REPLICATE 8 [0w; 255w; 1w; 254w])) =
    (0x00ff01fe00ff01fe00ff01fe00ff01fe00ff01fe00ff01fe00ff01fe00ff01few:bytes32)
Proof
  `word_to_bytes_be
     (0x00ff01fe00ff01fe00ff01fe00ff01fe00ff01fe00ff01fe00ff01fe00ff01few:bytes32) =
     FLAT (REPLICATE 8 [0w; 255w; 1w; 254w])` by EVAL_TAC >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  simp[byteTheory.word_to_bytes_be_def, byteTheory.word_of_bytes_be_def,
       byteTheory.word_of_bytes_word_to_bytes]
QED

Theorem invert_bytes32_mixed_test:
  evaluate_builtin cx acc (BaseT (BytesT (Fixed 32))) Not tys
    [BytesV (FLAT (REPLICATE 8 [0w; 255w; 1w; 254w]))] =
    INL (BytesV (FLAT (REPLICATE 8 [255w; 0w; 254w; 1w])))
Proof
  simp[evaluate_builtin_def, invert_mixed_bytes_word,
       wordsTheory.word_1comp_n2w] >> EVAL_TAC
QED

Theorem invert_uint256_boundaries_test:
  evaluate_builtin cx acc (BaseT (UintT 256)) Not tys [IntV 0] =
    INL (IntV (&(2 ** 256 - 1))) /\
  evaluate_builtin cx acc (BaseT (UintT 256)) Not tys
    [IntV (&(2 ** 256 - 1))] = INL (IntV 0)
Proof
  simp[evaluate_builtin_def, type_to_int_bound_def] >> EVAL_TAC
QED

(* Out-of-range states bypass static typing; inversion must still never return
   a negative integer as the old arithmetic subtraction did. *)
Theorem invert_oversized_uint_test:
  evaluate_builtin cx acc (BaseT (UintT 256)) Not tys
    [IntV (&(2 ** 256))] = INL (IntV (&(2 ** 256 - 1)))
Proof
  simp[evaluate_builtin_def, type_to_int_bound_def] >> EVAL_TAC
QED

Theorem invert_bool_test:
  evaluate_builtin cx acc (BaseT BoolT) Not tys [BoolV T] =
    INL (BoolV F) /\
  evaluate_builtin cx acc (BaseT BoolT) Not tys [BoolV F] =
    INL (BoolV T)
Proof
  simp[evaluate_builtin_def]
QED

Theorem invert_flag_test:
  evaluate_builtin
    (empty_evaluation_context with sources :=
      [(0w, [(NONE, [FlagDecl "Permissions" ["READ"; "WRITE"; "EXECUTE"]])])])
    acc (FlagT (NONE, "Permissions")) Not tys [FlagV 1] = INL (FlagV 6)
Proof
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE] >>
  EVAL_TAC
QED

(* Exercise evaluation of a literal through the recursive and CPS interpreters. *)
Theorem invert_bytes32_eval_test:
  eval_expr cx
    (Builtin (BaseT (BytesT (Fixed 32))) Not
      [Literal (BaseT (BytesT (Fixed 32))) (BytesL bs)]) st =
    (INL (Value (BytesV
      (word_to_bytes_be (~(word_of_bytes_be bs : bytes32))))), st)
Proof
  simp[Once evaluate_def, builtin_args_length_ok_def, type_check_def,
       assert_def, ignore_bind_def, bind_def] >>
  simp[Once evaluate_def, bind_def, return_def, evaluate_literal_def] >>
  simp[Once evaluate_def, bind_def, materialise_def, return_def] >>
  simp[Once evaluate_def, bind_def, return_def, get_accounts_def,
       evaluate_builtin_def, evaluate_literal_def, lift_sum_def]
QED

Theorem invert_bytes32_cps_test:
  fromtvk (cont (eval_expr_cps cx
    (Builtin (BaseT (BytesT (Fixed 32))) Not
      [Literal (BaseT (BytesT (Fixed 32))) (BytesL bs)]) st DoneK)) =
    (INL (Value (BytesV
      (word_to_bytes_be (~(word_of_bytes_be bs : bytes32))))), st)
Proof
  simp[GSYM eval_expr_eq_cont_cps, invert_bytes32_eval_test]
QED
