Theory jsonConstEvalWitness
Ancestors
  jsonConstEval jsonConstAST jsonAST vyperConstEval vyperAST
  vyperInterpreter vyperState vyperValue
Libs
  jsonConstASTLib vyperCheckContractFrontendLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../tests/fixtures/check_contract/constant_bound.json",
  "../tests/fixtures/check_contract/constant_shifts.json",
  "../tests/fixtures/check_contract/constant_shift_overflow.json"];

val fixture = "../tests/fixtures/check_contract/constant_bound.json";
val json = JSONDecode.decodeFile JSONDecode.raw fixture;
val declarations = JSONDecode.decode jsonConstASTLib.annotated_ast json;

(* Neither missing metadata nor malformed metadata may affect this decoder. *)
fun remove_metadata (JSON.OBJECT fields) = JSON.OBJECT
      (List.map (fn (key,v) => (key,remove_metadata v))
        (List.filter (fn (key,_) => key <> "folded_value" andalso key <> "type") fields))
  | remove_metadata (JSON.ARRAY values) = JSON.ARRAY (List.map remove_metadata values)
  | remove_metadata value = value;
fun poison_metadata (JSON.OBJECT fields) = JSON.OBJECT
      (("folded_value", JSON.STRING "untrusted") ::
       ("type", JSON.STRING "untrusted") ::
       List.map (fn (key,v) => (key,poison_metadata v))
        (List.filter (fn (key,_) => key <> "folded_value" andalso key <> "type") fields))
  | poison_metadata (JSON.ARRAY values) = JSON.ARRAY (List.map poison_metadata values)
  | poison_metadata value = value;
val () = app (fn modified =>
  if aconv declarations (JSONDecode.decode jsonConstASTLib.annotated_ast modified)
  then () else raise Fail "constant decoding depends on compiler metadata")
  [remove_metadata json, poison_metadata json];

val uint256 = ``BaseT (UintT 256)``;
val initializer = ``Builtin ^uint256 (Bop Add)
  [Literal ^uint256 (IntL 1); Literal ^uint256 (IntL 2)]``;
val expected = ``SOME [(NONE : num option,
  [VariableDecl Private (Constant ^initializer) "N" ^uint256 NONE;
   FunctionDecl External Pure F F "power"
     [("x", ^uint256); ("values", ArrayT ^uint256 (Fixed 3))] [] ^uint256
     [Return (SOME (Builtin ^uint256 (Bop Exp)
       [Name ^uint256 "x"; Literal ^uint256 (IntL 3)]))]])]``;
val translated = EVAL ``translate_constant_module ^declarations``;
val () = if aconv (rhs (concl translated)) expected then ()
  else raise Fail "constant bound/exponent translation mismatch";
Theorem constant_bound_and_exponent_translation = translated;

Theorem constant_initializer_runtime:
  eval_expr cx
    (Builtin (BaseT (UintT 256)) (Bop Add)
      [Literal (BaseT (UintT 256)) (IntL 1);
       Literal (BaseT (UintT 256)) (IntL 2)]) st =
  (INL (Value (IntV 3)), st)
Proof
  irule eval_integer_constant_sound >> EVAL_TAC
QED

val checked = vyperCheckContractFrontendLib.check_constant_contract_file_legacy
  {address = ``0w : address``, path = fixture};
val () = if optionSyntax.is_some (rhs (concl checked)) then ()
  else raise Fail "constant-bound contract rejected by check_contract";
Theorem constant_bound_contract_checked = checked;

fun rejects label term =
  let val result = rhs (concl (EVAL term)) in
    if optionSyntax.is_none result then ()
    else raise Fail ("constant frontend accepted " ^ label ^ ": " ^
                     term_to_string result)
  end;
val int1 = ``JE_Int 1 JT_None``;
val name_n = ``JE_Name "N" NONE JMissingSource JT_None``;
val () = app (fn (label,term) => rejects label term)
  [("division by zero", ``evaluate_constant [] ^uint256
      (JE_BinOp ^int1 JBop_FloorDiv (JE_Int 0 JT_None) JT_None)``),
   ("overflow", ``evaluate_constant [] (BaseT (UintT 8))
      (JE_BinOp (JE_Int 255 JT_None) JBop_Add ^int1 JT_None)``),
   ("out-of-range literal", ``evaluate_constant [] (BaseT (UintT 8))
      (JE_Int 256 JT_None)``),
   ("missing constant", ``evaluate_constant [] ^uint256 ^name_n``),
   ("unsupported expression", ``evaluate_constant [] ^uint256 (JE_Bool T)``),
   ("zero bound", ``resolve_constant_annotation []
      (CA_Array (CA_Integer 256 F) (JE_Int 0 JT_None))``),
   ("negative bound", ``resolve_constant_annotation []
      (CA_Array (CA_Integer 256 F) (JE_Int (-1) JT_None))``),
   ("invalid width", ``resolve_constant_annotation [] (CA_Integer 257 F)``),
   ("forward constant", ``translate_constant_module
      [CD_Constant "M" (CA_Integer 256 F) ^name_n;
       CD_Constant "N" (CA_Integer 256 F) ^int1]``),
   ("duplicate constant", ``translate_constant_module
      [CD_Constant "N" (CA_Integer 256 F) ^int1;
       CD_Constant "N" (CA_Integer 256 F) ^int1]``)];

(* Reject the source annotation whose unbounded value is 3, rather than
   silently resolving it to 1 through runtime wrapping. *)
val overflow_json = JSONDecode.decodeFile JSONDecode.raw
  "../tests/fixtures/check_contract/constant_shift_overflow.json";
val () = app (fn input =>
  let val decls = JSONDecode.decode jsonConstASTLib.annotated_ast input in
    rejects "wrapping shift bound" ``translate_constant_module ^decls``
  end) [overflow_json, remove_metadata overflow_json,
        poison_metadata overflow_json];
val overflow_declarations =
  JSONDecode.decode jsonConstASTLib.annotated_ast overflow_json;
Theorem constant_shift_overflow_rejected =
  EVAL ``translate_constant_module ^overflow_declarations``;

val () = app (fn (label,term) => rejects label term)
  [("unsigned left-shift overflow", ``evaluate_constant [] (BaseT (UintT 8))
      (JE_BinOp (JE_Int 128 JT_None) JBop_LShift ^int1 JT_None)``),
   ("signed left-shift overflow", ``evaluate_constant [] (BaseT (IntT 8))
      (JE_BinOp (JE_Int 64 JT_None) JBop_LShift ^int1 JT_None)``),
   ("negative shift count", ``evaluate_constant [] ^uint256
      (JE_BinOp ^int1 JBop_RShift (JE_Int (-1) JT_None) JT_None)``),
   ("constant shift count above 256", ``evaluate_constant [] ^uint256
      (JE_BinOp ^int1 JBop_RShift (JE_Int 257 JT_None) JT_None)``),
   ("signed runtime shift count", ``elaborate_integer []
      [("x", BaseT (IntT 256)); ("n", BaseT (IntT 256))]
      (BaseT (IntT 256))
      (JE_BinOp (JE_Name "x" NONE JMissingSource JT_None)
        JBop_RShift (JE_Name "n" NONE JMissingSource JT_None) JT_None)``)];

val () = app (fn bits => app (fn signed =>
  rejects ("integer width " ^ Int.toString bits)
    ``resolve_constant_annotation []
       (CA_Integer ^(numSyntax.term_of_int bits) ^(boolSyntax.mk_bool signed))``)
  [false,true]) [0,1,7,9,255,257];

Theorem constant_integer_widths:
  (!signed. resolve_constant_annotation [] (CA_Integer 8 signed) =
    SOME (BaseT (if signed then IntT 8 else UintT 8))) /\
  (!signed. resolve_constant_annotation [] (CA_Integer 16 signed) =
    SOME (BaseT (if signed then IntT 16 else UintT 16))) /\
  (!signed. resolve_constant_annotation [] (CA_Integer 256 signed) =
    SOME (BaseT (if signed then IntT 256 else UintT 256)))
Proof
  simp[resolve_constant_annotation_def]
QED

val shifts_fixture = "../tests/fixtures/check_contract/constant_shifts.json";
val shifts_json = JSONDecode.decodeFile JSONDecode.raw shifts_fixture;
val shifts_declarations =
  JSONDecode.decode jsonConstASTLib.annotated_ast shifts_json;
val () = app (fn input =>
  if aconv shifts_declarations
     (JSONDecode.decode jsonConstASTLib.annotated_ast input) then ()
  else raise Fail "shift decoding depends on compiler metadata")
  [remove_metadata shifts_json, poison_metadata shifts_json];
val int256 = ``BaseT (IntT 256)``;
val uint8 = ``BaseT (UintT 8)``;
val expected_shifts = ``SOME [(NONE : num option,
  [VariableDecl Private
     (Constant (Builtin ^uint256 (Bop ShL)
       [Literal ^uint256 (IntL 1); Literal ^uint256 (IntL 1)]))
     "N" ^uint256 NONE;
   VariableDecl Private
     (Constant (Builtin ^int256 (Bop ShR)
       [Builtin ^int256 (Bop Sub)
         [Literal ^int256 (IntL 0); Literal ^int256 (IntL 8)];
        Literal ^uint256 (IntL 1)]))
     "M" ^int256 NONE;
   FunctionDecl External Pure F F "left"
     [("x", ^int256); ("n", ^uint8);
      ("values", ArrayT ^uint256 (Fixed 2))] [] ^int256
     [Return (SOME (Builtin ^int256 (Bop ShL)
       [Name ^int256 "x"; Name ^uint8 "n"]))];
   FunctionDecl External Pure F F "right"
     [("x", ^int256); ("n", ^uint256)] [] ^int256
     [Return (SOME (Builtin ^int256 (Bop ShR)
       [Name ^int256 "x"; Name ^uint256 "n"]))];
   FunctionDecl External Pure F F "count_expression"
     [("x", ^int256); ("n", ^uint8)] [] ^int256
     [Return (SOME (Builtin ^int256 (Bop ShR)
       [Name ^int256 "x"; Builtin ^uint8 (Bop Add)
         [Literal ^uint8 (IntL 1); Name ^uint8 "n"]]))]])]``;
val translated_shifts = EVAL ``translate_constant_module ^shifts_declarations``;
val () = if aconv (rhs (concl translated_shifts)) expected_shifts then ()
  else raise Fail "unsigned shift-count translation mismatch";
Theorem constant_shifts_translation = translated_shifts;
val checked_shifts = vyperCheckContractFrontendLib.check_constant_contract_file_legacy
  {address = ``0w : address``, path = shifts_fixture};
val () = if optionSyntax.is_some (rhs (concl checked_shifts)) then ()
  else raise Fail "signed-shift contract rejected by check_contract";
Theorem constant_shifts_contract_checked = checked_shifts;

Theorem constant_dependency_evaluation:
  evaluate_constant [("N",3)] (BaseT (UintT 256))
    (JE_BinOp (JE_Name "N" NONE JMissingSource JT_None)
      JBop_Mult (JE_Int 2 JT_None) JT_None) =
  SOME (Builtin (BaseT (UintT 256)) (Bop Mul)
    [Literal (BaseT (UintT 256)) (IntL 3);
     Literal (BaseT (UintT 256)) (IntL 2)], 6)
Proof
  EVAL_TAC
QED
