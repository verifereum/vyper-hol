Theory jsonConstEvalWitness
Ancestors
  jsonConstEval jsonConstAST jsonAST vyperConstEval vyperAST
  vyperInterpreter vyperState vyperValue
Libs
  jsonConstASTLib vyperCheckContractFrontendLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../tests/fixtures/check_contract/constant_bound.json"];

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

val checked = vyperCheckContractFrontendLib.check_constant_contract_file
  {address = ``0w : address``, path = fixture};
val () = if optionSyntax.is_some (rhs (concl checked)) then ()
  else raise Fail "constant-bound contract rejected by check_contract";
Theorem constant_bound_contract_checked = checked;

fun rejects label term =
  if optionSyntax.is_none (rhs (concl (EVAL term))) then ()
  else raise Fail ("constant frontend accepted " ^ label);
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
