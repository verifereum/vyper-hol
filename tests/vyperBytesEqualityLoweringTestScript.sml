Theory vyperBytesEqualityLoweringTest
Ancestors
  jsonToVyper jsonToVyperExpr vyperAST compileVyper vyperCompiler
  exprLowering compileEnv venomInst
Libs jsonASTLib finite_mapLib wordsLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;

(* The variable keeps the comparison itself from folding in the frontend. *)
fun lower_equality literal_kind expected_shape = let
  val source = JSONDecode.decodeString jsonASTLib.json_expr
    ("{\"ast_type\":\"Compare\",\"op\":{\"ast_type\":\"Eq\"},\
     \ \"left\":{\"ast_type\":\"Name\",\"id\":\"data\",\"type\":{\"name\":\"Bytes\",\"length\":1}},\
     \ \"right\":{\"ast_type\":\"" ^ literal_kind ^ "\",\"value\":\"0x61\",\
     \          \"type\":{\"name\":\"Bytes\",\"length\":1}}}")
  val comparison = rhs (concl (EVAL ``translate_expr
    (module_expr_ctx [] (0:int) NONE [] [] [] []) ^source``))
  val env = ``build_compile_env [] External Nonpayable "check"
    [("data", BaseT (BytesT (Dynamic 1)))] (BaseT BoolT) [] F``
  val lowered = EVAL ``
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs))
      (FILTER (\i. i.inst_opcode = SHA3 \/ i.inst_opcode = EQ)
        (SND (compile_expr ^env (BaseT BoolT) ^comparison
          (initial_compile_state "entry"))).cs_current_insts)``
  val shape = rhs (concl lowered)
  val checked = EVAL ``^expected_shape ^shape``
in
  if aconv (rhs (concl checked)) boolSyntax.T then lowered
  else raise Fail (literal_kind ^ " equality lowered to unexpected SHA3/EQ: " ^
    term_to_string shape)
end;

Theorem hex_bytes_equality_uses_runtime_hash = lower_equality "HexBytes" ``
  \code. case code of
  | [(SHA3, _, [left]); (SHA3, _, [right]); (EQ, [lhs; rhs], _)] =>
      left <> right /\ lhs = Var left /\ rhs = Var right
  | _ => F``;

(* Keccak-256 of b"a" (0x61). *)
Theorem bytes_equality_uses_literal_hash = lower_equality "Bytes" ``
  \code. case code of
  | [(SHA3, _, [left]); (EQ, [lhs; rhs], _)] =>
      lhs = Var left /\
      rhs = Lit 0x3ac225168df54212a25c1c01fd35bebfea408fdac2e31ddd6f80a4bbf9a5f1cbw
  | _ => F``;
