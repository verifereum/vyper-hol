Theory sourceOrdinaryProgramBoundaryTest
Ancestors
  sourceOrdinaryProgram sourceOrdinaryExprElaborate sourceModuleEnv sourceModuleDefs
  sourceSyntax sourceConstAST vyperAST vyperTypeContract finite_map
Libs
  sourceOrdinaryProgramTestLib
fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract"];

val trust = ``<| smt_ids := [(["main"],NONE)]; smt_nominals := [];
  smt_type_defs := FEMPTY; smt_slots := [] |>``;
val layouts = ``[(0w:address,([]:storage_layout,[]:storage_layout))]``;
fun obj fs = JSON.OBJECT fs;
fun str s = JSON.STRING s;
fun arr xs = JSON.ARRAY xs;
fun ast k fs = obj (("ast_type",str k)::fs);
fun put key value (JSON.OBJECT fs) = obj ((key,value)::List.filter (fn (k,_) => key <> k) fs)
  | put _ _ _ = raise Fail "object";
fun name n = ast "Name" [("id",str n)];
fun integer n = ast "Int" [("value",JSON.INT n)];
fun call f args kws = ast "Call" [("func",f),("args",arr args),("keywords",arr kws)];
val uint = obj [("name",str "uint256"),("typeclass",str "integer"),("bits",JSON.INT 256),("is_signed",JSON.BOOL false)];
fun bytes n = obj [("name",str "Bytes"),("typeclass",str "bytes"),("length",JSON.INT n)];
fun typed t e = put "type" t e;
fun annotate j = case j of JSON.OBJECT fs => let
  val k = JSONDecode.decode (JSONDecode.field "ast_type" JSONDecode.string) j
  val j = obj (map (fn (k,v) => (k,annotate v)) fs)
  in if k = "FunctionDef" then put "func_type" (obj
      [("argument_types",arr [bytes 4,bytes 4]),("return_type",bytes 8)]) j
    else if k = "Call" then typed (bytes 8) j else if k = "Name" then
      (case JSONDecode.decode (JSONDecode.field "id" JSONDecode.string) j of
         "a" => typed (bytes 4) j | "b" => typed (bytes 4) j | _ => j)
    else j end
  | JSON.ARRAY xs => arr (map annotate xs) | j => j;
val raw_source = sourceOrdinaryProgramTestLib.get "annotated_ast"
  (sourceOrdinaryProgramTestLib.raw "fixtures/check_contract/source_ordinary/concat_residual_source.json");
val original = sourceOrdinaryProgramTestLib.standalone raw_source;
val annotated = obj [("ast",annotate (sourceOrdinaryProgramTestLib.get "ast" raw_source)),("imports",arr [])];
val paired = sourceOrdinaryClaimsLib.pair_program original raw_source annotated;
val input = sourceOrdinaryProgramTestLib.input paired trust layouts;
val checked = vyperCheckContractFrontendLib.check_contract_result input;
val () = sourceOrdinaryProgramTestLib.save "concat" checked;
val actual = #modules checked;
Theorem concat_remains_legacy_runtime_parent:
  ^actual = [(NONE,[FunctionDecl External Pure F F "f"
    [("a",BaseT (BytesT (Dynamic 4)));("b",BaseT (BytesT (Dynamic 4)))] []
    (BaseT (BytesT (Dynamic 8)))
    [Return (SOME (Builtin (BaseT (BytesT (Dynamic 8))) (Concat 8)
      [Name (BaseT (BytesT (Dynamic 4))) "a";Name (BaseT (BytesT (Dynamic 4))) "b"]))]])]
Proof
  EVAL_TAC
QED
val () = sourceOrdinaryProgramTestLib.invariant original raw_source annotated input checked;

(* Malformed required consumers are errors, never a whole-source/legacy retry. *)
fun program expr defaults ret = obj [("ast",ast "Module" [("body",arr
  [ast "FunctionDef" [("name",str "f"),("decorator_list",arr [name "external"]),
    ("func_type",obj [("argument_types",arr []),("return_type",uint)]),
    ("args",ast "arguments" [("args",arr []),("defaults",arr defaults)]),
    ("returns",ret),("body",arr [ast "Return" [("value",expr)]])]])]),("imports",arr [])];
fun rejected label source annotated = let
  val original = sourceOrdinaryProgramTestLib.standalone source
  val p = sourceOrdinaryClaimsLib.pair_program original source annotated
  val result = (ignore (vyperCheckContractFrontendLib.check_contract_result
      {fuel=sourceOrdinaryProgramTestLib.fuel,paired=p,address=sourceOrdinaryProgramTestLib.address,
       inherited={trust=trust,layouts=layouts,contexts= #contexts (#inherited input)}}); false)
    handle Fail _ => true | HOL_ERR _ => true
  in if result then print ("BRIDGE_REJECT " ^ label ^ "\n") else raise Fail ("accepted " ^ label) end;
val dynamic_method = program (call (name "method_id") [name "missing"] []) [] (name "uint256");
val () = rejected "standalone-dynamic-method-id" dynamic_method dynamic_method;
val invalid_child = ast "BinOp" [("left",integer 1),("op",ast "FloorDiv" []),("right",integer 0)];
val invalid_residual = program (typed uint (call (name "concat") [invalid_child,integer 1] [])) [] (name "uint256");
val () = rejected "invalid-child-of-residual" invalid_residual invalid_residual;
val invalid_bound = ast "Subscript" [("value",name "Bytes"),("slice",integer 0)];
val invalid_annotation = program (integer 0) [] invalid_bound;
val () = rejected "original-annotation-bound" invalid_annotation invalid_annotation;
val invalid_keyword = program (call (name "abi_encode") [integer 1]
  [ast "keyword" [("arg",str "ensure_tuple"),("value",integer 1)]]) []
  (ast "Subscript" [("value",name "Bytes"),("slice",integer 32)]);
val () = rejected "abi-boolean-not-integer" invalid_keyword invalid_keyword;
(* The formerly invalid #543 whole program has a bound dynamic string, not
   a missing name. Inherited types cannot turn it into a selector constant. *)
val method_var = sourceOrdinaryProgramTestLib.raw "fixtures/check_contract/source_syntax/method_id_var.json";
val () = rejected "method_id_var-expected-whole-program-rejection" method_var method_var;
val constant_original = program (integer 7) [] (name "uint256");
val constant_poison = program (typed (bytes 9) (integer 7)) [] (name "uint256");
val constant_loader = sourceOrdinaryProgramTestLib.standalone constant_original;
val constant_pair = sourceOrdinaryClaimsLib.pair_program constant_loader constant_original constant_poison;
val constant_checked = vyperCheckContractFrontendLib.check_contract_result
  (sourceOrdinaryProgramTestLib.input constant_pair trust layouts);
val constant_modules = #modules constant_checked;
Theorem original_constant_ignores_inherited_literal_type:
  ^constant_modules = [(NONE,[FunctionDecl External Nonpayable F F "f" [] []
    (BaseT (UintT 256)) [Return (SOME (Literal (BaseT (UintT 256)) (IntL 7)))]])]
Proof
  EVAL_TAC
QED
val () = print "BRIDGE_CONCAT_AND_BOUNDARY_PASS\n";
