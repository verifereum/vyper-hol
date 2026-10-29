Theory sourceModuleFrontendLibTest
Ancestors
  sourceModuleElaborate sourceModuleDecl sourceModuleEnv sourceModuleDefs
  sourceModuleStmt sourceSyntax sourceConstBuiltinCompute sourceConstBuiltinTest
  sourceConstBuiltin sourceTypeDefs sourceConstAST sourceConstAnnotation
  vyperTypeContract vyperAST vyperContext finite_map
Libs
  sourceModuleFrontendLib cv_transLib

fun holbuild_extra_deps (_ : string list) = ();
val () = holbuild_extra_deps ["../tests/fixtures/check_contract/source_syntax",
  "../lowering/defs/bytecode/folded-value-witnesses.txt"];

(* Proved executable Keccak equations, not imported selector/folding metadata. *)
val () = app (fn s => let
    val tm = listSyntax.mk_list (List.map (fn c => numSyntax.term_of_int (Char.ord c))
      (String.explode s),numSyntax.num)
    val th = cv_eval (mk_comb (``source_const_keccak``,tm))
  in computeLib.add_funs [th] end)
  ["hello","transfer(address,uint256)","foo()","f(uint256)","E(uint256)","x"];

val address = ``0w:address``;
val keys = ``[["main"]]``;
fun trust slots = ``<| smt_ids := [(["main"],NONE)]; smt_nominals := [];
  smt_type_defs := FEMPTY; smt_slots := ^slots |>``;
fun input program slots : sourceModuleFrontendLib.simple_input =
  {fuel=``80:num``,trust=trust slots,keys=keys,program=program};
fun layouts slots = ``[(^address,(^slots,[]:storage_layout))]``;
val manifest = TextIO.openIn "../lowering/defs/bytecode/folded-value-witnesses.txt";
val names = String.tokens Char.isSpace (TextIO.inputAll manifest);
val () = TextIO.closeIn manifest;
val () = if length names = 37 then () else raise Fail "retained witness manifest changed";
fun slots_for name = if name = "method_id_storage" then ``[((NONE,"m"),0:num)]:storage_layout``
  else if name = "i12_immut_with_storage" then ``[((NONE,"s"),0:num)]:storage_layout``
  else ``[]:storage_layout``;
fun fixture name = "../tests/fixtures/check_contract/source_syntax/" ^ name ^ ".json";
fun fold_variant replacement (JSON.OBJECT fields) = JSON.OBJECT
      ((case replacement of NONE => [] | SOME value => [("folded_value",value)]) @
       List.map (fn (k,v) => (k,fold_variant replacement v))
         (List.filter (fn (k,_) => k <> "folded_value") fields))
  | fold_variant replacement (JSON.ARRAY xs) = JSON.ARRAY (List.map (fold_variant replacement) xs)
  | fold_variant _ value = value;
val poison = JSON.OBJECT [("ast_type",JSON.STRING "Int"),("value",JSON.INT 777)];
fun source name = let
  val raw = JSONDecode.decodeFile JSONDecode.raw (fixture name)
  val original = JSONDecode.decode sourceSyntaxLib.annotated_ast raw
  val () = app (fn variant =>
    if aconv original (JSONDecode.decode sourceSyntaxLib.annotated_ast variant) then ()
    else raise Fail ("source module folded metadata dependency: " ^ name))
      [fold_variant NONE raw,fold_variant (SOME poison) raw]
  in original end;

val () = app (fn name => let
    val program = source name
    val slots = slots_for name
    val src = input program slots
  in
    if name = "method_id_var" then let
      val equation = EVAL ``source_module_elaborate_simple ^(#fuel src) ^(#trust src) ^keys ^program``
      val result = rhs (concl equation)
      val _ = if aconv result ``SM_Error (SME_Constant SCErr_Domain):
        (num option # toplevel list) list source_retained source_module_result`` then ()
        else raise Fail ("unexpected method_id_var outcome: " ^ term_to_string result)
    in ignore (save_thm ("source_module_" ^ name ^ "_reject",equation)) end
    else let
      val checked = sourceModuleFrontendLib.check_simple src {layouts=layouts slots,address=address}
      val elaboration = #elaboration checked
      val _ = save_thm ("source_module_" ^ name ^ "_ast", #equation elaboration)
      val _ = save_thm ("source_module_" ^ name ^ "_check", #checking checked)
      val _ = save_thm ("source_module_" ^ name ^ "_composition", #composition checked)
    in print ("SOURCE_MODULE_ACCEPT_CHECK " ^ name ^ "\n") end
  end) names;

(* Exact independently stated module equation: forward declarations, original
   defaults and local annotations are all elaborated in source contexts. *)
Definition source_module_forward_fixture_def:
  source_module_forward_fixture = SourceProgram (SourceModule
    [SD_Variable "A" (SCA_Qualified SCQ_Constant (SCA_Name ["uint256"]))
       (SOME (SX_Binary SCB_Add (SX_Name "B") (SX_Literal (SCL_Int 1))));
     SD_Variable "B" (SCA_Qualified SCQ_Constant (SCA_Name ["uint256"]))
       (SOME (SX_Literal (SCL_Int 2)));
     SD_Function "f" [SX_Name "external";SX_Name "pure"]
       [SourceArg "x" (SOME (SCA_Name ["uint256"]))] [SX_Name "A"]
       (SOME (SCA_Name ["uint256"]))
       [SS_AnnAssign "y" (SCA_Name ["uint256"])
          (SOME (SX_Binary SCB_Add (SX_Name "x") (SX_Name "A")));
        SS_Return (SOME (SX_Name "y"))]]) []
End

val forward = sourceModuleFrontendLib.check_simple
  (input ``source_module_forward_fixture`` ``[]:storage_layout``)
  {layouts=layouts ``[]:storage_layout``,address=address};
val source_module_forward_phase = save_thm ("source_module_forward_phase",
  #equation (#elaboration forward));

Theorem source_module_forward_defaults_locals_exact:
  source_module_elaborate_simple 80
    <| smt_ids := [(["main"],NONE)]; smt_nominals := [];
       smt_type_defs := FEMPTY; smt_slots := [] |> [["main"]] source_module_forward_fixture =
  SM_Ok (SourceRetained source_module_forward_fixture
    [(NONE,[VariableDecl Private (Constant (Literal (BaseT (UintT 256)) (IntL 3)))
               "A" (BaseT (UintT 256)) NONE;
            VariableDecl Private (Constant (Literal (BaseT (UintT 256)) (IntL 2)))
               "B" (BaseT (UintT 256)) NONE;
            FunctionDecl External Pure F F "f" [("x",BaseT (UintT 256))]
              [Literal (BaseT (UintT 256)) (IntL 3)] (BaseT (UintT 256))
              [AnnAssign "y" (BaseT (UintT 256))
                (Builtin (BaseT (UintT 256)) (Bop Add)
                  [Name (BaseT (UintT 256)) "x";Literal (BaseT (UintT 256)) (IntL 3)]);
               Return (SOME (Name (BaseT (UintT 256)) "y"))]])])
Proof
  CONV_TAC (LAND_CONV (REWR_CONV source_module_forward_phase)) >> EVAL_TAC
QED

val _ = save_thm ("source_module_forward_check", #composition forward);

fun audit thy = app (fn (name,th) => let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn s => s = "DISK_THM") oracles then ()
    else raise Fail ("source module kernel audit: " ^ thy ^ "." ^ name) end) (DB.thms thy);
val () = app audit ["sourceModuleDefs","sourceModuleEnv","sourceModuleStmt",
  "sourceModuleSignature","sourceModuleContext","sourceModuleDecl",
  "sourceModuleElaborate","sourceModuleFrontendLibTest"];
