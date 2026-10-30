Theory sourceShiftCountFrontendTest
Ancestors
  sourceShiftCountTest sourceModuleElaborate sourceModuleDefs sourceSyntax
  vyperTypeContract vyperAST finite_map
Libs
  vyperCheckContractFrontendLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["fixtures/check_contract"];

(* Existing #135 strict fixtures remain successful via BOTH APIs. Source JSON
   decoding of the same originals must produce exactly the same checked AST. *)
val address = ``0w : address``;
val fixtures = OS.Path.concat (OS.FileSys.getDir (),"fixtures/check_contract/");
fun audit th = let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
  if null (hyp th) andalso null axioms andalso
     List.all (fn s => s = "DISK_THM") oracles then ()
  else raise Fail "source shift regression theorem has assumptions/axioms/oracles" end;
fun check_fixture name = let
  val path = fixtures ^ name ^ ".json"
  val legacy = vyperCheckContractFrontendLib.check_constant_contract_file_legacy {address=address,path=path}
  val input = vyperCheckContractFrontendLib.Source.prepare_constant_file {address=address,path=path}
  val checked = vyperCheckContractFrontendLib.Source.check_contract_result input
  val strict = vyperCheckContractFrontendLib.Source.check_constant_contract_file {address=address,path=path}
  val original = JSONDecode.decodeFile
    (JSONDecode.field "annotated_ast" sourceSyntaxLib.annotated_ast)
    (fixtures ^ "source_ordinary/" ^ name ^ ".json")
  val same = vyperCheckContractFrontendLib.Source.check_contract_result
    {fuel= #fuel input,trust= #trust input,keys= #keys input,program=original,
     layouts= #layouts input,address=address}
  val () = app audit [legacy,strict,#checking checked,#composition checked,#checking same,#composition same]
  (* Legacy retains unfurled constant INITIALIZERS; Source reifies them.
     Preserve legacy acceptance/artifact and exact FUNCTION ASTs, not a false
     whole-module equality. Strict Source and genuine originals agree exactly. *)
  fun functions modules = let
    val [entry] = #1 (listSyntax.dest_list modules)
    val declarations = #1 (listSyntax.dest_list (snd (pairSyntax.dest_pair entry)))
  in List.filter (fn tm => same_const (#1 (strip_comb tm)) ``FunctionDecl``) declarations end
  val legacy_modules = List.last (#2 (strip_comb (lhs (concl legacy))))
  val () = if ListPair.allEq (fn (a,b) => aconv a b)
      (functions legacy_modules,functions (#modules (#elaboration checked))) andalso
      aconv (rhs (concl legacy)) (rhs (concl strict)) andalso
      aconv (concl strict) (concl (#checking checked)) andalso
      aconv (concl strict) (concl (#checking same)) then ()
    else raise Fail ("strict/source/legacy shift AST mismatch: " ^ name)
  val _ = save_thm (name ^ "_legacy",legacy)
  val _ = save_thm (name ^ "_source",strict)
  val _ = save_thm (name ^ "_source_composition",#composition checked)
  val _ = save_thm (name ^ "_original_composition",#composition same)
in () end;
val () = app check_fixture ["constant_bound","constant_shifts"];
