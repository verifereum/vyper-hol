structure sourceOrdinaryProgramTestLib = struct
open HolKernel Parse boolLib bossLib
open sourceOrdinaryProgramTheory sourceModuleDefsTheory sourceModuleEnvTheory
open sourceSyntaxTheory sourceTypeDefsTheory vyperASTTheory vyperTypeContractTheory
open finite_mapTheory sourceConstBuiltinTheory sourceConstBuiltinComputeTheory cv_transLib
(* Reuse the existing verified Keccak conversion; these are kernel equations
   from original strings, never compiler selectors or folded metadata. *)
val () = app (fn s => let
  val bytes = listSyntax.mk_list (map (fn c => numSyntax.term_of_int (Char.ord c))
    (String.explode s),numSyntax.num)
  val th = cv_eval (mk_comb (``source_const_keccak``,bytes))
  in computeLib.add_funs [th] end)
  ["hello","transfer(address,uint256)","foo()","f(uint256)","E(uint256)","x"];
fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract","../lowering/defs/bytecode"];
val address = ``0w:address``;
val fuel = ``80:num``;
fun raw path = JSONDecode.decodeFile JSONDecode.raw path;
fun get key json = JSONDecode.decode (JSONDecode.field key JSONDecode.raw) json;
fun unwrap json = case JSONDecode.decode (sourceConstASTLib.optional_field "annotated_ast" JSONDecode.raw) json of
  SOME j => j | NONE => json;
fun ev tm = rhs (concl (EVAL tm));
val audit = sourceOrdinaryAcceptanceLib.audit;
fun poison (JSON.OBJECT fs) = JSON.OBJECT (("folded_value",JSON.OBJECT
    [("ast_type",JSON.STRING "Int"),("value",JSON.INT 777),
     ("type",JSON.OBJECT [("typeclass",JSON.STRING "integer"),
       ("name",JSON.STRING "uint256"),("bits",JSON.INT 256),
       ("is_signed",JSON.BOOL false)])])::
    ("folded_literal",JSON.NULL)::List.map (fn (k,v) => (k,poison v))
      (List.filter (fn (k,_) => k <> "folded_value" andalso k <> "folded_literal") fs))
  | poison (JSON.ARRAY xs) = JSON.ARRAY (map poison xs) | poison j = j;
fun paired original original_json annotated = sourceOrdinaryClaimsLib.pair_program original original_json annotated;
(* Check the generator's explicit inherited origin map against the INDEPENDENT
   expected legacy IDs. Pairing itself still uses exact source/node IDs. *)
fun origins capture annotated identities = let
  val entries = JSONDecode.decode (JSONDecode.array JSONDecode.raw) (get "inherited_origins" capture)
  val expected = #1 (listSyntax.dest_list identities)
  fun modules json = get "ast" json :: JSONDecode.decode
    (JSONDecode.array JSONDecode.raw) (get "imports" json)
  val original = modules (get "annotated_ast" capture)
  val annotated = modules annotated
  val () = if length entries = length expected andalso length entries = length original
      andalso length entries = length annotated then () else raise Fail "ordinary origin inventory"
  fun one (entry,(identity,(source,claims))) = let
    val key = JSONDecode.decode (JSONDecode.array JSONDecode.string) (get "key" entry)
    val key = listSyntax.mk_list (map stringSyntax.fromMLstring key,``:string``)
    val module_id = case get "module_id" entry of JSON.NULL => ``NONE:num option``
      | JSON.INT n => optionSyntax.mk_some (numSyntax.mk_numeral (Arbnum.fromInt (IntInf.toInt n)))
      | _ => raise Fail "ordinary inherited module ID"
    val () = if aconv (pairSyntax.mk_pair (key,module_id)) identity then ()
      else raise Fail "ordinary inherited ID map disagrees with independent oracle"
    fun text key json = JSONDecode.decode JSONDecode.string (get key json)
    fun sid json = JSONDecode.decode JSONDecode.intInf (get "source_id" json)
    fun same node = if sid node = sid entry andalso
        text "resolved_path" node = text "path" entry andalso
        text "source_sha256sum" node = text "source_sha256" entry then ()
      else raise Fail "ordinary path/hash/source ID identity mismatch"
  in app same [source,claims] end
in app one (ListPair.zip (entries,ListPair.zip (expected,ListPair.zip (original,annotated)))) end;
fun input paired trust layouts =
  {fuel=fuel,paired=paired,address=address,inherited={trust=trust,layouts=layouts,
    contexts=sourceOrdinaryProgramLib.inherited_contexts paired trust}};
fun invariant original original_json annotated (inp:sourceOrdinaryProgramLib.input)
    (checked:sourceOrdinaryProgramLib.checked) = let
  val initial = #paired inp
  val clean = paired original original_json (sourceOrdinaryClaimsLib.without_folds annotated)
  val bad = paired original original_json (poison annotated)
  fun same p = let
    val contexts = sourceOrdinaryProgramLib.inherited_contexts p (#trust (#inherited inp))
    val () = if aconv (#claims initial) (#claims p) andalso
      aconv (#contexts (#inherited inp)) contexts then () else raise Fail "fold-dependent program input"
    val changed = vyperCheckContractFrontendLib.check_contract_result
      {fuel= #fuel inp,paired=p,address= #address inp,
       inherited={trust= #trust (#inherited inp),layouts= #layouts (#inherited inp),contexts=contexts}}
    val () = app audit [#composition changed,#theorem changed]
  in if aconv (#modules checked) (#modules changed) andalso
      aconv (#artifact checked) (#artifact changed) andalso
      aconv (concl (#composition checked)) (concl (#composition changed)) andalso
      aconv (concl (#theorem checked)) (concl (#theorem changed)) then ()
    else raise Fail "fold-dependent normalized module/check/artifact" end
  val () = app same [clean,bad]
in () end;
fun save name checked = let
  val elab = #elaboration (checked:sourceOrdinaryProgramLib.checked)
  val () = app audit [#projection (#paired checked),#shape (#paired checked),#source_match (#paired checked),
    #equation elab,#original elab,#linking elab,#theorem checked,#composition checked]
  val _ = save_thm (name ^ "_ordinary_phase",#equation elab)
  val _ = save_thm (name ^ "_ordinary_original",#original elab)
  val _ = save_thm (name ^ "_ordinary_check",#composition checked)
in () end;
(* The older full-Source oracle erases interface Acc Address identities.
   Ordinary residual calls intentionally retain those legacy constructors.
   Take their expected function bodies directly from the independent legacy
   fixture, never by rewriting/normalizing the actual bridge output. *)
fun expected_modules name identities slots modules = let
  val expected = sourceOrdinaryAcceptanceLib.expected_modules name identities slots modules
  val legacy = map pairSyntax.dest_pair (#1 (listSyntax.dest_list modules))
  fun one entry = let
    val (src,tops) = pairSyntax.dest_pair entry
    val old = case List.find (fn (s,_) => aconv s src) legacy of
      NONE => [] | SOME (_,ts) => #1 (listSyntax.dest_list ts)
    fun body tl = let val (ctor,args) = strip_comb tl in
      if name <> "decimal_folding" andalso #Name (dest_thy_const ctor) = "FunctionDecl" then
        valOf (List.find (fn candidate => let val (head,cs) = strip_comb candidate in
          #Name (dest_thy_const head) = "FunctionDecl" andalso
          aconv (List.nth (args,4)) (List.nth (cs,4)) end) old)
      else tl end
    in pairSyntax.mk_pair (src,listSyntax.mk_list
      (map body (#1 (listSyntax.dest_list tops)),``:toplevel``)) end
in listSyntax.mk_list (map one (#1 (listSyntax.dest_list expected)),``:num option # toplevel list``) end;
fun ordinary (name,path) = let
  val () = print ("BRIDGE_START " ^ name ^ "\n")
  val old = sourceOrdinaryAcceptanceLib.inherited path
  val identities = sourceOrdinaryAcceptanceLib.ids name
  val modules = #modules old
  val nominals = sourceOrdinaryAcceptanceLib.nominal_names identities modules
  val tenv = ev ``type_env_all_modules ^modules``
  val layouts = #layouts old
  val slots = ev ``FLAT (MAP (\(a,s,t). s ++ t) ^layouts)``
  val trust = ``<| smt_ids := ^identities; smt_nominals := ^nominals;
    smt_type_defs := ^tenv; smt_slots := ^slots |>``
  val source_path = "fixtures/check_contract/source_ordinary/" ^ name ^ ".json"
  val original = sourceModuleLoaderLib.load_file source_path
  val capture = raw source_path
  val original_json = get "annotated_ast" capture
  val annotated_path = "fixtures/check_contract/source_ordinary/annotated/" ^ name ^ ".json"
  val annotated = raw annotated_path
  val () = origins capture annotated identities
  val p = paired original original_json annotated
  val () = print ("BRIDGE_PAIRED " ^ name ^ "\n")
  val inp = input p trust layouts
  val checked = vyperCheckContractFrontendLib.check_contract_result inp
  val () = save name checked
  val expected = expected_modules name identities slots modules
  val () = if aconv (#modules checked) expected then () else raise Fail
    ("ordinary exact AST: " ^ name ^ "\nactual " ^ term_to_string (#modules checked) ^
      "\nexpected " ^ term_to_string expected)
  val legacy_check = vyperCheckContractLib.check_contract old
  val () = audit legacy_check
  val () = if aconv (rhs (concl legacy_check)) (optionSyntax.mk_some (#artifact checked)) then ()
    else raise Fail ("ordinary independent legacy artifact: " ^ name)
  val _ = save_thm (name ^ "_ordinary_expected_ast",REFL expected)
  val _ = save_thm (name ^ "_ordinary_legacy_artifact",legacy_check)
  val () = invariant original original_json annotated inp checked
  val () = if List.exists (fn n => n = name) ["simple","imported_struct","duplicate_interface"] then let
    val prepared = vyperCheckContractFrontendLib.prepare_check_input inp
    val scalar = vyperCheckContractFrontendLib.check_contract inp
    val () = app audit [#equation (#elaboration prepared),scalar]
    val () = if aconv (#modules (#input prepared)) (#modules checked) andalso
      aconv (concl scalar) (concl (#theorem checked)) then () else raise Fail "ordinary prepare/scalar API divergence"
    val file_input = {fuel=fuel,inherited= #inherited inp,address=address,
      original_path=source_path,annotated_path=annotated_path}
    val file = vyperCheckContractFrontendLib.check_contract_file_result file_input
    val file_scalar = vyperCheckContractFrontendLib.check_contract_file file_input
    val () = app audit [#composition file,file_scalar]
    in if aconv (concl (#composition file)) (concl (#composition checked)) andalso
        aconv (concl file_scalar) (concl scalar) then ()
      else raise Fail "ordinary file API divergence" end else ()
  val () = print ("BRIDGE_PASS " ^ name ^
    " exact-AST independent-artifact folds=delete/poison identical-modules+artifact+equations\n")
in () end;
fun standalone json : sourceModuleLoaderLib.loaded =
  {program=JSONDecode.decode sourceSyntaxLib.annotated_ast json,keys=``[["main"]]``,
   nonreentrant_defaults=``[F]``,declaration_only=``[F]``,provenance=json};
fun witness name = let
  val () = print ("BRIDGE_WITNESS_START " ^ name ^ "\n")
  val original_json = raw ("fixtures/check_contract/source_syntax/" ^ name ^ ".json")
  val original = standalone original_json
  val annotated = unwrap (raw ("../lowering/defs/bytecode/folded-value-oracle/" ^ name ^ ".json"))
  val p = paired original original_json annotated
  val slots = if name = "method_id_storage" then ``[((NONE,"m"),0:num)]:storage_layout``
    else if name = "i12_immut_with_storage" then ``[((NONE,"s"),0:num)]:storage_layout``
    else ``[]:storage_layout``
  val trust = ``<| smt_ids := [(["main"],NONE)]; smt_nominals := [];
    smt_type_defs := FEMPTY; smt_slots := ^slots |>``
  val layouts = ``[(^address,(^slots,[]:storage_layout))]``
  val inp = input p trust layouts
  val checked = vyperCheckContractFrontendLib.check_contract_result inp
  val () = save name checked
  val source = sourceModuleFrontendLib.check_simple
    {fuel=fuel,trust=trust,keys= #keys original,program= #program original}
    {layouts=layouts,address=address}
  val () = if aconv (#modules checked) (#modules (#elaboration source)) andalso
      aconv (#artifact checked) (#artifact source) then () else raise Fail ("witness AST/artifact: " ^ name)
  val () = invariant original original_json annotated inp checked
  val () = print ("BRIDGE_WITNESS_PASS " ^ name ^ "\n")
in () end;
end
