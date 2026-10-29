(* Full-Source acceptance extends the ordinary shared inventory and oracles. *)
structure sourceOrdinaryAcceptanceLib = struct
open HolKernel Parse boolLib bossLib
open sourceModuleElaborateTheory sourceModuleEnvTheory sourceModuleDefsTheory sourceTypeDefsTheory
open sourceSyntaxTheory sourceConstAnnotationTheory sourceConstASTTheory vyperTypeContractTheory
open vyperContextTheory vyperASTTheory vyperValueTheory finite_mapTheory
open sourceOrdinaryFixtureLib

(* Keep the original full-Source domain when the shared hybrid inventory gains
   address_bytes32: wide convert is not a supported full-Source expression.
   The shared ordinary/core tests still exercise that additional fixture. *)
val rows = List.filter (fn (name,_) => name <> "address_bytes32")
  sourceOrdinaryFixtureLib.rows;
val () = if length rows = 26 then () else raise Fail "full-Source inventory drift";

(* Full-Source interface expressions erase the legacy Acc Address wrapper;
   ordinary residual normalization deliberately preserves it. Adapt only the
   independent expected functions, never the elaborator's actual output. *)
fun canonical_interface_addresses tm = let val (head,args) = strip_comb tm in
  if is_const head andalso #Name (dest_thy_const head) = "Builtin" andalso length args = 3
     andalso aconv (List.nth (args,0)) ``BaseT AddressT``
     andalso aconv (List.nth (args,1)) ``Acc Address`` then
    (case #1 (listSyntax.dest_list (List.nth (args,2))) of
       [e] => canonical_interface_addresses e | _ => tm)
  else if is_comb tm then let val (f,x) = dest_comb tm in
    mk_comb (canonical_interface_addresses f,canonical_interface_addresses x) end
  else tm end;
fun expected_functions name modules =
  map canonical_interface_addresses (sourceOrdinaryFixtureLib.expected_functions name modules);
fun expected_modules name identities slots modules = let
  val expected = sourceOrdinaryFixtureLib.expected_modules name identities slots modules
  fun one entry = let val (src,tops) = pairSyntax.dest_pair entry
    fun declaration tl = if #Name (dest_thy_const (#1 (strip_comb tl))) = "FunctionDecl"
      then canonical_interface_addresses tl else tl
    in pairSyntax.mk_pair (src,listSyntax.mk_list
      (map declaration (#1 (listSyntax.dest_list tops)),``:toplevel``)) end
  in listSyntax.mk_list (map one (#1 (listSyntax.dest_list expected)),
    ``:num option # toplevel list``) end;
fun missing_attr field (JSON.OBJECT fields) = JSON.OBJECT (map (fn (key,value) =>
      if key = "attr" andalso (case value of JSON.STRING s => s = field | _ => false)
      then (key,JSON.STRING "missing") else (key,missing_attr field value)) fields)
  | missing_attr field (JSON.ARRAY values) = JSON.ARRAY (map (missing_attr field) values)
  | missing_attr field value = value;
fun run (name,path) = let
  val () = print ("ORDINARY_START " ^ name ^ "\n")
  val old = inherited path
  val () = print ("ORDINARY_PREPARED " ^ name ^ "\n")
  val modules = #modules old
  val identities = ids name
  val nominals = nominal_names identities modules
  val tenv = ev ``type_env_all_modules ^modules``
  val layouts = #layouts old
  val slots = ev ``FLAT (MAP (\(a,s,t). s ++ t) ^layouts)``
  val trust = ``<| smt_ids := ^identities; smt_nominals := ^nominals;
    smt_type_defs := ^tenv; smt_slots := ^slots |>``
  val source = sourceModuleLoaderLib.load_file (base ^ "source_ordinary/" ^ name ^ ".json")
  val checked = vyperCheckContractFrontendLib.Source.check_loaded_contract_result
    {fuel=fuel,trust=trust,source=source,layouts=layouts,address=address}
  val () = print ("ORDINARY_SOURCE_CHECKED " ^ name ^ "\n")
  val elab = #elaboration checked
  val legacy_check = vyperCheckContractLib.check_contract
    {in_deploy=true,address=address,modules=modules,layouts=layouts}
  val () = audit legacy_check
  val () = if aconv (rhs (concl legacy_check)) (rhs (concl (#checking checked))) then ()
    else raise Fail ("ordinary checker artifact mismatch: " ^ name)
  val _ = save_thm (name ^ "_legacy_check",legacy_check)
  val () = app audit [#equation elab,#original elab,#linking elab,#checking checked,#composition checked]
  val _ = save_thm (name ^ "_phase",#equation elab)
  val _ = save_thm (name ^ "_original",#original elab)
  val _ = save_thm (name ^ "_link",#linking elab)
  val _ = save_thm (name ^ "_check",#composition checked)
  val () = if name = "simple" orelse name = "imported_interface" then let
    val file = {fuel=fuel,trust=trust,layouts=layouts,address=address,
      path=base ^ "source_ordinary/" ^ name ^ ".json"}
    val from_file = vyperCheckContractFrontendLib.Source.check_contract_file_result file
    val scalar = vyperCheckContractFrontendLib.Source.check_contract_file file
    val () = app audit [#composition from_file,scalar]
    in if aconv (concl (#composition from_file)) (concl (#composition checked)) andalso
      aconv (concl scalar) (concl (#checking checked)) then ()
    else raise Fail ("public ordinary file/loaded disagreement: " ^ name) end else ()
  val () = if name = "imported_struct" orelse name = "imported_flag" then let
    val bad = JSONDecode.decode sourceModuleLoaderLib.source_capture
      (missing_attr (if name = "imported_struct" then "x" else "ADMIN")
        (JSONDecode.decodeFile JSONDecode.raw (base ^ "source_ordinary/" ^ name ^ ".json")))
    val rejects = (vyperCheckContractFrontendLib.Source.check_loaded_contract_result
      {fuel=fuel,trust=trust,source=bad,layouts=layouts,address=address}; false)
      handle HOL_ERR _ => true
    in if rejects then print ("ORDINARY_INVALID_MEMBER_REJECT " ^ name ^ "\n")
    else raise Fail ("unchecked source member/runtime candidate: " ^ name) end else ()
  val expected = expected_modules name identities slots modules
  val () = if aconv (#modules elab) expected then () else
    raise Fail ("exact ordinary module AST mismatch: " ^ name ^ "\nactual " ^
      term_to_string (#modules elab) ^ "\nexpected " ^ term_to_string expected)
  val actual_fns = functions (#modules elab)
  val old_fns = expected_functions name modules
  val equal = length actual_fns = length old_fns andalso ListPair.allEq (fn (a,b) => aconv a b) (actual_fns,old_fns)
  val () = print ("ORDINARY_FUNCTION_AST " ^ name ^ " " ^ Bool.toString equal ^ "\n")
  val () = if equal then () else raise Fail ("exact ordinary function AST mismatch: " ^ name ^
    "\nactual " ^ term_to_string (#modules elab) ^ "\nlegacy " ^ term_to_string modules)
  val () = print ("ORDINARY_PASS " ^ name ^ "\n")
  in true end handle e => (print ("ORDINARY_FAILURE " ^ name ^ ": " ^ General.exnMessage e ^ "\n"); false);
fun run_cases cases = let val outcomes = map run cases in
  if List.all I outcomes then () else raise Fail "ordinary source coverage has failures" end;
end
