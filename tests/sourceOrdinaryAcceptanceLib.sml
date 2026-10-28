structure sourceOrdinaryAcceptanceLib = struct
open HolKernel Parse boolLib bossLib
open sourceModuleElaborateTheory sourceModuleEnvTheory sourceModuleDefsTheory sourceTypeDefsTheory
open sourceSyntaxTheory sourceConstAnnotationTheory sourceConstASTTheory vyperTypeContractTheory
open vyperContextTheory vyperASTTheory vyperValueTheory finite_mapTheory

fun holbuild_extra_deps (_ : string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract"];
val base = "fixtures/check_contract/";
val address = ``0w:address``;
val fuel = ``80:num``;
val rows =
  map (fn n => (n,n ^ ".json")) ["simple","storage","address_bytes20",
    "constant_bound","constant_shifts","constant_shift_overflow","calldata_slice",
    "in_static_array","nested_pop","decimal_folding","raw_call_calldata","unreachable"] @
  map (fn n => (n,n ^ "/main.json")) ["scoped_locals","imported_flag","imported_struct",
    "imported_deploy","multimodule_storage","defaults_control","deployment","nonreentrant",
    "transient_storage","abi_encode","imported_interface","interface_struct_return"] @
  [("duplicate_interface","duplicate_interface/main/c.json"),("daddy","third_party/flex/daddy/daddy.json")];
val () = if length rows = 26 then () else raise Fail "ordinary source inventory drift";
fun audit th = let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
  if null (hyp th) andalso null axioms andalso List.all (fn s => s = "DISK_THM") oracles
  then () else raise Fail "non-kernel source ordinary certificate" end;
fun ev tm = rhs (concl (bossLib.EVAL tm));
(* Complete legacy translation is an independent expected-AST oracle only.
   Only its layouts and nominal declarations/types become source trust. *)
fun inherited path = vyperCheckContractFrontendLib.prepare_check_input_legacy
  {in_deploy=true,address=address,
   annotated_ast=JSONDecode.decodeFile jsonASTLib.annotated_ast (base ^ path),
   storage_layout=JSONDecode.decodeFile jsonASTLib.storage_layout (base ^ path)};
(* Explicit legacy evidence: duplicate IPing aliases share original source ID 1,
   hence module SOME 3; an alias must not allocate a fresh module identity. *)
fun ids name = if name = "duplicate_interface" then
    ``[(["main";"c"],NONE);(["utils";"interfaces";"IPing"],SOME 3);(["utils";"pinger"],SOME 4)]``
  else if name = "imported_interface" then ``[(["main"],NONE);(["oracle"],SOME 3)]``
  else if name = "interface_struct_return" then ``[(["main"],NONE);(["manager"],SOME 3)]``
  else if List.exists (fn n => n = name) ["scoped_locals","imported_flag","imported_struct",
    "imported_deploy","multimodule_storage"] then ``[(["main"],NONE);(["lib"],SOME 3)]``
  else ``[(["main"],NONE:num option)]``;
fun nominal_names ids modules = let
  val entries = #1 (listSyntax.dest_list modules)
  val keys = map pairSyntax.dest_pair (#1 (listSyntax.dest_list ids))
  fun one entry = let val (src,tops) = pairSyntax.dest_pair entry
    val key = #1 (valOf (List.find (fn (_,s) => aconv src s) keys))
    fun decl tl = let val (c,args) = strip_comb tl
      val name = if null args then "" else #Name (dest_thy_const c)
      fun named identity = let val p = listSyntax.mk_list
        (#1 (listSyntax.dest_list key) @ [hd args], ``:string``)
        in [pairSyntax.mk_pair (p,identity)] end
      in if name = "StructDecl" then named ``STI_Struct (^src,^(hd args))``
      else if name = "FlagDecl" then named ``STI_Flag (^src,^(hd args))``
      else if name = "InterfaceDecl" then named ``STI_Interface`` else [] end
    in List.concat (map decl (#1 (listSyntax.dest_list tops))) end
  in listSyntax.mk_list (List.concat (map one entries), ``:string list # source_type_identity``) end;
fun functions modules = let
  fun one entry = let val (src,tops) = pairSyntax.dest_pair entry in
    pairSyntax.mk_pair (src,listSyntax.mk_list (List.filter (fn tl =>
      #Name (dest_thy_const (#1 (strip_comb tl))) = "FunctionDecl")
      (#1 (listSyntax.dest_list tops)),``:toplevel``)) end
  in List.filter (fn entry => not (null (#1 (listSyntax.dest_list (#2 (pairSyntax.dest_pair entry))))))
    (map one (#1 (listSyntax.dest_list modules))) end;
(* Independent decimal observations are also pinned by
   vyperDecimalFrontendTest. The ordinary JSON's folded Decimal.value contains
   source text, so its legacy AST intentionally keeps arithmetic here. *)
fun canonical_interface_addresses tm = let val (head,args) = strip_comb tm in
  if is_const head andalso #Name (dest_thy_const head) = "Builtin" andalso length args = 3
     andalso aconv (List.nth (args,0)) ``BaseT AddressT``
     andalso aconv (List.nth (args,1)) ``Acc Address`` then
    (case #1 (listSyntax.dest_list (List.nth (args,2))) of
       [e] => canonical_interface_addresses e | _ => tm)
  else if is_comb tm then let val (f,x) = dest_comb tm in
    mk_comb (canonical_interface_addresses f,canonical_interface_addresses x) end
  else tm end;
fun expected_functions name modules = if name <> "decimal_folding" then
  map canonical_interface_addresses (functions modules) else let
  val values = [("minmax","582231230000000"),("integer_minmax","83"),
    ("arithmetic","92500000000"),("negative","-37500000000"),("scientific","125000002")]
  fun entry e = let val (src,tops) = pairSyntax.dest_pair e
    fun body tl = let val (_,args) = strip_comb tl
      val id = stringSyntax.fromHOLstring (List.nth (args,4))
      in case List.find (fn (n,_) => n = id) values of NONE => tl | SOME (_,n) => let
        val ty = if id = "integer_minmax" then ``BaseT (UintT 256)`` else ``BaseT DecimalT``
        val value = intSyntax.term_of_int (Arbint.fromString n)
        val lit = if id = "integer_minmax" then ``IntL ^value`` else ``DecimalL ^value``
        val id = stringSyntax.fromMLstring id
        in ``FunctionDecl External Nonpayable F F ^id [] [] ^ty [Return (SOME (Literal ^ty ^lit))]`` end end
    in pairSyntax.mk_pair (src,listSyntax.mk_list (map body (#1 (listSyntax.dest_list tops)),``:toplevel``)) end
  in map entry (functions modules) end;
(* Exact SOURCE declarations: imported slot annotations are inherited layout
   facts, and these three integer initializers are independently known folds.
   No expected expression is computed by the source elaborator under test. *)
fun expected_modules name identities slots modules = let
  val old = map pairSyntax.dest_pair (#1 (listSyntax.dest_list modules))
  val expected_fns = map pairSyntax.dest_pair (expected_functions name modules)
  fun lookup entries src = case List.find (fn (s,_) => aconv src s) entries of
    NONE => [] | SOME (_,xs) => #1 (listSyntax.dest_list xs)
  fun decl src tl = let val (ctor,args) = strip_comb tl
    val kind = #Name (dest_thy_const ctor)
    fun slot id = ev ``ALOOKUP ^slots (^src,^id)``
    in if kind = "FunctionDecl" then
      valOf (List.find (fn candidate => aconv (List.nth (#2 (strip_comb candidate),4))
        (List.nth (args,4))) (lookup expected_fns src))
    else if kind = "VariableDecl" then let
      val vis = List.nth (args,0) val mut = List.nth (args,1)
      val id = List.nth (args,2) val ty = List.nth (args,3)
      val constant = #Name (dest_thy_const (#1 (strip_comb mut))) = "Constant"
      val n = if name = "constant_bound" andalso stringSyntax.fromHOLstring id = "N" then SOME 3
        else if name = "constant_shifts" then
          (if stringSyntax.fromHOLstring id = "N" then SOME 2 else SOME (~4)) else NONE
      val mut = if constant andalso Option.isSome n then
          let val value = intSyntax.term_of_int (Arbint.fromInt (valOf n))
          in ``Constant (Literal ^ty (IntL ^value))`` end else mut
      val sl = if constant orelse #Name (dest_thy_const (#1 (strip_comb mut))) = "Immutable"
        then List.nth (args,4) else slot id
      in ``VariableDecl ^vis ^mut ^id ^ty ^sl`` end
    else if kind = "HashMapDecl" then
      list_mk_comb (ctor,List.take (args,5) @ [slot (List.nth (args,2))])
    else tl end
  fun one entry = let val (_,src) = pairSyntax.dest_pair entry in
    pairSyntax.mk_pair (src,listSyntax.mk_list (map (decl src) (lookup old src),``:toplevel``)) end
  in listSyntax.mk_list (map one (#1 (listSyntax.dest_list identities)),``:num option # toplevel list``) end;
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
