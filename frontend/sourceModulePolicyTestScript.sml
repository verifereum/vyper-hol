Theory sourceModulePolicyTest
Ancestors
  sourceModuleContext sourceModuleSignature sourceModuleElaborate sourceModuleDecl sourceModuleLink sourceModuleEnv sourceModuleDefs
  sourceSyntax sourceTypeDefs sourceConstAST sourceConstAnnotation vyperAST vyperContext finite_map
  sourceMeaningCompile sourceModuleCompile
Libs
  sourceModuleLoaderLib sourceModuleFrontendLib vyperCheckContractFrontendLib

fun holbuild_extra_deps (_ : string list) = ();
val () = holbuild_extra_deps [
  "../tests/fixtures/check_contract/source_loader/imported_interface.json",
  "../tests/fixtures/check_contract/source_loader/interface_struct_return.json",
  "../tests/fixtures/check_contract/source_loader/imported_deploy.json",
  "../tests/fixtures/check_contract/source_loader/interface_override.json",
  "../tests/fixtures/check_contract/source_loader/nonreentrant.json"];
val layouts = ``[(0w:address,([]:storage_layout,[]:storage_layout))]``;
val main_trust = ``<| smt_ids := [(["main"],NONE)]; smt_nominals := [];
  smt_type_defs := FEMPTY; smt_slots := [] |>``;
fun captured_source name = sourceModuleLoaderLib.load_file
  ("../tests/fixtures/check_contract/source_loader/" ^ name ^ ".json");
fun check_with_layouts name trust layouts =
  vyperCheckContractFrontendLib.Source.check_loaded_contract_result
    {fuel=``50:num``,trust=trust,source=captured_source name,layouts=layouts,address=``0w:address``};
fun check name trust = check_with_layouts name trust layouts;
fun audit th = let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn s => s = "DISK_THM") oracles then () else
    raise Fail "source policy test has a non-kernel dependency" end;
fun save name checked = let val elab = #elaboration (checked:sourceModuleFrontendLib.checked)
  val () = List.app audit [#equation elab,#original elab,#linking elab,#composition checked]
  val _ = save_thm (name ^ "_phase",#equation elab)
  val _ = save_thm (name ^ "_original",#original elab)
  val _ = save_thm (name ^ "_link",#linking elab)
  val _ = save_thm (name ^ "_check",#composition checked)
  in () end;
fun exact name (checked:sourceModuleFrontendLib.checked) expected =
  if aconv (#modules (#elaboration checked)) expected then () else
    raise Fail ("source policy exact AST: " ^ name ^ "\nactual: " ^
      term_to_string (#modules (#elaboration checked)) ^ "\nexpected: " ^ term_to_string expected);

(* Explicit inherited transient layout: the pin assigns the lock slot 0.
   The source loader does not invent this layout or silently disable locking. *)
val lock_name = stringSyntax.fromMLstring "$.nonreentrant_key";
val nr = check_with_layouts "nonreentrant" main_trust
  ``[(0w,([],[((NONE,^lock_name),0)]))] :
    (address # (storage_layout # storage_layout)) list``;
val () = save "nonreentrant" nr;
val () = exact "nonreentrant" nr
  ``[(NONE,[FunctionDecl External Nonpayable T F "locked" [] [] NoneT [Pass];
    FunctionDecl External Nonpayable F F "unlocked" [] [] NoneT [Pass];
    FunctionDecl External Pure F F "pure_value" [] [] (BaseT (UintT 256))
      [Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))];
    FunctionDecl Internal Nonpayable F F "helper" [] [] NoneT [Pass];
    FunctionDecl Deploy Nonpayable F F "__init__" [] [] NoneT [Pass]])] :
      (num option # toplevel list) list``;

val interface_trust =
  ``<| smt_ids := [(["main"],NONE);(["oracle"],SOME 1)]; smt_nominals := [];
    smt_type_defs := FEMPTY; smt_slots := [] |>``;
val imported = check "imported_interface" interface_trust;
val () = save "imported_interface" imported;
val () = exact "imported_interface" imported
  ``[(NONE,[FunctionDecl External View F F "read"
    [("addr",BaseT AddressT);("x",BaseT (UintT 256))] [] (BaseT (UintT 256))
    [Return (SOME (Call (BaseT (UintT 256))
      (ExtCall T F ("read_value",[BaseT (UintT 256)],BaseT (UintT 256)) [])
      [Name (BaseT AddressT) "addr";Name (BaseT (UintT 256)) "x"] NONE))]]);
    (SOME 1,[])]``;

val interface_source = captured_source "imported_interface";
val erased_policy : sourceModuleLoaderLib.loaded =
  {program= #program interface_source,keys= #keys interface_source,
   nonreentrant_defaults=``[F;F]``,declaration_only=``[F;F]``,provenance=JSON.NULL};
val () = if (sourceModuleFrontendLib.elaborate_loaded
  {fuel=``50:num``,trust=interface_trust,source=erased_policy}; false)
  handle HOL_ERR _ => true then () else raise Fail "inferred interface policy from ellipsis";

val record_trust =
  ``<| smt_ids := [(["main"],NONE);(["manager"],SOME 1)];
    smt_nominals := [(["manager";"Record"],STI_Struct (SOME 1,"Record"))];
    smt_type_defs := FEMPTY |+ ((SOME 1,"Record"),StructArgs [("value",BaseT (UintT 256))]);
    smt_slots := [] |>``;
val record = check "interface_struct_return" record_trust;
val () = save "interface_struct_return" record;
val () = exact "interface_struct_return" record
  ``[(NONE,[FunctionDecl External View F F "read" [("addr",BaseT AddressT)] []
      (BaseT (UintT 256))
      [AnnAssign "record" (StructT (SOME 1,"Record"))
        (Call (StructT (SOME 1,"Record"))
          (ExtCall T F ("get_record",[],StructT (SOME 1,"Record")) [])
          [Name (BaseT AddressT) "addr"] NONE);
       Return (SOME (Attribute (BaseT (UintT 256))
         (Name (StructT (SOME 1,"Record")) "record") "value"))]]);
    (SOME 1,[StructDecl "Record" [("value",BaseT (UintT 256))]])]``;

(* A receiver's source type, not a compiler field hint or the caller's expected
   return type, determines legal struct projections. Missing fields reject. *)
fun missing_field (JSON.OBJECT fields) = JSON.OBJECT (List.map (fn (key,value) =>
      if key = "attr" andalso (case value of JSON.STRING "value" => true | _ => false) then
        (key,JSON.STRING "missing") else (key,missing_field value)) fields)
  | missing_field (JSON.ARRAY values) = JSON.ARRAY (List.map missing_field values)
  | missing_field value = value;
val bad_record = JSONDecode.decode sourceModuleLoaderLib.source_capture
  (missing_field (JSONDecode.decodeFile JSONDecode.raw
    "../tests/fixtures/check_contract/source_loader/interface_struct_return.json"));
val () = if (vyperCheckContractFrontendLib.Source.check_loaded_contract_result
  {fuel=``50:num``,trust=record_trust,source=bad_record,layouts=layouts,address=``0w:address``}; false)
  handle HOL_ERR _ => true then () else raise Fail "invented nominal field";

val deploy = check "imported_deploy"
  ``<| smt_ids := [(["main"],NONE);(["lib"],SOME 1)]; smt_nominals := [];
    smt_type_defs := FEMPTY; smt_slots := [] |>``;
val () = save "imported_deploy" deploy;
val () = exact "imported_deploy" deploy
  ``[(NONE,[FunctionDecl Deploy Nonpayable F F "__init__" [] [] NoneT
      [Expr (Call NoneT (IntCall (SOME 1,"__init__")) [] NONE)]]);
    (SOME 1,[FunctionDecl Deploy Nonpayable F F "__init__" [] [] NoneT [Pass]])]``;

(* Imported interface identities reach override signature compatibility too.
   The .vyi omits redundant @external and the overriding body calls through an
   interface-annotated parameter. The abstract declaration emits no body. *)
val overridden = check "interface_override"
  ``<| smt_ids := [(["main"],NONE);(["oracle"],SOME 1);(["lib"],SOME 2)];
    smt_nominals := []; smt_type_defs := FEMPTY; smt_slots := [] |>``;
val () = save "interface_override" overridden;
val () = exact "interface_override" overridden
  ``[(NONE,[FunctionDecl Internal View F F "helper" [("target",BaseT AddressT)] []
      (BaseT (UintT 256)) [Return (SOME (Call (BaseT (UintT 256))
        (ExtCall T F ("read_value",[BaseT (UintT 256)],BaseT (UintT 256)) [])
        [Name (BaseT AddressT) "target";Literal (BaseT (UintT 256)) (IntL 1)] NONE))];
    FunctionDecl External View F F "read" [("addr",BaseT AddressT)] [] (BaseT (UintT 256))
      [Return (SOME (Call (BaseT (UintT 256)) (IntCall (NONE,"helper"))
        [Name (BaseT AddressT) "addr"] NONE))]]);
    (SOME 1,[]);(SOME 2,[])]``;

(* Policy terms are explicit inputs, not guessed from ellipses or metadata.
   Flipping declaration-only cannot turn implementation bodies into interfaces. *)
val actual_nr = captured_source "nonreentrant";
val lie : sourceModuleLoaderLib.loaded =
  {program= #program actual_nr,keys= #keys actual_nr,nonreentrant_defaults=``[F]``,
   declaration_only=``[T]``,provenance=JSON.NULL};
val () = if (sourceModuleFrontendLib.elaborate_loaded
  {fuel=``50:num``,trust=main_trust,source=lie}; false)
  handle HOL_ERR _ => true then () else raise Fail "fabricated interface bodies";
val incomplete : sourceModuleLoaderLib.loaded =
  {program= #program actual_nr,keys= #keys actual_nr,nonreentrant_defaults=``[]:bool list``,
   declaration_only=``[F]``,provenance=JSON.NULL};
val () = if (sourceModuleLoaderLib.policies incomplete; false)
  handle HOL_ERR _ => true then () else raise Fail "truncated policy registry";

Theorem missing_policy_registry_rejected:
  source_module_link_program trust [] [["main"]] program =
    SM_Error (SME_Declaration "policy-registry")
Proof
  simp[source_module_link_program_def]
QED

Theorem nonreentrant_policy_not_inferred:
  source_module_policy_signature 10 ctx [] (SourceModulePolicy T F)
    (SD_Function "f" [SX_Name "external";SX_Name "reentrant"] [] [] NONE [SS_Pass]) =
  source_module_policy_signature 10 ctx [] (SourceModulePolicy F F)
    (SD_Function "f" [SX_Name "external";SX_Name "reentrant"] [] [] NONE [SS_Pass])
Proof
  simp[source_module_policy_signature_def, source_module_declaration_only_def,
    source_module_nonreentrant_default_def]
QED
