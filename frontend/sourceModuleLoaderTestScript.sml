Theory sourceModuleLoaderTest
Ancestors
  sourceModuleElaborate sourceModuleEnv sourceModuleDefs sourceSyntax sourceConstAnnotation
  vyperAST vyperContext finite_map
Libs
  sourceModuleLoaderLib sourceModuleFrontendLib

fun holbuild_extra_deps (_ : string list) = ();
val () = holbuild_extra_deps ["../tests/fixtures/check_contract/source_syntax/c27_const_binop_fold.json",
  "../tests/fixtures/check_contract/source_loader/multimodule_storage.json"];
val syntax = JSONDecode.decodeFile JSONDecode.raw
  "../tests/fixtures/check_contract/source_syntax/c27_const_binop_fold.json";
fun capture program = JSON.OBJECT
  [("protocol",JSON.STRING "vyper-hol/source-loader-v1"),
   ("phase",JSON.STRING "annotate_python_ast-before-get_node"),
   ("vyper_pin",JSON.STRING "cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c"),
   ("keys",JSON.ARRAY [JSON.ARRAY [JSON.STRING "main"]]),
   ("nonreentrancy_by_default",JSON.ARRAY [JSON.BOOL false]),
   ("declaration_only",JSON.ARRAY [JSON.BOOL false]),
   ("annotated_ast",program),("provenance",JSON.NULL)];
val loaded = JSONDecode.decode sourceModuleLoaderLib.source_capture (capture syntax);
val expected = JSONDecode.decode sourceSyntaxLib.annotated_ast syntax;
val () = if aconv (#program loaded) expected andalso aconv (#keys loaded) ``[["main"]]`` then ()
  else raise Fail "source loader changed retained source/namespace";
val _ = save_thm ("source_loader_retained_syntax",REFL (#program loaded));
val () = if (JSONDecode.decode sourceModuleLoaderLib.source_capture syntax; false)
  handle JSONDecode.JSONError _ => true then ()
  else raise Fail "ordinary annotated JSON accepted as pre-erasure protocol";
fun poison (JSON.OBJECT fs) = JSON.OBJECT
      (("folded_value",JSON.NULL)::List.map (fn (k,v) => (k,poison v))
        (List.filter (fn (k,_) => k <> "folded_value") fs))
  | poison (JSON.ARRAY xs) = JSON.ARRAY (List.map poison xs)
  | poison v = v;
val poisoned = JSONDecode.decode sourceModuleLoaderLib.source_capture (capture (poison syntax));
val () = if aconv (#program loaded) (#program poisoned) then () else
  raise Fail "source loader consumed folded metadata";

(* Actual pinned pre-erasure capture of the ordinary multimodule-storage source.
   Both raw parser source_ids are 0: canonical loader keys, not those IDs, supply
   the distinct identities used by HOL. No compiler expressions enter this test. *)
val storage_source = sourceModuleLoaderLib.load_file
  "../tests/fixtures/check_contract/source_loader/multimodule_storage.json";
val () = if aconv (#nonreentrant_defaults storage_source) ``[F;F]`` andalso
  aconv (#declaration_only storage_source) ``[F;F]`` then ()
  else raise Fail "source loader fixture policies changed";
val storage_checked = sourceModuleFrontendLib.check_loaded
  {fuel=``40:num``,source=storage_source,
   trust=``<| smt_ids := [(["main"],NONE);(["lib"],SOME 1)]; smt_nominals := [];
     smt_type_defs := FEMPTY; smt_slots := [((SOME 1,"stored"),0)] |>``}
  {layouts=``[(0w:address,([((SOME 1,"stored"),0)]:storage_layout,[]:storage_layout))]``,
   address=``0w:address``};
val _ = save_thm ("source_loader_storage_phase",#equation (#elaboration storage_checked));
val _ = save_thm ("source_loader_storage_check",#composition storage_checked);
val _ = save_thm ("source_loader_storage_links",#linking (#elaboration storage_checked));
(* A true default policy is accepted, not discarded. In contrast, claiming
   declaration-only for a bodyful implementation does not fabricate a stub. *)
val nr_source : sourceModuleLoaderLib.loaded =
  {program= #program loaded,keys= #keys loaded,nonreentrant_defaults=``[T]``,
   declaration_only=``[F]``,provenance=JSON.NULL};
val nr_elaborated = sourceModuleFrontendLib.elaborate_loaded
  {fuel=``40:num``,source=nr_source,
   trust=``<| smt_ids := [(["main"],NONE)]; smt_nominals := [];
     smt_type_defs := FEMPTY; smt_slots := [] |>``};
val _ = save_thm ("source_loader_policy_supported",#equation nr_elaborated);
