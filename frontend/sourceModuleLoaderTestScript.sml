Theory sourceModuleLoaderTest
Ancestors
  sourceModuleEnv sourceModuleDefs sourceSyntax sourceConstAnnotation
  vyperAST vyperContext finite_map
Libs
  sourceModuleLoaderLib

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

(* Pinned pre-erasure policies and canonical loader keys remain shared trust. *)
val storage_source = sourceModuleLoaderLib.load_file
  "../tests/fixtures/check_contract/source_loader/multimodule_storage.json";
val () = if aconv (#nonreentrant_defaults storage_source) ``[F;F]`` andalso
  aconv (#declaration_only storage_source) ``[F;F]`` then ()
  else raise Fail "source loader fixture policies changed";
val nr_source : sourceModuleLoaderLib.loaded =
  {program= #program loaded,keys= #keys loaded,nonreentrant_defaults=``[T]``,
   declaration_only=``[F]``,provenance=JSON.NULL};
val () = if aconv (sourceModuleLoaderLib.policies nr_source)
  ``[( ["main"],SourceModulePolicy T F)]`` then ()
  else raise Fail "source loader discarded default policy";
val incomplete : sourceModuleLoaderLib.loaded =
  {program= #program loaded,keys= #keys loaded,nonreentrant_defaults=``[]:bool list``,
   declaration_only=``[F]``,provenance=JSON.NULL};
val () = if (sourceModuleLoaderLib.policies incomplete; false)
  handle HOL_ERR _ => true then () else raise Fail "truncated policy registry";
