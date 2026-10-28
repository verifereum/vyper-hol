(* Seven retained and two Boolean source-driven wrapper parity certificates. Backend equations are
   computed on the exact source-checked AST, with no legacy frontend dependency.
   Independently pinned byte arrays are data, never evaluation rewrite rules. *)
Theory sourceModuleParity
Ancestors
  sourceModuleParityInput sourceModuleFrontendLibTest sourceModuleCompile
  sourceModuleElaborate sourceModuleDefs sourceSyntax vyperAST finite_map
  compileVyper exprLowering contractABI concretizeMemLocDefs codegenReadyCompute
  byte option alist integer_word
Libs sourceModuleParityLib wordsLib finite_mapLib cv_transLib

fun holbuild_extra_deps (_ : string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract/source_syntax",
  "../lowering/defs/bytecode/folded-value-oracle",
  "../lowering/defs/bytecode/folded-value-parity-fixtures.txt"];
val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos]);
val () = app (fn tm => computeLib.add_funs [cv_eval tm])
  [``function_selector "f" [Uint 256]``, ``function_selector "f" []``];
val () = cv_auto_trans largest_pow_base_def;
val () = computeLib.add_funs [cv_eval ``largest_pow_base 3 256 F``];

val () = app (fn name => let
  val tops = sourceModuleParityLib.tops name
  val expected = sourceModuleParityLib.expected name
  val () = print ("SOURCE_PARITY_COMPUTE " ^ name ^ "\n")
  val backend = EVAL ``compile_vyper (K SOME) (o1_policy all_capabilities) ^tops``
  val comparison = EVAL (mk_eq (rhs (concl backend),optionSyntax.mk_some expected))
  val () = if aconv (rhs (concl comparison)) T then ()
    else raise Fail ("source-checked backend differs from pin or is residual: " ^ name)
  val exact_backend = TRANS backend (EQT_ELIM comparison)
  val _ = save_thm (name ^ "_exact_checked_backend",exact_backend)
  val equation = sourceModuleParityLib.wrapper name exact_backend
  val () = if same_const (#1 (strip_comb (rhs (concl equation)))) ``SM_Ok`` then ()
    else raise Fail ("source wrapper did not compile: " ^ name)
  val _ = save_thm (name ^ "_python_parity",equation)
  val _ = save_thm (name ^ "_composition",
    MATCH_MP sourceModuleCompileTheory.source_module_compile_equations equation)
  in print ("SOURCE_PARITY_MATCH " ^ name ^ " deploy+runtime\n") end)
  sourceModuleParityLib.certified;
val () = sourceModuleParityLib.audit "sourceModuleParityInput";
val () = sourceModuleParityLib.audit "sourceModuleParity";
