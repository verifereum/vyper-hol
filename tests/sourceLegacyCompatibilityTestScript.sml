(* Compatibility boundary on freshly decoded annotated-only legacy input:
   six accept, while unnormalized pow_folded_exp rejects in both modes.
   Positive raw compilation is closed, not pinned parity or semantic correctness.
   Ordinary normalized inputs retain all nine exact byte checks. *)
Theory sourceLegacyCompatibilityTest
Ancestors
  sourceOrdinaryProgramParityTest compileVyper exprLowering contractABI
  concretizeMemLocDefs codegenReadyCompute byte option alist integer_word
Libs
  sourceBytecodeFixtureLib vyperCheckContractFrontendLib jsonASTLib
  wordsLib finite_mapLib cv_transLib

fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["../lowering/defs/bytecode/folded-value-sources",
  "../lowering/defs/bytecode/folded-value-oracle",
  "../lowering/defs/bytecode/folded-value-parity-fixtures.txt",
  "../lowering/defs/bytecode/folded-value-witnesses.txt"];
(* Needed only when legacy and ordinary executable ASTs differ. *)
val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY,integer_wordTheory.i2w_pos]);
val () = app (fn tm => computeLib.add_funs [cv_eval tm])
  [``function_selector "f" [Uint 256]``,``function_selector "f" []``];
val () = cv_auto_trans largest_pow_base_def;
val () = computeLib.add_funs [cv_eval ``largest_pow_base 3 256 F``];

val () = app (fn (name,expected_positive) => let
  val path = sourceBytecodeFixtureLib.base ^ "/folded-value-oracle/" ^ name ^ ".json"
  val input = vyperCheckContractFrontendLib.prepare_check_input_legacy
    {in_deploy = false, address = sourceBytecodeFixtureLib.address,
     annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path,
     storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout path}
  fun certify suffix input = let
    (* EVAL can leave determined ABI-size existentials such as
       ?n. 36 = n /\ 36 <= n. Simplify those logical residuals, not outcomes. *)
    val result = (EVAL THENC SIMP_CONV (srw_ss()) [])
      (vyperCheckContractLib.mk_check_contract input)
    val outcome = rhs (concl result)
    val matches = if expected_positive then optionSyntax.is_some outcome
      else optionSyntax.is_none outcome
    val () = if matches then () else
      raise Fail ("unexpected legacy checker outcome: " ^ name ^ suffix)
    in save_thm (name ^ suffix,result) end
  val _ = certify "_legacy_runtime_check" input
  val _ = certify "_legacy_deploy_check"
    {in_deploy = true, address = #address input,
     modules = #modules input, layouts = #layouts input}
  val () = if not expected_positive then
    print ("LEGACY_COMPATIBILITY " ^ name ^
      " runtime/deploy REJECT: exponent needs source normalization\n")
    else let
  val tops = case #1 (listSyntax.dest_list (#modules input)) of
      [entry] => #2 (pairSyntax.dest_pair entry)
    | _ => raise Fail ("legacy compatibility expected one module: " ^ name)
  val application = ``compile_vyper (K SOME) (o1_policy all_capabilities) ^tops``
  val ordinary = DB.fetch "sourceOrdinaryProgramParityTest"
    (name ^ "_exact_checked_backend")
  val reused = aconv (lhs (concl ordinary)) application
  val () = if name <> "fold_add" orelse not reused then ()
    else raise Fail "fold_add legacy input must retain original arithmetic"
  val _ = if name <> "fold_add" then () else let
    val ordinary_tops = rand (lhs (concl ordinary))
    val different = EVAL (mk_neg (mk_eq (tops,ordinary_tops)))
    val _ = save_thm ("fold_add_legacy_input_differs",EQT_ELIM different)
    in () end
  (* Reuse only a syntactically identical full compile application; otherwise
     compute the fresh legacy input without comparing it to oracle bytes. *)
  val exact = if reused then ordinary else EVAL application
  val () = sourceBytecodeFixtureLib.require_actual_byte_pair (rhs (concl exact))
  val _ = save_thm (name ^ "_legacy_exact_backend",exact)
  in print ("LEGACY_COMPATIBILITY " ^ name ^
    " runtime/deploy ACCEPT, closed raw backend SOME bytes, backend=" ^
    (if reused then "identical ordinary AST\n" else "direct legacy EVAL\n")) end
  in () end) sourceBytecodeFixtureLib.legacy_outcomes;
val () = sourceBytecodeFixtureLib.audit "sourceLegacyCompatibilityTest";
