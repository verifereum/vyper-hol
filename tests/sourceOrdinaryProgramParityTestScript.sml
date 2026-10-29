Theory sourceOrdinaryProgramParityTest
Ancestors
  sourceOrdinaryProgramWitnessTest
  sourceOrdinaryProgram sourceModuleDefs sourceSyntax vyperAST
  compileVyper exprLowering contractABI concretizeMemLocDefs codegenReadyCompute
  byte option alist integer_word
Libs
  sourceBytecodeFixtureLib wordsLib finite_mapLib cv_transLib
fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["../lowering/defs/bytecode/folded-value-oracle",
  "../lowering/defs/bytecode/folded-value-parity-fixtures.txt",
  "../lowering/defs/bytecode/folded-value-witnesses.txt"];
val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY,integer_wordTheory.i2w_pos]);
val () = app (fn tm => computeLib.add_funs [cv_eval tm])
  [``function_selector "f" [Uint 256]``,``function_selector "f" []``];
val () = cv_auto_trans largest_pow_base_def;
val () = computeLib.add_funs [cv_eval ``largest_pow_base 3 256 F``];
fun owner _ = "sourceOrdinaryProgramWitnessTest";
val () = app (fn name => let
  val checked = DB.fetch (owner name) (name ^ "_ordinary_check")
  val (_,args) = strip_comb (lhs (concl checked))
  val (retained,art) = pairSyntax.dest_pair (hd (snd (strip_comb (rhs (concl checked)))))
  val modules = rhs (concl (EVAL ``retained_executable ^retained``))
  val tops = #2 (pairSyntax.dest_pair (hd (#1 (listSyntax.dest_list modules))))
  val expected = sourceBytecodeFixtureLib.expected name
  val backend = EVAL ``compile_vyper (K SOME) (o1_policy all_capabilities) ^tops``
  val comparison = EVAL (mk_eq (rhs (concl backend),optionSyntax.mk_some expected))
  val () = if aconv (rhs (concl comparison)) T then () else raise Fail ("ordinary bytecode parity: " ^ name)
  val exact = TRANS backend (EQT_ELIM comparison)
  val compiler = ``\(modules : (num option # toplevel list) list). case modules of [(NONE,tops)] =>
    compile_vyper (K SOME) (o1_policy all_capabilities) tops | _ => NONE``
  val application = List.foldl (fn (arg,f) => mk_icomb (f,arg))
    ``source_ordinary_compile`` (compiler::args)
  val composition = simpLib.SIMP_CONV (srw_ss())
    [source_ordinary_compile_def,checked,source_module_bind_def,retained_executable_def,exact] application
  val equations = MATCH_MP source_ordinary_compile_equations composition
  val () = sourceBytecodeFixtureLib.audit (owner name)
  val _ = save_thm (name ^ "_ordinary_python_parity",composition)
  val _ = save_thm (name ^ "_ordinary_compiler_equations",equations)
  in print ("ORDINARY_BYTECODE_MATCH " ^ name ^ " deploy+runtime, same checked artifact\n") end)
  sourceBytecodeFixtureLib.certified;
val () = sourceBytecodeFixtureLib.audit "sourceOrdinaryProgramParityTest";
