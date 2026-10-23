Theory foldedValueParity
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  byte option alist integer_word
Libs
  vyperCheckContractFrontendLib jsonASTLib finite_mapLib wordsLib
  evalCompilerBytecodeLib memoryStoreWitnessLib

(* Independent pinned-Python outputs are data. Each theorem below is obtained
   by checked evaluation of the compiler on the actual exported frontend AST. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../folded-value-oracle", "../folded-value-parity-fixtures.txt"];
val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos]);

val fixture_root = "../folded-value-oracle";
fun parity name = let
  (* program checks the real AST/layout in both deployment modes. *)
  val tops = memoryStoreWitnessLib.program fixture_root name
  val evaluation = EVAL (memoryStoreWitnessLib.compile_term tops)
  val expected = optionSyntax.mk_some
    (memoryStoreWitnessLib.oracle fixture_root name)
  val comparison = EQT_ELIM (EVAL
    (boolSyntax.mk_eq (rhs (concl evaluation), expected)))
  val parity_theorem = TRANS evaluation comparison
  val () = if null (List.filter (fn oracle => oracle <> "DISK_THM")
    (#1 (Tag.dest_tag (Thm.tag parity_theorem)))) then ()
    else raise Fail ("unexpected theorem oracle: " ^ name)
in ignore (save_thm (name ^ "_python_parity", parity_theorem)) end;

val () = app parity
  ["fold_add", "pow_folded_exp", "fold_cmp", "enc_mid_const",
   "fold_powmod", "fold_addmod", "fold_abs"];
