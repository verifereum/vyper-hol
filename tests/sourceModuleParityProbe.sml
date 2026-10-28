(* Batch validation, not an interactive proof-state workflow.
   Each emitted HOL byte array comes from a closed kernel wrapper equation. *)
val () = OS.FileSys.chDir "tests";
val () = app load ["sourceModuleParityInputTheory", "sourceModuleParityLib",
  "supportedProgramTheory", "concretizeMemLocDefsTheory", "codegenReadyComputeTheory",
  "hurdUtilsContextTheory", "finite_mapLib", "wordsLib", "intLib", "cv_transLib", "Timeout"];
open HolKernel Parse boolLib bossLib;
val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos]);
val () = app (fn tm => computeLib.add_funs [cv_transLib.cv_eval tm])
  [``function_selector "f" [Uint 256]``, ``function_selector "f" [Int 256]``,
   ``function_selector "f" []``];
fun report text = (TextIO.output (TextIO.stdErr,text ^ "\n"); TextIO.flushOut TextIO.stdErr);
fun write_file path text = let val s = TextIO.openOut path in
  TextIO.output (s,text) before TextIO.closeOut s end;
fun hex_byte tm = let
  val n = Arbnum.toInt (Arbnum.mod (wordsSyntax.dest_word_literal tm,Arbnum.fromInt 256))
  val s = Int.fmt StringCvt.HEX n in if size s = 1 then "0" ^ s else s end;
fun hex_list tm = String.map Char.toLower
  (String.concat (map hex_byte (#1 (listSyntax.dest_list tm))));
val output = "../.agent-files/source-module-parity/hol";
val () = (OS.FileSys.mkDir output handle OS.SysErr _ => ());
fun write name suffix text = write_file (output ^ "/" ^ name ^ suffix) text;
fun check_tag th = let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
  if null (hyp th) andalso null axioms andalso
    List.all (fn s => s = "DISK_THM") oracles then ()
  else raise Fail "non-kernel wrapper certificate" end;
fun probe name = let
  val start = Time.now ()
  val () = report ("SOURCE_PROBE_START " ^ name)
  val input = sourceModuleParityLib.tops name
  val compiler = EVAL ``compile_vyper (K SOME) (o1_policy all_capabilities) ^input``
  val () = write name ".compiler" (term_to_string (concl compiler))
  val wrapper = sourceModuleParityLib.wrapper name compiler
  val () = check_tag compiler
  val () = check_tag wrapper
  val () = write name ".wrapper" (term_to_string (concl wrapper))
  val () = write name ".audit" "hyp=0 axioms=0 non_disk_oracles=0\n"
  val sp = rhs (concl (EVAL ``supported_program ^input``))
  val result = rhs (concl compiler)
  val status = if optionSyntax.is_none result then "BACKEND_NONE"
    else if not (optionSyntax.is_some result) then "BACKEND_RESIDUAL"
    else let
      val (deploy,runtime) = pairSyntax.dest_pair (optionSyntax.dest_some result)
      val hex = "deploy=" ^ hex_list deploy ^ "\nruntime=" ^ hex_list runtime ^ "\n"
      val () = write name ".hex" hex
      val expected = sourceModuleParityLib.read
        ("../.agent-files/source-module-parity/single/" ^ name ^ "/generated/" ^ name ^ ".hex")
      in if hex = expected then "MATCH" else "BYTE_MISMATCH" end
  val receipt = status ^ " supported=" ^ term_to_string sp ^ " seconds=" ^
    Time.toString (Time.- (Time.now (),start)) ^ "\n"
  val () = write name ".status" receipt
  in report ("SOURCE_PROBE " ^ name ^ " " ^ receipt) end;
fun bounded name = if name = "method_id_var" then
    (check_tag (DB.fetch "sourceModuleParityInput" "method_id_var_compile_reject");
     write name ".status" "PIN_INVALID_REJECT\n")
  else (Timeout.apply (Time.fromSeconds 120) probe name handle exn =>
    (write name ".status" ("VALIDATION_FAILURE " ^ General.exnMessage exn ^ "\n");
     report ("SOURCE_PROBE_FAILED " ^ name ^ " " ^ General.exnMessage exn)));
val () = app bounded sourceModuleParityLib.names;
val () = sourceModuleParityLib.audit "sourceModuleParityInput";
