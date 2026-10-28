(* Checked frontend inputs and independent bytecode comparisons for memory stores. *)
structure memoryStoreWitnessLib = struct

open HolKernel Parse boolLib bossLib
open compileVyperTheory supportedProgramTheory

fun read path = let val input = TextIO.openIn path in
  TextIO.inputAll input before TextIO.closeIn input end

fun write path text = let val output = TextIO.openOut path in
  TextIO.output (output, text) before TextIO.closeOut output end

fun program root name = let
  val path = OS.Path.concat (root, name ^ ".json")
  val input = vyperCheckContractFrontendLib.prepare_check_input_legacy
    {in_deploy = false, address = ``0w : address``,
     annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path,
     storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout path}
  val _ = vyperCheckContractLib.check_contract input
  val _ = vyperCheckContractLib.check_contract
    {in_deploy = true, address = #address input,
     modules = #modules input, layouts = #layouts input}
in
  case #1 (listSyntax.dest_list (#modules input)) of
    [entry] => #2 (pairSyntax.dest_pair entry)
  | _ => raise Fail ("expected one source module in " ^ name)
end

fun compile_term tops =
  ``compile_vyper (K SOME) (o1_policy all_capabilities) ^tops``

fun report text =
  (TextIO.output (TextIO.stdErr, text ^ "\n"); TextIO.flushOut TextIO.stdErr)

(* Runs f on x and returns its result with the CPU seconds it took. *)
fun cpu_seconds f x = let
  val timer = Timer.startCPUTimer ()
  val result = f x
  val {usr, sys} = Timer.checkCPUTimer timer
in (result, Time.toReal (Time.+ (usr, sys))) end

(* Prints "WITNESS <name> frontend=<s> eval=<s>" (CPU seconds) so a build log
   gives each fixture's cost. *)
fun evaluate root name = let
  val (tops, frontend) = cpu_seconds (program root) name
  val term = compile_term tops
  val (evaluation, eval) = cpu_seconds EVAL term
  val _ = report ("WITNESS " ^ name ^ " frontend=" ^ Real.fmt (StringCvt.FIX (SOME 1)) frontend
                  ^ " eval=" ^ Real.fmt (StringCvt.FIX (SOME 1)) eval)
in {term = term, evaluation = evaluation} end

fun oracle root name = let
  val lines = String.tokens (fn ch => ch = #"\n")
    (read (OS.Path.concat (root, name ^ ".hex")))
  fun value key =
    case List.find (String.isPrefix (key ^ "=")) lines of
      SOME line => String.extract (line, size key + 1, NONE)
    | NONE => raise Fail ("missing " ^ key ^ " in " ^ name)
in
  pairSyntax.mk_pair
    (evalCompilerBytecodeLib.hex_bytes_tm (value "deploy"),
     evalCompilerBytecodeLib.hex_bytes_tm (value "runtime"))
end

fun hex_byte term = let
  val value = Arbnum.mod (wordsSyntax.dest_word_literal term, Arbnum.fromInt 256)
  val text = Int.fmt StringCvt.HEX (Arbnum.toInt value)
in if size text = 1 then "0" ^ text else text end

fun hex_list term = String.map Char.toLower
  (String.concat (map hex_byte (#1 (listSyntax.dest_list term))))

fun probe root output_root name = let
  fun status message = report ("WITNESS " ^ name ^ " " ^ message)
  val _ = status "FRONTEND"
  val tops = program root name
  val _ = status "ACCEPT/ACCEPT"
  val sp = rhs (concl (EVAL ``supported_program ^tops``))
  val _ = status ("SP=" ^ term_to_string sp)
  val _ = status "COMPILE"
  val result = rhs (concl (EVAL (compile_term tops)))
  val _ = status ("EVALUATED head=" ^ term_to_string (#1 (strip_comb result)))
  val _ = write (OS.Path.concat (output_root, name ^ ".term"))
    (term_to_string result)
in
  if optionSyntax.is_none result then status "NONE"
  else if not (optionSyntax.is_some result) then
    (write (OS.Path.concat (output_root, name ^ ".residual"))
       (term_to_string result);
     status "RESIDUAL")
  else let
    val (deploy, runtime) = pairSyntax.dest_pair (optionSyntax.dest_some result)
    val bytes = "deploy=" ^ hex_list deploy ^ "\nruntime=" ^ hex_list runtime ^ "\n"
    val _ = write (OS.Path.concat (output_root, name ^ ".hex")) bytes
    val expected = read (OS.Path.concat (root, name ^ ".hex"))
  in status (if bytes = expected then "MATCH" else "PARITY_DEFECT") end
end

end
