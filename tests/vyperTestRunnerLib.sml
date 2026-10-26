structure vyperTestRunnerLib :> vyperTestRunnerLib = struct

open HolKernel boolLib listSyntax vyperTestRunnerTheory cv_transLib
local open Timeout in end

(* A hung test still fails its theory; the old per-test limit was 120 s. *)
fun time_limit tests = Time.fromSeconds (Int.toLarge (120 + 10 * tests))

val run_tests_tm = prim_mk_const{Thy="vyperTestRunner",Name="run_tests"}
val trace_ty = mk_thy_type{Thy="vyperTestRunner",Tyop="trace",Args=[]}
val traces_ty = mk_list_type trace_ty

val traces_prefix = "traces_"
val name_prefix = "name_"

fun is_trace_constant tm =
  let
    val {Name=name, ...} = dest_thy_const tm
  in
    String.isPrefix traces_prefix name andalso type_of tm = traces_ty
  end

val all_traces = List.filter is_trace_constant o constants

fun trace_index tm = let
  val {Name=name, ...} = dest_thy_const tm
  val digits = Substring.taker Char.isDigit (Substring.full name)
in
  case Int.fromString (Substring.string digits) of
    SOME i => i
  | NONE => raise Fail ("Trace name has no index: " ^ name)
end

(* Chunk k of n holds the traces whose index is k mod n, so the n chunks
   together replay every trace exactly once. *)
fun trace_chunk (k, n) traces =
  if 0 <= k andalso k < n then
    List.filter (fn tm => trace_index tm mod n = k) traces
  else raise Fail (String.concat [
    "trace_chunk: chunk ", Int.toString k, " of ", Int.toString n,
    " is not in 0 to chunks - 1"])

fun test_name traces_const = let
  val {Thy, Name, ...} = dest_thy_const traces_const
  val suffix = String.extract(Name, String.size traces_prefix, NONE)
in
  DB.fetch Thy (name_prefix ^ suffix ^ "_def")
  |> concl |> rhs |> stringSyntax.fromHOLstring
end

fun report_failure (traces_const, result) = TextIO.print (String.concat [
  "Failure in test ", test_name traces_const, " (",
  #Name (dest_thy_const traces_const), "): ",
  term_to_string (rand result), "\n"])

(* All the tests run in one cv_eval, so the interpreter's code equations are
   prepared once rather than once per test. *)
fun eval_tests [] = []
  | eval_tests traces = let
  val n = List.length traces
  val rtm = mk_comb(run_tests_tm, mk_list(traces, traces_ty))
  val rth = Timeout.apply (time_limit n) cv_eval rtm
            handle Timeout.TIMEOUT _ => raise Fail (String.concat [
              "Timeout running ", Int.toString n, " tests in ",
              current_theory ()])
in
  #1 (dest_list (rhs (concl rth)))
end

fun run_tests_on_traces traces = let
  val n = List.length traces
  val results = eval_tests traces
  val failures =
    List.filter (not o sumSyntax.is_inl o #2) (ListPair.zipEq (traces, results))
  val () = List.app report_failure failures
  val () = TextIO.print (String.concat [
    "[vyper-tests] theory=", current_theory (), " tests=", Int.toString n,
    " failed=", Int.toString (List.length failures), "\n"])
in
  if List.null failures then ()
  else raise Fail (String.concat [
    Int.toString (List.length failures), " of ", Int.toString n,
    " tests failed in ", current_theory (), ": ",
    String.concatWith ", " (List.map (test_name o #1) failures)])
end

end
