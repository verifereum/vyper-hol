structure vyperTestRunnerLib :> vyperTestRunnerLib = struct

open HolKernel boolLib listSyntax vyperTestRunnerTheory cv_transLib
local open Timeout in end

(* A hung test still fails its theory; the old per-test limit was 120 s. *)
fun time_limit tests = Time.fromSeconds (Int.toLarge (120 + 10 * tests))

val run_test_tm = prim_mk_const{Thy="vyperTestRunner",Name="run_test"}
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

val evaluations_run = ref 0

(* Checkpoint-free CI has not compacted the loaded trace theories. Share
   their repeated terms once, then collect temporary CV interpreters between
   evaluations rather than relying on host-sized automatic heap limits. *)
fun prepare_eval batch = let
  val () = if !evaluations_run = 0
           then PolyML.shareCommonData PolyML.rootFunction else ()
  val () = if batch orelse !evaluations_run mod 8 = 0
           then PolyML.fullGC () else ()
in
  evaluations_run := !evaluations_run + 1
end

(* Keep the theorem-saving API for callers that need an individual result.
   Generated suites use run_tests_on_traces to amortize CV preparation. *)
fun run_test_on_traces traces_const = let
  val () = prepare_eval false
  val {Thy, Name=traces_name, ...} = dest_thy_const traces_const
  val () = if String.isPrefix traces_prefix traces_name then ()
           else raise Fail ("Unexpected trace name: " ^ traces_name)
  val suffix = String.extract(traces_name, String.size traces_prefix, NONE)
  val result_name = String.concat ["result_", suffix]
  val rtm = mk_comb(run_test_tm, traces_const)
  val rth = Timeout.apply (Time.fromSeconds 120) cv_eval rtm
            handle Timeout.TIMEOUT _ => raise Fail (
              String.concat ["Timeout in test ", result_name])
  val ttm = sumSyntax.mk_isl $ rtm
  val eth = (RAND_CONV (REWR_CONV rth) THENC cv_eval) ttm
  val tth = EQT_ELIM eth handle HOL_ERR _ =>
            raise Fail (String.concat [
              "Failure in test ", result_name, ": ",
              term_to_string $ rand $ rhs $ concl rth,
              " from test ",
              DB.fetch Thy (name_prefix ^ suffix ^ "_def")
              |> concl |> rhs |> stringSyntax.fromHOLstring])
  val tth = save_thm (result_name, tth)
in
  ()
end

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
  val () = prepare_eval true
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
