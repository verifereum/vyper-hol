structure vyperTestRunnerLib :> vyperTestRunnerLib = struct

open HolKernel boolLib listSyntax vyperTestRunnerTheory cv_transLib
local open Timeout in end

val time_limit = Time.fromSeconds 120

val run_test_tm = prim_mk_const{Thy="vyperTestRunner",Name="run_test"}
val trace_ty = mk_thy_type{Thy="vyperTestRunner",Tyop="trace",Args=[]}
val traces_ty = mk_list_type trace_ty

val traces_prefix = "traces_"
val name_prefix = "name_"
val result_prefix = "result_"

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

fun run_test_on_traces traces_const = let
  val {Thy, Name=traces_name, ...} = dest_thy_const traces_const
  val () = if String.isPrefix traces_prefix traces_name then ()
           else raise Fail ("Unexpected trace name: " ^ traces_name)
  val suffix = String.extract(traces_name, String.size traces_prefix, NONE)
  val result_name = String.concat [result_prefix, suffix]
  val rtm = mk_comb(run_test_tm, traces_const)
  val rth = Timeout.apply time_limit cv_eval rtm
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

end
