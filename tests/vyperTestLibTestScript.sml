Theory vyperTestLibTest
Ancestors vyperTestRunner
Libs vyperTestLib vyperTestRunnerLib cv_transLib

fun source code = JSON.OBJECT [("source_code", JSON.STRING code)];

fun expect label expected jsons =
  if unsupported_source_reason_for jsons = expected then ()
  else raise Fail ("source classification: " ^ label);

val _ = expect "calldata len" NONE [source "return len(msg.data)"];
val _ = expect "calldata slice" NONE [source "return slice(msg.data, 0, 4)"];
val _ = expect "calldata raw_call" NONE
  [source "raw_call(target, msg.data, max_outsize=32)"];
val _ = expect "gas retained" (SOME "unsupported source pattern: msg.gas")
  [source "raw_call(target, msg.data, gas=msg.gas)"];
val _ = expect "explicit gas retained" (SOME "unsupported source pattern: gas=")
  [source "raw_call(target, msg.data, gas=1000)"];
val _ = expect "negative missing source" (SOME "missing source_code") [];
val _ = expect "blank source" (SOME "blank source_code") [source " \n"];

(* The runner must handle word-bearing traces without changing its saved
   proposition, and must still reject failures with the original test name. *)
Definition traces_runner_words_def:
  traces_runner_words =
    [Call <| sender := 1w; target := 2w; callData := [3w]; value := 0;
             timeStamp := 0; blockNumber := 0; blockHashes := [4w];
             blobHashes := []; blobBaseFee := 0; gasLimit := 0;
             gasPrice := 0; chainId := 0; static := F; expectedOutput := NONE |>]
End

val () = cv_trans traces_runner_words_def;
val () = run_test_on_traces ``traces_runner_words``;
val () =
  if aconv (concl (DB.fetch "-" "result_runner_words"))
           ``ISL (run_test traces_runner_words)`` then ()
  else raise Fail "runner changed the saved proposition";

Definition traces_runner_failure_def:
  traces_runner_failure =
    [Call <| sender := 1w; target := 2w; callData := [3w]; value := 0;
             timeStamp := 0; blockNumber := 0; blockHashes := [4w];
             blobHashes := []; blobBaseFee := 0; gasLimit := 0;
             gasPrice := 0; chainId := 0; static := F;
             expectedOutput := SOME [] |>]
End

Definition name_runner_failure_def:
  name_runner_failure = "runner negative regression"
End

val () = cv_trans traces_runner_failure_def;
val rejected =
  (run_test_on_traces ``traces_runner_failure``; false)
  handle Fail message =>
    String.isSubstring "Failure in test result_runner_failure:" message andalso
    String.isSubstring "runner negative regression" message;
val () = if rejected then () else raise Fail "runner accepted a failing trace";

(* Both APIs must coexist: batching retains word-bearing trace support and
   reports every failing entry, including failures after a successful entry. *)
val () = run_tests_on_traces [];
val () = run_tests_on_traces [``traces_runner_words``];
val () = run_tests_on_traces
  [``traces_runner_words``, ``traces_runner_words``];
val batch_rejected =
  (run_tests_on_traces
     [``traces_runner_words``, ``traces_runner_failure``,
      ``traces_runner_words``, ``traces_runner_failure``]; false)
  handle Fail message =>
    String.isSubstring "2 of 4 tests failed in " message andalso
    String.isSubstring "runner negative regression" message;
val () = if batch_rejected then ()
         else raise Fail "batch runner lost failures or their test names";
