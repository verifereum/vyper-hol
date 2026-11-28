(* Same JSON inputs for the standalone decoder and kernel-checked replay. *)
Theory vyperTestEmitSmoke
Ancestors
  vyperSmallStepCV
  vyperTestRunner cv
Libs
  vyperJsonReplayLib cv_transLib cv_repLib cv_miscLib cv_computeLib

fun holbuild_extra_deps (_ : string list) = ();
fun holbuild_extra_outputs (_ : string list) = ();
val fixtures = ["fixtures/run_test_json/basic.json",
                "fixtures/run_test_json/checkpoint_source_state.json",
                "fixtures/run_test_json/checkpoint_message_calls.json",
                "fixtures/run_test_json/checkpoint_code_provenance.json",
                "fixtures/run_test_json/checkpoint_raw_init_transient.json",
                "fixtures/run_test_json/checkpoint_raw_underfunded.json"];
val () = holbuild_extra_deps
  ["fixtures/run_test_json/basic.json",
   "fixtures/run_test_json/checkpoint_source_state.json",
   "fixtures/run_test_json/checkpoint_message_calls.json",
   "fixtures/run_test_json/checkpoint_code_provenance.json",
   "fixtures/run_test_json/checkpoint_raw_init_transient.json",
   "fixtures/run_test_json/checkpoint_raw_underfunded.json"];
val () = holbuild_extra_outputs [".emit/json-smoke.expected"];
val () = OS.FileSys.mkDir ".emit" handle OS.SysErr _ => ();

(* Exercise the replay consumer, including the complete-document boundary. *)
val () = let
  fun with_json_file contents consume = let
    val path = OS.FileSys.tmpName ()
    fun remove () = OS.FileSys.remove path
    fun run () = let
      val stream = TextIO.openOut path
      val () = TextIO.output (stream,contents)
        handle ex => (TextIO.closeOut stream; raise ex)
      val () = TextIO.closeOut stream
    in consume path end
    val result = run () handle ex => (remove (); raise ex)
    val () = remove ()
  in result end
  fun accepts contents = with_json_file contents (fn path =>
    case vyperJsonReplayLib.prepare_file path of
      [(_,traces)] =>
        if listSyntax.is_nil traces then ()
        else raise Fail "empty JSON trace array prepared nonempty traces"
    | _ => raise Fail "empty JSON trace array did not prepare one case")
  fun rejects contents = with_json_file contents (fn path => let
    val rejected =
      (vyperJsonReplayLib.prepare_file path; false) handle _ => true
  in
    if rejected then ()
    else raise Fail "replay accepted content after the JSON document"
  end)
in
  List.app accepts ["[]", "[] \t\r\n"];
  List.app rejects ["[] {}", "[] garbage", "[]\011", "[]\012"]
end;

val prepared = List.concat (List.map vyperJsonReplayLib.prepare_file fixtures);
val replays = List.concat (List.map vyperJsonReplayLib.replay_file fixtures);
val expected_status =
  [("test_basic_code",true), ("test_output_mismatch",false),
   ("test_expected_revert",true), ("test_unexpected_revert",false),
   ("test_null_code",true), ("test_raw_without_deployer_nonce",true),
   ("test_raw_deployer_nonce",true), ("test_raw_deployer_nonce_rewind",false),
   ("test_raw_deployer_nonce_address_mismatch",false),
   ("test_checkpoint_balance",true), ("test_checkpoint_balance_mismatch",false),
   ("test_internal_error_on_expected_revert",false),
   ("test_short_calldata",false), ("test_trace_abi_ignored",true),
   ("test_blueprint_call",false),
   (* a static call writing state raises "write in static context",
      which the runner counts as an expected failure *)
   ("test_static_call_rejects_state_write",true),
   ("test_static_call_write_reason",false),
   ("test_checkpoint_source_state",true),
   ("test_checkpoint_source_storage_mismatch",false),
   ("test_checkpoint_eoa_message",true), ("test_checkpoint_self_message",true),
   ("test_checkpoint_insufficient_message",true),
   ("test_checkpoint_raw_fallback",true),
   ("test_checkpoint_trace_code_ignored",true),
   ("test_checkpoint_trace_code_nonce_mismatch",false),
   ("test_checkpoint_raw_code_mismatch",false),
   (* Real py-evm/exporter capture: constructor TSTORE, a second constructor's
      nested STATICCALL reading it, failed-constructor rollback, raw calls
      before and after an explicit transient clear, and a changed-slot control. *)
   ("test_checkpoint_raw_init_transient",true),
   ("test_checkpoint_raw_init_transient_mismatch",false),
   ("test_checkpoint_raw_underfunded",true),
   ("test_checkpoint_raw_underfunded_gas_price_ignored",true),
   ("test_checkpoint_raw_underfunded_nonce_mismatch",false),
   ("test_checkpoint_raw_underfunded_unexpected_success",false)];
val expected_names = List.map #1 expected_status;
(* Failures must report the intended mismatch boundary. *)
val expected_errors =
  [("test_raw_deployer_nonce_rewind",
    "raw deployment deployer nonce below replay"),
   ("test_raw_deployer_nonce_address_mismatch",
    "raw deployment address mismatch"),
   ("test_checkpoint_balance_mismatch",
    "field=balance slot=none expected=8 actual=7"),
   ("test_checkpoint_source_storage_mismatch",
    "field=storage slot=0 expected=10 actual=9"),
   ("test_internal_error_on_expected_revert", "Name not in scope"),
   (* calldata_dispatch, not the trace ABI, rejects a call without its argument *)
   ("test_short_calldata", "calldata_dispatch: no entry"),
   (* a blueprint has no source to dispatch on: not an accepted revert *)
   ("test_blueprint_call", "call get sources"),
   (* the same static call expecting success: shows the expected failure
      above is "write in static context" and no other accepted revert *)
   ("test_static_call_write_reason", "write in static context"),
   ("test_checkpoint_trace_code_nonce_mismatch",
    "field=nonce slot=none expected=2 actual=1"),
   ("test_checkpoint_raw_code_mismatch", "field=code slot=none"),
   ("test_checkpoint_raw_init_transient_mismatch",
    "field=transient_storage slot=1 expected=43 actual=42"),
   ("test_checkpoint_raw_underfunded_nonce_mismatch",
    "field=nonce slot=none expected=1 actual=2"),
   ("test_checkpoint_raw_underfunded_unexpected_success",
    "raw deployment success mismatch")];
val () =
  if List.map #1 prepared = expected_names then ()
  else raise Fail "prepared fixture names differ from expected names or order";
val () =
  if List.map #1 replays = expected_names then ()
  else raise Fail "replayed fixture names differ from expected names or order";

fun write_cv stream tm =
  if cvSyntax.is_cv_num tm then
    (case total numSyntax.dest_numeral (cvSyntax.dest_cv_num tm) of
       SOME n => TextIO.output (stream,"N " ^ Arbnum.toString n)
     | NONE => raise Fail ("non-concrete CV number: " ^ term_to_string tm))
  else if cvSyntax.is_cv_pair tm then
    let val (left,right) = cvSyntax.dest_cv_pair tm in
      TextIO.output (stream,"P "); write_cv stream left;
      TextIO.output (stream," "); write_cv stream right
    end
  else raise Fail ("non-concrete CV value: " ^ term_to_string tm);
fun concrete tm = rhs (concl (cv_compute (cv_eqs_for tm) tm));
val expected = TextIO.openOut ".emit/json-smoke.expected";
fun emit_case (name,theorem) = let
  val result = rhs (concl theorem)
  val success = sumSyntax.is_inl result
  val wanted = case List.find (fn (key,_) => key=name) expected_status of
      SOME (_,value) => value | NONE => raise Fail ("unexpected fixture case: " ^ name)
  val () = if success=wanted then ()
    else raise Fail (name ^ ": unexpected HOL result: " ^ term_to_string result)
  val () = case List.find (fn (key,_) => key=name) expected_errors of
      NONE => ()
    | SOME (_,error) =>
        if String.isSubstring error (term_to_string result) then ()
        else raise Fail (name ^ ": expected error " ^ error ^ ", got " ^
                         term_to_string result)
  val traces = case List.find (fn (key,_) => key=name) prepared of
      SOME (_,value) => value | NONE => raise Fail ("missing prepared case: " ^ name)
  val input = vyperJsonReplayLib.encode_traces traces
  val result_cv = concrete (cv_rep_cv_tm (concl (cv_rep_for [] result)))
  val _ = save_thm (name,theorem)
  val () = TextIO.output (expected,name ^ "\t" ^ Bool.toString success ^ "\t")
  val () = write_cv expected input
  val () = TextIO.output (expected,"\t")
  val () = write_cv expected result_cv
  val () = TextIO.output (expected,"\n")
  val () = print ("KERNEL_REPLAY " ^ name ^ " " ^ term_to_string result ^ "\n")
in () end;
val () = List.app emit_case replays;
val () = TextIO.closeOut expected;
