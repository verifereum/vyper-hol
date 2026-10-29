(* Same JSON inputs for the standalone decoder and kernel-checked replay. *)
Theory vyperTestEmitSmoke
Ancestors
  vyperTestRunner cv
Libs
  vyperJsonReplayLib cv_transLib cv_repLib cv_miscLib cv_computeLib

fun holbuild_extra_deps (_ : string list) = ();
fun holbuild_extra_outputs (_ : string list) = ();
val () = holbuild_extra_deps ["fixtures/run_test_json/basic.json"];
val () = holbuild_extra_outputs [".emit/json-smoke.expected"];
val () = OS.FileSys.mkDir ".emit" handle OS.SysErr _ => ();

val fixture = "fixtures/run_test_json/basic.json";
val prepared = vyperJsonReplayLib.prepare_file fixture;
val replays = vyperJsonReplayLib.replay_file fixture;
val expected_status =
  [("test_basic_code",true), ("test_output_mismatch",false),
   ("test_expected_revert",true), ("test_unexpected_revert",false),
   ("test_null_code",true)];

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
