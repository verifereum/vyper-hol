val () = load "jsonImportTerm";
val () = load "jsonASTLib";
val () = load "JsonTraceDecodeFn";
structure vyperJsonReplayLib :> vyperJsonReplayLib = struct

open HolKernel boolLib bossLib cv_transLib cv_repLib cv_miscLib cv_computeLib
     wordsLib intLib
     vyperTestRunnerTheory jsonToVyperTheory

structure Decode = JsonTraceDecodeFn (
  structure B = JsonImportHol
  structure AST = jsonASTLib
  fun translate_annotated_ast jsonast =
    rhs (concl (EVAL (mk_comb (
      prim_mk_const {Thy="jsonToVyper", Name="translate_annotated_ast"},
      jsonast))))
)

val run_test_tm = prim_mk_const {Thy="vyperTestRunner", Name="run_test"}
val trace_ty = mk_thy_type {Thy="vyperTestRunner", Tyop="trace", Args=[]}

fun prepare_file path = let
  val cases = Decode.decode_cases (JSONDecode.decodeFile JSONDecode.raw path)
  fun prepare (name,traces) =
    (name, rhs (concl (EVAL (listSyntax.mk_list (traces,trace_ty)))))
in List.map prepare cases end

(* Normalize concrete data (not execution) before CV's first-order evaluator;
   word encodings can otherwise retain dimindex type witnesses. *)
fun trace_representation traces = let
  fun word_representation word = let
    val from = cv_typeLib.from_term_for (type_of word)
    val trivial = ISPECL [from,word] cv_repTheory.cv_rep_trivial
  in (word,CONV_RULE (cv_rep_cv_tm_conv EVAL) trivial) end
  val words = find_terms wordsSyntax.is_word_literal traces
  val representation = cv_rep_for (map word_representation words) traces
  val encoded = cv_rep_cv_tm (concl representation)
in CONV_RULE
     (cv_rep_cv_tm_conv (cv_compute (cv_eqs_for encoded))) representation
end

fun encode_traces traces =
  cv_rep_cv_tm (concl (trace_representation traces))

fun replay (name,traces) = let
  val source = mk_comb (run_test_tm,traces)
  val input = trace_representation traces
  val representation = cv_rep_for [(traces,input)] source
  val conversion = MATCH_MP
    (MATCH_MP cv_repTheory.cv_rep_eval representation)
    (cv_typeLib.from_to_thm_for (type_of source))
  val equation = MP conversion TRUTH
  val invocation = rand (rhs (concl equation))
  val computed = CONV_RULE
    (RAND_CONV (RAND_CONV (cv_compute (cv_eqs_for invocation)))) equation
  val theorem = CONV_RULE (RAND_CONV EVAL) computed
  val (left,_) = dest_eq (concl theorem)
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
  val () =
    if aconv left source andalso null (Thm.hyp theorem) andalso null axioms
       andalso List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail (name ^ ": replay is not an exact kernel-closed conversion")
in (name,theorem) end

fun replay_file path = List.map replay (prepare_file path)

end
