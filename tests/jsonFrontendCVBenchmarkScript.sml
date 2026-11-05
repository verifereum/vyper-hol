Theory jsonFrontendCVBenchmark
Ancestors
  jsonToVyperCV jsonToVyperExprCV jsonToVyperExpr vyperAST
Libs
  jsonASTLib jsonToVyperCVLib cv_transLib wordsLib intLib

(* These are committed compiler outputs already used by frontend regressions;
   neither Vyper, exported execution traces nor the native runner is required. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["fixtures/check_contract/simple.json",
   "fixtures/check_contract/scoped_locals/main.json",
   "fixtures/check_contract/nested_initializes/main.json"];

val fixtures =
  [("simple", "fixtures/check_contract/simple.json"),
   ("scoped_locals", "fixtures/check_contract/scoped_locals/main.json"),
   ("nested_initializes", "fixtures/check_contract/nested_initializes/main.json")];

(* Exactly the annotated-AST importer input used by vyperTestLib, including its
   deployment wrapper. File I/O, JSON decoding and term construction are outside
   both timers; the timed boundary is the test runner's AST translation call. *)
fun load_input (name, path) = let
  val json = JSONDecode.decodeFile JSONDecode.raw path
  val wrapped = JSON.OBJECT [("annotated_ast", json)]
  val ast = JSONDecode.decode jsonASTLib.wrapped_annotated_ast wrapped
  val tm = mk_comb
    (prim_mk_const {Thy = "jsonToVyper", Name = "translate_annotated_ast"}, ast)
  in (name, tm) end;
val inputs = List.map load_input fixtures;

fun timed label f x = let
  val real_timer = Timer.startRealTimer ()
  val cpu_timer = Timer.startCPUTimer ()
  val result = f x
  val {usr, sys} = Timer.checkCPUTimer cpu_timer
  val wall = Timer.checkRealTimer real_timer
  val () = print ("FRONTEND_CV " ^ label ^
    " cpu_s=" ^ Time.toString (Time.+ (usr, sys)) ^
    " wall_s=" ^ Time.toString wall ^ "\n")
  in result end;

fun check_result tm th =
  if null (hyp th) andalso is_eq (concl th) andalso
     aconv (lhs (concl th)) tm andalso
     optionSyntax.is_some (rhs (concl th))
  then () else raise Fail "frontend benchmark needs an unconditional SOME result";

fun parity tm reference actual = let
  val () = check_result tm reference
  val () = check_result tm actual
  val () = if aconv (rhs (concl reference)) (rhs (concl actual)) then ()
           else raise Fail "EVAL/cv_eval frontend RHS mismatch"
  in TRANS (SYM reference) actual end;

(* First use in this process, not a claim of OS-cold caches. Includes CV input
   encoding, code selection, result decoding and defined-input condition proofs.
   The two evaluators receive the very same closed HOL application term. *)
fun cold (name, tm) = let
  val reference = timed ("phase=cold case=" ^ name ^ " mode=EVAL") EVAL tm
  val actual = timed ("phase=cold case=" ^ name ^ " mode=cv_eval")
    jsonToVyperCVLib.eval tm
  val _ = save_thm (name ^ "_translation", actual)
  val _ = save_thm (name ^ "_rhs_parity", parity tm reference actual)
  val () = print ("FRONTEND_CV phase=cold case=" ^ name ^ " parity=PASS\n")
  in (tm, reference) end;
val references = List.map cold inputs;

(* Scale deployment/import workloads by repeating the real three-module suite,
   not by translating empty modules or timing already-computed theorems. Each
   item calls the conversion anew; parity checking is outside the timers. *)
fun warm scale = let
  val work = List.concat (List.tabulate (scale, fn _ => references))
  val terms = List.map #1 work
  val label = "phase=warm scale=" ^ Int.toString scale ^
    " translations=" ^ Int.toString (length terms)
  fun run mode conv = timed (label ^ " mode=" ^ mode) (List.map conv) terms
  val (evals, cvs) = if scale = 1 then
      (run "EVAL" EVAL, run "cv_eval" jsonToVyperCVLib.eval)
    else let val cvs = run "cv_eval" jsonToVyperCVLib.eval
         in (run "EVAL" EVAL, cvs) end
  val () = ListPair.appEq (fn ((tm, reference), (ev, cv)) =>
    (ignore (parity tm reference ev); ignore (parity tm reference cv)))
    (work, ListPair.zip (evals, cvs))
  val () = print ("FRONTEND_CV " ^ label ^ " parity=PASS\n")
  in () end;
val () = List.app warm [1, 4];

(* Regression for the defined-input boundary: no unconditional value is assigned
   to HD [] in the source frontend, and the evaluator must not assume it away. *)
Theorem interface_constructor_defined_input_boundary:
  ~interface_constructor_result_pre (BaseT AddressT) [] /\
  interface_constructor_result_pre (BaseT AddressT)
    [Literal (BaseT AddressT) (BytesL [])]
Proof
  simp[interface_constructor_result_pre_cases]
QED

val () =
  if (ignore (jsonToVyperCVLib.eval
       ``interface_constructor_result (BaseT AddressT) []``); false)
     handle HOL_ERR _ => true | Fail _ => true
  then () else raise Fail "frontend CV evaluator accepted undefined HD []";
