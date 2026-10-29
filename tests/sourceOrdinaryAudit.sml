(* Run from the repository root:
   holbuild --maxheap 12000 run tests/sourceOrdinaryAudit.sml
   Read-only audit; no new evaluator rules or theorem-producing shortcuts. *)
val _ = List.app load
  ["sourceLegacyCompatibilityTestTheory", "sourceOrdinaryProgramInventoryTestTheory",
   "vyperCheckContractFrontendLibTestTheory",
   "vyperCheckContractLibTestTheory", "vyperTypeBuiltinsTheory",
   "vyperTypeContractSoundnessTheory", "supportedExprFormPropsTheory",
   "vyperLoweringCorrectTheory", "vyperCheckContractFrontendLib"];
(* Fixture inventory checks run again even when every theory is a cache hit. *)
val audit_cwd = OS.FileSys.getDir ();
val _ = OS.FileSys.chDir "tests";
val _ = load "sourceBytecodeFixtureLib";
val _ = load "sourceOrdinaryFixtureLib";

open HolKernel Parse boolLib bossLib compileVyperTheory;
val audited_theories =
  ["sourceOrdinaryProgramWitnessTest", "sourceOrdinaryProgramParityTest",
   "sourceLegacyCompatibilityTest", "vyperCheckContractFrontendLibTest",
   "vyperCheckContractLibTest", "vyperTypeBuiltins",
   "vyperTypeContractSoundness", "supportedExprFormProps"];
val _ = app sourceBytecodeFixtureLib.audit audited_theories;
fun require message condition = if condition then () else raise Fail message;
fun fetch theory name suffix = DB.fetch theory (name ^ suffix);
fun inventory theory suffix names = require ("wrong certificate inventory: " ^ theory ^ suffix)
  (Lib.set_eq (map #1 (List.filter (String.isSuffix suffix o #1) (DB.thms theory)))
    (map (fn name => name ^ suffix) names));
val ordinary_groups = [("sourceOrdinaryProgramCoreTest",0,6),
  ("sourceOrdinaryProgramExprTest",6,6), ("sourceOrdinaryProgramModulesTest",12,6),
  ("sourceOrdinaryProgramPolicyTest",18,6), ("sourceOrdinaryProgramLargeTest",24,3)];
val ordinary_inventory = List.concat (map (fn (owner,start,count) => map
  (fn (name,_) => (owner,name))
  (List.take (List.drop (sourceOrdinaryFixtureLib.rows,start),count))) ordinary_groups);
val _ = require "expected 27 distinct ordinary inventory cases"
  (length ordinary_inventory = 27 andalso
   length (Lib.mk_set (map #2 ordinary_inventory)) = 27 andalso
   Lib.set_eq (map #2 ordinary_inventory) (map #1 sourceOrdinaryFixtureLib.rows));
val _ = app (fn (owner,name) => app (fn suffix =>
  sourceOrdinaryFixtureLib.audit (fetch owner name suffix))
  ["_ordinary_phase", "_ordinary_original", "_ordinary_check",
   "_ordinary_expected_ast", "_ordinary_legacy_artifact"]) ordinary_inventory;
val witnesses = List.filter (fn name => name <> "method_id_var") sourceBytecodeFixtureLib.names;
val _ = require "expected 36 ordinary witnesses" (length witnesses = 36);
val _ = app (fn suffix => inventory "sourceOrdinaryProgramWitnessTest" suffix witnesses)
  ["_ordinary_phase", "_ordinary_original", "_ordinary_check",
   "_ordinary_expected_ast", "_ordinary_expected_artifact"];
val _ = app (fn suffix => inventory "sourceLegacyCompatibilityTest" suffix sourceBytecodeFixtureLib.seven)
  ["_legacy_runtime_check", "_legacy_deploy_check"];
val _ = inventory "sourceLegacyCompatibilityTest" "_legacy_exact_backend"
  sourceBytecodeFixtureLib.legacy_accepted;
(* 21 fixture certificates: 14 checker outcomes, six positive backends and
   the input distinction. cv_auto_trans additionally exports its definition
   and kernel-derived translation theorem, neither a fixture acceptance. *)
val _ = require "expected 23 legacy exports (14+6+1 fixture certificates + 2 cv exports)"
  (length (DB.thms "sourceLegacyCompatibilityTest") = 23);
val _ = require "wrong explicit legacy outcome coverage"
  (Lib.set_eq sourceBytecodeFixtureLib.legacy_outcomes
    [("fold_add",true), ("pow_folded_exp",false), ("fold_cmp",true),
     ("enc_mid_const",true), ("fold_powmod",true), ("fold_addmod",true),
     ("fold_abs",true)]);
val _ = app (fn suffix => inventory "sourceOrdinaryProgramParityTest" suffix sourceBytecodeFixtureLib.certified)
  ["_exact_checked_backend", "_ordinary_python_parity", "_ordinary_compiler_equations"];

(* Reopen checker equations on fresh raw ASTs and compare with independent
   per-case expectations, including rejection. Only the six accepted fixtures
   require raw compilation to SOME bytes; no legacy pinned parity is claimed. *)
val _ = app (fn (name,expected_positive) => let
  val path = sourceBytecodeFixtureLib.base ^ "/folded-value-oracle/" ^ name ^ ".json"
  val input = vyperCheckContractFrontendLib.prepare_check_input_legacy
    {in_deploy = false, address = sourceBytecodeFixtureLib.address,
     annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path,
     storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout path}
  fun check suffix input = let
    val actual = fetch "sourceLegacyCompatibilityTest" name suffix
    in require ("wrong legacy expected outcome: " ^ name ^ suffix)
      (aconv (lhs (concl actual)) (vyperCheckContractLib.mk_check_contract input)
       andalso (if expected_positive then optionSyntax.is_some (rhs (concl actual))
         else optionSyntax.is_none (rhs (concl actual)))) end
  val _ = check "_legacy_runtime_check" input
  val _ = check "_legacy_deploy_check"
    {in_deploy = true, address = #address input,
     modules = #modules input, layouts = #layouts input}
  val _ = if not expected_positive then () else let
  val tops = case #1 (listSyntax.dest_list (#modules input)) of
      [entry] => #2 (pairSyntax.dest_pair entry)
    | _ => raise Fail ("expected one legacy module: " ^ name)
  val application = ``compile_vyper (K SOME) (o1_policy all_capabilities) ^tops``
  val actual = fetch "sourceLegacyCompatibilityTest" name "_legacy_exact_backend"
  val _ = require ("wrong legacy backend input: " ^ name)
    (aconv (lhs (concl actual)) application)
  val _ = sourceBytecodeFixtureLib.require_actual_byte_pair (rhs (concl actual))
  val _ = if name <> "fold_add" then () else let
    val ordinary = fetch "sourceOrdinaryProgramParityTest" name "_exact_checked_backend"
    val ordinary_tops = rand (lhs (concl ordinary))
    val different = DB.fetch "sourceLegacyCompatibilityTest" "fold_add_legacy_input_differs"
    val _ = require "fold_add legacy/ordinary input boundary lost" (not (aconv tops ordinary_tops))
    in require "wrong fold_add input-boundary statement"
      (aconv (concl different) (mk_neg (mk_eq (tops,ordinary_tops)))) end
  in () end
  in print ("LEGACY EXPECTED " ^ (if expected_positive then "ACCEPT + RAW SOME" else "REJECT") ^
    " STATEMENTS PASS: " ^ name ^ "\n") end)
  sourceBytecodeFixtureLib.legacy_outcomes;

(* Ordinary exact backends are tied to the same retained checked artifact. *)
val _ = app (fn name => let
  val checked = fetch "sourceOrdinaryProgramWitnessTest" name "_ordinary_check"
  val (retained,_) = pairSyntax.dest_pair (hd (snd (strip_comb (rhs (concl checked)))))
  val modules = rhs (concl (EVAL ``sourceSyntax$retained_executable ^retained``))
  val tops = #2 (pairSyntax.dest_pair (hd (#1 (listSyntax.dest_list modules))))
  val expected = sourceBytecodeFixtureLib.expected name
  val statement = ``compile_vyper (K SOME) (o1_policy all_capabilities) ^tops = SOME ^expected``
  val actual = fetch "sourceOrdinaryProgramParityTest" name "_exact_checked_backend"
  val _ = require ("wrong ordinary backend statement: " ^ name) (aconv (concl actual) statement)
  in print ("ORDINARY BACKEND STATEMENT PASS: " ^ name ^ "\n") end)
  sourceBytecodeFixtureLib.certified;
val _ = DB.fetch "vyperCheckContractLibTest" "check_contract_rejects_method_id_eval";
val _ = OS.FileSys.chDir audit_cwd;
val _ = print "AUDIT PASS: 27 ordinary inventory cases; 36 ordinary witnesses; seven legacy runtime/deploy outcomes (six accept, pow_folded_exp rejects); six raw compilation certificates; fold_add inputs differ; nine ordinary exact pipeline parities; closed non-oracle fixture/frontend/checker/type/supported proofs\n";
val _ = print "LEGACY STATUS: old exact byte parity not asserted because false; annotated-only original arithmetic may differ from ordinary normalization; no legacy semantic correctness claim\n";

(* Report existing admissions separately; never certify these as clean. *)
val _ = app (fn name => let
  val th = DB.fetch "vyperLoweringCorrect" name
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in print ("BASELINE LOWERING TAGS: " ^ name ^ " = " ^
    String.concatWith "," oracles ^ " axioms=" ^ Int.toString (length axioms) ^ "\n") end)
  ["lower_vyper_runtime_unit_correct", "lower_vyper_runtime_unit_source_unit_ok",
   "lower_vyper_runtime_unit_memory_ok"];
