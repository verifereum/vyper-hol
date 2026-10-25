(* Run from the repository root: holbuild --maxheap 12000 run <this file>.
   Read-only audit: no evaluator rules or theorem-producing shortcuts. *)
val _ = List.app load
  ["foldedValueParityTheory", "foldedValueValidationPrepTheory",
   "vyperTypeBuiltinsTheory", "vyperTypeContractSoundnessTheory",
   "supportedExprFormPropsTheory", "vyperLoweringCorrectTheory",
   "memoryStoreWitnessLib"];

val audited_theories =
  ["foldedValueParityCompute", "foldedValueParityAbiCompute",
   "foldedValueParityAbiInput", "foldedValueParityAbiPipeline",
   "foldedValueParityAbiReady", "foldedValueParityAbi",
   "foldedValueParityAdd", "foldedValueParityPow",
   "foldedValueParityConstants", "foldedValueParity",
   "vyperCheckContractFrontendLibTest", "vyperCheckContractLibTest",
   "vyperTypeBuiltins", "vyperTypeContractSoundness",
   "supportedExprFormProps"];
fun check_closed (theory, (name, th)) =
  if null (Thm.hyp th) andalso
     null (List.filter (fn oracle => oracle <> "DISK_THM")
       (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("non-closed/oracle theorem: " ^ theory ^ "." ^ name);
val _ = app (fn theory => app (fn entry => check_closed (theory, entry))
  (DB.thms theory)) audited_theories;

val root = "lowering/defs/bytecode/folded-value-oracle";
val fixtures = ["fold_add", "pow_folded_exp", "fold_cmp", "enc_mid_const",
                "fold_powmod", "fold_addmod", "fold_abs"];
val _ = if length (DB.thms "foldedValueParity") = length fixtures then ()
        else raise Fail "expected exactly seven exported parity theorems";
val _ = app (fn name => let
  val actual = DB.fetch "foldedValueParity" (name ^ "_python_parity")
  val tops = memoryStoreWitnessLib.program root name
  val oracle = memoryStoreWitnessLib.oracle root name
  val expected = Parse.Term
    [QUOTE "compileVyper$compile_vyper (K SOME) ",
     QUOTE "(o1_policy all_capabilities) ", ANTIQUOTE tops,
     QUOTE " = SOME ", ANTIQUOTE oracle]
in
  if Term.aconv (Thm.concl actual) expected then
    print ("PARITY STATEMENT PASS: " ^ name ^ "\n")
  else raise Fail ("wrong parity statement: " ^ name)
end) fixtures;
val _ = DB.fetch "vyperCheckContractLibTest"
  "check_contract_rejects_method_id_eval";
val _ = print "AUDIT PASS: exact seven oracle equalities; closed, non-oracle fixture/frontend/checker/type/supported proofs\n";

(* Preserve the distinction between this task's checked proofs and existing
   project admissions. Report these, never silently certify them as clean. *)
val _ = app (fn name => let
  val th = DB.fetch "vyperLoweringCorrect" name
  val tags = #1 (Tag.dest_tag (Thm.tag th))
in print ("BASELINE LOWERING TAGS: " ^ name ^ " = " ^
          String.concatWith "," tags ^ "\n") end)
  ["lower_vyper_runtime_unit_correct", "lower_vyper_runtime_unit_source_unit_ok",
   "lower_vyper_runtime_unit_memory_ok"];
