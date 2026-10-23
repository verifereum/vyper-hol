(* Checked boundary audit, not a constructor simulation. *)
Theory immutableConstructorAudit
Ancestors
  immutableRelation exprLowering stmtLowering moduleLowering

Theorem immutable_audit_word_store:
  (istore 0 42w (s with vs_memory := [])).vs_memory =
    immutable_word_bytes 42w
Proof
  EVAL_TAC
QED

Theorem immutable_audit_two_word_copy:
  (mcopy 96 0 64
    (s with vs_memory := REPLICATE 32 1w ++ REPLICATE 32 2w)).vs_memory =
  REPLICATE 32 1w ++ REPLICATE 32 2w ++ REPLICATE 32 0w ++
  REPLICATE 32 1w ++ REPLICATE 32 2w
Proof
  EVAL_TAC
QED

(* Neither bump allocation nor the zero base creates actual memory capacity. *)
Theorem immutable_audit_alloca_memory:
  (case exec_alloca (instruction id ALLOCA [Lit 96w] [out]) s 96w of
     OK s' => s'.vs_memory = s.vs_memory
   | _ => F)
Proof
  simp[venomExecSemanticsTheory.exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >>
  simp[venomStateTheory.update_var_def] >>
  PairCases_on `x` >> simp[venomStateTheory.update_var_def]
QED

Theorem immutable_audit_zero_base_no_capacity:
  (update_var out 0w (s with vs_memory := [])).vs_memory = []
Proof
  simp[venomStateTheory.update_var_def]
QED

(* A short String[40] requires 96 canonical bytes. Its actual literal writes
   only the length word and one padded data word. The next capacity word
   can still contain old data. This does not falsify decoded-value validity. *)
Theorem immutable_audit_short_string_padding:
  let mem = (mstore 0 1w
    (mstore 32 (word_of_bytes T (0w:bytes32)
       (97w :: REPLICATE 31 0w))
       (s with vs_memory := REPLICATE 96 1w))).vs_memory in
    val_in_memory (BaseTV (StringT 40)) (StringV "a") 0 mem /\
    LENGTH mem = 96 /\
    DROP 64 mem = REPLICATE 32 1w /\
    mem <> encode_immutable_value (BaseTV (StringT 40)) (StringV "a")
Proof
  EVAL_TAC >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_EVAL_CONV) >> EVAL_TAC
QED

(* The assignment path intentionally skips normalization for two bytestring
   types, even when the declared capacities differ. *)
Theorem immutable_audit_bytestring_assignment_path:
  compile_assign_value cenv dst LocCode src F src_loc
    (BaseT (StringT 40)) (BaseT (StringT 1)) NONE 96 =
  compile_imm_store_words cenv.ce_imm_alloca src dst 3 0
Proof
  simp[stmtLoweringTheory.compile_assign_value_def,
       compileEnvTheory.is_bytestring_type_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_return_def, FUN_EQ_THM]
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then
       print ("IMMUTABLE_AUDIT_KERNEL_CLOSED " ^ name ^ "\n")
     else raise Fail ("Unclosed immutable audit theorem: " ^ name)
  end) (DB.thms "immutableConstructorAudit");
