(* The complete actual array encoder satisfies the recursive containing-function contract. *)
Theory abiEncoderCorrectArray
Ancestors
  abiEncoderArrayRun abiEncoderCorrect abiEncoderInputLayout abiEncoderChildInputs
  abiEncoderAdmissible abiDecoderEffect abiDecoderContract abiDecoderLoop fragExec compileEnv
  valueEncoding contractABI venomState words list

Theorem abi_encoder_correct_array:
  (if active then abi_encoder_correct ei else abi_encoder_static_leaf ei) ==>
  abi_encoder_correct (AbiDynArray ei asz msz active)
Proof
  strip_tac >> simp_tac bool_ss [abi_encoder_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_pre _ _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_pre_def]) >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `ct` (qx_choose_then `values` (MAP_EVERY assume_tac o CONJUNCTS)) o
      REWRITE_RULE [abi_encoder_array_input_iff]) >>
  qpat_x_assum `at = Array NONE ct` SUBST_ALL_TAC >>
  qpat_x_assum `av = ListV values` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`final` |-> `end_st`, `ty` |-> `ct:abi_type`,
    `avs` |-> `values:abi_value list`,
    `output_size` |-> `LENGTH (enc (Array NONE ct) (ListV values))`] abi_encoder_array_run) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_encoder_buffer_pre_exact] >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_CORRECT_ARRAY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array correctness not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderCorrectArray");
