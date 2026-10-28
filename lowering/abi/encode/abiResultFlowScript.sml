(* TOP-LEVEL: every recursive encoder returns an operand preceding its final
   SSA frontier. This covers arbitrary nested children and loop bodies.
   Helpers discard irrelevant compiler prefixes when checking final results. *)
Theory abiResultFlow
Ancestors
  abiFieldOperands abiChildCode abiChildStructure abiStaticChildCode
  abiEncodeVarFlow abiStaticLoopCode abiEncoder emitHelperProps
  compileEnv context emitHelper list pair arithmetic

Definition compiler_operand_result_def:
  compiler_operand_result (action:compile_state -> operand # compile_state) <=>
    !cs. abi_operand_before (SND (action cs)).cs_next_var (FST (action cs))
End

Theorem compiler_operand_result_bind:
  !action cont.
    (!value. compiler_operand_result (cont value)) ==>
    compiler_operand_result (comp_bind action cont)
Proof
  rpt gen_tac >> simp_tac bool_ss [compiler_operand_result_def] >>
  DISCH_TAC >> qx_gen_tac `cs` >> Cases_on `action cs` >>
  rename1 `action cs = (value,mid)` >> simp[comp_bind_def] >>
  first_x_assum (qspecl_then [`value`, `mid`] ACCEPT_TAC)
QED

Theorem compiler_operand_result_ignore_bind:
  !action next.
    compiler_operand_result next ==>
    compiler_operand_result (comp_ignore_bind action next)
Proof
  rpt gen_tac >> DISCH_TAC >> rewrite_tac[comp_ignore_bind_def] >>
  irule compiler_operand_result_bind >> simp[]
QED

Theorem compiler_operand_result_literal:
  !value. compiler_operand_result (comp_return (Lit value))
Proof
  simp[compiler_operand_result_def, comp_return_def, abi_operand_before_def]
QED

Theorem emit_op_result_before:
  !opc operands cs ret cs'.
    emit_op opc operands cs = (ret,cs') ==>
    abi_operand_before cs'.cs_next_var ret
Proof
  rpt gen_tac >> DISCH_TAC >> drule emitted_insts_emit_op >> strip_tac >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `cs'.cs_next_var`] abi_operand_before_reserved) >>
  impl_tac >- simp[] >> simp[compiler_var_name_def]
QED

Theorem compiler_operand_result_emit_op:
  !opc operands. compiler_operand_result (emit_op opc operands)
Proof
  rpt gen_tac >> simp_tac bool_ss [compiler_operand_result_def] >>
  qx_gen_tac `cs` >> Cases_on `emit_op opc operands cs` >>
  rename1 `emit_op opc operands cs = (ret,cs')` >> simp[] >>
  drule emit_op_result_before >> simp[]
QED

Theorem compiler_operand_result_compile:
  !action cs ret cs'.
    compiler_operand_result action /\ action cs = (ret,cs') ==>
    abi_operand_before cs'.cs_next_var ret
Proof
  simp_tac bool_ss [compiler_operand_result_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `cs` mp_tac) >> simp[]
QED

fun encoder_result_tac () =
  rpt (FIRST [MATCH_ACCEPT_TAC compiler_operand_result_literal,
    MATCH_ACCEPT_TAC compiler_operand_result_emit_op,
    first_assum MATCH_ACCEPT_TAC,
    ho_match_mp_tac compiler_operand_result_bind >> gen_tac,
    irule compiler_operand_result_ignore_bind,
    IF_CASES_TAC]);

Theorem compiler_operand_result_abi_word:
  !dst src. compiler_operand_result (compile_abi_encode_static dst src)
Proof
  rpt gen_tac >> rewrite_tac[compile_abi_encode_static_def] >> encoder_result_tac ()
QED

Theorem compiler_operand_result_abi_encode:
  !dst src info. compiler_operand_result (compile_abi_encode_to_buf dst src info)
Proof
  rpt gen_tac >> Cases_on `info`
  >- simp[Once compile_abi_encode_child_def, compiler_operand_result_abi_word]
  >- (simp_tac bool_ss [Once compile_abi_encode_child_def, LET_THM] >> encoder_result_tac ())
  >- (simp_tac bool_ss [Once compile_abi_encode_child_def] >> encoder_result_tac ())
  >- (simp_tac bool_ss [Once compile_abi_encode_child_def, LET_THM] >> encoder_result_tac ()) >>
  rename1 `compiler_operand_result (compile_abi_encode_to_buf dst src (AbiComplex entries))` >>
  Cases_on `entries` >> simp_tac bool_ss [Once compile_abi_encode_child_def, LET_THM] >>
  encoder_result_tac ()
QED

Theorem compile_abi_encode_result_before:
  !dst src info cs ret cs'.
    compile_abi_encode_to_buf dst src info cs = (ret,cs') ==>
    abi_operand_before cs'.cs_next_var ret
Proof
  rpt gen_tac >> DISCH_TAC >> irule compiler_operand_result_compile >>
  qexistsl_tac [`compile_abi_encode_to_buf dst src info`, `cs`] >>
  simp[compiler_operand_result_abi_encode]
QED

Theorem compile_abi_child_result_before:
  !dst src info is_dyn head_offset dyn_ptr cs ret cs'.
    compile_abi_encode_child dst src info is_dyn head_offset dyn_ptr cs = (ret,cs') ==>
    abi_operand_before cs'.cs_next_var ret
Proof
  rpt gen_tac >> Cases_on `is_dyn`
  >- (simp_tac bool_ss [compile_abi_child_dynamic_cuts] >>
      disch_then (qx_choose_then `mid` strip_assume_tac) >>
      drule compile_abi_encode_result_before >> DISCH_TAC >>
      irule abi_operand_before_mono >> qexists_tac `mid.cs_next_var` >>
      simp[abi_child_suffix_cut_def]) >>
  simp_tac bool_ss [compile_abi_child_static_cuts] >>
  DISCH_TAC >> drule compile_abi_encode_result_before >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive ABI result operand flow: " ^ name)
  end) (DB.thms "abiResultFlow")
