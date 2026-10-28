(* TOP-LEVEL: execute the actual bytestring ABI instruction program.
   Input operands avoid its eight outputs; existing output values may be
   overwritten on subsequent loop iterations. Aliasing is represented by the
   exact store-before-copy memory effect rather than silently excluded here. *)
Theory abiBytestringExec
Ancestors
  abiBytestringCode ssaOperandFrame exprLoweringProps emitHelperProps
  venomExecSemantics venomState venomInst list rich_list words
Libs wordsLib

Definition bytestring_round_word_def:
  bytestring_round_word (length_word:bytes32) =
    word_and 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
      (31w + length_word)
End

Definition bytestring_copy_state_def:
  bytestring_copy_state (dst_addr:bytes32) (src_addr:bytes32) ss =
    let length_word = mload (w2n src_addr) ss in
    let rounded = bytestring_round_word length_word in
    mcopy (w2n dst_addr) (w2n src_addr) (w2n (32w + length_word))
      (mstore (w2n (dst_addr + rounded)) 0w ss)
End

(* Reuse the kernel-proved dispatch equations for these five opcodes. *)
val bytestring_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc)
       [``MLOAD``, ``ADD``, ``AND``, ``MSTORE``, ``MCOPY``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem bytestring_encoder_execution:
  !id names dst src ss dst_addr src_addr.
    LENGTH names = 8 /\ ALL_DISTINCT names /\
    EVERY (\name. src <> Var name /\ dst <> Var name) names /\
    eval_operand src ss = SOME src_addr /\ eval_operand dst ss = SOME dst_addr ==>
    ?out.
      run_inst_seq (bytestring_encoder_insts id names dst src) ss = OK out /\
      eval_operand (Var (EL 7 names)) out =
        SOME (32w + bytestring_round_word (mload (w2n src_addr) ss)) /\
      out with vs_vars := ss.vs_vars = bytestring_copy_state dst_addr src_addr ss /\
      (!arg_op. EVERY (\name. arg_op <> Var name) names ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >> fs[LENGTH_EQ_NUM_compute] >>
  qmatch_goalsub_rename_tac
    `bytestring_encoder_insts id [v0;v1;v2;v3;v4;v5;v6;v7] dst src` >>
  gvs[ALL_DISTINCT] >>
  asm_simp_tac (srw_ss()) (bytestring_steps @
   [bytestring_encoder_insts_def, run_inst_seq_def,
    mk_inst_def, exec_read1_def, exec_pure2_def, exec_write2_def,
    eval_operand_update_var_avoids, eval_operand_update_var,
    eval_operand_mstore_eq, eval_operand_mcopy_eq, eval_operand_lit,
    mload_update_var, mstore_update_var, mcopy_update_var,
    update_var_reset_vars, GSYM mstore_reset_vars, GSYM mcopy_reset_vars,
    bytestring_round_word_def, bytestring_copy_state_def, LET_THM]) >>
  rpt gen_tac >> strip_tac >> fs[] >>
  simp[eval_operand_update_var_avoids, eval_operand_mstore_eq, eval_operand_mcopy_eq]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI bytestring execution theorem: " ^ name)
  end)
  (DB.thms "abiBytestringExec")
