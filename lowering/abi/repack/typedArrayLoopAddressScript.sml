(* TOP-LEVEL: the actual array-copy body computes independent source and
   target strides before entering its recursive child. Replayed temporaries
   are allowed; only operands read after a write must avoid that output.
   Helpers expose address values and unchanged memory/control fields. *)
Theory typedArrayLoopAddress
Ancestors
  typedArrayLoopCode typedArrayLoopStructure abiStaticLoopCode logBytesStoreProps
  ssaOperandFrame fragBlockPath fragExec compileEnv exprLoweringProps emitHelperProps instIdxIndep
  venomExecSemantics venomState venomInst list rich_list words arithmetic

Definition typed_array_loop_address_state_def:
  typed_array_loop_address_state var_base (counter_word:bytes32) dst_addr src_addr dst_size src_size ss =
    let src_offset = counter_word * n2w src_size in
    let dst_offset = counter_word * n2w dst_size in
    update_var (compiler_var_name var_base 6) (dst_addr + dst_offset)
      (update_var (compiler_var_name var_base 5) (src_addr + src_offset)
        (update_var (compiler_var_name var_base 4) dst_offset
          (update_var (compiler_var_name var_base 3) src_offset ss)))
End

val typed_address_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc) [``MUL``, ``ADD``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem typed_array_loop_addresses_straight:
  !id var_base dst src dst_size src_size.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (typed_array_loop_addresses id var_base dst src dst_size src_size) /\
    LENGTH (typed_array_loop_addresses id var_base dst src dst_size src_size) = 4
Proof
  simp[typed_array_loop_addresses_def, mk_inst_def, is_terminator_def]
QED

Theorem typed_array_loop_addresses_execution:
  !id var_base dst src dst_size src_size ss counter_word dst_addr src_addr.
    eval_operand (Var (compiler_var_name var_base 0)) ss = SOME counter_word /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    src <> Var (compiler_var_name var_base 3) /\ src <> Var (compiler_var_name var_base 4) /\
    dst <> Var (compiler_var_name var_base 3) /\ dst <> Var (compiler_var_name var_base 4) /\
    dst <> Var (compiler_var_name var_base 5) ==>
    run_inst_seq (typed_array_loop_addresses id var_base dst src dst_size src_size) ss =
      OK (typed_array_loop_address_state var_base counter_word dst_addr src_addr dst_size src_size ss)
Proof
  rpt gen_tac >> strip_tac >>
  asm_simp_tac (srw_ss()) (typed_address_steps @
    [typed_array_loop_addresses_def, typed_array_loop_address_state_def,
     run_inst_seq_def, mk_inst_def, exec_pure2_def, eval_operand_lit,
     eval_operand_update_var, eval_operand_update_var_avoids, LET_THM])
QED

Theorem typed_array_loop_address_control[simp]:
  !var_base counter_word dst_addr src_addr dst_size src_size ss.
    (typed_array_loop_address_state var_base counter_word dst_addr src_addr dst_size src_size ss).
      vs_current_bb = ss.vs_current_bb /\
    (typed_array_loop_address_state var_base counter_word dst_addr src_addr dst_size src_size ss).
      vs_inst_idx = ss.vs_inst_idx /\
    (typed_array_loop_address_state var_base counter_word dst_addr src_addr dst_size src_size ss).
      vs_halted = ss.vs_halted /\
    (typed_array_loop_address_state var_base counter_word dst_addr src_addr dst_size src_size ss).
      vs_memory = ss.vs_memory
Proof
  simp[typed_array_loop_address_state_def, LET_THM, update_var_def]
QED

Theorem typed_array_loop_address_values:
  !var_base counter_word dst_addr src_addr dst_size src_size ss.
    eval_operand (Var (compiler_var_name var_base 5))
      (typed_array_loop_address_state var_base counter_word dst_addr src_addr dst_size src_size ss) =
      SOME (src_addr + counter_word * n2w src_size) /\
    eval_operand (Var (compiler_var_name var_base 6))
      (typed_array_loop_address_state var_base counter_word dst_addr src_addr dst_size src_size ss) =
      SOME (dst_addr + counter_word * n2w dst_size)
Proof
  simp[typed_array_loop_address_state_def, LET_THM, eval_operand_update_var,
    eval_operand_update_var_avoids]
QED

Theorem typed_array_loop_address_operand_frame:
  !var_base counter_word dst_addr src_addr dst_size src_size ss arg_op.
    EVERY (\j. arg_op <> Var (compiler_var_name var_base j)) [3;4;5;6] ==>
    eval_operand arg_op
      (typed_array_loop_address_state var_base counter_word dst_addr src_addr dst_size src_size ss) =
      eval_operand arg_op ss
Proof
  simp[typed_array_loop_address_state_def, LET_THM, eval_operand_update_var_avoids]
QED

Theorem typed_array_loop_address_natural:
  !addr i elem_size.
    w2n (addr:bytes32) + i * elem_size < dimword(:256) ==>
    w2n (addr + n2w i * n2w elem_size) = w2n addr + i * elem_size
Proof
  simp[word_mul_n2w, log_field_address]
QED

Theorem typed_array_loop_addresses_path:
  !ctx func cs cond_label body_label exit_label len_op dst src dst_size src_size
      ss counter_word dst_addr src_addr.
    fn_has_code cs
      (typed_array_loop_start cs cond_label body_label exit_label len_op dst src dst_size src_size) func /\
    ss.vs_current_bb = body_label /\ ss.vs_inst_idx = 0 /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME counter_word /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    src <> Var (compiler_var_name cs.cs_next_var 3) /\ src <> Var (compiler_var_name cs.cs_next_var 4) /\
    dst <> Var (compiler_var_name cs.cs_next_var 3) /\ dst <> Var (compiler_var_name cs.cs_next_var 4) /\
    dst <> Var (compiler_var_name cs.cs_next_var 5) ==>
    fragment_path ctx func ss
      ((typed_array_loop_address_state cs.cs_next_var counter_word dst_addr src_addr dst_size src_size ss)
        with vs_inst_idx := 4)
Proof
  rpt gen_tac >> strip_tac >> drule_all typed_array_loop_prefix_contains >> strip_tac >>
  drule_all typed_array_loop_addresses_execution >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `ss`,
    `typed_array_loop_address_state cs.cs_next_var counter_word dst_addr src_addr dst_size src_size ss`,
    `body_bb`, `typed_array_loop_addresses cs.cs_next_id cs.cs_next_var dst src dst_size src_size`]
    fragment_path_prefix) >> simp[typed_array_loop_addresses_straight]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed array-copy address theorem: " ^ name)
  end) (DB.thms "typedArrayLoopAddress")
