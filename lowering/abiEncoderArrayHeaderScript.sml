(* Actual encoder loop header: the count is a live operand from initialization.
   TOP-LEVEL: exact emitted shape, concrete header execution and CFG simulation. *)
Theory abiEncoderArrayHeader
Ancestors
  abiEncoderArrayCode abiDecoderExecution abiDecoderLoop abiDecoderContract
  fragExec compileEnv emitHelperProps exprLoweringProps emitHelper venomExecSemantics venomExecProofs
  venomState venomInst words list arithmetic

Definition abi_encode_array_header_insts_def:
  abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl =
    [mk_inst id MLOAD [ip] [iv];
     mk_inst (id+1) LT [Var iv;count_op] [cmp];
     mk_inst (id+2) ISZERO [Var cmp] [done];
     mk_inst (id+3) JNZ [Var done;Label exit_lbl;Label body_lbl] []]
End

Definition abi_encode_array_header_state_def:
  abi_encode_array_header_state iv cmp done i n s =
    update_var done (bool_to_word (~(i<n)))
      (update_var cmp (bool_to_word (i<n)) (update_var iv (n2w i) s))
End

Theorem abi_encode_array_header_shape:
  abi_encode_array_header ip count_op st =
    ((fresh_label_output "enc_dyn_hdr" st.cs_next_label,
      fresh_label_output "enc_dyn_body" (st.cs_next_label+1),
      fresh_label_output "enc_dyn_exit" (st.cs_next_label+2)),
     st with <|cs_next_var := st.cs_next_var+3; cs_next_id := st.cs_next_id+5;
       cs_next_label := st.cs_next_label+3;
       cs_current_bb := fresh_label_output "enc_dyn_body" (st.cs_next_label+1);
       cs_current_insts := [];
       cs_blocks :=
         <|bb_label := fresh_label_output "enc_dyn_hdr" st.cs_next_label;
           bb_instructions := abi_encode_array_header_insts (st.cs_next_id+1) ip count_op
             (STRING #"%" (toString st.cs_next_var))
             (STRING #"%" (toString (st.cs_next_var+1)))
             (STRING #"%" (toString (st.cs_next_var+2)))
             (fresh_label_output "enc_dyn_body" (st.cs_next_label+1))
             (fresh_label_output "enc_dyn_exit" (st.cs_next_label+2))|> ::
         <|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts ++
           [mk_inst st.cs_next_id JMP [Label (fresh_label_output "enc_dyn_hdr" st.cs_next_label)] []]|> ::
         st.cs_blocks|>)
Proof
  simp[abi_encode_array_header_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_label_def, new_block_def, emit_op_def, emit_inst_def, fresh_id_def, fresh_var_def,
    emit_def, abi_encode_array_header_insts_def]
QED

Theorem abi_encode_array_header_prefix:
  count_op <> Var iv /\ eval_operand ip s = SOME p /\
  eval_operand count_op s = SOME (n2w n) /\ mload (w2n p) s = n2w i /\
  i <= n /\ n < dimword (:256) ==>
  run_inst_seq (TAKE 3 (abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl)) s =
    OK (abi_encode_array_header_state iv cmp done i n s)
Proof
  strip_tac >>
  `eval_operand count_op (update_var iv (n2w i) s) = SOME (n2w n)` by
    (Cases_on `count_op` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst id MLOAD [ip] [iv]) s = OK (update_var iv (n2w i) s)` by
    simp[Once step_inst_base_def, exec_read1_def, mk_inst_def] >>
  `i < dimword (:256)` by decide_tac >>
  simp[abi_encode_array_header_insts_def, run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def,
    eval_operand_def, lookup_var_update_var, w2n_n2w] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_pure1_def,
    eval_operand_def, lookup_var_update_var, abi_encode_array_header_state_def] >>
  Cases_on `i<n` >> simp[bool_to_word_def]
QED

Theorem abi_encode_array_header_control:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\ count_op <> Var iv /\
  eval_operand ip s = SOME p /\ eval_operand count_op s = SOME (n2w n) /\
  mload (w2n p) s = n2w i /\ i <= n /\ n < dimword (:256) ==>
  exec_block fuel ctx <|bb_label := hdr; bb_instructions :=
    abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|> s =
    OK (jump_to (if i<n then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done i n s))
Proof
  strip_tac >> drule_all abi_encode_array_header_prefix >> strip_tac >>
  qspecl_then [`TAKE 3 (abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl)`,
    `s`, `fuel`, `ctx`, `<|bb_label := hdr; bb_instructions :=
      abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|>`]
    mp_tac exec_block_run_inst_seq >>
  simp[abi_encode_array_header_insts_def, mk_inst_def, is_terminator_def] >> strip_tac >> simp[] >>
  simp[Once exec_block_def, get_instruction_def, abi_encode_array_header_insts_def] >>
  simp[step_inst_def, Once step_inst_base_def, mk_inst_def,
    abi_encode_array_header_state_def, eval_operand_def, lookup_var_update_var] >>
  Cases_on `i<n` >> simp[bool_to_word_def, lookup_var_def, update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, jump_to_def, is_terminator_def]
QED

Theorem abi_encode_array_header_sim:
  lookup_block hdr func.fn_blocks = SOME <|bb_label := hdr; bb_instructions :=
    abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|> /\
  lookup_block body_lbl func.fn_blocks = SOME body_bb /\
  lookup_block exit_lbl func.fn_blocks = SOME exit_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ phi_prefix_length exit_bb.bb_instructions = 0 /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\ count_op <> Var iv /\
  eval_operand ip s = SOME p /\ eval_operand count_op s = SOME (n2w n) /\
  mload (w2n p) s = n2w i /\ i <= n /\ n < dimword (:256) ==>
  abi_decode_sim ctx func s (jump_to (if i<n then body_lbl else exit_lbl)
    (abi_encode_array_header_state iv cmp done i n s))
Proof
  strip_tac >> irule abi_decode_edge_sim >>
  simp[jump_to_def, abi_encode_array_header_state_def, update_var_def] >> conj_tac
  >- (gen_tac >> drule_all abi_encode_array_header_control >>
      simp[jump_to_def, abi_encode_array_header_state_def, update_var_def]) >>
  Cases_on `i<n` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_HEADER_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array header not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayHeader");
