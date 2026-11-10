(* Same-witness validation of the decoder observation/history boundaries. *)
Theory entryDecoderEndpointValidation
Ancestors
  entryDecoderStateFrame entryDecoderHistoryFrame abiDecoderValidBytes
  abiDecoderExecution allocaHistory venomState venomExecSemantics list

Theorem entry_valid_bytes_endpoint_frame:
  compile_abi_decode_to_buf dst src opc (Lit 0w) hi (DecBytestring n) st = ((),st') /\
  abi_decoder_valid_bytes_pre n at bs payload st src dst opc (Lit 0w) hi 0 sb d s /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    ~is_terminator i.inst_opcode) (emitted_insts st st') /\
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  fn_has_code st st' fn /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d t.vs_memory /\
    val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d t.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    entry_decoder_obs s t /\
    alloca_history fn (t with vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  strip_tac >> `Lit 0w = Lit 0w \/ opc = MLOAD` by simp[] >>
  drule_all abi_decoder_valid_bytes_sequence >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st') /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st')` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all entry_decoder_sequence_obs >> strip_tac >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Theorem entry_header_endpoint_frame:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  abi_decode_source_opcode opc /\ src <> Var iv /\ iv <> cv /\
  eval_operand ip s = SOME p /\ eval_operand src s = SOME srcaddr /\
  mload (w2n p) s = n2w i /\ abi_decode_load opc srcaddr s = n2w ncount /\
  i <= ncount /\ ncount < dimword(:256) /\ alloca_history fn s ==>
  let t = jump_to (if i < ncount then body_lbl else exit_lbl)
      (abi_decode_header_state iv cv cmp done i ncount s)
  in exec_block fuel ctx
       <|bb_label := hdr; bb_instructions :=
         abi_decode_header_insts id ip src opc iv cv cmp done body_lbl exit_lbl|> s = OK t /\
     entry_decoder_obs s t /\ alloca_history fn t
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_decode_header_control >> strip_tac >> simp[] >>
  conj_tac >- simp[abi_decode_header_state_def] >>
  irule alloca_history_jump >> simp[jump_to_def] >> qexists_tac `s` >>
  simp[abi_decode_header_state_def, jump_to_def, update_var_def]
QED

Theorem entry_backedge_endpoint_frame:
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w i) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ i < ncount /\ ncount < dimword(:256) /\
  alloca_history fn s ==>
  let t = jump_to hdr
    (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s))
  in exec_block fuel ctx bb s = OK t /\ entry_decoder_obs s t /\ alloca_history fn t
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_decode_backedge_control >> strip_tac >> simp[] >>
  irule alloca_history_jump >> simp[jump_to_def] >> qexists_tac `s` >>
  simp[jump_to_def, mstore_def, write_memory_with_expansion_def, update_var_def]
QED

(* Recursive integration interface audit:
   calldataOwnedLoopClosure.calldata_owned_loop_from_header defines H at
   lines 144-170. Retain EVERY conjunct of H and the separate prefix-memory
   predicate at lines 250-252; strengthen H j u scratch by
     entry_decoder_obs initial u /\ alloca_history fn u.
   Keep the existing Safe/Pull pair unchanged. Finite induction is on
   LENGTH vs-j (iterate, lines 288-297); the successor endpoint must have
   H+ (SUC j) v (scratch++new), prefix-memory, Safe u v and Pull u v.
   The child premise (lines 212-247) must take history at entry and return
   the SAME child/new supplying all its old conjuncts, additionally
     entry_decoder_obs entry child /\ alloca_history fn child.
   The entry setup needs the same strengthening from head to entry.
   Input history at the header is transported to head by the checked
   header wrapper above (both body and terminal branches). The checked
   backedge wrapper transports child history to the next header, using
   its explicit index-zero endpoint; equality of allocation maps alone
   would not justify a nonzero-cursor child endpoint.
   Remaining production dependencies: jointly strengthened setup and child
   producers; bytes compilation must discharge same-block/prefix/opcode
   premises of entry_valid_bytes_endpoint_frame from actual code facts.
   No such missing property is assumed for the frozen theorem here. *)

val () =
  List.app (fn th =>
    let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    in if null axioms andalso null (Thm.hyp th) andalso
          List.all (fn name => name = "DISK_THM") oracles
       then () else raise Fail "entry endpoint validation inherited admission"
    end) [entry_valid_bytes_endpoint_frame, entry_header_endpoint_frame,
          entry_backedge_endpoint_frame];
