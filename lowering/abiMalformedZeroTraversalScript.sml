(* Empty dynamic traversal executes only its initial jump and final header. *)
Theory abiMalformedZeroTraversal
Ancestors
  abiMalformedTraversal abiMalformedRecursiveInterface abiMalformedPrefix
  abiDecoderLoopEmit abiDecoderContract abiDecodeRanges fragExec
  compileEnv venomState venomInst venomExecSemantics words list arithmetic

Theorem abi_malformed_zero_traversal:
  abi_malformed_entry ctx func cenv cx es start sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  eval_operand ip s = SOME (n2w slot) /\ mload slot s = 0w /\
  slot < dimword (:256) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (slot,32) /\
  inst.inst_id IN sites /\ inst.inst_id <> live /\ inst.inst_id <> dstid /\
  fresh_vars_wrt limit_st s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME entry_bb /\
  entry_bb.bb_instructions = prefix ++ [mk_inst entry_id JMP [Label hdr] []] /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts hid ip src MLOAD base_op start.cs_next_var body_lbl exit_lbl|> /\
  phi_prefix_length (abi_decode_position_header_insts hid ip src MLOAD base_op start.cs_next_var body_lbl exit_lbl) = 0 /\
  final.cs_current_bb = exit_lbl /\ final.cs_current_insts = [] /\
  p+32 <= L /\ abi_head_word (DROP p xs) = 0 /\
  start.cs_next_var + 4 + abi_decode_position_header_delta base_op <= limit_st.cs_next_var ==>
  frag_outcome ctx func s final
    (\u. (?avs. abi_reflected_prefix env ty (DROP (p+32) xs) 0 avs) /\
      abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s u /\
      fresh_vars_wrt limit_st u)
    (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >>
  `?h. abi_decode_sim ctx func s h /\
    abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st
      sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q 0 s 0 h /\
    h.vs_current_bb = hdr /\ h.vs_inst_idx = 0 /\ ~h.vs_halted` by
    (irule abi_malformed_traversal_initial >> simp[] >>
     qexists_tac `entry_id` >> simp[]) >>
  irule abi_malformed_outcome_sim >> qexists_tac `h` >> simp[] >>
  irule abi_malformed_traversal_done >> simp[] >>
  goal_assum (drule_at (Pat `abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q 0 s 0 h`)) >>
  simp[] >> qexistsl_tac [`body_lbl`, `hid`] >> simp[]
QED
