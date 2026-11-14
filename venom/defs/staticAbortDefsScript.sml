(* A straight prefix ending at a static storage or log fault. *)
Theory staticAbortDefs
Ancestors
  venomInst venomState list

Definition static_abort_pair_def:
  static_abort_pair (bb : basic_block) (i : num) (j : num) <=>
    i <= j /\ j < LENGTH bb.bb_instructions /\
    MEM (EL j bb.bb_instructions).inst_opcode [SSTORE; TSTORE; LOG] /\
    !k inst.
      i <= k /\ k < j /\ get_instruction bb k = SOME inst ==>
      ~is_terminator inst.inst_opcode /\
      ~MEM inst.inst_opcode
        [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2;
         SSTORE; TSTORE; LOG]
End

Definition static_abort_at_def:
  static_abort_at (bb : basic_block) (i : num) <=>
    ?j. static_abort_pair bb i j
End

Definition in_static_abort_prefix_def:
  in_static_abort_prefix (fn : ir_function) (s : venom_state) <=>
    s.vs_call_ctx.cc_static /\
    ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
         static_abort_at bb s.vs_inst_idx
End
