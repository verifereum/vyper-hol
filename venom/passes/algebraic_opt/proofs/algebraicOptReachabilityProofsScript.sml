Theory algebraicOptReachabilityProofs
Ancestors
  algebraicOptDefs venomExecSemantics venomState

(* A chain boundary must retain a Boolean value at value-sensitive uses;
   at truthy uses the root word itself suffices. *)
Theorem ao_two_iszero_boundary:
  !w:bytes32.
    (bool_to_word (bool_to_word (w = 0w) = 0w) = 0w <=> w = 0w) /\
    bool_to_word (bool_to_word (w = 0w) = 0w) = bool_to_word (w <> 0w)
Proof
  gen_tac >> Cases_on `w = 0w` >> simp[bool_to_word_def]
QED

(* Reads in a parallel PHI batch all use s, even if one output is an
   input of the other. This equation also covers loop back edges. *)
Theorem ao_parallel_phi_pair:
  !s i j x y a b.
    i.inst_opcode = PHI /\ j.inst_opcode = PHI /\
    eval_one_phi s i = SOME (x,a) /\
    eval_one_phi s j = SOME (y,b) ==>
    eval_phis s [i;j] = OK (update_var x a (update_var y b s))
Proof
  rpt strip_tac >> simp[eval_phis_def]
QED

(* A consumer-level provenance interface cannot read a producer's
   operands from a post-PHI environment: its source environment is s. *)
Theorem ao_phi_selected_operand:
  !s inst prev op out w.
    inst.inst_outputs = [out] /\ s.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME op /\
    eval_operand op s = SOME w ==>
    eval_one_phi s inst = SOME (out,w)
Proof
  rpt strip_tac >> simp[eval_one_phi_def]
QED

(* One producer step exposes precisely the value a chain consumer needs.
   It does not assert that the source operand stays unchanged on a loop. *)
Theorem ao_iszero_producer_step:
  !inst s op out w.
    inst.inst_opcode = ISZERO /\ inst.inst_operands = [op] /\
    inst.inst_outputs = [out] /\ eval_operand op s = SOME w ==>
    step_inst_base inst s = OK (update_var out (bool_to_word (w = 0w)) s)
Proof
  rpt strip_tac >> simp[step_inst_base_def, exec_pure1_def]
QED

(* T marks a run_blocks entry, F a sequential instruction boundary.
   Residual fuel is explicit: PHI processing consumes the block fuel,
   while sequential steps do not. No acyclicity premise excludes loops. *)
Inductive ao_source_prefix:
  (!ctx fn s0 n.
    ao_source_prefix ctx fn s0 n n T s0) /\
  (!ctx fn s0 n k s bb p.
    ao_source_prefix ctx fn s0 n (SUC k) T s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK p ==>
    ao_source_prefix ctx fn s0 n k F
      (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
  (!ctx fn s0 n k s bb inst t.
    ao_source_prefix ctx fn s0 n k F s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    ~is_terminator inst.inst_opcode /\
    step_inst k ctx inst s = OK t ==>
    ao_source_prefix ctx fn s0 n k F
      (t with vs_inst_idx := SUC s.vs_inst_idx)) /\
  (!ctx fn s0 n k s bb inst t.
    ao_source_prefix ctx fn s0 n k F s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\
    step_inst k ctx inst s = OK t /\ ~t.vs_halted ==>
    ao_source_prefix ctx fn s0 n k T t)
End

(* This tests both loop re-entry (t may have the same block label as s)
   and the separation between predecessor and post-PHI environments. *)
Theorem ao_source_prefix_edge_phis:
  !ctx fn s0 n k s bb inst t next p.
    ao_source_prefix ctx fn s0 n (SUC k) F s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\
    step_inst (SUC k) ctx inst s = OK t /\ ~t.vs_halted /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME next /\
    eval_phis t next.bb_instructions = OK p ==>
    ao_source_prefix ctx fn s0 n k F
      (p with vs_inst_idx := phi_prefix_length next.bb_instructions)
Proof
  rpt strip_tac >> irule (cj 2 ao_source_prefix_rules) >>
  goal_assum (drule_at Any) >> simp[] >>
  irule (cj 4 ao_source_prefix_rules) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
