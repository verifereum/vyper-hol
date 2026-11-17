(* Compiler syntax: weak closure of slots-fragment jump targets. *)
Theory bodyFullStoreSlotsStaticControl
Ancestors
  fragFuelLoopAbiDecDyn exprSimAbiEncodeObliviousCode exprSimAbiGasBridge
  context compileEnv emitHelper exprLoweringProps fragExec list pred_set
  venomInst

val slots_J = ``\T i.
  (i.inst_opcode = JMP ==> ?l. i.inst_operands = [Label l] /\ l IN T) /\
  (i.inst_opcode = JNZ ==> ?v l r.
    i.inst_operands = [v; Label l; Label r] /\ l IN T /\ r IN T)``;
val slots_B = ``\a b. {l | (?bb. MEM bb (emitted_blocks a b) /\ l = bb.bb_label) \/
  l = b.cs_current_bb}``;
val slots_closed = ``\T m. !a r b. m a = (r,b) ==>
  entry_shape a b /\ EVERY ((^slots_J) (T UNION (^slots_B) a b)) (frag_code a b)``;
val slots_skel = ``\hdr body exit (p:compile_state -> unit # compile_state)
    (h:compile_state -> unit # compile_state) (q:compile_state -> unit # compile_state).
  do p; new_block hdr; h; new_block body; q; new_block exit; return () od``;

val slots_sequence = rpt (FIRST [
  CHANGED_TAC BETA_TAC,
  first_assum (MATCH_ACCEPT_TAC o BETA_RULE),
  MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_return),
  MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_label),
  (MATCH_MP_TAC (BETA_RULE abi_dyn_branchless_closed) >>
    simp[code_action_fresh_var] >> NO_TAC),
  (MATCH_MP_TAC (BETA_RULE abi_dyn_closed_emit_op) >> simp[] >> NO_TAC),
  (MATCH_MP_TAC (BETA_RULE abi_dyn_closed_emit_inst) >> simp[mk_inst_def] >> NO_TAC),
  (MATCH_MP_TAC (BETA_RULE abi_dyn_closed_emit_void) >> simp[mk_inst_def] >> NO_TAC),
  ho_match_mp_tac (BETA_RULE abi_dyn_closed_bind),
  ho_match_mp_tac (BETA_RULE abi_dyn_closed_ignore_bind),
  conj_tac, gen_tac]);

Theorem store_slots_word_loop_skeleton[local]:
  !src dst cnt tr.
  comp_ignore_bind (compile_word_copy_loop_op src dst cnt LocMemory
    (if tr then LocTransient else LocStorage) F) (comp_return ()) =
  do lh <- fresh_label "wcopy_cond";
     lb <- fresh_label "wcopy_body";
     le <- fresh_label "wcopy_exit";
     ctr <- fresh_var;
     (^slots_skel) lh lb le
       (do emit_inst ASSIGN [Lit 0w] [ctr]; emit_inst JMP [Label lh] [] od)
       (do done_op <- emit_op EQ [Var ctr; cnt];
           emit_inst JNZ [done_op; Label le; Label lb] [] od)
       (do off <- emit_op MUL [Var ctr; Lit 32w];
           src_off <- emit_op ADD [src; off];
           loaded <- emit_op MLOAD [src_off];
           dst_off <- emit_op ADD [dst; Var ctr];
           emit_void (if tr then TSTORE else SSTORE) [dst_off; loaded];
           nc <- emit_op ADD [Var ctr; Lit 1w];
           emit_inst ASSIGN [nc] [ctr]; emit_inst JMP [Label lh] [] od) od
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp_tac std_ss [compile_word_copy_loop_op_def, compile_word_copy_loop_base_def,
    word_scale_def, compile_ptr_load_def, compile_ptr_store_def,
    comp_ignore_bind_def, comp_bind_assoc, fragFuelTheory.comp_bind_return, LET_THM]
QED

Theorem store_slots_primitive_control:
  (!T src dst cnt tr. (^(inst [alpha |-> ``:unit``] slots_closed)) T
    (comp_ignore_bind (compile_word_copy_loop_op src dst cnt LocMemory
      (if tr then LocTransient else LocStorage) F) (comp_return ()))) /\
  (!T src. (^(inst [alpha |-> ``:operand``] slots_closed)) T (compile_bytestring_word_count src)) /\
  (!T src off. (^(inst [alpha |-> ``:operand``] slots_closed)) T (compile_lit_byte_offset src off))
Proof
  rpt conj_tac
  >- (rpt gen_tac >> pure_rewrite_tac[store_slots_word_loop_skeleton] >>
      BETA_TAC >>
      ntac 3 (ho_match_mp_tac (BETA_RULE abi_dyn_closed_bind) >>
        conj_tac >- MATCH_ACCEPT_TAC (BETA_RULE abi_dyn_closed_label) >> gen_tac) >>
      ho_match_mp_tac (BETA_RULE abi_dyn_closed_bind) >>
      conj_tac >- (MATCH_MP_TAC (BETA_RULE abi_dyn_branchless_closed) >>
        simp[code_action_fresh_var]) >> gen_tac >>
      MATCH_MP_TAC (BETA_RULE abi_dyn_skeleton_closed) >>
      Cases_on `tr` >> slots_sequence)
  >- (rpt gen_tac >> pure_rewrite_tac[compile_bytestring_word_count_def] >>
      slots_sequence) >>
  rpt gen_tac >> pure_rewrite_tac[compile_lit_byte_offset_def] >>
  IF_CASES_TAC >- slots_sequence >> Cases_on `src` >>
  simp_tac std_ss [venomStateTheory.operand_case_def] >> slots_sequence
QED
