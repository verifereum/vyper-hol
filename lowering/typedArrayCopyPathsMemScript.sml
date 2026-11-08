(* Operational paths for the control and pointer portions of typed array copies. *)
Theory typedArrayCopyPathsMem
Ancestors
  typedCopyOperationalPaths typedArrayBoundControlMem typedArrayLoopLayoutMem typedArrayLoopControlMem
  fragGasSeqMem fragGasPathMem venomExecSemantics venomState venomInst
  emitHelperProps exprLoweringProps words arithmetic list rich_list

Theorem typed_array_bound_header_path_mem:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      [mk_inst id LT [Var ctr; bound] [cmp];
       mk_inst (id+1) ISZERO [Var cmp] [done];
       mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []]|> /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  eval_operand bound s = SOME (n2w n) /\ i <= n /\ n < dimword(:256) /\
  lookup_block (if i < n then body_lbl else exit_lbl) fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 ==>
  ?count. gas_path_mem ctx fn s count
    (OK (jump_to (if i < n then body_lbl else exit_lbl)
      (typed_sa_header_state cmp done i n s)))
Proof
  strip_tac >>
  drule_all typed_array_bound_header_control >> disch_then assume_tac >>
  drule typed_array_bound_header_mem_safe >> disch_then assume_tac >>
  irule exec_block_no_phi_path_mem >> goal_assum (drule_at Any) >>
  simp[] >>
  simp[mk_inst_def, jump_to_def, typed_sa_header_state_def, update_var_def]
QED

Theorem typed_sa_backedge_path_mem:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ typed_sa_backedge_insts id ctr nv hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  i < ncount /\ ncount < dimword(:256) /\
  lookup_block hdr fn.fn_blocks = SOME header_bb /\
  phi_prefix_length header_bb.bb_instructions = 0 ==>
  ?count. gas_path_mem ctx fn s count
    (OK (jump_to hdr (typed_sa_backedge_state ctr nv i s)))
Proof
  strip_tac >>
  drule_all typed_sa_backedge_control >> disch_then assume_tac >>
  drule_all typed_sa_backedge_mem_safe >> disch_then assume_tac >>
  irule exec_block_no_phi_path_mem >> goal_assum (drule_at Any) >>
  simp[] >>
  simp[DROP_APPEND, typed_sa_backedge_insts_def, mk_inst_def, jump_to_def,
       typed_sa_backedge_state_def, update_var_def]
QED

Theorem typed_sa_pointer_path_mem:
  code =
    [mk_inst id MUL [Var ctr; Lit (n2w src_stride)] [so];
     mk_inst (id+1) MUL [Var ctr; Lit (n2w dst_stride)] [dso];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) ADD [dst; Var dso] [dp]] /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code bb.bb_instructions /\
  ALL_DISTINCT [so;dso;sp;dp] /\ ~MEM ctr [so;dso;sp;dp] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [so;dso;sp;dp]) /\
  eval_operand src s = SOME (n2w source_base) /\
  eval_operand dst s = SOME (n2w dest_base) /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 ==>
  ?u. gas_path_mem ctx fn s 0 (OK u) /\ u.vs_inst_idx = 4 /\
    eval_operand (Var sp) u = SOME (n2w (source_base + src_stride*i)) /\
    eval_operand (Var dp) u = SOME (n2w (dest_base + dst_stride*i)) /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. ~MEM x [so;dso;sp;dp] ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> drule_all typed_sa_pointer_run >>
  disch_then (qspecl_then [`src_stride`, `id`, `dst_stride`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qexists_tac `q with vs_inst_idx := 4` >> conj_tac
  >- (`gas_path_mem ctx fn s
         (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
         (OK (q with vs_inst_idx := s.vs_inst_idx + LENGTH code))` by
        (irule run_inst_seq_gas_path_mem >>
         gvs[] >> simp[mk_inst_def, is_terminator_def]) >>
      gvs[mk_inst_def]) >>
  fs[venom_state_component_equality, eval_operand_def, lookup_var_def]
QED
