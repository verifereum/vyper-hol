(* Supplied-runtime interface for the checked relative memory read. *)
Theory abiDecodePtrLoadReplay
Ancestors
  abiDecodePtrRead abiDecodePtrMemberFrame bodyPtrDefs compileEnv venomState venomExecSemantics stateFrame

Theorem abi_decode_relative_load_success_replay_ptr:
  compile_abi_dec_addr (Var src) pos sa = (addr,sb) /\
  emit_op MLOAD [addr] sb = (v,sc) /\
  fn_has_code sa sc func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_ptr_window G tn s src b h /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\
  p+32 <= h /\ w2n b+h < dimword(:256) /\
  run_inst_seq (emitted_insts sa sc) s = OK u ==>
  ?out G' tn'. v = Var out /\ not_fresh_at sc out /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sc) s G' tn' /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
      (OK (u with vs_inst_idx := LENGTH sc.cs_current_insts)) /\
    lookup_var out u = SOME (mload (w2n b+p) s) /\
    op_prov G' v = NONE /\ op_taint tn' v = {} /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
    state_frame u = state_frame s /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (fresh_vars_wrt sa s ==> fresh_vars_wrt sc u) /\
    (?ap. addr = Var ap /\ not_fresh_at sc ap /\
      abi_decode_ptr_window G' tn' u ap (b+n2w p) (h-p)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all abi_decode_ptr_relative_load >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `u = t with vs_inst_idx := s.vs_inst_idx` by
    (qpat_x_assum `run_inst_seq _ _ = OK u` mp_tac >>
     qpat_x_assum `run_inst_seq _ _ = OK (t with vs_inst_idx := _)` mp_tac >>
     simp[NoAsms]) >>
  `t with vs_inst_idx := LENGTH sc.cs_current_insts = t` by
    (qpat_x_assum `t.vs_inst_idx = _` mp_tac >>
     simp[NoAsms, venom_state_component_equality]) >>
  qexistsl_tac [`out`, `G'`, `tn'`] >>
  gvs[state_frame_def, lookup_var_def, abi_decode_ptr_window_def, ptr_covers_def,
      fresh_vars_wrt_def]
QED
