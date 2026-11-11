(* Counted control boundaries for typed array-copy loops. *)
Theory typedCopyReturnControlPtr
Ancestors assignBasePtrStoragePath fragGasSeqPtr fragGasPathPtr stateFrame
  venomState venomInst finite_map ptrDiscipline arithmetic words

Theorem typed_copy_backedge_counted:
  !s fn bb id ctr nv i lbl tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ADD [Var ctr; Lit 1w] [nv]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) ASSIGN [Var nv] [ctr]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) JMP [Label lbl] []) /\
    lookup_var ctr s = SOME (n2w i) /\ FLOOKUP G ctr = NONE /\
    op_taint tn (Var ctr) = {} /\ ctr <> nv /\ ~ctx_has_dalloca ctx ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      lookup_var ctr t = SOME (n2w (SUC i)) /\ FLOOKUP H ctr = NONE /\
      op_taint tm (Var ctr) = {} /\
      t.vs_current_bb = lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      execution_frame t = execution_frame s /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_memory = s.vs_memory /\
      tm.t_mem = tn.t_mem /\ tm.t_imm = tn.t_imm /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\
      (!x. x <> ctr /\ x <> nv ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_storage_increment_prefix >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG Gf tf u 0 Gf tf (OK (jump_to lbl u))` by
    (irule assign_base_storage_jump_counted >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`Gf`, `tf`, `jump_to lbl u`] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  simp[jump_to_def, lookup_var_def] >>
  gvs[execution_frame_def]
QED
