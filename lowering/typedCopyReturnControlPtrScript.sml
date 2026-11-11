(* Counted control boundaries for typed array-copy loops. *)
Theory typedCopyReturnControlPtr
Ancestors assignBasePtrStoragePath fragGasSeqPtr fragGasPathPtr stateFrame
  venomState venomInst finite_map ptrDiscipline arithmetic words
  bodyPtrAttributeAdd emitHelperProps emitHelper compileEnv

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

(* Clean address arithmetic needs no provenance when the child is empty. *)
Theorem typed_copy_clean_address_counted:
  emit_op ADD [Var root;offset] sa = (dst,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var root s = SOME a /\ eval_operand offset s = SOME b /\
  op_taint tn (Var root) = {} /\ op_taint tn offset = {} ==>
  ?out t H tf. dst = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
    lookup_var out t = SOME (a+b) /\ op_taint tf (Var out) = {} /\
    not_fresh_at sb out /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ op_taint tf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `eval_operand (Var root) s = SOME a` by simp[eval_operand_def] >>
  drule_all (attribute_emit_binop_path_ptr |> SPEC_ALL |>
    Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   not_fresh_at sb out /\ (!v. not_fresh_at sa v ==> v <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  qexists_tac `out` >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> `v <> out` by metis_tac[] >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED
