(* Counted bytestring copy: retain the length prefix's actual endpoint. *)
Theory assignBasePtrBytesCopy
Ancestors assignBasePtrBytesPrefix assignBasePtrMcopyTransport context
  compileEnv emitHelper emitHelperProps exprLoweringProps venomInst
  list rich_list fragExec assignBasePtrMcopy fragGasPathPtr
  venomExecSemantics venomState words ptrDiscipline bodyPtrDefs
  ghostPcTransportPtr

Theorem assign_base_store_bytestring_split:
  !src dst sa sb.
    compile_store_bytestring src dst sa = ((),sb) ==>
    ?out sm.
      compile_bytestring_copy_len src sa = (out,sm) /\
      emit_void MCOPY [dst;src;out] sm = ((),sb) /\
      sb.cs_current_bb = sm.cs_current_bb /\
      sb.cs_current_insts = sm.cs_current_insts ++
        [mk_inst sm.cs_next_id MCOPY [dst;src;out] []]
Proof
  rpt gen_tac >>
  simp[compile_store_bytestring_def, comp_bind_def] >>
  Cases_on `compile_bytestring_copy_len src sa` >>
  rpt strip_tac >> qexistsl_tac [`q`, `r`] >>
  gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, emit_def, comp_return_def]
QED

Theorem assign_base_store_bytestring_layout:
  !src dst sa sm sb out fn.
    compile_bytestring_copy_len src sa = (out,sm) /\
    emit_void MCOPY [dst;src;out] sm = ((),sb) /\
    fn_has_code sa sb fn ==>
    ?bb.
      sm.cs_current_bb = sa.cs_current_bb /\
      lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (emitted_insts sa sm)
        (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions) /\
      get_instruction bb (LENGTH sm.cs_current_insts) =
        SOME (mk_inst sm.cs_next_id MCOPY [dst;src;out] []) /\
      LENGTH sm.cs_current_insts = LENGTH sa.cs_current_insts + 4 /\
      LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 5
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_bytestring_copy_len_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_return_def, comp_ignore_bind_def,
      fresh_id_def, fresh_var_def, emit_def, fn_has_code_def,
      IS_PREFIX_APPEND, emitted_insts_def, DROP_APPEND1] >>
  simp[get_instruction_def, EL_APPEND_EQN, IS_PREFIX_APPEND] >>
  metis_tac[APPEND_ASSOC]
QED

Theorem assign_base_bytes_mcopy_path:
  !s fn bb id dst src out n d a tn G ctx D PG.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MCOPY [Var dst;Var src;out] []) /\
    eval_operand out s = SOME (n2w n) /\ op_taint tn out = {} /\
    n < dimword (:256) /\
    lookup_var dst s = SOME d /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s n /\ ptr_covers G tn src s n /\
    ~ctx_has_dalloca ctx ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id MCOPY [Var dst;Var src;out] [])
        (mcopy (w2n d) (w2n a) n s))
      (step_taint (mk_inst id MCOPY [Var dst;Var src;out] []) s
        (mcopy (w2n d) (w2n a) n s) tn)
      (OK (mcopy (w2n d) (w2n a) n s with
        vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id MCOPY [Var dst;Var src;out] []) s =
    OK (mcopy (w2n d) (w2n a) n s)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def]) >>
  `ptr_covers G tn dst s (w2n (n2w n : bytes32)) /\
   ptr_covers G tn src s (w2n (n2w n : bytes32))` by simp[] >>
  drule_all assign_base_mcopy_operand_edge_ptr >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >> simp[] >>
  disch_then assume_tac >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >>
  disch_then irule >>
  simp[cj 1 gas_path_ptr_rules, mcopy_def, write_memory_with_expansion_def]
QED

(* instIdxIndep's equivalent equation is local to that theory. *)
Theorem assign_base_mcopy_cursor:
  !dst src n s k.
    mcopy dst src n (s with vs_inst_idx := k) =
      (mcopy dst src n s with vs_inst_idx := k)
Proof
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem assign_base_store_bytestring_counted:
  !src dst sa sb fn s a d len G tn D ctx PG.
    compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME d /\
    mload (w2n a) s = n2w len /\
    32 + 32 * word_size len < dimword (:256) /\
    ptr_covers G tn src s 32 /\
    ptr_covers G tn src s (32 + 32 * word_size len) /\
    ptr_covers G tn dst s (32 + 32 * word_size len) /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?sm out q G1 tn1.
      compile_bytestring_copy_len (Var src) sa = (out,sm) /\
      eval_operand out q = SOME (n2w (32 + 32 * word_size len)) /\
      (q with vs_vars := s.vs_vars) = s /\
      tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
      tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
      (!p. not_fresh_at sa p ==>
        lookup_var p q = lookup_var p s /\ FLOOKUP G1 p = FLOOKUP G p /\
        op_taint tn1 (Var p) = op_taint tn (Var p)) /\
      gas_path_ptr D 0 ctx fn PG G tn s 0
        (step_prov PG G1 (mk_inst sm.cs_next_id MCOPY [Var dst;Var src;out] [])
          (mcopy (w2n d) (w2n a) (32 + 32 * word_size len) q))
        (step_taint (mk_inst sm.cs_next_id MCOPY [Var dst;Var src;out] []) q
          (mcopy (w2n d) (w2n a) (32 + 32 * word_size len) q) tn1)
        (OK (mcopy (w2n d) (w2n a) (32 + 32 * word_size len) q with
          vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  rpt strip_tac >>
  drule assign_base_store_bytestring_split >> strip_tac >>
  drule_all assign_base_store_bytestring_layout >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[] >>
  drule_all assign_base_bytes_prefix_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `lookup_var dst q = SOME d /\ lookup_var src q = SOME a /\
   ptr_covers G' tn' dst q (32 + 32 * word_size len) /\
   ptr_covers G' tn' src q (32 + 32 * word_size len)` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `~q.vs_halted /\ q.vs_current_bb = sa.cs_current_bb` by
    fs[venom_state_component_equality] >>
  qexistsl_tac [`sm`, `out`, `q`, `G'`, `tn'`] >> simp[] >>
  drule gas_path_ptr_then >> simp[] >> disch_then irule >>
  mp_tac (Q.SPEC `q with vs_inst_idx := LENGTH sm.cs_current_insts`
    assign_base_bytes_mcopy_path) >>
  simp[assign_base_mcopy_cursor, arithmeticTheory.ADD1] >>
  disch_then irule >> gvs[lookup_var_def]
QED
