(* Memory safety of slice suffixes with live, non-aliasing input operands. *)
Theory sliceDataOperandMemory
Ancestors
  builtinBytes builtinBytesMemory exprSimWordBuiltins exprSimSliceBounds loweringHalt
  allocaFootprint abiBuiltinAllocation fragExecMem instMemFrontier
  exprLoweringProps emitHelperProps emitHelper compileEnv context venomInst
  venomState venomExecSemantics venomMemDefs finite_map list words arithmetic

Theorem slice_copy_store_live_mem_ok[local]:
  !st s buf_op src start count_op p data off count.
    (!x z. MEM x [buf_op;src;start;count_op] /\ x = Var z ==>
       not_fresh_at st z) /\
    eval_operand buf_op s = SOME (n2w p) /\
    eval_operand src s = SOME data /\ eval_operand start s = SOME off /\
    eval_operand count_op s = SOME count /\
    w2n (data + off) + w2n count <= s.vs_alloca_next /\
    p + 32 + w2n count <= s.vs_alloca_next /\
    p + 32 < dimword (:256) ==>
    run_inst_seq_mem_ok
      [mk_inst st.cs_next_id ADD [buf_op; Lit 32w]
         [STRING #"%" (toString st.cs_next_var)];
       mk_inst (st.cs_next_id + 1) ADD [src; start]
         [STRING #"%" (toString (st.cs_next_var + 1))];
       mk_inst (st.cs_next_id + 2) MCOPY
         [Var (STRING #"%" (toString st.cs_next_var));
          Var (STRING #"%" (toString (st.cs_next_var + 1))); count_op] [];
       mk_inst (st.cs_next_id + 3) MSTORE [buf_op; count_op] []] s
Proof
  rpt strip_tac >>
  `!x j v ss. MEM x [buf_op;src;start;count_op] /\ st.cs_next_var <= j ==>
      eval_operand x (update_var (STRING #"%" (toString j)) v ss) = eval_operand x ss` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `st` >> simp[] >> metis_tac[]) >>
  `p < dimword (:256)` by decide_tac >>
  `n2w p + 32w = (n2w (p + 32):bytes32)` by simp[word_add_n2w] >>
  `!id ops outs t. inst_mem_below_frontier (mk_inst id ADD ops outs) t` by
    (rpt gen_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  fs[MEM] >>
  simp[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
       below_frontier_MCOPY, below_frontier_MSTORE,
       step_inst_base_opcode_eqs, mk_inst_def, mcopy_operand_frame,
       exec_pure2_def, eval_operand_def, lookup_var_update_var]
QED

Theorem slice_allocated_live_suffix_mem_ok[local]:
  !st buf st1 n s src start count_op (len:bytes32) data off count p.
    compile_alloc_buffer n st = (buf, st1) /\
    (!x z. MEM x [src;start;count_op] /\ x = Var z ==> not_fresh_at st z) /\
    alloca_next_valid s /\
    eval_operand src s = SOME data /\ eval_operand start s = SOME off /\
    eval_operand count_op s = SOME count /\
    w2n off + w2n count <= w2n len /\
    w2n data + w2n len <= s.vs_alloca_next /\
    32 + w2n count <= n /\ n < dimword (:256) /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id n s).vs_allocas
      st.cs_next_id = SOME (p, n) /\ p + n < dimword (:256) ==>
    run_inst_seq_mem_ok
      (emitted_insts st st1 ++
       [mk_inst st1.cs_next_id ADD [buf.buf_operand; Lit 32w]
          [STRING #"%" (toString st1.cs_next_var)];
        mk_inst (st1.cs_next_id + 1) ADD [src; start]
          [STRING #"%" (toString (st1.cs_next_var + 1))];
        mk_inst (st1.cs_next_id + 2) MCOPY
          [Var (STRING #"%" (toString st1.cs_next_var));
           Var (STRING #"%" (toString (st1.cs_next_var + 1))); count_op] [];
        mk_inst (st1.cs_next_id + 3) MSTORE [buf.buf_operand; count_op] []]) s
Proof
  rpt strip_tac >> rename1 `eval_operand count_op s = SOME cnt` >>
  gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `n < dimword (:256)` by decide_tac >>
  drule_all step_alloca_site >>
  disch_then (qspec_then `STRING #"%" (toString st.cs_next_var)` assume_tac) >>
  drule_all alloca_site_frontier >> strip_tac >>
  once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base _ s = OK ss` >>
  simp[] >>
  `!x. MEM x [src;start;count_op] ==> eval_operand x ss = eval_operand x s` by
    (rpt strip_tac >> simp[Abbr `ss`] >>
     `eval_operand x (update_var (STRING #"%" (toString st.cs_next_var))
        (n2w p) (abi_builtin_allocate_state st.cs_next_id n s)) =
      eval_operand x (abi_builtin_allocate_state st.cs_next_id n s)` by
       (irule eval_operand_update_not_fresh >> qexists_tac `st` >>
        simp[] >> fs[MEM] >> metis_tac[]) >>
     simp[] >> irule eval_operand_same_vars >>
     simp[abi_builtin_allocate_state_def]) >>
  `s.vs_alloca_next <= ss.vs_alloca_next` by
    simp[Abbr `ss`, allocate_frontier_mono] >>
  `p + n <= ss.vs_alloca_next` by simp[Abbr `ss`] >>
  qspec_then `cs'` mp_tac slice_copy_store_live_mem_ok >>
  simp[] >> disch_then irule >>
  conj_tac
  >- (gvs[not_fresh_at_def] >> rpt strip_tac >> gvs[] >>
      `st.cs_next_var <= n'` by decide_tac >> metis_tac[]) >>
  qexistsl_tac [`cnt`, `data`, `off`, `p`] >>
  `eval_operand (Var (STRING #"%" (toString st.cs_next_var))) ss = SOME (n2w p)` by
    simp[Abbr `ss`, eval_operand_def, lookup_var_update_var] >>
  simp[] >> qspecl_then [`data`, `off`] mp_tac word_add_upper >> decide_tac
QED

Theorem compile_slice_data_live_mem_ok:
  !src_len src_data start len_op outsz sa op sb s len data off count p.
    compile_slice_data src_len src_data start len_op outsz sa = (op, sb) /\
    (!x z. MEM x [src_len;src_data;start;len_op] /\ x = Var z ==>
       not_fresh_at sa z) /\ alloca_next_valid s /\
    eval_operand src_len s = SOME len /\
    eval_operand src_data s = SOME data /\
    eval_operand start s = SOME off /\
    eval_operand len_op s = SOME count /\
    w2n data + w2n len <= s.vs_alloca_next /\
    32 + w2n count <= outsz /\ outsz < dimword (:256) /\
    FLOOKUP (abi_builtin_allocate_state (sa.cs_next_id + 6) outsz s).vs_allocas
      (sa.cs_next_id + 6) = SOME (p, outsz) /\
    p + outsz < dimword (:256) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt gen_tac >> strip_tac >> rename1 `eval_operand len_op s = SOME cnt` >>
  qpat_x_assum `compile_slice_data _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_slice_data_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> rename1 `compile_assert_slice_bounds start len_op src_len sa = (u, sc)` >>
  Cases_on `u` >> rename1 `compile_alloc_buffer outsz sc = (buf, st1)` >>
  gvs[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  drule (cj 3 builtinBytesMemoryTheory.slice_bounds_shape) >> strip_tac >>
  drule alloc_buffer_extends >> strip_tac >> qmatch_goalsub_abbrev_tac `emitted_insts sa sb1` >>
  `run_inst_seq_mem_ok
     (emitted_insts sa sc ++ (emitted_insts sc st1 ++
       [mk_inst st1.cs_next_id ADD [buf.buf_operand; Lit 32w]
          [STRING #"%" (toString st1.cs_next_var)];
        mk_inst (st1.cs_next_id + 1) ADD [src_data; start]
          [STRING #"%" (toString (st1.cs_next_var + 1))];
        mk_inst (st1.cs_next_id + 2) MCOPY
          [Var (STRING #"%" (toString st1.cs_next_var));
           Var (STRING #"%" (toString (st1.cs_next_var + 1))); len_op] [];
        mk_inst (st1.cs_next_id + 3) MSTORE [buf.buf_operand; len_op] []])) s` suffices_by
      (qmatch_goalsub_abbrev_tac `emitted_insts sc st1 ++ zs` >>
       `emitted_insts sa sb1 = emitted_insts sa sc ++ (emitted_insts sc st1 ++ zs)` by
         (irule emitted_insts_chain_suffix >> qexistsl_tac [`sc`, `st1`] >>
          simp[Abbr `sb1`, Abbr `zs`, APPEND_ASSOC]) >> simp[]) >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- (irule compile_assert_slice_bounds_mem_ok >> metis_tac[]) >> rpt strip_tac >>
  `(!z. start = Var z ==> not_fresh_at sa z) /\ (!z. len_op = Var z ==> not_fresh_at sa z) /\
   (!z. src_len = Var z ==> not_fresh_at sa z)` by metis_tac[] >>
  drule_all slice_bounds_run_frame >>
  Cases_on `off + cnt <+ off \/ len <+ off + cnt` >> gvs[] >> strip_tac >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`Abbrev (sb1 = _)`, `sc.cs_current_insts = _`, `st1.cs_current_insts = _`] >>
  `w2n off + w2n cnt <= w2n len` by
    (mp_tac (Q.INST [`a` |-> `w2n (off:bytes32)`, `n` |-> `w2n (cnt:bytes32)`, `limit` |-> `w2n (len:bytes32)`] slice_bounds_word) >>
     simp[n2w_w2n] >>
     map_every (fn q => qspec_then q mp_tac w2n_lt) [`off`, `cnt`, `len`] >>
     simp[dimword_def] >> decide_tac) >>
  `!x. MEM x [src_len;src_data;start;len_op] ==>
       eval_operand x s' = eval_operand x s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]
     >- metis_tac[] >>
     qpat_x_assum `s' = _` SUBST1_TAC >> simp[]) >>
  drule vars_only_alloca_frame >>
  disch_then (qspecl_then [`sa.cs_next_id + 6`, `outsz`] strip_assume_tac) >>
  drule builtinBytesMemoryTheory.slice_bounds_shape >> strip_tac >>
  irule slice_allocated_live_suffix_mem_ok >>
  simp[] >> conj_tac
  >- (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, DECIDE ``!n:num. n <= n + 5``]) >>
  qexistsl_tac [`len`, `outsz`, `p`] >> simp[] >> decide_tac
QED
