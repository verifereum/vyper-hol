(* Memory footprints of the byte builtins' straight-line fragments. *)
Theory builtinBytesMemory
Ancestors
  builtinBytes allocaFootprint fragExecMem instMemFrontier abiBuiltinAllocation
  exprLoweringProps emitHelperProps emitHelper compileEnv context venomInst
  venomState venomExecSemantics venomMemDefs finite_map list words arithmetic

Theorem slice_bounds_shape:
  compile_assert_slice_bounds a n limit sa = ((), sb) ==>
  sb.cs_next_var = sa.cs_next_var + 5 /\
  sb.cs_next_id = sa.cs_next_id + 6 /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id ADD [a; n]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) LT
       [Var (STRING #"%" (toString sa.cs_next_var)); a]
       [STRING #"%" (toString (sa.cs_next_var + 1))];
     mk_inst (sa.cs_next_id + 2) GT
       [Var (STRING #"%" (toString sa.cs_next_var)); limit]
       [STRING #"%" (toString (sa.cs_next_var + 2))];
     mk_inst (sa.cs_next_id + 3) OR
       [Var (STRING #"%" (toString (sa.cs_next_var + 1)));
        Var (STRING #"%" (toString (sa.cs_next_var + 2)))]
       [STRING #"%" (toString (sa.cs_next_var + 3))];
     mk_inst (sa.cs_next_id + 4) ISZERO
       [Var (STRING #"%" (toString (sa.cs_next_var + 3)))]
       [STRING #"%" (toString (sa.cs_next_var + 4))];
     mk_inst (sa.cs_next_id + 5) ASSERT
       [Var (STRING #"%" (toString (sa.cs_next_var + 4)))] []]
Proof
  simp[compile_assert_slice_bounds_def, comp_bind_def, comp_ignore_bind_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, same_blocks_def]
QED

Theorem compile_assert_slice_bounds_mem_ok:
  !start len src_len sa sb s.
    compile_assert_slice_bounds start len src_len sa = ((), sb) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >> drule slice_bounds_shape >> strip_tac >>
  gvs[] >> irule run_inst_seq_mem_ok_every >>
  simp[EVERY_DEF, mk_inst_def] >> rpt conj_tac >> gen_tac >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem eval_operand_update_not_fresh[local]:
  !sa a ss n w. (!z. a = Var z ==> not_fresh_at sa z) /\ sa.cs_next_var <= n ==>
    eval_operand a (update_var (STRING #"%" (toString n)) w ss) = eval_operand a ss
Proof
  gen_tac >> Cases >> simp[eval_operand_def, lookup_var_update_var] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[]
QED

Theorem slice_bounds_mod[local]:
  !modulus a n limit. a < modulus /\ n < modulus /\ limit < modulus ==>
  ((a + n) MOD modulus < a \/ limit < (a + n) MOD modulus <=>
   modulus <= a + n \/ limit < a + n)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `a + n < modulus`
  >- simp[LESS_MOD] >>
  `a + n < 2 * modulus` by decide_tac >>
  `(a + n) MOD modulus = a + n - modulus` by
    (irule MOD_UNIQUE >> qexists_tac `1` >> simp[] >> decide_tac) >>
  simp[] >> decide_tac
QED

Theorem slice_bounds_ok[local]:
  compile_assert_slice_bounds a n limit sa = ((), sb) /\
  fresh_vars_wrt sa s /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  w2n wa + w2n wn <= w2n wl /\
  t = s with vs_vars := t.vs_vars /\
  fresh_vars_wrt sb t /\
  (!x w. eval_operand x s = SOME w ==> eval_operand x t = SOME w)
Proof
  strip_tac >>
  `!x w z. eval_operand x s = SOME w /\ x = Var z ==> not_fresh_at sa z` by
    (rw[not_fresh_at_def] >>
     metis_tac[fresh_vars_wrt_eval_operand, GREATER_EQ]) >>
  `!j w ss. sa.cs_next_var <= j ==>
      eval_operand a (update_var (STRING #"%" (toString j)) w ss) = eval_operand a ss` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  `!j w ss. sa.cs_next_var <= j ==>
      eval_operand limit (update_var (STRING #"%" (toString j)) w ss) = eval_operand limit ss` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  drule slice_bounds_shape >> strip_tac >>
  Cases_on `w2n (wa + wn) < w2n wa` >>
  Cases_on `w2n wl < w2n (wa + wn)` >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, exec_pure1_def, bool_to_word_def,
       eval_operand_def, lookup_var_update_var, WORD_OR_CLAUSES,
       bool_to_word_def] >>
  strip_tac >> gvs[] >>
  conj_tac
  >- (qspec_then `dimword (:256)` mp_tac slice_bounds_mod >>
      disch_then (qspecl_then [`w2n wa`, `w2n wn`, `w2n wl`] mp_tac) >>
      gvs[word_add_def, w2n_n2w, w2n_lt]) >>
  conj_tac
  >- simp[update_var_def] >>
  conj_tac
  >- (gvs[fresh_vars_wrt_def, update_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  `!j v ss. sa.cs_next_var <= j ==>
      eval_operand x (update_var (STRING #"%" (toString j)) v ss) = eval_operand x ss` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  simp[]
QED

Theorem compile_bytestring_src_mem_ok:
  !src sa result sb s p.
    compile_bytestring_src src sa = (result, sb) /\
    eval_operand src s = SOME p /\ w2n p + 32 <= s.vs_alloca_next ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[compile_bytestring_src_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       run_inst_seq_mem_ok_cons, below_frontier_MLOAD] >>
  Cases_on `step_inst_base
    (mk_inst sa.cs_next_id MLOAD [src]
      [STRING #"%" (toString sa.cs_next_var)]) s` >>
  simp[run_inst_seq_mem_ok_last] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

(* The successful bounds check limits the load to the source interval.
   Failing checks terminate before the load. *)
Theorem word_add_upper[local]:
  !a b : bytes32. w2n (a + b) <= w2n a + w2n b
Proof
  simp[word_add_def, w2n_n2w, MOD_LESS_EQ]
QED

Theorem compile_extract32_load_mem_ok:
  !src_len src_data start sa op sb s len data off.
    compile_extract32_load src_len src_data start sa = (op, sb) /\
    fresh_vars_wrt sa s /\
    eval_operand src_len s = SOME len /\
    eval_operand src_data s = SOME data /\
    eval_operand start s = SOME off /\
    w2n data + w2n len <= s.vs_alloca_next ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_assert_slice_bounds start (Lit 32w) src_len sa` >>
  rename1 `compile_assert_slice_bounds start (Lit 32w) src_len sa = (u, sc)` >>
  Cases_on `u` >> gvs[] >>
  rename1 `compile_assert_slice_bounds start (Lit 32w) src_len sa = ((), sc)` >>
  drule slice_bounds_shape >> strip_tac >>
  qpat_x_assum `compile_extract32_load _ _ _ _ = _` mp_tac >>
  simp[compile_extract32_load_def, comp_bind_def, comp_ignore_bind_def,
       emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def,
       emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       rich_listTheory.DROP_APPEND2] >>
  `run_inst_seq_mem_ok
     (emitted_insts sa sc ++
      [mk_inst (sa.cs_next_id + 6) ADD [src_data; start]
         [STRING #"%" (toString (sa.cs_next_var + 5))];
       mk_inst (sa.cs_next_id + 7) MLOAD
         [Var (STRING #"%" (toString (sa.cs_next_var + 5)))]
         [STRING #"%" (toString (sa.cs_next_var + 6))]]) s` suffices_by simp[] >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- (irule compile_assert_slice_bounds_mem_ok >> metis_tac[]) >>
  qpat_x_assum `emitted_insts _ _ = _` kall_tac >>
  qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
  rpt strip_tac >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all slice_bounds_ok >> strip_tac >>
  fs[dimword_def] >>
  `eval_operand src_data s' = SOME data /\ eval_operand start s' = SOME off` by metis_tac[] >>
  `s'.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `s' = s with vs_vars := _` mp_tac >>
     simp[venom_state_component_equality]) >>
  simp[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       run_inst_seq_mem_ok_last, below_frontier_MLOAD,
       eval_operand_def, lookup_var_update_var, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE] >>
  qspecl_then [`data`, `off`] mp_tac word_add_upper >> decide_tac
QED

Theorem mcopy_operand_frame[local]:
  eval_operand x (mcopy dst src n s) = eval_operand x s /\
  (mcopy dst src n s).vs_alloca_next = s.vs_alloca_next
Proof
  conj_tac
  >- (irule eval_operand_same_vars >>
      simp[mcopy_def, write_memory_with_expansion_def]) >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem slice_copy_store_mem_ok[local]:
  !st s buf_op src start count_op p data off count.
    fresh_vars_wrt st s /\
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
  `!x w j v ss. eval_operand x s = SOME w /\ st.cs_next_var <= j ==>
      eval_operand x (update_var (STRING #"%" (toString j)) v ss) = eval_operand x ss` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `st` >> simp[not_fresh_at_def] >>
     metis_tac[fresh_vars_wrt_eval_operand, GREATER_EQ]) >>
  `p < dimword (:256)` by decide_tac >>
  `n2w p + 32w = (n2w (p + 32):bytes32)` by simp[word_add_n2w] >>
  `!id ops outs t. inst_mem_below_frontier (mk_inst id ADD ops outs) t` by
    (rpt gen_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
       below_frontier_MCOPY, below_frontier_MSTORE,
       step_inst_base_opcode_eqs, mk_inst_def, mcopy_operand_frame,
       exec_pure2_def, eval_operand_def, lookup_var_update_var]
QED

Theorem allocate_frontier_mono[local]:
  s.vs_alloca_next <= (abi_builtin_allocate_state id n s).vs_alloca_next
Proof
  Cases_on `FLOOKUP s.vs_allocas id = NONE` >>
  simp[abi_builtin_allocate_state_def]
QED

Theorem slice_allocated_suffix_mem_ok[local]:
  !st buf st1 n s src start count_op (len:bytes32) data off count p.
    compile_alloc_buffer n st = (buf, st1) /\
    fresh_vars_wrt st s /\ alloca_next_valid s /\
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
  drule_all compile_alloc_buffer_mem_ok >> strip_tac >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac >- simp[] >>
  qmatch_asmsub_abbrev_tac `step_inst_base _ s = OK ss` >>
  simp[run_inst_seq_def] >> rpt strip_tac >> gvs[] >>
  `!x w. eval_operand x s = SOME w ==> eval_operand x ss = SOME w` by
    (rpt strip_tac >> simp[Abbr `ss`] >>
     irule eval_operand_update_unbound >> simp[] >>
     irule fresh_vars_wrt_next >> qexists_tac `st` >> simp[]) >>
  `eval_operand buf.buf_operand ss = SOME (n2w p)` by
    simp[Abbr `ss`, eval_operand_def, lookup_var_update_var] >>
  `s.vs_alloca_next <= ss.vs_alloca_next` by
    simp[Abbr `ss`, allocate_frontier_mono] >>
  `p + buf.buf_size <= ss.vs_alloca_next` by simp[Abbr `ss`] >>
  qspec_then `st1` mp_tac slice_copy_store_mem_ok >>
  simp[] >> disch_then irule >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`cnt`, `data`, `off`, `p`] >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  qspecl_then [`data`, `off`] mp_tac word_add_upper >> decide_tac
QED

Theorem alloc_buffer_extends[local]:
  compile_alloc_buffer n st = (buf, st1) ==>
  st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emitHelperTheory.emit_op_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]
QED

Theorem emitted_insts_chain_suffix[local]:
  !sa sc st sb xs ys zs.
    sc.cs_current_insts = sa.cs_current_insts ++ xs /\
    st.cs_current_insts = sc.cs_current_insts ++ ys /\
    sb.cs_current_insts = st.cs_current_insts ++ zs ==>
    emitted_insts sa sb = xs ++ (ys ++ zs)
Proof
  rpt strip_tac >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       rich_listTheory.DROP_APPEND2]
QED

Theorem vars_only_alloca_frame[local]:
  !s t id n. t = s with vs_vars := t.vs_vars ==>
    (alloca_next_valid t <=> alloca_next_valid s) /\
    t.vs_alloca_next = s.vs_alloca_next /\
    (abi_builtin_allocate_state id n t).vs_allocas =
      (abi_builtin_allocate_state id n s).vs_allocas
Proof
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >>
  Cases_on `FLOOKUP s.vs_allocas id = NONE` >>
  simp[alloca_next_valid_def, abi_builtin_allocate_state_def]
QED

(* The ALLOCA follows the six instructions of the bounds check.  The site
   can be fresh or reused by a loop; its recorded size must agree. *)
Theorem compile_slice_data_mem_ok:
  !src_len src_data start len_op outsz sa op sb s len data off count p.
    compile_slice_data src_len src_data start len_op outsz sa = (op, sb) /\
    fresh_vars_wrt sa s /\ alloca_next_valid s /\
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
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `compile_assert_slice_bounds start len_op src_len sa = (u, sc)` >>
  Cases_on `u` >>
  rename1 `compile_alloc_buffer outsz sc = (buf, st1)` >>
  gvs[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  drule (cj 3 slice_bounds_shape) >> strip_tac >>
  drule alloc_buffer_extends >> strip_tac >>
  qmatch_goalsub_abbrev_tac `emitted_insts sa sb1` >>
  `run_inst_seq_mem_ok
     (emitted_insts sa sc ++ (emitted_insts sc st1 ++
       [mk_inst st1.cs_next_id ADD [buf.buf_operand; Lit 32w]
          [STRING #"%" (toString st1.cs_next_var)];
        mk_inst (st1.cs_next_id + 1) ADD [src_data; start]
          [STRING #"%" (toString (st1.cs_next_var + 1))];
        mk_inst (st1.cs_next_id + 2) MCOPY
          [Var (STRING #"%" (toString st1.cs_next_var));
           Var (STRING #"%" (toString (st1.cs_next_var + 1))); len_op] [];
        mk_inst (st1.cs_next_id + 3) MSTORE [buf.buf_operand; len_op] []])) s`
    suffices_by
      (qmatch_goalsub_abbrev_tac `emitted_insts sc st1 ++ zs` >>
       `emitted_insts sa sb1 =
          emitted_insts sa sc ++ (emitted_insts sc st1 ++ zs)` by
         (irule emitted_insts_chain_suffix >> qexistsl_tac [`sc`, `st1`] >>
          simp[Abbr `sb1`, Abbr `zs`, APPEND_ASSOC]) >> simp[]) >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- (irule compile_assert_slice_bounds_mem_ok >> metis_tac[]) >>
  rpt strip_tac >> drule_all slice_bounds_ok >> strip_tac >>
  qpat_x_assum `Abbrev (sb1 = _)` kall_tac >>
  qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
  qpat_x_assum `st1.cs_current_insts = _` kall_tac >>
  drule vars_only_alloca_frame >>
  disch_then (qspecl_then [`sa.cs_next_id + 6`, `outsz`] strip_assume_tac) >>
  drule (cj 2 slice_bounds_shape) >> strip_tac >>
  irule slice_allocated_suffix_mem_ok >>
  simp[] >> qexistsl_tac [`cnt`, `data`, `len`, `outsz`, `off`, `p`] >>
  simp[] >> decide_tac
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BYTE_MEMORY_KERNEL_AUDIT OK\n"
     else raise Fail "byte memory footprint inherited admission"
  end) [compile_assert_slice_bounds_mem_ok, compile_bytestring_src_mem_ok,
        compile_extract32_load_mem_ok, compile_slice_data_mem_ok];


(* Probe the body entry boundary: a source-visible local owns enough room
   for the bytestring header read, including an unsuccessful read prefix. *)
Theorem compile_bytestring_src_local_mem_ok:
  !ctx func cenv cx es s name entry p sz sa result sb.
    stmt_state_rel ctx func cenv cx es s /\
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    32 <= sz /\
    compile_bytestring_src (Var p) sa = (result, sb) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all local_ptr_below_frontier >> strip_tac >>
  irule compile_bytestring_src_mem_ok >>
  qexistsl_tac [`w`, `result`, `Var p`] >>
  simp[eval_operand_def] >> decide_tac
QED

(* Actual allocation followed by its header store.  Site reuse is allowed;
   the allocation lookup identifies the reused region's size. *)
Theorem compile_alloc_buffer_header_store_mem_ok:
  !n sa buf sm value sb s p.
    compile_alloc_buffer n sa = (buf, sm) /\
    emit_void MSTORE [buf.buf_operand; value] sm = ((), sb) /\
    fresh_vars_wrt sa s /\ alloca_next_valid s /\
    FLOOKUP (abi_builtin_allocate_state sa.cs_next_id n s).vs_allocas
      sa.cs_next_id = SOME (p,n) /\
    32 <= n /\ n < dimword (:256) ==>
    run_inst_seq_mem_ok
      (emitted_insts sa sm ++ emitted_insts sm sb) s
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_alloc_buffer_mem_ok >> strip_tac >>
  irule run_inst_seq_mem_ok_append >> simp[] >>
  rpt strip_tac >>
  gvs[run_inst_seq_def] >>
  irule emit_mstore_mem_ok >>
  goal_assum (drule_at Any) >>
  qexists_tac `n2w p` >>
  simp[eval_operand_def, lookup_var_update_var] >>
  `p MOD dimword (:256) <= p` by simp[MOD_LESS_EQ] >>
  decide_tac
QED

