(* Counted-path consumers of the capacity-correct literal constructor. *)
Theory reasonLiteralConsumerPtr
Ancestors
  literalCapacityPtr reasonMemoryConsumerPtr revertReasonEntryPtr fragGasPathPtr
  exprSimLiteralBuffer fragGasSeqPtr fragExec context exprLoweringProps
  entrySinkExtraction loweringPosts bodyPtrDefs venomState words arithmetic
  list rich_list ptrDiscipline valueEncoding valueEncodingProps contractABI
  finite_map pred_set vfmConstants exprSimPtrLiteralBuffer emitHelper compileEnv exprSimCopy

Theorem literal_capacity_checked_endpoint:
  compile_bytelike_literal bs mx sa = (buf,sb) /\ fn_has_code sa sb fn /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> drule literal_bytelike_counted_shape >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, same_blocks_def] >>
     gvs[IS_PREFIX_APPEND] >> simp[DROP_APPEND1]) >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  gvs[same_blocks_def, ADD_COMM]
QED

Theorem literal_capacity_revert_resources:
  compile_bytelike_literal bs mx sa = (buf,sb) /\ LENGTH bs <= mx /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_has_code sa sb fn /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ 32+32*word_size mx < dimword(:256) ==>
  ?t b p Gf tnf.
    buf.buf_operand = Var p /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    stmt_state_rel ctx fn cenv cx es t /\
    lookup_var p t = SOME (n2w b) /\
    ptr_covers Gf tnf p t (32+contractABI$ceil32 (LENGTH bs)) /\
    mload b t = n2w (LENGTH bs) /\
    (!j. b <= j /\ j < b+32 ==> j NOTIN tnf.t_mem) /\
    b+32+32*word_size mx < dimword(:256) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,32+32*word_size mx) /\
    sa.cs_next_id < sb.cs_next_id /\ copy_old_operand sb (Var p)
Proof
  strip_tac >> drule_all literal_capacity_bytelike_ptr_run >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  drule_all literal_capacity_bytelike_alloca_mem >> strip_tac >>
  `word_size (LENGTH bs) <= word_size mx` by
    (simp[word_size_def] >> irule DIV_LE_MONOTONE >> decide_tac) >>
  `stmt_state_rel ctx fn cenv cx es t` by
    (irule literal_ptr_state_memory_frame >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
     qexistsl [`b`,`sa`,`sh`] >> asm_rewrite_tac[] >>
     rpt gen_tac >> disch_tac >>
     qpat_x_assum `u.vs_memory = s.vs_memory` (fn th => rewrite_tac[GSYM th]) >>
     first_x_assum irule >> decide_tac) >>
  `t.vs_allocas = u.vs_allocas` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = u` mp_tac >>
     disch_then (mp_tac o AP_TERM ``\s:venom_state. s.vs_allocas``) >> simp[]) >>
  drule literal_capacity_bytelike_shape >> strip_tac >>
  `sa.cs_next_id < sb.cs_next_id` by
    (qspec_then `sh'` mp_tac (Q.SPECL [`Var p'`,`bs:word8 list`,`32`] ci_mono_compile_store_byte_chunks) >>
     qspec_then `sm` mp_tac
       (Q.SPECL [`MSTORE`,`[Var p'; Lit (n2w (LENGTH (bs:word8 list)))]`] ci_mono_emit_void) >>
     gvs[ci_mono_def] >> decide_tac) >>
  `p' = p` by (qpat_x_assum `buf.buf_operand = Var p'` mp_tac >> simp[]) >>
  qpat_x_assum `p' = p` SUBST_ALL_TAC >>
  `copy_old_operand sb (Var p)` by
    (qspec_then `sh'` mp_tac
       (Q.SPECL [`Var p`,`bs:word8 list`,`32`] ci_mono_compile_store_byte_chunks) >>
     gvs[ci_mono_def, copy_old_operand_def, not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `b < dimword(:256)` by decide_tac >>
  qexistsl [`t`,`b`,`p`,`Gf`,`tnf`] >>
  simp[ptr_covers_def, contractABITheory.ceil32_def, word_size_def,
       mload_def, mem_word_at_def, w2n_n2w] >>
  conj_tac >- (fs[word_size_def]) >>
  fs[mem_word_at_def] >> rpt strip_tac >> simp[] >> decide_tac
QED

Theorem compile_literal_revert_path_ptr:
  compile_bytelike_literal bs mx sa = (buf,sm) /\ LENGTH bs <= mx /\
  compile_revert_with_reason cenv (LocatedValue msg_ty (base_ptr buf))
    mt ms sm = ((),sb) /\ ~is_word_type msg_ty /\
  fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  32+32*word_size mx < dimword(:256) /\
  32+contractABI$ceil32 (LENGTH bs) <= ms /\ LENGTH bs+63 < dimword(:256) /\
  64+ms < dimword(:256) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes
    (STRING #"%" (toString (sm.cs_next_var+k)))) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (Abort Revert_abort z)
Proof
  strip_tac >> drule_all literal_capacity_revert_resources >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  drule_all literal_capacity_checked_endpoint >> strip_tac >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  `?z Gh th. gas_path_ptr D 0 ctx fn PG Gf tnf u 0 Gh th (Abort Revert_abort z)` by
    (irule compile_revert_reason_memory_path_ptr >> simp[Abbr `u`] >>
     goal_assum (drule_at (Pat `compile_revert_with_reason _ _ _ _ _ = _`)) >>
     qexistsl [`n2w b`,`LENGTH bs`,`cx`,`es`,`base_ptr buf`,`p`,`msg_ty`] >>
     `b < dimword(:256)` by decide_tac >>
     simp[base_ptr_def, is_word_type_def, w2n_n2w, ADD_COMM,
          stmt_state_rel_inst_idx] >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!k. k < 3 ==> not_local_ptr _ _ _` (qspec_then `k` mp_tac) >>
       simp[ADD_COMM]) >>
     conj_tac >- (qpat_x_assum `mload b t = _` mp_tac >> simp[mload_def]) >>
     conj_tac >- (qpat_x_assum `lookup_var p t = _` mp_tac >> simp[lookup_var_def]) >>
     reverse conj_tac >- metis_tac[ADD_COMM] >>
     disj1_tac >> qexistsl [`sa.cs_next_id`,`b`,`32+32*word_size mx`] >>
     simp[] >> decide_tac) >>
  drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ (OK _)`) gas_path_ptr_then >>
  disch_then drule >> simp[NoAsms] >> metis_tac[]
QED
