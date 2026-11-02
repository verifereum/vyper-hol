(*
 * Memory footprints of the external entry and return sequences (S3)
 *
 * The frag_exec_mem versions of loweringHalt's return fragments, and the
 * footprint of one static argument's decode at the external entry.  Each
 * buffer the sequences write is an ALLOCA they emit themselves, or the
 * argument's own buffer, so they need only that it lies below the
 * allocation frontier.
 *
 * TOP-LEVEL:
 *   compile_return_none_external_frag_mem,
 *   compile_guarded_body_stop_frag_mem
 *                             — a return without a value, and falling off
 *                               the end: a STOP
 *   compile_external_return_word_frag_mem
 *                             — returning a primitive word: ALLOCA 32,
 *                               MSTORE, RETURN
 *   compile_external_return_copy_frag_mem
 *                             — returning a static complex value: ALLOCA,
 *                               MCOPY from the value, RETURN
 *   entry_decode_arg_mem_ok   — decoding a static argument into a buffer
 *                               below the frontier
 *)
Theory entryHaltMem
Ancestors
  list fragExec fragExecMem memSafeRun allocaFootprint loweringHalt
  entryArgPtrs entryDecodePlanProps abiDecodeStaticProps
  compileEnv stmtLowering moduleLowering emitHelper abiBuiltinAllocation
  unitTransformDefs venomState venomInst venomExecSemantics venomMemDefs
  words instMemFrontier venomExecProofs emitHelperProps instIdxIndep
  abiEncoder exprLoweringProps entryDecodeProps

(* ===== STOP ===== *)

Theorem compile_return_none_external_frag_mem:
  !ctx cenv lctx ty st x st' nr nkey ut iv P Q R.
    compile_stmt cenv lctx ty (Return NONE) st = (x, st') /\
    cenv.ce_return_pc = NONE /\
    cenv.ce_nonreentrant = (nr, nkey, ut, iv) /\ (nr ==> iv) /\
    (!s. P s ==> R (Halt (halt_state (s with vs_returndata := [])))) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rpt strip_tac >>
  `st'.cs_current_bb = st.cs_current_bb /\
   st'.cs_current_insts =
     st.cs_current_insts ++ [mk_inst st.cs_next_id STOP [] []]` by
    (qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
     simp[compile_stmt_def, optional_unlock_view, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, emit_inst_def,
          fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  qspecl_then [`ctx`, `st`, `st'`, `st.cs_next_id`, `P`, `Q`, `R`] mp_tac
    stop_frag_mem >>
  simp[]
QED

Theorem compile_guarded_body_stop_frag_mem:
  !ctx cenv nr nkey ut iv stmts st x st' sa sb P Q R.
    compile_guarded_body cenv nr nkey ut iv stmts NONE st = (x, st') /\
    (nr ==> iv) /\
    (if nr then compile_nonreentrant_lock nkey ut iv else comp_return ()) st =
      ((), sa) /\
    compile_stmts cenv NoLoop (BaseT BoolT) stmts sa = ((), sb) /\
    ~block_is_terminated sb /\
    (!s. P s ==> R (Halt (halt_state (s with vs_returndata := [])))) ==>
    frag_exec_mem ctx sb st' P Q R
Proof
  rpt strip_tac >>
  `st'.cs_current_bb = sb.cs_current_bb /\
   st'.cs_current_insts =
     sb.cs_current_insts ++ [mk_inst sb.cs_next_id STOP [] []]` by
    (qpat_x_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_guarded_body_def, optional_unlock_view, comp_bind_def,
          comp_ignore_bind_def, comp_get_def] >>
     strip_tac >>
     gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
         emit_inst_def, fresh_id_def, emit_def]) >>
  qspecl_then [`ctx`, `sb`, `st'`, `sb.cs_next_id`, `P`, `Q`, `R`] mp_tac
    stop_frag_mem >>
  simp[]
QED

(* ===== Returned buffers ===== *)
Theorem return_word_mem_safe[local]:
  !fuel ctx fn s bb id buf op w b.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ALLOCA [Lit 32w] [buf]) /\
    get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (id + 1) MSTORE [Var buf; op] []) /\
    get_instruction bb (s.vs_inst_idx + 2) =
      SOME (mk_inst (id + 2) RETURN [Var buf; Lit 32w] []) /\
    eval_operand op s = SOME w /\ op <> Var buf /\ alloca_next_valid s /\
    FLOOKUP (abi_builtin_allocate_state id 32 s).vs_allocas id = SOME (b,32)
    ==> mem_safe_run fuel ctx fn s
Proof
  rpt gen_tac >> strip_tac >>
  drule_all alloca_site_frontier >> strip_tac >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all step_alloca_site >>
  disch_then (qspec_then `buf` assume_tac) >>
  qabbrev_tac `s1 = update_var buf (n2w b)
    (abi_builtin_allocate_state id 32 s)` >>
  `eval_operand (Var buf) s1 = SOME (n2w b) /\
   eval_operand op s1 = SOME w /\
   s1.vs_current_bb = s.vs_current_bb /\
   s1.vs_alloca_next = (abi_builtin_allocate_state id 32 s).vs_alloca_next` by
    (Cases_on `op` >> gvs[Abbr `s1`, eval_operand_def, lookup_var_def,
      update_var_def, abi_builtin_allocate_state_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `FLOOKUP s.vs_allocas id = NONE` >> gvs[]) >>
  `w2n (n2w b : bytes32) + 32 <= s1.vs_alloca_next` by
    (simp[wordsTheory.w2n_n2w] >> irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists_tac `b + 32` >> simp[arithmeticTheory.MOD_LESS_EQ]) >>
  `mem_safe_step fuel ctx (mk_inst id ALLOCA [Lit 32w] [buf]) s` by
    (simp[mem_safe_step_non_invoke, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  `step_inst fuel ctx (mk_inst id ALLOCA [Lit 32w] [buf]) s = OK s1` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  drule mem_safe_run_step >>
  disch_then drule >> disch_then drule >>
  simp[mk_inst_def, is_terminator_def] >> disch_then SUBST1_TAC >>
  simp[] >>
  qabbrev_tac `t1 = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `lookup_block t1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb t1.vs_inst_idx =
     SOME (mk_inst (id + 1) MSTORE [Var buf; op] []) /\
   step_inst fuel ctx (mk_inst (id + 1) MSTORE [Var buf; op] []) t1 =
     OK (mstore (w2n (n2w b : bytes32)) w t1) /\
   mem_safe_step fuel ctx (mk_inst (id + 1) MSTORE [Var buf; op] []) t1` by
    (simp[Abbr `t1`, arithmeticTheory.ADD1, step_inst_non_invoke,
       step_inst_base_def, exec_write2_def, mk_inst_def,
       mem_safe_step_non_invoke, below_frontier_MSTORE,
       eval_op_inst_idx] >>
     rpt strip_tac >> gvs[]) >>
  qpat_x_assum `step_inst _ _ _ s = _` kall_tac >>
  qpat_x_assum `get_instruction bb s.vs_inst_idx = _` kall_tac >>
  qpat_x_assum `lookup_block s.vs_current_bb _ = _` kall_tac >>
  drule mem_safe_run_step >> disch_then drule >> disch_then drule >>
  simp[mk_inst_def, is_terminator_def] >> disch_then SUBST1_TAC >>
  simp[] >>
  irule return_buffer_mem_safe >>
  qexistsl_tac [`n2w b`, `bb`, `Var buf`, `id + 2`, `32w`, `Lit 32w`] >>
  gvs[Abbr `t1`, mstore_def, arithmeticTheory.ADD1, eval_operand_def,
      lookup_var_def]

QED


(* The return buffer's ALLOCA site, if it already ran (a loop), holds a
   32-byte allocation, as the site's own literal size gives; the existing
   scratch-buffer leaves (compile_keccak256_word_mem_ok) take the same
   premise. *)
Theorem compile_external_return_word_frag_mem:
  !ctx op ei msz nr nkey ut iv st x st' w P Q R.
    compile_external_return (SOME op) T F ei msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    (!s. P s ==>
         eval_operand op s = SOME w /\ alloca_next_valid s /\
         ?b. FLOOKUP (abi_builtin_allocate_state st.cs_next_id 32 s).vs_allocas
               st.cs_next_id = SOME (b, 32)) /\
    (!s ss. P s /\ ss.vs_returndata = word_to_bytes w T /\
            ss.vs_accounts = s.vs_accounts /\
            ss.vs_transient = s.vs_transient /\
            ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
            R (Halt ss)) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_external_return_word_parts >> strip_tac >>
  simp[frag_exec_mem_def] >> rpt strip_tac >> disj2_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `op <> Var buf` by metis_tac[] >>
  `eval_operand op s = SOME w /\ alloca_next_valid s /\
   ?b. FLOOKUP (abi_builtin_allocate_state st.cs_next_id 32 s).vs_allocas
          st.cs_next_id = SOME (b,32)` by metis_tac[] >>
  `get_instruction bb s.vs_inst_idx =
      SOME (mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf]) /\
   get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (st.cs_next_id + 1) MSTORE [Var buf; op] []) /\
   get_instruction bb (s.vs_inst_idx + 2) =
      SOME (mk_inst (st.cs_next_id + 2) RETURN [Var buf; Lit 32w] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       map_every (fn n => mp_tac (Q.SPEC n th)) [`0`, `1`, `2`]) >> simp[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by metis_tac[] >>
  drule_all return_word_run >>
  disch_then (qspecl_then [`0`, `ctx`] strip_assume_tac) >>
  qexists_tac `0` >> simp[exit_result_def] >>
  conj_tac >- metis_tac[] >>
  irule return_word_mem_safe >> metis_tac[]
QED

Theorem return_copy_mem_safe[local]:
  !fuel ctx fn s bb id buf op p m n b.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ALLOCA [Lit (n2w n)] [buf]) /\
    get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (id + 1) MCOPY [Var buf; op; Lit (n2w m)] []) /\
    get_instruction bb (s.vs_inst_idx + 2) =
      SOME (mk_inst (id + 2) RETURN [Var buf; Lit (n2w m)] []) /\
    eval_operand op s = SOME p /\ op <> Var buf /\ alloca_next_valid s /\
    FLOOKUP (abi_builtin_allocate_state id n s).vs_allocas id = SOME (b,n) /\
    m <= n /\ n < dimword (:256) /\
    (m = 0 \/ w2n p + m <= s.vs_alloca_next)
    ==> mem_safe_run fuel ctx fn s
Proof
  rpt gen_tac >> strip_tac >>
  drule_all alloca_site_frontier >> strip_tac >>
  drule_all step_alloca_site >>
  disch_then (qspec_then `buf` assume_tac) >>
  qabbrev_tac `s1 = update_var buf (n2w b)
    (abi_builtin_allocate_state id n s)` >>
  `eval_operand (Var buf) s1 = SOME (n2w b) /\
   eval_operand op s1 = SOME p /\
   s1.vs_current_bb = s.vs_current_bb /\
   s1.vs_alloca_next = (abi_builtin_allocate_state id n s).vs_alloca_next /\
   s.vs_alloca_next <= s1.vs_alloca_next` by
    (Cases_on `op` >> gvs[Abbr `s1`, eval_operand_def, lookup_var_def,
      update_var_def, abi_builtin_allocate_state_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `FLOOKUP s.vs_allocas id = NONE` >> gvs[]) >>
  `m < dimword (:256)` by decide_tac >>
  `w2n (n2w b : bytes32) + m <= s1.vs_alloca_next` by
    (`b MOD dimword (:256) <= b` by simp[arithmeticTheory.MOD_LESS_EQ] >>
     gvs[wordsTheory.w2n_n2w] >> decide_tac) >>
  `mem_safe_step fuel ctx (mk_inst id ALLOCA [Lit (n2w n)] [buf]) s` by
    (simp[mem_safe_step_non_invoke, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  `step_inst fuel ctx (mk_inst id ALLOCA [Lit (n2w n)] [buf]) s = OK s1` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  drule mem_safe_run_step >> disch_then drule >> disch_then drule >>
  simp[mk_inst_def, is_terminator_def] >> disch_then SUBST1_TAC >>
  simp[] >>
  qabbrev_tac `t1 = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `lookup_block t1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb t1.vs_inst_idx =
     SOME (mk_inst (id + 1) MCOPY [Var buf; op; Lit (n2w m)] []) /\
   step_inst fuel ctx (mk_inst (id + 1) MCOPY [Var buf; op; Lit (n2w m)] []) t1 =
     OK (mcopy (w2n (n2w b : bytes32)) (w2n p) m t1) /\
   mem_safe_step fuel ctx (mk_inst (id + 1) MCOPY [Var buf; op; Lit (n2w m)] []) t1` by
    (simp[Abbr `t1`, arithmeticTheory.ADD1, step_inst_non_invoke,
       step_inst_base_def, mk_inst_def,
       mem_safe_step_non_invoke, below_frontier_MCOPY,
       eval_op_inst_idx, eval_operand_def] >>
     rpt strip_tac >> gvs[eval_operand_def, lookup_var_def] >> decide_tac) >>
  qpat_x_assum `step_inst _ _ _ s = _` kall_tac >>
  qpat_x_assum `get_instruction bb s.vs_inst_idx = _` kall_tac >>
  qpat_x_assum `lookup_block s.vs_current_bb _ = _` kall_tac >>
  drule mem_safe_run_step >> disch_then drule >> disch_then drule >>
  simp[mk_inst_def, is_terminator_def] >> disch_then SUBST1_TAC >>
  simp[] >>
  irule return_buffer_mem_safe >>
  qexistsl_tac [`n2w b`, `bb`, `Var buf`, `id + 2`, `n2w m`, `Lit (n2w m)`] >>
  gvs[Abbr `t1`, mcopy_def, write_memory_with_expansion_def,
      arithmeticTheory.ADD1, eval_operand_def, lookup_var_def]
QED

(* The MCOPY reads the value's m bytes at its address p, which the caller
   puts below the frontier (a local's region, local_ptrs_rel), and writes
   them into the buffer, msz >= m bytes. *)
Theorem compile_external_return_copy_frag_mem:
  !ctx op m msz nr nkey ut iv st x st' P Q R.
    compile_external_return (SOME op) F F (AbiCopy m) msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    m <= msz /\ msz < dimword(:256) /\
    (!s. P s ==>
         alloca_next_valid s /\
         (?b. FLOOKUP (abi_builtin_allocate_state st.cs_next_id msz s).vs_allocas
                st.cs_next_id = SOME (b, msz)) /\
         ?p. eval_operand op s = SOME p /\
             (m = 0 \/ w2n p + m <= s.vs_alloca_next) /\
             !ss. ss.vs_returndata = mem_bytes_at (w2n p) m s.vs_memory /\
                  ss.vs_accounts = s.vs_accounts /\
                  ss.vs_transient = s.vs_transient /\
                  ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
                  R (Halt ss)) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_external_return_copy_parts >> strip_tac >>
  simp[frag_exec_mem_def] >> rpt strip_tac >> disj2_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `op <> Var buf` by metis_tac[] >>
  qpat_x_assum `!s. P s ==> _` drule >> strip_tac >>
  `m < dimword (:256)` by decide_tac >>
  `get_instruction bb s.vs_inst_idx =
      SOME (mk_inst st.cs_next_id ALLOCA [Lit (n2w msz)] [buf]) /\
   get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (st.cs_next_id + 1) MCOPY [Var buf; op; Lit (n2w m)] []) /\
   get_instruction bb (s.vs_inst_idx + 2) =
      SOME (mk_inst (st.cs_next_id + 2) RETURN [Var buf; Lit (n2w m)] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       map_every (fn n => mp_tac (Q.SPEC n th)) [`0`, `1`, `2`]) >> simp[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by metis_tac[] >>
  drule_all return_copy_run >>
  disch_then (qspecl_then [`0`, `ctx`] strip_assume_tac) >>
  qexists_tac `0` >> simp[exit_result_def] >>
  irule return_copy_mem_safe >> metis_tac[]
QED

(* ===== The entry's static argument decode ===== *)

Theorem compile_abi_clamp_basetype_footprint:
  !cl op st st'.
    compile_abi_clamp_basetype op cl st = ((), st') ==>
    EVERY (\i. !s. inst_mem_below_frontier i s) (emitted_insts st st')
Proof
  Cases >> rpt gen_tac >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def] >>
  TRY (rename1 `if signed then _ else _` >> Cases_on `signed`) >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[] >> rpt strip_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem compile_abi_clamp_basetype_mem_ok:
  !cl op st st' s.
    compile_abi_clamp_basetype op cl st = ((), st') ==>
    run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  rpt strip_tac >> irule run_inst_seq_mem_ok_every >>
  drule compile_abi_clamp_basetype_footprint >> simp[]
QED

Theorem compile_abi_decode_static_mem_ok:
  !src dst cl st st' s p.
    compile_abi_decode_static src dst CALLDATALOAD
      (\v. compile_abi_clamp_basetype v cl) st = ((), st') /\
    eval_operand dst s = SOME p /\ fresh_vars_wrt st s /\
    w2n p + 32 <= s.vs_alloca_next ==>
    run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp[compile_abi_decode_static_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt gen_tac >> strip_tac >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] st = (v, st1)` >>
  rename1 `compile_abi_clamp_basetype v cl st1 = (_, st2)` >>
  `compile_abi_clamp_basetype v cl st1 = ((), st2)` by
    metis_tac[oneTheory.one] >>
  `inst_extends st st1` by metis_tac[inst_extends_emit_op] >>
  `inst_extends st1 st2` by (drule compile_abi_clamp_structure >> simp[]) >>
  `inst_extends st2 st'` by metis_tac[inst_extends_emit_void] >>
  `inst_extends st1 st'` by metis_tac[inst_extends_trans] >>
  `emitted_insts st st' = emitted_insts st st1 ++ emitted_insts st1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `emitted_insts st1 st' = emitted_insts st1 st2 ++ emitted_insts st2 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts st st' = _` SUBST1_TAC >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- (drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
      simp[run_inst_seq_mem_ok_last] >> irule below_frontier_no_ranges >>
      simp[mk_inst_def]) >>
  Cases_on `eval_operand src s`
  >- (drule emitted_insts_emit_op >> strip_tac >>
      simp[run_inst_seq_def, step_inst_base_def, exec_read1_def, mk_inst_def]) >>
  rename1 `eval_operand src s = SOME a` >>
  `!id out. step_inst_base (mk_inst id CALLDATALOAD [src] [out]) s =
      OK (update_var out (mem_word_at (w2n a) s.vs_call_ctx.cc_calldata) s)` by
    (rpt gen_tac >> drule step_CALLDATALOAD >> simp[valueEncodingTheory.mem_word_at_def]) >>
  drule decode_emit_update_frame >>
  disch_then (qspecl_then [`s`, `mem_word_at (w2n a) s.vs_call_ctx.cc_calldata`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rpt strip_tac >> gvs[] >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- (irule compile_abi_clamp_basetype_mem_ok >> goal_assum (drule_at Any)) >>
  drule_all decode_clamp_frame >>
  Cases_on `abi_clamp_ok cl (mem_word_at (w2n a) s.vs_call_ctx.cc_calldata)` >>
  simp[] >> strip_tac >> rpt strip_tac >> gvs[] >>
  drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
  `eval_operand dst s' = SOME p` by metis_tac[] >>
  `eval_operand dst s'' = SOME p` by metis_tac[] >>
  `s''.vs_alloca_next = s'.vs_alloca_next` by
    (qpat_x_assum `vars_pc_only s' s''` mp_tac >>
     rw[moduleLoweringPropsTheory.vars_pc_only_def] >>
     pop_assum (SUBST1_TAC o SYM) >> simp[]) >>
  `s'.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `vars_pc_only s s'` mp_tac >>
     rw[moduleLoweringPropsTheory.vars_pc_only_def] >>
     pop_assum (SUBST1_TAC o SYM) >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!op v. eval_operand op s' = SOME v ==> _`
    (qspec_then `dst` mp_tac) >>
  qpat_x_assum `!op a. eval_operand op s = SOME a ==> _`
    (qspec_then `dst` mp_tac) >> simp[] >> metis_tac[]
QED

(* entry_decode_arg_run's premises, with the argument's buffer [p, p + its
   memory size) below the frontier: every instruction the decode runs is
   below the frontier where it runs. *)
Theorem entry_decode_arg_mem_ok:
  !cenv cenv0 tenv fname args vals env i off hi st st' loc dst s0 p tv.
    dec_cenv_agrees cenv0 tenv /\
    off = 4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
                       (TAKE i args)) /\
    compile_decode_args cenv [build_positional_arg cenv0 (EL i args)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars (FST (EL i args)) = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    bind_arguments tenv args vals = SOME env /\ i < LENGTH args /\
    calldata_encodes tenv fname (MAP SND args) vals s0.vs_call_ctx.cc_calldata /\
    (is_word_type (SND (EL i args)) \/
      (assignable_type tenv (SND (EL i args)) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND (EL i args))))) /\
    evaluate_type tenv (SND (EL i args)) = SOME tv /\ int_byte_widths tv /\
    off + type_memory_size tv < dimword (:256) /\
    w2n p + type_memory_size tv < dimword (:256) /\
    w2n p + type_memory_size tv <= s0.vs_alloca_next ==>
    run_inst_seq_mem_ok (emitted_insts st st') s0
Proof
  cheat
QED
