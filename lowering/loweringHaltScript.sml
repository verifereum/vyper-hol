(*
 * The halt half of S1 (#640): the return sequences of an external function
 * end in a Halt whose return data and effects are the success case of
 * external_call_result_rel (stated with it, in vyperLoweringCorrect, as
 * external_return_word_result_rel and external_stop_result_rel).  The
 * fragment lemmas are stated with frag_exec (fragExec), like the statement
 * lemmas of stmtLoweringProps and loweringSlice.
 *
 * Main lemmas:
 *   return_bytes_word_value — the canonical return bytes of a word value
 *                             (bool, integer, decimal, flag) are its
 *                             32-byte big-endian encoding
 *   compile_external_return_word_frag — returning a primitive word value
 *                             halts with that word as return data
 *   stop_frag               — a STOP halts with empty return data
 *   compile_external_return_stop_frag, compile_return_none_external_frag
 *                           — the external return sequences without a value
 *   external_halt_success   — the effects compared on success, from
 *                             state_rel at the return
 *
 * Helpers: run_from_step, run_from_halt, fn_has_code_same_block,
 *   step_alloca_frame, step_stop, step_return, mem_bytes_at_mstore_same,
 *   enc_singleton_static
 *
 * Scope: no nonreentrant unlock (none, or a view function, whose return
 * does not unlock).  state_rel relates only the contract's own storage and
 * transient storage, so the accounts and the transient storage of every
 * address are hypotheses at the return: the success case compares all of
 * them (#625's relation leaves them out).
 *)

Theory loweringHalt
Ancestors
  list rich_list finite_map
  fragExec loweringSlice
  stmtLowering context emitHelper emitHelperProps compileEnv
  valueEncoding valueEncodingProps venomMemProps
  e2eDefs vyperABI contractABI vyperInterpreter vyperState vyperValue
  vyperValueOperation vfmExecution
  venomExecSemantics venomInst venomInstProofs venomState
Libs
  monadsyntax

(* ===== Venom steps ===== *)

(* A straight-line instruction steps run_from to the next index. *)
Theorem run_from_step:
  !fuel ctx fn s bb inst s1.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s1 ==>
    run_from fuel ctx fn s =
    run_from fuel ctx fn (s1 with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >>
  `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  simp[run_from_def, Once exec_block_def, step_inst_non_invoke]
QED

(* A step that halts is the result of the run. *)
Theorem run_from_halt:
  !fuel ctx fn s bb inst s'.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode <> INVOKE /\ step_inst_base inst s = Halt s' ==>
    run_from fuel ctx fn s = Halt s'
Proof
  rw[run_from_def, Once exec_block_def, step_inst_non_invoke]
QED

(* The instructions a fragment appends to the current block are in fn. *)
Theorem fn_has_code_same_block:
  !st st' fn new.
    fn_has_code st st' fn /\ st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++ new ==>
    ?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
         !i. i < LENGTH new ==>
             get_instruction bb (LENGTH st.cs_current_insts + i) =
             SOME (EL i new)
Proof
  rw[fn_has_code_def] >> qexists_tac `bb` >> rw[] >>
  gvs[IS_PREFIX_APPEND, get_instruction_def] >>
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC] >> simp[EL_APPEND2, EL_APPEND1]
QED

(* ALLOCA binds its output and changes nothing else the return reads. *)
Theorem step_alloca_frame:
  !id sz out s.
    ?a s1.
      step_inst_base (mk_inst id ALLOCA [Lit sz] [out]) s = OK s1 /\
      lookup_var out s1 = SOME a /\
      (!x. x <> out ==> lookup_var x s1 = lookup_var x s) /\
      s1.vs_memory = s.vs_memory /\ s1.vs_labels = s.vs_labels /\
      s1.vs_accounts = s.vs_accounts /\ s1.vs_transient = s.vs_transient /\
      s1.vs_logs = s.vs_logs /\ s1.vs_requests = s.vs_requests /\
      s1.vs_current_bb = s.vs_current_bb /\ s1.vs_inst_idx = s.vs_inst_idx
Proof
  rpt gen_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_alloca_def] >>
  CASE_TAC >> TRY (PairCases_on `x`) >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem step_stop:
  !id s.
    step_inst_base (mk_inst id STOP [] []) s =
    Halt (halt_state (s with vs_returndata := []))
Proof
  rpt gen_tac >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def]
QED

Theorem step_return:
  !id op1 op2 s off sz.
    eval_operand op1 s = SOME off /\ eval_operand op2 s = SOME sz ==>
    step_inst_base (mk_inst id RETURN [op1; op2] []) s =
    Halt (halt_state
            (set_returndata (mem_bytes_at (w2n off) (w2n sz) s.vs_memory) s))
Proof
  rpt strip_tac >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, mem_bytes_at_def]
QED

Theorem mem_bytes_at_mstore_same:
  !off w s. mem_bytes_at off 32 (mstore off w s).vs_memory = word_to_bytes w T
Proof
  rpt gen_tac >>
  qabbrev_tac `M = (mstore off w s).vs_memory` >>
  `word_of_bytes T (0w:bytes32) (mem_bytes_at off 32 M) = w` by
    (qspecl_then [`off`, `w`, `s`] mp_tac mstore_mem_word_at_same >>
     simp[mem_word_at_def, mem_bytes_at_def, Abbr `M`]) >>
  `word_to_bytes (word_of_bytes T (0w:bytes32) (mem_bytes_at off 32 M)) T =
   mem_bytes_at off 32 M` by simp[word_bytes_roundtrip_256] >>
  metis_tac[]
QED

(* ===== Return bytes ===== *)

Theorem enc_singleton_static:
  !t v. ~is_dynamic t ==> enc (Tuple [t]) (ListV [v]) = enc t v
Proof
  rw[enc_def, REV_DEF]
QED

(* The source's return value of a word type is the word the lowering
   holds, and the canonical return bytes are its 32-byte encoding: the
   singleton wrapping tuple of a static type encodes as the element. *)
Theorem return_bytes_word_value:
  !tops tenv ret tv v0 v.
    evaluate_type tenv ret = SOME tv /\ safe_cast tv v0 = SOME v /\
    word_value v0 ==>
    v = v0 /\ return_bytes tops ret v (word_to_bytes (val_to_w256 v0) T)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `v0` >> gvs[word_value_def] >>
  Cases_on `ret` >> gvs[evaluate_type_def, AllCaseEqs()] >>
  gvs[safe_cast_def, AllCaseEqs()] >>
  simp[return_bytes_def, enc_def, REV_DEF, val_to_w256_def] >>
  TRY (Cases_on `b` >> simp[] >> NO_TAC) >>
  gvs[within_int_bound_def] >>
  `~(i < 0)` by intLib.COOPER_TAC >>
  simp[integer_wordTheory.i2w_def]
QED

(* ===== The return sequences ===== *)

(* A STOP ends the run, with empty return data. *)
Theorem stop_frag:
  !ctx st st' id P Q R.
    st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++ [mk_inst id STOP [] []] /\
    (!s. P s ==> R (Halt (halt_state (s with vs_returndata := [])))) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >> simp[frag_exec_def] >> rpt strip_tac >>
  qspecl_then [`st`, `st'`, `fn`, `[mk_inst id STOP [] []]`] mp_tac
    fn_has_code_same_block >>
  impl_tac >- simp[] >> strip_tac >>
  pop_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  disj2_tac >> qexists_tac `0` >>
  qspecl_then [`0`, `ctx`, `fn`, `s`, `bb`, `mk_inst id STOP [] []`,
               `halt_state (s with vs_returndata := [])`] mp_tac
    run_from_halt >>
  impl_tac >- simp[step_stop, mk_inst_def] >>
  simp[exit_result_def]
QED

Theorem compile_external_return_stop_frag:
  !ctx pw rr ei msz nr nkey ut iv st x st' P Q R.
    compile_external_return NONE pw rr ei msz nr nkey ut iv st = (x, st') /\
    (nr ==> iv) /\
    (!s. P s ==> R (Halt (halt_state (s with vs_returndata := [])))) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >>
  `st'.cs_current_bb = st.cs_current_bb /\
   st'.cs_current_insts =
     st.cs_current_insts ++ [mk_inst st.cs_next_id STOP [] []]` by
    (qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `nr` >>
     gvs[compile_external_return_def, compile_nonreentrant_unlock_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def,
         emit_inst_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[]) >>
  qspecl_then [`ctx`, `st`, `st'`, `st.cs_next_id`, `P`, `Q`, `R`]
    mp_tac stop_frag >>
  simp[]
QED

(* return with no value, in an external function. *)
Theorem compile_return_none_external_frag:
  !ctx cenv lctx ty st x st' P Q R.
    compile_stmt cenv lctx ty (Return NONE) st = (x, st') /\
    cenv.ce_return_pc = NONE /\
    (FST cenv.ce_nonreentrant ==> SND (SND (SND cenv.ce_nonreentrant))) /\
    (!s. P s ==> R (Halt (halt_state (s with vs_returndata := [])))) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >>
  `?nr nkey ut iv. cenv.ce_nonreentrant = (nr, nkey, ut, iv)` by
    metis_tac[pairTheory.ABS_PAIR_THM] >>
  qspecl_then [`ctx`, `F`, `F`, `ARB`, `0`, `nr`, `nkey`, `ut`, `iv`,
               `st`, `x`, `st'`, `P`, `Q`, `R`] mp_tac
    compile_external_return_stop_frag >>
  disch_then irule >> gvs[] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[compile_stmt_def, compile_external_return_def]
QED

(* Returning a primitive word: ALLOCA a 32-byte buffer, MSTORE the word,
   RETURN the buffer.  The returned operand is no temporary of the return
   sequence, as compile_expr_correct says of an expression's operand. *)
Theorem compile_external_return_word_frag:
  !ctx op ei msz nr nkey ut iv st x st' w P Q R.
    compile_external_return (SOME op) T F ei msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    (!s. P s ==> eval_operand op s = SOME w) /\
    (!s ss. P s /\ ss.vs_returndata = word_to_bytes w T /\
            ss.vs_accounts = s.vs_accounts /\
            ss.vs_transient = s.vs_transient /\
            ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
            R (Halt ss)) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `buf = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `A = mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf]` >>
  qabbrev_tac `M = mk_inst (st.cs_next_id + 1) MSTORE [Var buf; op] []` >>
  qabbrev_tac `Rt = mk_inst (st.cs_next_id + 2) RETURN [Var buf; Lit 32w] []` >>
  `st'.cs_current_bb = st.cs_current_bb /\
   st'.cs_current_insts = st.cs_current_insts ++ [A; M; Rt]` by
    (qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `nr` >>
     gvs[compile_external_return_def, compile_nonreentrant_unlock_def,
         compile_alloc_buffer_def, emit_op_def, emit_void_def,
         emit_inst_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, fresh_var_def, emit_def,
         Abbr `A`, Abbr `M`, Abbr `Rt`, Abbr `buf`] >>
     rpt strip_tac >> gvs[]) >>
  simp[frag_exec_def] >> rpt strip_tac >> disj2_tac >>
  qspecl_then [`st`, `st'`, `fn`, `[A; M; Rt]`] mp_tac
    fn_has_code_same_block >>
  impl_tac >- simp[] >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME A /\
   get_instruction bb (SUC s.vs_inst_idx) = SOME M /\
   get_instruction bb (SUC (SUC s.vs_inst_idx)) = SOME Rt` by
    (first_assum (qspec_then `0` mp_tac) >>
     first_assum (qspec_then `1` mp_tac) >>
     first_x_assum (qspec_then `2` mp_tac) >>
     simp[arithmeticTheory.ADD1]) >>
  `eval_operand op s = SOME w` by metis_tac[] >>
  `~not_fresh_at st buf` by
    (simp[not_fresh_at_def, Abbr `buf`] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `op <> Var buf` by metis_tac[] >>
  (* the ALLOCA *)
  qspecl_then [`st.cs_next_id`, `32w`, `buf`, `s`] strip_assume_tac
    step_alloca_frame >>
  qabbrev_tac `s1' = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `!f. run_from f ctx fn s = run_from f ctx fn s1'` by
    (gen_tac >>
     qspecl_then [`f`, `ctx`, `fn`, `s`, `bb`, `A`, `s1`] mp_tac
       run_from_step >>
     impl_tac >- fs[Abbr `A`, mk_inst_def, is_terminator_def] >>
     simp[Abbr `s1'`]) >>
  `!o'. eval_operand o' s1' = eval_operand o' s1` by
    (Cases >> simp[Abbr `s1'`, eval_operand_def, lookup_var_def]) >>
  `eval_operand (Var buf) s1' = SOME a /\ eval_operand op s1' = SOME w` by
    (qpat_x_assum `!o'. _` (fn th => rewrite_tac[th]) >>
     simp[eval_operand_def] >> Cases_on `op` >> gvs[eval_operand_def]) >>
  (* the MSTORE *)
  qabbrev_tac `s2 = mstore (w2n a) w s1'` >>
  `step_inst_base M s1' = OK s2` by
    (qunabbrev_tac `M` >> qunabbrev_tac `s2` >> irule step_MSTORE >>
     asm_rewrite_tac[]) >>
  `M.inst_opcode = MSTORE /\ Rt.inst_opcode = RETURN` by
    simp[Abbr `M`, Abbr `Rt`, mk_inst_def] >>
  `s1'.vs_current_bb = s.vs_current_bb /\
   s1'.vs_inst_idx = SUC s.vs_inst_idx` by simp[Abbr `s1'`] >>
  qabbrev_tac `s2' = s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx)` >>
  `!f. run_from f ctx fn s1' = run_from f ctx fn s2'` by
    (gen_tac >>
     qspecl_then [`f`, `ctx`, `fn`, `s1'`, `bb`, `M`, `s2`] mp_tac
       run_from_step >>
     impl_tac >- (fs[is_terminator_def] >> metis_tac[]) >>
     simp[Abbr `s2'`]) >>
  (* the RETURN *)
  `s2'.vs_current_bb = s.vs_current_bb /\
   s2'.vs_inst_idx = SUC (SUC s.vs_inst_idx) /\
   s2'.vs_vars = s1.vs_vars /\
   s2'.vs_memory = (mstore (w2n a) w s1').vs_memory /\
   s2'.vs_accounts = s.vs_accounts /\ s2'.vs_transient = s.vs_transient /\
   s2'.vs_logs = s.vs_logs /\ s2'.vs_requests = s.vs_requests` by
    simp[Abbr `s2'`, Abbr `s2`, Abbr `s1'`, mstore_def] >>
  `eval_operand (Var buf) s2' = SOME a` by
    fs[eval_operand_def, lookup_var_def] >>
  qabbrev_tac `ss = halt_state (set_returndata
                     (mem_bytes_at (w2n a) 32 s2'.vs_memory) s2')` >>
  `step_inst_base Rt s2' = Halt ss` by
    (qunabbrev_tac `Rt` >> qunabbrev_tac `ss` >>
     `w2n (32w:bytes32) = 32` by simp[wordsTheory.dimword_def] >>
     `eval_operand (Lit 32w) s2' = SOME 32w` by simp[eval_operand_def] >>
     metis_tac[step_return]) >>
  `!f. run_from f ctx fn s2' = Halt ss` by
    (gen_tac >>
     qspecl_then [`f`, `ctx`, `fn`, `s2'`, `bb`, `Rt`, `ss`] mp_tac
       run_from_halt >>
     impl_tac >- (fs[] >> metis_tac[]) >> simp[]) >>
  qexists_tac `0` >> asm_rewrite_tac[] >> simp[exit_result_def] >>
  qpat_x_assum `!s ss. P s /\ _ ==> R (Halt ss)`
    (qspecl_then [`s`, `ss`] mp_tac) >>
  impl_tac >- (simp[Abbr `ss`, halt_state_def, set_returndata_def] >>
               asm_rewrite_tac[mem_bytes_at_mstore_same]) >>
  simp[]
QED

(* ===== The effects compared on success ===== *)

(* With state_rel at the return, a Halt that leaves the effects as they
   were gives the effects external_call_result_rel compares on success. *)
Theorem external_halt_success:
  !func cenv cx es s ss tops tx srcs exps layouts.
    state_rel func cenv cx es s /\
    s.vs_accounts = process_deletions es.pending_deletions es.accounts /\
    s.vs_transient = es.tStorage /\
    ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
    ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
    ss.vs_accounts =
      (finalize_pending_deletions
         (abstract_machine_from_state srcs exps layouts es)).accounts /\
    ss.vs_transient =
      (finalize_pending_deletions
         (abstract_machine_from_state srcs exps layouts es)).tStorage /\
    logs_correspond (compiled_event_info tops) (type_env tops) tx.target
      (finalize_pending_deletions
         (abstract_machine_from_state srcs exps layouts es)).logs
      ss.vs_logs /\
    ss.vs_requests = es.requests
Proof
  rpt strip_tac >>
  `log_entry_equiv cenv cx.txn.target = $= /\
   log_entry_corresponds (compiled_event_info tops) (type_env tops)
     tx.target = $=` by
    simp[FUN_EQ_THM, log_entry_equiv_def,
         log_entry_corresponds_concrete_event] >>
  fs[state_rel_def, logs_rel_def, logs_correspond_def, LIST_REL_eq,
     finalize_pending_deletions_def, abstract_machine_from_state_def]
QED
