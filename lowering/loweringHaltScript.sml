(*
 * The halt half of S1 (#640): the return sequences of an external function
 * end in a Halt whose return data and effects are the success case of
 * external_call_result_rel (stated with it, in vyperLoweringCorrect, as
 * external_return_word_result_rel, external_return_prim_result_rel,
 * external_return_none_result_rel and
 * external_fallthrough_result_rel).  The fragment lemmas are stated with
 * frag_exec (fragExec), like the statement lemmas of stmtLoweringProps and
 * loweringSlice.
 *
 * Main lemmas:
 *   return_bytes_word_value — the canonical return bytes of a word value
 *                             (bool, integer, decimal, flag) are its
 *                             32-byte big-endian encoding
 *   return_bytes_prim_value — the same for every word type the lowering
 *                             returns with one MSTORE (also address and
 *                             bytesN), the word given by typed_val_to_w256
 *   compile_external_return_word_frag — returning a primitive word value
 *                             halts with that word as return data
 *   compile_return_none_external_frag — a return without a value halts
 *                             with empty return data
 *   compile_guarded_body_stop_frag — so does falling off the end of a
 *                             function without a return type
 *   external_halt_success   — the effects compared on success, from
 *                             state_rel at the return
 *
 * Helpers:
 *   compile_external_return_word_parts — the code of a word return
 *   return_word_run         — running that code
 *   step_alloca_frame       — ALLOCA changes nothing the return reads
 *   optional_unlock_view    — with nr ==> iv the optional unlock is empty
 *
 * Scope: no nonreentrant unlock (none, or a view function, whose return
 * does not unlock).  state_rel relates only the contract's own storage and
 * transient storage, so the accounts and the transient storage of every
 * address are hypotheses at the return: the success case compares all of
 * them (#625's relation leaves them out; #665 tracks deriving them).
 *)

Theory loweringHalt
Ancestors
  list rich_list finite_map
  fragExec loweringSlice
  stmtLowering moduleLowering context emitHelper emitHelperProps compileEnv
  valueEncoding valueEncodingProps venomMemProps
  e2eDefs vyperABI contractABI vyperInterpreter vyperState vyperValue
  vyperValueOperation vfmExecution
  venomExecSemantics venomInst venomInstProofs venomState
Libs
  monadsyntax dep_rewrite wordsLib

(* ===== Venom steps ===== *)

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
  Cases_on `FLOOKUP s.vs_allocas id`
  >- simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rename1 `FLOOKUP s.vs_allocas id = SOME p` >> PairCases_on `p` >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* ===== Return bytes ===== *)

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
  gvs[safe_cast_def, AllCaseEqs()]
  >~ [`BoolV bv`]
  >- (Cases_on `bv` >>
      simp[return_bytes_def, enc_def, REV_DEF, val_to_w256_def]) >>
  simp[return_bytes_def, enc_def, REV_DEF, val_to_w256_def] >>
  rename1 `within_int_bound _ i` >> gvs[within_int_bound_def] >>
  `~(i < 0)` by intLib.COOPER_TAC >>
  simp[integer_wordTheory.i2w_def]
QED

(* The same for every word type the lowering returns with one MSTORE
   (is_word_type: also address and bytesN), with the word the lowering
   holds given by typed_val_to_w256, as compile_name_correct gives it: an
   address is the 20 bytes right-aligned (the ABI's uint160), a bytesN
   value its N bytes left-aligned (the ABI's bytesN, right-padded with
   zeros), as the compiler's BytesM_T literals are. *)
Theorem return_bytes_prim_value:
  !tops tenv ret tv v0 v.
    evaluate_type tenv ret = SOME tv /\ safe_cast tv v0 = SOME v /\
    is_word_type ret ==>
    v = v0 /\
    return_bytes tops ret v (word_to_bytes (typed_val_to_w256 tv v0) T)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `ret` >> gvs[is_word_type_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v0` >> gvs[safe_cast_def, AllCaseEqs()] >>
  simp[return_bytes_def, enc_def, REV_DEF, typed_val_to_w256_def,
       val_to_w256_def]
  >~ [`PAD_LEFT`]
  >- (simp[GSYM wordsTheory.w2w_def] >>
      DEP_REWRITE_TAC[w2w_word_of_bytes_be_pad_left] >>
      simp[] >> EVAL_TAC)
  >~ [`PAD_RIGHT`]
  >- (simp[listTheory.PAD_RIGHT, GSYM rich_listTheory.REPLICATE_GENLIST,
           TAKE_LENGTH_TOO_LONG, byteTheory.word_of_bytes_be_def] >>
      irule word_bytes_roundtrip_256 >> simp[])
  >~ [`n2w (if _ then _ else _)`]
  >- (Cases_on `b` >> simp[]) >>
  rename1 `within_int_bound _ i` >> gvs[within_int_bound_def] >>
  `~(i < 0)` by intLib.COOPER_TAC >>
  simp[integer_wordTheory.i2w_def]
QED

(* ===== The return sequences ===== *)

(* With no unlock (none, or a view function), the optional unlock emits
   nothing. *)
Theorem optional_unlock_view:
  !nr nkey ut iv.
    (nr ==> iv) ==>
    (if nr then compile_nonreentrant_unlock nkey ut iv else comp_return ()) =
    comp_return ()
Proof
  rpt strip_tac >> Cases_on `nr` >> gvs[compile_nonreentrant_unlock_def]
QED

(* A return without a value, in an external function: a STOP. *)
Theorem compile_return_none_external_frag:
  !ctx cenv lctx ty st x st' nr nkey ut iv P Q R.
    compile_stmt cenv lctx ty (Return NONE) st = (x, st') /\
    cenv.ce_return_pc = NONE /\
    cenv.ce_nonreentrant = (nr, nkey, ut, iv) /\ (nr ==> iv) /\
    (!s. P s ==> R (Halt (halt_state (s with vs_returndata := [])))) ==>
    frag_exec ctx st st' P Q R
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
    stop_frag >>
  simp[]
QED

(* Falling off the end of a function without a return type, with no
   unlock: the code after the body sa..sb, when sb does not end its
   block, is a STOP. *)
Theorem compile_guarded_body_stop_frag:
  !ctx cenv nr nkey ut iv stmts st x st' sa sb P Q R.
    compile_guarded_body cenv nr nkey ut iv stmts NONE st = (x, st') /\
    (nr ==> iv) /\
    (if nr then compile_nonreentrant_lock nkey ut iv else comp_return ()) st =
      ((), sa) /\
    compile_stmts cenv NoLoop (BaseT BoolT) stmts sa = ((), sb) /\
    ~block_is_terminated sb /\
    (!s. P s ==> R (Halt (halt_state (s with vs_returndata := [])))) ==>
    frag_exec ctx sb st' P Q R
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
    stop_frag >>
  simp[]
QED

(* The code of a primitive word return with no unlock: ALLOCA a 32-byte
   buffer, MSTORE the word into it, RETURN the buffer.  The buffer is
   fresh at st. *)
Theorem compile_external_return_word_parts:
  !op ei msz nr nkey ut iv st x st'.
    compile_external_return (SOME op) T F ei msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) ==>
    ?buf.
      ~not_fresh_at st buf /\
      st'.cs_current_bb = st.cs_current_bb /\
      st'.cs_current_insts =
        st.cs_current_insts ++
        [mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf];
         mk_inst (st.cs_next_id + 1) MSTORE [Var buf; op] [];
         mk_inst (st.cs_next_id + 2) RETURN [Var buf; Lit 32w] []]
Proof
  rpt strip_tac >>
  qexists_tac `STRING #"%" (toString st.cs_next_var)` >>
  conj_tac
  >- (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_external_return_def, optional_unlock_view,
       compile_alloc_buffer_def, emit_op_def, emit_void_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

(* Running that code: the RETURN halts with the word's 32 bytes as return
   data, and nothing on the way touches the effects. *)
Theorem return_word_run:
  !fuel ctx fn s bb id buf op w.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ALLOCA [Lit 32w] [buf]) /\
    get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (id + 1) MSTORE [Var buf; op] []) /\
    get_instruction bb (s.vs_inst_idx + 2) =
      SOME (mk_inst (id + 2) RETURN [Var buf; Lit 32w] []) /\
    eval_operand op s = SOME w /\ op <> Var buf ==>
    ?ss. run_from fuel ctx fn s = Halt ss /\
         ss.vs_returndata = word_to_bytes w T /\
         ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
         ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests
Proof
  rpt strip_tac >>
  qspecl_then [`id`, `32w`, `buf`, `s`] strip_assume_tac step_alloca_frame >>
  qabbrev_tac `s1' = s1 with vs_inst_idx := s.vs_inst_idx + 1` >>
  `run_from fuel ctx fn s = run_from fuel ctx fn s1'` by
    (qspecl_then [`fuel`, `ctx`, `fn`, `s`, `bb`,
                  `mk_inst id ALLOCA [Lit 32w] [buf]`, `s1`]
       mp_tac run_from_step >>
     simp[is_terminator_def, Abbr `s1'`, arithmeticTheory.ADD1]) >>
  `eval_operand (Var buf) s1' = SOME a /\ eval_operand op s1' = SOME w` by
    (Cases_on `op` >> gvs[Abbr `s1'`, eval_operand_def, lookup_var_def]) >>
  qabbrev_tac `s2' = mstore (w2n a) w s1' with
                       vs_inst_idx := s.vs_inst_idx + 2` >>
  `run_from fuel ctx fn s1' = run_from fuel ctx fn s2'` by
    (qspecl_then [`fuel`, `ctx`, `fn`, `s1'`, `bb`,
                  `mk_inst (id + 1) MSTORE [Var buf; op] []`,
                  `mstore (w2n a) w s1'`] mp_tac run_from_step >>
     simp[is_terminator_def, step_MSTORE, Abbr `s2'`, Abbr `s1'`,
          arithmeticTheory.ADD1]) >>
  `eval_operand (Var buf) s2' = SOME a` by
    gvs[Abbr `s2'`, eval_operand_def, lookup_var_def, mstore_def] >>
  `s2'.vs_current_bb = s.vs_current_bb /\
   s2'.vs_inst_idx = s.vs_inst_idx + 2 /\
   s2'.vs_accounts = s.vs_accounts /\ s2'.vs_transient = s.vs_transient /\
   s2'.vs_logs = s.vs_logs /\ s2'.vs_requests = s.vs_requests` by
    simp[Abbr `s2'`, Abbr `s1'`, mstore_def] >>
  `w2n (32w:bytes32) = 32` by simp[wordsTheory.dimword_def] >>
  qabbrev_tac `ss = halt_state (set_returndata (word_to_bytes w T) s2')` >>
  `step_inst_base (mk_inst (id + 2) RETURN [Var buf; Lit 32w] []) s2' =
   Halt ss` by
    (qspecl_then [`Var buf`, `Lit 32w`, `a`, `32w`, `id + 2`, `s2'`]
       mp_tac step_RETURN >>
     simp[eval_operand_def, GSYM mem_bytes_at_def, Abbr `ss`] >>
     simp[Abbr `s2'`, mem_bytes_at_mstore_same]) >>
  qexists_tac `ss` >>
  qspecl_then [`fuel`, `ctx`, `fn`, `s2'`, `bb`,
               `mk_inst (id + 2) RETURN [Var buf; Lit 32w] []`, `ss`]
    mp_tac run_from_halt >>
  simp[Abbr `ss`, halt_state_def, set_returndata_def]
QED

(* Returning a primitive word: the code of
   compile_external_return_word_parts halts with the word as return data.
   The returned operand is no temporary of the return sequence, as
   compile_expr_correct says of an expression's operand. *)
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
  drule_all compile_external_return_word_parts >> strip_tac >>
  simp[frag_exec_def] >> rpt strip_tac >> disj2_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `op <> Var buf` by metis_tac[] >>
  `eval_operand op s = SOME w` by metis_tac[] >>
  qspecl_then [`0`, `ctx`, `fn`, `s`, `bb`, `st.cs_next_id`, `buf`, `op`,
               `w`] mp_tac return_word_run >>
  impl_tac
  >- (qpat_x_assum `!i. _` (fn th =>
        map_every (fn n => mp_tac (Q.SPEC n th)) [`0`, `1`, `2`]) >>
      simp[]) >>
  strip_tac >> qexists_tac `0` >> simp[exit_result_def] >>
  qpat_x_assum `!s ss. _ ==> R (Halt ss)` (qspecl_then [`s`, `ss`] mp_tac) >>
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
