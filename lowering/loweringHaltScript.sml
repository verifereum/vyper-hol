(*
 * The halt half of S1 (#640): the return sequences of an external function
 * end in a Halt whose return data and effects are the success case of
 * external_call_result_rel (stated with it, in vyperLoweringCorrect, as
 * external_return_word_result_rel, external_return_prim_result_rel,
 * external_return_none_result_rel, external_fallthrough_result_rel and
 * their _unlock versions).  The fragment lemmas are stated with
 * frag_exec (fragExec), like the statement lemmas of stmtLoweringProps and
 * loweringSlice.
 *
 * Main lemmas:
 *   return_bytes_prim_value — the canonical return bytes of a value of a
 *                             word type (bool, integer, decimal, flag,
 *                             address, bytesN) are its 32-byte big-endian
 *                             encoding, typed_val_to_w256
 *   return_bytes_word_value — its case for the values word_value covers,
 *                             with val_to_w256
 *   compile_external_return_word_frag — returning a primitive word value
 *                             halts with that word as return data
 *   compile_return_none_external_frag — a return without a value halts
 *                             with empty return data
 *   compile_guarded_body_stop_frag — so does falling off the end of a
 *                             function without a return type
 *   external_halt_success   — the effects compared on success, from
 *                             state_rel at the return
 *   compile_external_return_word_unlock_frag,
 *   compile_return_none_external_unlock_frag,
 *   compile_guarded_body_stop_unlock_frag — the same three, in a function
 *                             whose return may release a transient
 *                             nonreentrant lock: one TSTORE of 0 at the
 *                             lock key before the halt
 *   external_halt_success_unlock — the effects compared on success, from
 *                             the source state after the release
 *
 * Helpers:
 *   word_value_prim         — word_value values are of word types
 *   compile_external_return_word_parts — the code of a word return
 *   return_word_run         — running that code
 *   step_alloca_frame       — ALLOCA changes nothing the return reads
 *   step_TSTORE             — TSTORE writes the running contract's
 *                             transient storage
 *   optional_unlock_view    — with nr ==> iv the optional unlock is empty
 *   optional_unlock_code, optional_unlock_frag — the optional unlock's
 *                             code, and running it
 *   unlock_stop_frag        — the optional unlock, then STOP
 *   compile_external_return_unlock — a return sequence is the optional
 *                             unlock, then the sequence without one
 *
 * Scope: the lemmas without _unlock have no unlock (nr ==> iv: no lock,
 * or a view function, whose return does not unlock); the _unlock ones
 * also allow a transient lock (nr /\ ~iv ==> ut), and leave out the
 * SSTORE lock of pre-Cancun targets.  They are stated over the compiler's
 * lock key nkey; that it is the source's cx.nonreentrant_slot is not
 * shown here (the lowering does not use transient locks yet, #564).
 * state_rel relates only the contract's own storage and
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

(* TSTORE writes its value at its key in the running contract's transient
   storage. *)
Theorem step_TSTORE:
  !op1 op2 v1 v2 id s.
    eval_operand op1 s = SOME v1 /\ eval_operand op2 s = SOME v2 ==>
    step_inst_base (mk_inst id TSTORE [op1; op2] []) s = OK (tstore v1 v2 s)
Proof
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_write2_def]
QED

(* ===== Return bytes ===== *)

(* The source's return value of a word type (is_word_type: also address
   and bytesN, which the lowering returns with one MSTORE) is the value the
   lowering holds, and the canonical return bytes are the 32-byte encoding
   of its word at the return type, typed_val_to_w256: an address is its 20
   bytes right-aligned (the ABI's uint160), a bytesN value its N bytes
   left-aligned (the ABI's bytesN, right-padded with zeros), as the
   compiler's BytesM_T literals are.  The singleton wrapping tuple of a
   static type encodes as the element. *)
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
  >- (rename1 `if bv then _ else _` >> Cases_on `bv` >> simp[]) >>
  rename1 `within_int_bound _ i` >> gvs[within_int_bound_def] >>
  `~(i < 0)` by intLib.COOPER_TAC >>
  simp[integer_wordTheory.i2w_def]
QED

(* The values word_value covers (bool, integer, decimal, flag) are of such
   types, and their word at any type is val_to_w256. *)
Theorem word_value_prim:
  !tenv ret tv v0 v.
    evaluate_type tenv ret = SOME tv /\ safe_cast tv v0 = SOME v /\
    word_value v0 ==>
    is_word_type ret /\ typed_val_to_w256 tv v0 = val_to_w256 v0
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `v0` >> gvs[word_value_def, typed_val_to_w256_def] >>
  Cases_on `ret` >> gvs[evaluate_type_def, AllCaseEqs()] >>
  gvs[safe_cast_def, AllCaseEqs(), is_word_type_def, typed_val_to_w256_def]
QED

(* The case of those values. *)
Theorem return_bytes_word_value:
  !tops tenv ret tv v0 v.
    evaluate_type tenv ret = SOME tv /\ safe_cast tv v0 = SOME v /\
    word_value v0 ==>
    v = v0 /\ return_bytes tops ret v (word_to_bytes (val_to_w256 v0) T)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all word_value_prim >> strip_tac >>
  drule_all return_bytes_prim_value >> gvs[]
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

(* ===== Returns that release the lock ===== *)

(* The optional unlock with a transient lock: nothing, or, for a
   nonreentrant function that is not a view, one TSTORE of 0 at the lock
   key. *)
Theorem optional_unlock_code:
  !nr nkey ut iv st st'.
    (if nr then compile_nonreentrant_unlock nkey ut iv else comp_return ())
      st = ((), st') /\
    (nr /\ ~iv ==> ut) ==>
    st' =
      if nr /\ ~iv then
        st with <| cs_current_insts :=
                     st.cs_current_insts ++
                     [mk_inst st.cs_next_id TSTORE [Lit (n2w nkey); Lit 0w] []];
                   cs_next_id := st.cs_next_id + 1 |>
      else st
Proof
  rpt strip_tac >> Cases_on `nr` >> Cases_on `iv` >>
  gvs[compile_nonreentrant_unlock_def, comp_return_def, emit_void_def,
      comp_bind_def, fresh_id_def, emit_def]
QED

(* Running it: the TSTORE writes 0 at the key in the transient storage of
   the running contract, and changes nothing else. *)
Theorem optional_unlock_frag:
  !ctx nr nkey ut iv st st' P Q R.
    (if nr then compile_nonreentrant_unlock nkey ut iv else comp_return ())
      st = ((), st') /\
    (nr /\ ~iv ==> ut) /\
    (!s. P s ==>
         Q ((if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
              vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >> drule_all optional_unlock_code >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  Cases_on `nr` >> Cases_on `iv` >>
  gvs[exprLoweringPropsTheory.emitted_insts_def,
      exprLoweringPropsTheory.run_inst_seq_def, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def] >> rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[exec_write2_def, eval_operand_def]
QED

(* A return without a value, or a fallthrough, in an external function:
   the optional unlock, then a STOP. *)
Theorem unlock_stop_frag:
  !ctx nr nkey ut iv st x st' P Q R.
    comp_ignore_bind
      (if nr then compile_nonreentrant_unlock nkey ut iv else comp_return ())
      (emit_inst STOP [] []) st = (x, st') /\
    (nr /\ ~iv ==> ut) /\
    (!s ss. P s /\ ss.vs_returndata = [] /\
            ss.vs_accounts = s.vs_accounts /\
            ss.vs_transient =
              (if nr /\ ~iv then (tstore (n2w nkey) 0w s).vs_transient
               else s.vs_transient) /\
            ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
            R (Halt ss)) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >>
  Cases_on `(if nr then compile_nonreentrant_unlock nkey ut iv
             else comp_return ()) st` >>
  rename1 `_ st = (u, st1)` >> Cases_on `u` >>
  `st'.cs_blocks = st1.cs_blocks /\ st'.cs_current_bb = st1.cs_current_bb /\
   st'.cs_current_insts =
     st1.cs_current_insts ++ [mk_inst st1.cs_next_id STOP [] []]` by
    (qpat_x_assum `comp_ignore_bind _ _ _ = _` mp_tac >>
     REWRITE_TAC[comp_ignore_bind_def, comp_bind_def] >>
     qpat_x_assum `_ st = ((), st1)` (fn th => REWRITE_TAC[th]) >>
     simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  drule_all optional_unlock_code >> strip_tac >>
  `cs_extends st st1` by
    (qpat_x_assum `st1 = _` SUBST1_TAC >> irule cs_extends_same_block >>
     rw[]) >>
  qpat_x_assum `st1 = _` kall_tac >>
  qspecl_then
    [`ctx`, `st`, `st1`, `st'`, `P`,
     `\s1. ?s. P s /\
           s1 = (if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
                  vs_inst_idx := LENGTH st1.cs_current_insts`,
     `Q`, `R`] mp_tac frag_exec_seq >>
  impl_tac >> simp[] >> rpt conj_tac
  >- (qspecl_then
      [`ctx`, `nr`, `nkey`, `ut`, `iv`, `st`, `st1`, `P`,
       `\s1. ?s. P s /\
             s1 = (if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
                    vs_inst_idx := LENGTH st1.cs_current_insts`,
       `R`] mp_tac optional_unlock_frag >>
      impl_tac >- (simp[] >> metis_tac[]) >> simp[])
  >- (qspecl_then
      [`ctx`, `st1`, `st'`, `st1.cs_next_id`,
       `\s1. ?s. P s /\
             s1 = (if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
                    vs_inst_idx := LENGTH st1.cs_current_insts`,
       `Q`, `R`] mp_tac stop_frag >>
      impl_tac >> simp[] >> simp[PULL_EXISTS] >> rpt strip_tac >>
      rename1 `P s0` >> first_x_assum irule >>
      qpat_assum `P s0` (irule_at Any) >>
      Cases_on `nr` >> Cases_on `iv` >> gvs[halt_state_def, tstore_def])
  >> irule cs_extends_same_block >> simp[]
QED

(* The return sequence of compile_external_return is the optional unlock,
   then the sequence without an unlock. *)
Theorem compile_external_return_unlock:
  !rv p rr ei msz nr nkey ut iv st x st'.
    compile_external_return rv p rr ei msz nr nkey ut iv st = (x, st') ==>
    ?st1.
      (if nr then compile_nonreentrant_unlock nkey ut iv else comp_return ())
        st = ((), st1) /\
      compile_external_return rv p rr ei msz F nkey ut iv st1 = (x, st')
Proof
  rpt strip_tac >>
  Cases_on `(if nr then compile_nonreentrant_unlock nkey ut iv
             else comp_return ()) st` >>
  rename1 `_ st = (u, st1)` >> Cases_on `u` >> qexists_tac `st1` >>
  qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  REWRITE_TAC[compile_external_return_def, comp_ignore_bind_def,
              comp_bind_def] >>
  qpat_x_assum `_ st = ((), st1)` (fn th => REWRITE_TAC[th]) >>
  simp[comp_return_def]
QED

(* Returning a primitive word, with the optional unlock first. *)
Theorem compile_external_return_word_unlock_frag:
  !ctx op ei msz nr nkey ut iv st x st' w P Q R.
    compile_external_return (SOME op) T F ei msz nr nkey ut iv st =
      (x, st') /\
    (nr /\ ~iv ==> ut) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    (!s. P s ==> eval_operand op s = SOME w) /\
    (!s ss. P s /\ ss.vs_returndata = word_to_bytes w T /\
            ss.vs_accounts = s.vs_accounts /\
            ss.vs_transient =
              (if nr /\ ~iv then (tstore (n2w nkey) 0w s).vs_transient
               else s.vs_transient) /\
            ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
            R (Halt ss)) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >>
  drule compile_external_return_unlock >> strip_tac >>
  drule_all optional_unlock_code >> strip_tac >>
  `st1.cs_next_var = st.cs_next_var /\ cs_extends st st1` by
    (qpat_x_assum `st1 = _` SUBST1_TAC >> rw[] >>
     irule cs_extends_same_block >> simp[]) >>
  qpat_x_assum `st1 = _` kall_tac >>
  `st'.cs_blocks = st1.cs_blocks` by
    (qpat_x_assum `compile_external_return _ _ _ _ _ F _ _ _ _ = _` mp_tac >>
     simp[compile_external_return_def, compile_alloc_buffer_def, emit_op_def,
          emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  qspecl_then [`op`, `ei`, `msz`, `F`, `nkey`, `ut`, `iv`, `st1`, `x`, `st'`]
    mp_tac compile_external_return_word_parts >>
  simp[] >> strip_tac >>
  qspecl_then
    [`ctx`, `st`, `st1`, `st'`, `P`,
     `\s1. ?s. P s /\
           s1 = (if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
                  vs_inst_idx := LENGTH st1.cs_current_insts`,
     `Q`, `R`] mp_tac frag_exec_seq >>
  impl_tac >> simp[] >> rpt conj_tac
  >- (qspecl_then
      [`ctx`, `nr`, `nkey`, `ut`, `iv`, `st`, `st1`, `P`,
       `\s1. ?s. P s /\
             s1 = (if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
                    vs_inst_idx := LENGTH st1.cs_current_insts`,
       `R`] mp_tac optional_unlock_frag >>
      impl_tac >- (simp[] >> metis_tac[]) >> simp[])
  >- (qspecl_then
      [`ctx`, `op`, `ei`, `msz`, `F`, `nkey`, `ut`, `iv`, `st1`, `x`, `st'`,
       `w`,
       `\s1. ?s. P s /\
             s1 = (if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
                    vs_inst_idx := LENGTH st1.cs_current_insts`,
       `Q`, `R`] mp_tac compile_external_return_word_frag >>
      impl_tac >> simp[] >> simp[PULL_EXISTS] >> rpt conj_tac
      >- (rpt strip_tac >> gvs[not_fresh_at_def])
      >- (rpt strip_tac >> rename1 `P s0` >>
          `eval_operand op s0 = SOME w` by metis_tac[] >>
          Cases_on `op` >> Cases_on `nr` >> Cases_on `iv` >>
          gvs[eval_operand_def, lookup_var_def, tstore_def])
      >> rpt strip_tac >> rename1 `P s0` >> first_x_assum irule >>
      qpat_assum `P s0` (irule_at Any) >>
      Cases_on `nr` >> Cases_on `iv` >> gvs[tstore_def])
  >> irule cs_extends_same_block >> simp[]
QED

(* A return without a value, in an external function, with the optional
   unlock first. *)
Theorem compile_return_none_external_unlock_frag:
  !ctx cenv lctx ty st x st' nr nkey ut iv P Q R.
    compile_stmt cenv lctx ty (Return NONE) st = (x, st') /\
    cenv.ce_return_pc = NONE /\
    cenv.ce_nonreentrant = (nr, nkey, ut, iv) /\ (nr /\ ~iv ==> ut) /\
    (!s ss. P s /\ ss.vs_returndata = [] /\
            ss.vs_accounts = s.vs_accounts /\
            ss.vs_transient =
              (if nr /\ ~iv then (tstore (n2w nkey) 0w s).vs_transient
               else s.vs_transient) /\
            ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
            R (Halt ss)) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `nr`, `nkey`, `ut`, `iv`, `st`, `x`, `st'`, `P`, `Q`,
               `R`] mp_tac unlock_stop_frag >>
  impl_tac >> simp[] >> rpt conj_tac
  >- (qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
      simp[compile_stmt_def])
  >> first_assum ACCEPT_TAC
QED

(* Falling off the end of a function without a return type, with the
   optional unlock first: from the end sb of the body's code, when it does
   not end its block. *)
Theorem compile_guarded_body_stop_unlock_frag:
  !ctx cenv nr nkey ut iv stmts st x st' sa sb P Q R.
    compile_guarded_body cenv nr nkey ut iv stmts NONE st = (x, st') /\
    (nr /\ ~iv ==> ut) /\
    (if nr then compile_nonreentrant_lock nkey ut iv else comp_return ()) st =
      ((), sa) /\
    compile_stmts cenv NoLoop (BaseT BoolT) stmts sa = ((), sb) /\
    ~block_is_terminated sb /\
    (!s ss. P s /\ ss.vs_returndata = [] /\
            ss.vs_accounts = s.vs_accounts /\
            ss.vs_transient =
              (if nr /\ ~iv then (tstore (n2w nkey) 0w s).vs_transient
               else s.vs_transient) /\
            ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
            R (Halt ss)) ==>
    frag_exec ctx sb st' P Q R
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `nr`, `nkey`, `ut`, `iv`, `sb`, `x`, `st'`, `P`, `Q`,
               `R`] mp_tac unlock_stop_frag >>
  impl_tac >> simp[] >> rpt conj_tac
  >- (qpat_x_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[compile_guarded_body_def, comp_bind_def, comp_ignore_bind_def,
           comp_get_def])
  >> first_assum ACCEPT_TAC
QED

(* ===== The effects compared on success ===== *)

(* With state_rel at the return, a Halt that leaves the effects as they
   were, except for the optional unlock's TSTORE, gives the effects
   external_call_result_rel compares on success, from the state es' after
   the source releases the lock at the same key. *)
Theorem external_halt_success_unlock:
  !func cenv cx es es' s ss nr nkey iv tops tx srcs exps layouts.
    state_rel func cenv cx es s /\
    s.vs_accounts = process_deletions es.pending_deletions es.accounts /\
    s.vs_transient = es.tStorage /\
    (if nr /\ ~iv then release_nonreentrant_lock cx.txn.target nkey
     else vyperState$return ()) es = (INL (), es') /\
    ss.vs_accounts = s.vs_accounts /\
    ss.vs_transient =
      (if nr /\ ~iv then (tstore (n2w nkey) 0w s).vs_transient
       else s.vs_transient) /\
    ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
    ss.vs_accounts =
      (finalize_pending_deletions
         (abstract_machine_from_state srcs exps layouts es')).accounts /\
    ss.vs_transient =
      (finalize_pending_deletions
         (abstract_machine_from_state srcs exps layouts es')).tStorage /\
    logs_correspond (compiled_event_info tops) (type_env tops) tx.target
      (finalize_pending_deletions
         (abstract_machine_from_state srcs exps layouts es')).logs
      ss.vs_logs /\
    ss.vs_requests = es'.requests
Proof
  rpt gen_tac >> strip_tac >>
  `es' = es with tStorage := ss.vs_transient` by
    (Cases_on `nr` >> Cases_on `iv` >>
     gvs[release_nonreentrant_lock_def, vyperStateTheory.bind_def,
         get_transient_storage_def, update_transient_def,
         vyperStateTheory.return_def, tstore_def, state_rel_def,
         call_ctx_rel_def, update_transient_storage_def,
         lookup_transient_storage_def,
         evaluation_state_component_equality]) >>
  `log_entry_equiv cenv cx.txn.target = $= /\
   log_entry_corresponds (compiled_event_info tops) (type_env tops)
     tx.target = $=` by
    simp[FUN_EQ_THM, log_entry_equiv_def,
         log_entry_corresponds_concrete_event] >>
  fs[state_rel_def, logs_rel_def, logs_correspond_def, LIST_REL_eq,
     finalize_pending_deletions_def, abstract_machine_from_state_def]
QED

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
  qspecl_then [`func`, `cenv`, `cx`, `es`, `es`, `s`, `ss`, `F`, `0`, `F`,
               `tops`, `tx`, `srcs`, `exps`, `layouts`] mp_tac
    external_halt_success_unlock >>
  simp[vyperStateTheory.return_def]
QED
