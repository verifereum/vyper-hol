(*
 * The halt half of S1 (#640): the return sequences of an external function
 * end in a Halt whose return data and effects are the success case of
 * external_call_result_rel (stated with it, in vyperLoweringCorrect, as
 * external_return_word_result_rel, external_return_prim_result_rel,
 * external_return_static_result_rel, external_return_abi_result_rel,
 * external_return_none_result_rel, external_fallthrough_result_rel and
 * their _unlock versions).  The fragment lemmas are stated with frag_exec
 * (fragExec), like the statement lemmas of stmtLoweringProps and
 * loweringSlice.
 *
 * Main lemmas:
 *   return_bytes_prim_value — the canonical return bytes of a value of a
 *                             word type (bool, integer, decimal, flag,
 *                             address, bytesN) are its 32-byte big-endian
 *                             encoding, typed_val_to_w256
 *   return_bytes_word_value — its case for the values word_value covers,
 *                             with val_to_w256
 *   return_bytes_static_value — the canonical return bytes of a value of
 *                             a static type are its bytes in memory
 *   compile_external_return_word_frag — returning a primitive word value
 *                             halts with that word as return data
 *   compile_external_return_copy_frag — returning a static complex value
 *                             (tuple, struct, fixed array) halts with its
 *                             bytes in memory as return data
 *   compile_external_return_abi_frag — returning a value through the ABI
 *                             encoder halts with its ABI encoding as
 *                             return data
 *   compile_return_none_external_frag — a return without a value halts
 *                             with empty return data
 *   compile_guarded_body_stop_frag — so does falling off the end of a
 *                             function without a return type
 *   external_halt_success   — the effects compared on success, from
 *                             state_rel at the return
 *   compile_external_return_word_unlock_frag,
 *   compile_external_return_copy_unlock_frag,
 *   compile_external_return_abi_unlock_frag,
 *   compile_return_none_external_unlock_frag,
 *   compile_guarded_body_stop_unlock_frag — the same five, in a function
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
 *   compile_external_return_copy_parts, return_copy_run — the same for a
 *                             static complex return
 *   safe_cast_some_eq       — a successful safe_cast returns its input
 *   step_alloca_frame       — ALLOCA changes nothing the return reads
 *   step_TSTORE             — TSTORE writes the running contract's
 *                             transient storage
 *   optional_unlock_view    — with nr ==> iv the optional unlock is empty
 *   optional_unlock_code, optional_unlock_frag — the optional unlock's
 *                             code, and running it
 *   unlock_stop_frag        — the optional unlock, then STOP
 *   compile_external_return_unlock — a return sequence is the optional
 *                             unlock, then the sequence without one
 *   compile_external_return_unlock_seq, optional_unlock_state — running
 *                             it: the unlock, then the sequence without
 *                             one, from a state that reads the same
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
 * Accounts stay raw during execution; the success bridge processes the
 * preserved pending-deletion list at the boundary, including on the
 * static-copy, ABI-encoder and optional-unlock return paths.
 *)

Theory loweringHalt
Ancestors
  list rich_list finite_map
  fragExec loweringSlice
  stmtLowering moduleLowering context emitHelper emitHelperProps compileEnv
  abiEncoder abiEncoderProps
  valueEncoding valueEncodingProps
  e2eDefs vyperABI contractABI vyperInterpreter vyperState vyperValue
  vyperValueOperation vfmExecution
  venomExecSemantics venomInst venomInstProofs venomState venomMemProps
  vyperTyping vyperTypeABI
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
      s1.vs_pending_deletions = s.vs_pending_deletions /\
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

(* A successful safe_cast returns its argument: it only checks bounds. *)
Theorem safe_cast_some_eq:
  (!tv v v'. safe_cast tv v = SOME v' ==> v' = v) /\
  (!tvs vs acc out.
     safe_cast_list tvs vs acc = SOME out ==> out = REVERSE acc ++ vs)
Proof
  ho_match_mp_tac safe_cast_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac
  >~ [`safe_cast_list (_::_) (_::_) _`]
  >- (simp_tac (srw_ss()) [Once safe_cast_def] >>
      Cases_on `safe_cast tv v` >> simp_tac (srw_ss()) [] >>
      rename1 `safe_cast tv v = SOME x` >>
      qpat_x_assum `!v'. _ ==> v' = v` (qspec_then `x` mp_tac) >>
      qpat_x_assum `!v'. _` (qspec_then `x` mp_tac) >>
      asm_rewrite_tac[] >> rpt strip_tac >> res_tac >>
      asm_rewrite_tac[] >> simp_tac (srw_ss()) [])
  >~ [`safe_cast _ _ = SOME _ ==> _`]
  >- (simp_tac (srw_ss()) [Once safe_cast_def, AllCaseEqs(), LET_THM] >>
      rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      simp_tac (srw_ss()) [] >>
      RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
      first_x_assum drule_all >> strip_tac >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp_tac (srw_ss()) [GSYM UNZIP_MAP, ZIP_UNZIP] >>
      qpat_x_assum `MAP FST _ = MAP FST _` (REWRITE_TAC o single o GSYM) >>
      simp_tac (srw_ss()) [GSYM UNZIP_MAP, ZIP_UNZIP]) >>
  pop_assum mp_tac >> simp_tac (srw_ss()) [Once safe_cast_def] >>
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> simp_tac (srw_ss()) []
QED

(* The source's return value of a static type is the value the lowering
   holds in memory, and the canonical return bytes are those memory bytes:
   the singleton wrapping tuple of a static type encodes as the element. *)
Theorem return_bytes_static_value:
  !tops ret tv v0 v off mem.
    evaluate_type (type_env tops) ret = SOME tv /\ safe_cast tv v0 = SOME v /\
    ~is_dynamic (vyper_to_abi_type (type_env tops) ret) /\
    val_in_memory tv v0 off mem ==>
    v = v0 /\
    return_bytes tops ret v (mem_bytes_at off (type_memory_size tv) mem)
Proof
  rpt gen_tac >> strip_tac >>
  `v = v0` by metis_tac[safe_cast_some_eq] >>
  qpat_x_assum `v = v0` SUBST_ALL_TAC >>
  `value_has_type tv v0` by metis_tac[safe_cast_result_well_typed] >>
  simp[return_bytes_def] >> IF_CASES_TAC
  >- gvs[evaluate_type_def, type_memory_size_def, mem_bytes_at_def] >>
  `?av. vyper_to_abi (type_env tops) ret v0 = SOME av` by
    metis_tac[vyper_to_abi_total] >>
  drule_all val_in_memory_static_abi >> strip_tac >>
  qexists_tac `av` >> simp[] >> rw[enc_def, REV_DEF]
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

(* The code of a static complex return (tuple, struct, fixed array) with
   no unlock: ALLOCA a buffer, MCOPY the value's m bytes of memory into it,
   RETURN them.  The buffer is fresh at st. *)
Theorem compile_external_return_copy_parts:
  !op m msz nr nkey ut iv st x st'.
    compile_external_return (SOME op) F F (AbiCopy m) msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) ==>
    ?buf.
      ~not_fresh_at st buf /\
      st'.cs_current_bb = st.cs_current_bb /\
      st'.cs_current_insts =
        st.cs_current_insts ++
        [mk_inst st.cs_next_id ALLOCA [Lit (n2w msz)] [buf];
         mk_inst (st.cs_next_id + 1) MCOPY [Var buf; op; Lit (n2w m)] [];
         mk_inst (st.cs_next_id + 2) RETURN [Var buf; Lit (n2w m)] []]
Proof
  rpt strip_tac >>
  qexists_tac `STRING #"%" (toString st.cs_next_var)` >>
  conj_tac
  >- (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_external_return_def, optional_unlock_view,
       compile_alloc_buffer_def, Once compile_abi_encode_child_def,
       emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >>
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
         ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
         ss.vs_pending_deletions = s.vs_pending_deletions
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
   s2'.vs_logs = s.vs_logs /\ s2'.vs_requests = s.vs_requests /\
   s2'.vs_pending_deletions = s.vs_pending_deletions` by
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

(* Running the code of compile_external_return_copy_parts: the RETURN
   halts with the m bytes at the operand's address as return data, and
   nothing on the way touches the effects.  m < dimword keeps the size
   literal from wrapping. *)
Theorem return_copy_run:
  !fuel ctx fn s bb id buf op p m msz.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ALLOCA [Lit (n2w msz)] [buf]) /\
    get_instruction bb (s.vs_inst_idx + 1) =
      SOME (mk_inst (id + 1) MCOPY [Var buf; op; Lit (n2w m)] []) /\
    get_instruction bb (s.vs_inst_idx + 2) =
      SOME (mk_inst (id + 2) RETURN [Var buf; Lit (n2w m)] []) /\
    eval_operand op s = SOME p /\ op <> Var buf /\ m < dimword(:256) ==>
    ?ss. run_from fuel ctx fn s = Halt ss /\
         ss.vs_returndata = mem_bytes_at (w2n p) m s.vs_memory /\
         ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
         ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
         ss.vs_pending_deletions = s.vs_pending_deletions
Proof
  rpt strip_tac >>
  qspecl_then [`id`, `n2w msz`, `buf`, `s`] strip_assume_tac
    step_alloca_frame >>
  qabbrev_tac `s1' = s1 with vs_inst_idx := s.vs_inst_idx + 1` >>
  `run_from fuel ctx fn s = run_from fuel ctx fn s1'` by
    (qspecl_then [`fuel`, `ctx`, `fn`, `s`, `bb`,
                  `mk_inst id ALLOCA [Lit (n2w msz)] [buf]`, `s1`]
       mp_tac run_from_step >>
     simp[is_terminator_def, Abbr `s1'`, arithmeticTheory.ADD1]) >>
  `eval_operand (Var buf) s1' = SOME a /\ eval_operand op s1' = SOME p` by
    (Cases_on `op` >> gvs[Abbr `s1'`, eval_operand_def, lookup_var_def]) >>
  `w2n (n2w m : bytes32) = m` by simp[] >>
  qabbrev_tac `s2' = mcopy (w2n a) (w2n p) m s1' with
                       vs_inst_idx := s.vs_inst_idx + 2` >>
  `step_inst_base (mk_inst (id + 1) MCOPY [Var buf; op; Lit (n2w m)] []) s1'
   = OK (mcopy (w2n a) (w2n p) m s1')` by
    simp[step_inst_base_def, mk_inst_def, eval_operand_def] >>
  `run_from fuel ctx fn s1' = run_from fuel ctx fn s2'` by
    (qspecl_then [`fuel`, `ctx`, `fn`, `s1'`, `bb`,
                  `mk_inst (id + 1) MCOPY [Var buf; op; Lit (n2w m)] []`,
                  `mcopy (w2n a) (w2n p) m s1'`] mp_tac run_from_step >>
     simp[is_terminator_def, Abbr `s2'`, Abbr `s1'`, arithmeticTheory.ADD1]) >>
  `eval_operand (Var buf) s2' = SOME a` by
    gvs[Abbr `s2'`, eval_operand_def, lookup_var_def, mcopy_def,
        write_memory_with_expansion_def] >>
  `s2'.vs_current_bb = s.vs_current_bb /\
   s2'.vs_inst_idx = s.vs_inst_idx + 2 /\
   s2'.vs_accounts = s.vs_accounts /\ s2'.vs_transient = s.vs_transient /\
   s2'.vs_logs = s.vs_logs /\ s2'.vs_requests = s.vs_requests /\
   s2'.vs_pending_deletions = s.vs_pending_deletions` by
    simp[Abbr `s2'`, Abbr `s1'`, mcopy_def, write_memory_with_expansion_def] >>
  `mem_bytes_at (w2n a) m s2'.vs_memory = mem_bytes_at (w2n p) m s.vs_memory`
    by simp[Abbr `s2'`, Abbr `s1'`, mem_bytes_at_def, mcopy_padded_read] >>
  qabbrev_tac `ss = halt_state
                     (set_returndata (mem_bytes_at (w2n p) m s.vs_memory) s2')` >>
  `step_inst_base (mk_inst (id + 2) RETURN [Var buf; Lit (n2w m)] []) s2' =
   Halt ss` by
    (qspecl_then [`Var buf`, `Lit (n2w m)`, `a`, `n2w m`, `id + 2`, `s2'`]
       mp_tac step_RETURN >>
     simp[eval_operand_def, GSYM mem_bytes_at_def, Abbr `ss`]) >>
  qexists_tac `ss` >>
  qspecl_then [`fuel`, `ctx`, `fn`, `s2'`, `bb`,
               `mk_inst (id + 2) RETURN [Var buf; Lit (n2w m)] []`, `ss`]
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
            ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
            ss.vs_pending_deletions = s.vs_pending_deletions ==>
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

(* Returning a static complex value (tuple, struct, fixed array): the code
   of compile_external_return_copy_parts halts with the m bytes at the
   operand's address as return data. *)
Theorem compile_external_return_copy_frag:
  !ctx op m msz nr nkey ut iv st x st' P Q R.
    compile_external_return (SOME op) F F (AbiCopy m) msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    m < dimword(:256) /\
    (!s. P s ==>
         ?p. eval_operand op s = SOME p /\
             !ss. ss.vs_returndata = mem_bytes_at (w2n p) m s.vs_memory /\
                  ss.vs_accounts = s.vs_accounts /\
                  ss.vs_transient = s.vs_transient /\
                  ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
                  ss.vs_pending_deletions = s.vs_pending_deletions ==>
                  R (Halt ss)) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_external_return_copy_parts >> strip_tac >>
  simp[frag_exec_def] >> rpt strip_tac >> disj2_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `op <> Var buf` by metis_tac[] >>
  first_x_assum drule >> strip_tac >>
  qspecl_then [`0`, `ctx`, `fn`, `s`, `bb`, `st.cs_next_id`, `buf`, `op`,
               `p`, `m`, `msz`] mp_tac return_copy_run >>
  impl_tac
  >- (qpat_x_assum `!i. _` (fn th =>
        map_every (fn n => mp_tac (Q.SPEC n th)) [`0`, `1`, `2`]) >>
      simp[]) >>
  strip_tac >> qexists_tac `0` >> simp[exit_result_def]
QED

Definition halt_comp_grows_def:
  halt_comp_grows (m : 'a compiler) <=>
    !s x t. m s = (x,t) ==>
      cs_extends s t /\ s.cs_next_id <= t.cs_next_id /\
      s.cs_next_var <= t.cs_next_var
End

Theorem halt_comp_grows_return[local]:
  !x. halt_comp_grows (comp_return x)
Proof
  simp[halt_comp_grows_def, comp_return_def, cs_extends_refl]
QED

Theorem halt_comp_grows_bind[local]:
  !m f. halt_comp_grows m /\ (!a. halt_comp_grows (f a)) ==>
    halt_comp_grows (comp_bind m f)
Proof
  rw[halt_comp_grows_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >>
  metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem halt_comp_grows_ignore_bind[local]:
  !m n. halt_comp_grows m /\ halt_comp_grows n ==>
    halt_comp_grows (comp_ignore_bind m n)
Proof
  rpt strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  irule halt_comp_grows_bind >> simp[]
QED

Theorem halt_comp_grows_emit[local]:
  !i. halt_comp_grows (emit i)
Proof
  rw[halt_comp_grows_def] >>
  drule cs_extends_emit >> strip_tac >>
  gvs[emit_def]
QED

Theorem halt_comp_grows_fresh_id[local]:
  halt_comp_grows fresh_id
Proof
  rw[halt_comp_grows_def] >>
  drule cs_extends_fresh_id >> strip_tac >>
  gvs[fresh_id_def]
QED

Theorem halt_comp_grows_fresh_var[local]:
  halt_comp_grows fresh_var
Proof
  rw[halt_comp_grows_def] >>
  drule cs_extends_fresh_var >> strip_tac >>
  gvs[fresh_var_def]
QED

Theorem halt_comp_grows_fresh_label[local]:
  !sfx. halt_comp_grows (fresh_label sfx)
Proof
  rw[halt_comp_grows_def] >>
  drule cs_extends_fresh_label >> strip_tac >>
  gvs[fresh_label_def]
QED

Theorem halt_comp_grows_new_block[local]:
  !lbl. halt_comp_grows (new_block lbl)
Proof
  rw[halt_comp_grows_def] >>
  drule cs_extends_new_block >> strip_tac >>
  gvs[new_block_def]
QED

Theorem halt_comp_grows_emit_op[local]:
  !opc args. halt_comp_grows (emit_op opc args)
Proof
  rw[emit_op_def] >> irule halt_comp_grows_bind >>
  simp[halt_comp_grows_fresh_id] >> gen_tac >>
  irule halt_comp_grows_bind >> simp[halt_comp_grows_fresh_var] >>
  gen_tac >> irule halt_comp_grows_ignore_bind >>
  simp[halt_comp_grows_emit, halt_comp_grows_return]
QED

Theorem halt_comp_grows_emit_inst[local]:
  !opc args outs. halt_comp_grows (emit_inst opc args outs)
Proof
  rw[emit_inst_def] >> irule halt_comp_grows_bind >>
  simp[halt_comp_grows_fresh_id, halt_comp_grows_emit]
QED

Theorem halt_comp_grows_emit_void[local]:
  !opc args. halt_comp_grows (emit_void opc args)
Proof
  rw[emit_void_def] >> irule halt_comp_grows_bind >>
  simp[halt_comp_grows_fresh_id, halt_comp_grows_emit]
QED

Theorem halt_comp_grows_alloc_buffer[local]:
  !n. halt_comp_grows (compile_alloc_buffer n)
Proof
  rw[compile_alloc_buffer_def] >> irule halt_comp_grows_bind >>
  simp[halt_comp_grows_emit_op, halt_comp_grows_return]
QED

Theorem halt_comp_grows_static[local]:
  !dst src. halt_comp_grows (compile_abi_encode_static dst src)
Proof
  rw[compile_abi_encode_static_def] >>
  irule halt_comp_grows_bind >> simp[halt_comp_grows_emit_op] >>
  gen_tac >> irule halt_comp_grows_ignore_bind >>
  simp[halt_comp_grows_emit_void, halt_comp_grows_return]
QED

Theorem halt_comp_grows_static_info[local]:
  !dst src ei. halt_comp_grows (compile_abi_encode_static_info dst src ei)
Proof
  rpt gen_tac >> Cases_on `ei` >> simp[compile_abi_encode_static_info_def,
    halt_comp_grows_static, halt_comp_grows_return] >>
  irule halt_comp_grows_ignore_bind >>
  simp[halt_comp_grows_emit_void, halt_comp_grows_return]
QED

Theorem halt_comp_grows_dyn_static_loop[local]:
  !dst src ei asz msz len.
    halt_comp_grows (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  rpt gen_tac >> rewrite_tac[compile_abi_encode_dyn_static_loop_def] >>
  rpt (FIRST [CHANGED_TAC (simp[LET_THM,
          halt_comp_grows_alloc_buffer, halt_comp_grows_emit_op,
          halt_comp_grows_emit_void, halt_comp_grows_emit_inst,
          halt_comp_grows_fresh_label, halt_comp_grows_new_block,
          halt_comp_grows_static_info]),
        irule halt_comp_grows_bind >> conj_tac,
        irule halt_comp_grows_ignore_bind >> conj_tac,
        gen_tac])
QED

Theorem halt_comp_grows_encoder[local]:
  (!dst cp ei dyn off dp.
    halt_comp_grows (compile_abi_encode_child dst cp ei dyn off dp)) /\
  (!dst src ei. halt_comp_grows (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src eis so ho dp.
    halt_comp_grows (compile_abi_encode_complex_elems dst src eis so ho dp)) /\
  (!dst src ei asz msz len.
    halt_comp_grows (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >>
  rpt strip_tac >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  rpt (FIRST [CHANGED_TAC (gvs[LET_THM,
          halt_comp_grows_alloc_buffer, halt_comp_grows_emit_op,
          halt_comp_grows_emit_void, halt_comp_grows_emit_inst,
          halt_comp_grows_fresh_label, halt_comp_grows_new_block,
          halt_comp_grows_static, halt_comp_grows_return,
          halt_comp_grows_dyn_static_loop]),
        irule halt_comp_grows_bind >> conj_tac,
        irule halt_comp_grows_ignore_bind >> conj_tac,
        gen_tac, IF_CASES_TAC])
QED

Theorem compile_abi_encode_to_buf_extends:
  !dst src ei st len st'.
    compile_abi_encode_to_buf dst src ei st = (len,st') ==>
    cs_extends st st'
Proof
  mp_tac (cj 2 halt_comp_grows_encoder) >>
  simp[halt_comp_grows_def] >> metis_tac[]
QED

Theorem compile_abi_encode_to_buf_next_id:
  !dst src ei st len st'.
    compile_abi_encode_to_buf dst src ei st = (len,st') ==>
    st.cs_next_id <= st'.cs_next_id
Proof
  mp_tac (cj 2 halt_comp_grows_encoder) >>
  simp[halt_comp_grows_def] >> metis_tac[]
QED

Theorem frag_ids_count_diff:
  !a b. frag_ids a b = count b.cs_next_id DIFF count a.cs_next_id
Proof
  rw[frag_ids_def, pred_setTheory.EXTENSION] >> decide_tac
QED

Theorem frag_ids_card:
  !a b. CARD (frag_ids a b) = b.cs_next_id - a.cs_next_id
Proof
  rpt gen_tac >> Cases_on `a.cs_next_id <= b.cs_next_id`
  >- (`count b.cs_next_id INTER count a.cs_next_id = count a.cs_next_id`
        by (rw[pred_setTheory.EXTENSION] >> decide_tac) >>
      simp[frag_ids_count_diff, pred_setTheory.CARD_DIFF_EQN]) >>
  `frag_ids a b = {}` by
    (rw[frag_ids_def, pred_setTheory.EXTENSION] >> decide_tac) >> simp[]
QED

Theorem compile_external_return_abi_parts:
  !op ei msz nr nkey ut iv st x st'.
    compile_external_return (SOME op) F F ei msz nr nkey ut iv st =
      (x, st') /\ (nr ==> iv) ==>
    ?buf sa len sb.
      compile_alloc_buffer msz st = (buf, sa) /\
      compile_abi_encode_to_buf buf.buf_operand op ei sa = (len, sb) /\
      emit_inst RETURN [buf.buf_operand; len] [] sb = (x, st')
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_external_return_def, optional_unlock_view,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> metis_tac[]
QED

Theorem step_alloca_fresh:
  !id n out s.
    FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) ==>
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s =
      OK (update_var out (n2w s.vs_alloca_next)
        (s with <| vs_allocas := s.vs_allocas |+
                      (id, (s.vs_alloca_next,n));
                   vs_alloca_next := s.vs_alloca_next + n |>))
Proof
  rpt strip_tac >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_alloca_def, wordsTheory.w2n_n2w]
QED

Theorem step_alloca_fresh_inv:
  !id n out s s1.
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    alloca_inv s ==> alloca_inv s1
Proof
  rpt strip_tac >> irule alloca_inv_step_inst >>
  qexistsl_tac [`ARB`, `0`, `mk_inst id ALLOCA [Lit (n2w n)] [out]`, `s`] >>
  simp[step_inst_non_invoke]
QED

Theorem enc_scratch_unallocated:
  !st st' lo top s.
    alloca_inv s /\ lo <= s.vs_alloca_next /\ top < dimword (:256) /\
    (!i. i IN frag_ids st st' ==> FLOOKUP s.vs_allocas i = NONE) /\
    s.vs_alloca_next + 32 * (st'.cs_next_id - st.cs_next_id) <= top ==>
    enc_scratch (frag_ids st st') lo top s
Proof
  rpt strip_tac >>
  `{i | i IN frag_ids st st' /\ FLOOKUP s.vs_allocas i = NONE} =
    frag_ids st st'` by
    (rw[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  simp[enc_scratch_def, frag_ids_card] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem enc_pre_unallocated:
  !st st' ops lo top tv v src dst n s.
    (!y. MEM (Var y) ops ==> not_fresh_at st y) /\
    val_in_memory tv v src s.vs_memory /\
    src + type_memory_size tv <= dst /\ dst + n <= lo /\
    alloca_inv s /\ lo <= s.vs_alloca_next /\ top < dimword (:256) /\
    (!i. i IN frag_ids st st' ==> FLOOKUP s.vs_allocas i = NONE) /\
    s.vs_alloca_next + 32 * (st'.cs_next_id - st.cs_next_id) <= top ==>
    enc_pre st st' ops lo top tv v src [(dst,n)] s
Proof
  rpt strip_tac >>
  `enc_scratch (frag_ids st st') lo top s` by
    (irule enc_scratch_unallocated >> simp[]) >>
  simp[enc_pre_def, venomMemDefsTheory.regions_disjoint_def]
QED

Theorem step_alloca_enc_pre:
  !id msz out op s p st st' tv v n top.
    FLOOKUP s.vs_allocas id = NONE /\ id NOTIN frag_ids st st' /\
    (!y. op = Var y ==> y <> out) /\
    (!y. MEM (Var y) [Var out;op] ==> not_fresh_at st y) /\
    eval_operand op s = SOME p /\
    val_in_memory tv v (w2n p) s.vs_memory /\
    w2n p + type_memory_size tv <= s.vs_alloca_next /\ n <= msz /\
    alloca_inv s /\
    (!i. i IN frag_ids st st' ==> FLOOKUP s.vs_allocas i = NONE) /\
    s.vs_alloca_next + msz + 32 * (st'.cs_next_id - st.cs_next_id) <= top /\
    top < dimword (:256) ==>
    ?s1.
      step_inst_base (mk_inst id ALLOCA [Lit (n2w msz)] [out]) s = OK s1 /\
      eval_operand (Var out) s1 = SOME (n2w s.vs_alloca_next) /\
      eval_operand op s1 = SOME p /\
      enc_pre st st' [Var out;op] (s.vs_alloca_next + msz) top
        tv v (w2n p) [(s.vs_alloca_next,n)] s1 /\
      s1.vs_accounts = s.vs_accounts /\ s1.vs_transient = s.vs_transient /\
      s1.vs_logs = s.vs_logs /\ s1.vs_requests = s.vs_requests /\
      s1.vs_pending_deletions = s.vs_pending_deletions
Proof
  rpt strip_tac >>
  `msz < dimword (:256)` by decide_tac >>
  drule_all step_alloca_fresh >>
  disch_then (qspec_then `out` assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK s1` >> qexists_tac `s1` >>
  `alloca_inv s1` by (irule step_alloca_fresh_inv >> metis_tac[]) >>
  simp[Abbr `s1`, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE] >>
  conj_tac
  >- (Cases_on `op` >> gvs[eval_operand_def, lookup_var_def,
        update_var_def, FLOOKUP_UPDATE]) >>
  irule enc_pre_unallocated >>
  gvs[update_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem compile_alloc_buffer_parts:
  !n st buf st'.
    compile_alloc_buffer n st = (buf,st') ==>
    buf.buf_operand = Var (STRING #"%" (toString st.cs_next_var)) /\
    buf.buf_size = n /\ st'.cs_next_id = st.cs_next_id + 1 /\
    st'.cs_next_var = st.cs_next_var + 1 /\
    ~not_fresh_at st (STRING #"%" (toString st.cs_next_var)) /\
    not_fresh_at st' (STRING #"%" (toString st.cs_next_var)) /\
    (!y. not_fresh_at st y ==> not_fresh_at st' y)
Proof
  rpt gen_tac >>
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_TRANS,
            arithmeticTheory.LESS_EQ_ADD]
QED

Theorem compile_alloc_buffer_frag:
  !ctx n st buf st' P Q R.
    compile_alloc_buffer n st = (buf,st') /\
    (!s. P s ==> ?s1.
      step_inst_base
        (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
          [STRING #"%" (toString st.cs_next_var)]) s = OK s1 /\
      Q (s1 with vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  irule frag_exec_run_inst_seq >>
  simp[exprLoweringPropsTheory.emitted_insts_def,
       rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def,
       exprLoweringPropsTheory.run_inst_seq_def] >>
  rpt strip_tac >> disj1_tac >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `s1` >> gvs[mk_inst_def]
QED

Theorem enc_frame_var:
  !st st' lo top outs s0 s name w.
    enc_frame st st' lo top outs s0 s /\ not_fresh_at st name /\
    eval_operand (Var name) s0 = SOME w ==>
    eval_operand (Var name) s = SOME w
Proof
  simp[enc_frame_def, eval_operand_def] >> metis_tac[]
QED

(* The encoder preserves all effects, including deferred deletions. *)
Theorem enc_frame_effects:
  !st st' lo top outs s0 s.
    enc_frame st st' lo top outs s0 s ==>
    s.vs_accounts = s0.vs_accounts /\ s.vs_transient = s0.vs_transient /\
    s.vs_logs = s0.vs_logs /\ s.vs_requests = s0.vs_requests /\
    s.vs_pending_deletions = s0.vs_pending_deletions
Proof
  simp[enc_frame_def]
QED

Theorem return_buffer_run:
  !fuel ctx fn s bb id buf len b bytes.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id RETURN [buf;len] []) /\
    eval_operand buf s = SOME b /\
    eval_operand len s = SOME (n2w (LENGTH bytes)) /\
    LENGTH bytes < dimword (:256) /\
    mem_bytes_at (w2n b) (LENGTH bytes) s.vs_memory = bytes ==>
    ?ss. run_from fuel ctx fn s = Halt ss /\ ss.vs_returndata = bytes /\
      ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
      ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
      ss.vs_pending_deletions = s.vs_pending_deletions
Proof
  rpt strip_tac >>
  qabbrev_tac `ss = halt_state (set_returndata bytes s)` >>
  `step_inst_base (mk_inst id RETURN [buf;len] []) s = Halt ss` by
    (qspecl_then [`buf`, `len`] mp_tac step_RETURN >>
     disch_then drule >> disch_then drule >>
     simp[GSYM mem_bytes_at_def, Abbr `ss`]) >>
  qexists_tac `ss` >> conj_tac
  >- (irule run_from_halt >>
      qexistsl_tac [`bb`, `mk_inst id RETURN [buf;len] []`] >>
      simp[mk_inst_def]) >>
  simp[Abbr `ss`, halt_state_def, set_returndata_def]
QED

Theorem emit_return_buffer_frag:
  !ctx buf len st x st' bytes P Q R.
    emit_inst RETURN [buf;len] [] st = (x,st') /\
    (!s. P s ==> ?b.
      eval_operand buf s = SOME b /\
      eval_operand len s = SOME (n2w (LENGTH bytes)) /\
      LENGTH bytes < dimword (:256) /\
      mem_bytes_at (w2n b) (LENGTH bytes) s.vs_memory = bytes /\
      (!ss. ss.vs_returndata = bytes /\ ss.vs_accounts = s.vs_accounts /\
        ss.vs_transient = s.vs_transient /\ ss.vs_logs = s.vs_logs /\
        ss.vs_requests = s.vs_requests /\
        ss.vs_pending_deletions = s.vs_pending_deletions ==> R (Halt ss))) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[frag_exec_def] >> rpt strip_tac >> disj2_tac >>
  drule fn_has_code_same_block >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx =
     SOME (mk_inst st.cs_next_id RETURN [buf;len] [])` by simp[] >>
  drule_all (SRULE [] return_buffer_run) >>
  disch_then (qspecl_then [`0`, `ctx`] mp_tac) >>
  strip_tac >> qexists_tac `0` >> simp[exit_result_def]
QED

Theorem enc_pre_inst_idx[simp]:
  !st st' ops lo top tv v src outs s k.
    enc_pre st st' ops lo top tv v src outs (s with vs_inst_idx := k) =
    enc_pre st st' ops lo top tv v src outs s
Proof
  simp[enc_pre_def, enc_scratch_def, venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def]
QED

Theorem compile_alloc_buffer_extends:
  !n st buf st'. compile_alloc_buffer n st = (buf,st') ==>
    cs_extends st st'
Proof
  mp_tac halt_comp_grows_alloc_buffer >>
  simp[halt_comp_grows_def] >> metis_tac[]
QED

Theorem emit_inst_metadata:
  !opc ops outs st x st'. emit_inst opc ops outs st = (x,st') ==>
    st'.cs_next_id = st.cs_next_id + 1 /\ cs_extends st st'
Proof
  rpt gen_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> irule cs_extends_same_block >> simp[]
QED

Theorem compile_alloc_buffer_enc_frag:
  !ctx msz st buf sa sb sf op s0 p tv v n R.
    compile_alloc_buffer msz st = (buf,sa) /\
    sa.cs_next_id <= sb.cs_next_id /\ sb.cs_next_id <= sf.cs_next_id /\
    (!y. op = Var y ==> not_fresh_at st y) /\
    eval_operand op s0 = SOME p /\
    val_in_memory tv v (w2n p) s0.vs_memory /\
    w2n p + type_memory_size tv <= s0.vs_alloca_next /\ n <= msz /\
    alloca_inv s0 /\
    (!i. i IN frag_ids st sf ==> FLOOKUP s0.vs_allocas i = NONE) /\
    s0.vs_alloca_next + msz + 32 * (sf.cs_next_id - st.cs_next_id) <
      dimword (:256) ==>
    frag_exec ctx st sa (\s. s = s0)
      (\s1. eval_operand buf.buf_operand s1 = SOME (n2w s0.vs_alloca_next) /\
        eval_operand op s1 = SOME p /\
        enc_pre sa sb [buf.buf_operand;op] (s0.vs_alloca_next + msz)
          (s0.vs_alloca_next + msz + 32 * (sf.cs_next_id - st.cs_next_id))
          tv v (w2n p) [(s0.vs_alloca_next,n)] s1 /\
        s1.vs_accounts = s0.vs_accounts /\ s1.vs_transient = s0.vs_transient /\
        s1.vs_logs = s0.vs_logs /\ s1.vs_requests = s0.vs_requests /\
        s1.vs_pending_deletions = s0.vs_pending_deletions) R
Proof
  rpt strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  irule compile_alloc_buffer_frag >>
  qexistsl_tac [`buf`, `msz`] >>
  asm_simp_tac (srw_ss()) [instIdxIndepTheory.eval_op_inst_idx] >>
  irule step_alloca_enc_pre >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      gvs[frag_ids_def] >> decide_tac) >>
  conj_tac >- (simp[frag_ids_def] >> decide_tac) >>
  first_x_assum irule >> simp[frag_ids_def] >> decide_tac
QED

Theorem compile_abi_encode_return_frag:
  !ctx name op ei sa len sb x sf env ty tv v av s1 b p lo top Q R.
    compile_abi_encode_to_buf (Var name) op ei sa = (len,sb) /\
    emit_inst RETURN [Var name;len] [] sb = (x,sf) /\
    abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
    not_fresh_at sa name /\ eval_operand (Var name) s1 = SOME b /\
    eval_operand op s1 = SOME p /\
    enc_pre sa sb [Var name;op] lo top tv v (w2n p)
      [(w2n b,LENGTH (enc (vyper_to_abi_type env ty) av))] s1 /\
    LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
    (!ss. ss.vs_returndata = enc (vyper_to_abi_type env ty) av /\
      ss.vs_accounts = s1.vs_accounts /\ ss.vs_transient = s1.vs_transient /\
      ss.vs_logs = s1.vs_logs /\ ss.vs_requests = s1.vs_requests /\
      ss.vs_pending_deletions = s1.vs_pending_deletions ==>
      R (Halt ss)) ==>
    frag_exec ctx sa sf (\s. s = s1) Q R
Proof
  rpt strip_tac >>
  drule_all (cj 2 compile_abi_encode_frag) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule compile_abi_encode_to_buf_extends >> strip_tac >>
  drule emit_inst_metadata >> strip_tac >>
  qmatch_asmsub_abbrev_tac `frag_exec ctx sa sb _ post _` >>
  irule frag_exec_seq >> qexistsl_tac [`post`, `sb`] >>
  simp[] >> conj_tac
  >- (irule frag_exec_conseq >>
      qexistsl_tac [`\s. s = s1`, `post`, `\r. F`] >> simp[]) >>
  irule emit_return_buffer_frag >>
  qexistsl_tac [`Var name`, `enc (vyper_to_abi_type env ty) av`, `len`, `x`] >>
  simp[Abbr `post`] >> rpt strip_tac >>
  qexists_tac `b` >>
  `eval_operand (Var name) s = SOME b` by
    (irule enc_frame_var >> metis_tac[]) >>
  drule enc_frame_effects >> strip_tac >> simp[]
QED

(* Returning a value through the ABI encoder with plan ei for its type
   (the non-word, non-raw path, without a lock release): ALLOCA a buffer
   of msz bytes, encode the value into it, RETURN the encoding.  The
   buffer and the encoder's scratch cells are fresh allocas, above the
   value: none of the fragment's ALLOCAs has run, and the value lies below
   the alloca frontier.  The frontier stays below 2 ** 256 while they run,
   and the encoding fits in the buffer. *)
Theorem compile_external_return_abi_frag:
  !ctx op ei msz nr nkey ut iv st x st' env ty tv v av P Q R.
    compile_external_return (SOME op) F F ei msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
    LENGTH (enc (vyper_to_abi_type env ty) av) <= msz /\
    (!s. P s ==>
         ?p. eval_operand op s = SOME p /\
             val_in_memory tv v (w2n p) s.vs_memory /\
             w2n p + type_memory_size tv <= s.vs_alloca_next /\
             alloca_inv s /\
             (!i. i IN frag_ids st st' ==> FLOOKUP s.vs_allocas i = NONE) /\
             s.vs_alloca_next + msz + 32 * (st'.cs_next_id - st.cs_next_id) <
               dimword (:256) /\
             !ss. ss.vs_returndata = enc (vyper_to_abi_type env ty) av /\
                  ss.vs_accounts = s.vs_accounts /\
                  ss.vs_transient = s.vs_transient /\
                  ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
                  ss.vs_pending_deletions = s.vs_pending_deletions ==>
                  R (Halt ss)) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >>
  drule_all compile_external_return_abi_parts >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule compile_abi_encode_to_buf_next_id >> strip_tac >>
  drule compile_abi_encode_to_buf_extends >> strip_tac >>
  drule emit_inst_metadata >> strip_tac >>
  irule frag_exec_pointwise >> qx_gen_tac `s0` >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `sb.cs_next_id <= st'.cs_next_id` by decide_tac >>
  drule_all compile_alloc_buffer_enc_frag >>
  disch_then (qspecl_then [`ctx`, `R`] mp_tac) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `frag_exec ctx st sa _ ready R` >>
  irule frag_exec_seq >> qexistsl_tac [`ready`, `sa`] >>
  simp[] >> conj_tac
  >- metis_tac[cs_extends_trans] >>
  qpat_x_assum `frag_exec ctx st sa _ _ _` kall_tac >>
  qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  irule frag_exec_pointwise >> simp[Abbr `ready`] >>
  qx_gen_tac `s1` >> strip_tac >>
  `s0.vs_alloca_next < dimword (:256) /\
   LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256)` by decide_tac >>
  `enc_pre sa sb [buf.buf_operand;op] (msz + s0.vs_alloca_next)
      (msz + (s0.vs_alloca_next + 32 * (sb.cs_next_id + 1 - st.cs_next_id)))
      tv v (w2n p)
      [(w2n (n2w s0.vs_alloca_next : 256 word),
        LENGTH (enc (vyper_to_abi_type env ty) av))] s1` by
    simp[wordsTheory.w2n_n2w] >>
  `!ss. ss.vs_returndata = enc (vyper_to_abi_type env ty) av /\
    ss.vs_accounts = s1.vs_accounts /\ ss.vs_transient = s1.vs_transient /\
    ss.vs_logs = s1.vs_logs /\ ss.vs_requests = s1.vs_requests /\
    ss.vs_pending_deletions = s1.vs_pending_deletions ==>
    R (Halt ss)` by (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  qpat_x_assum `buf.buf_operand = _` SUBST_ALL_TAC >>
  drule_all compile_abi_encode_return_frag >>
  disch_then (qspecl_then [`ctx`, `Q`] ACCEPT_TAC)
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
            ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
            ss.vs_pending_deletions = s.vs_pending_deletions ==>
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
            ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
            ss.vs_pending_deletions = s.vs_pending_deletions ==>
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

(* The state after the optional unlock, at the start of the return
   sequence without an unlock: only the transient storage (for a release)
   and the instruction index differ, so operands, memory and allocas read
   the same.  Pending deletions are preserved until the success boundary. *)
Theorem optional_unlock_state:
  !nr iv nkey n s u.
    u = (if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
          vs_inst_idx := n ==>
    (!op. eval_operand op u = eval_operand op s) /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    (alloca_inv u <=> alloca_inv s) /\
    u.vs_accounts = s.vs_accounts /\
    u.vs_transient =
      (if nr /\ ~iv then (tstore (n2w nkey) 0w s).vs_transient
       else s.vs_transient) /\
    u.vs_logs = s.vs_logs /\ u.vs_requests = s.vs_requests /\
    u.vs_pending_deletions = s.vs_pending_deletions
Proof
  rpt gen_tac >> strip_tac >> Cases_on `nr /\ ~iv` >>
  gvs[tstore_def, venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.allocas_non_overlapping_def,
      venomMemDefsTheory.alloca_next_valid_def] >>
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

(* A return sequence with the optional unlock first: the unlock, then
   the sequence without one from the state it leaves. *)
Theorem compile_external_return_unlock_seq:
  !ctx rv p rr ei msz nr nkey ut iv st x st' P Q R.
    compile_external_return rv p rr ei msz nr nkey ut iv st = (x, st') /\
    (nr /\ ~iv ==> ut) /\
    (!st1.
       compile_external_return rv p rr ei msz F nkey ut iv st1 = (x, st') /\
       st1.cs_next_var = st.cs_next_var /\
       st.cs_next_id <= st1.cs_next_id ==>
       cs_extends st1 st' /\
       frag_exec ctx st1 st'
         (\s1. ?s. P s /\
               s1 = (if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
                      vs_inst_idx := LENGTH st1.cs_current_insts)
         Q R) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >>
  drule compile_external_return_unlock >> strip_tac >>
  drule_all optional_unlock_code >> strip_tac >>
  `st1.cs_next_var = st.cs_next_var /\ st.cs_next_id <= st1.cs_next_id /\
   cs_extends st st1` by
    (qpat_x_assum `st1 = _` SUBST1_TAC >> rw[] >>
     irule cs_extends_same_block >> simp[]) >>
  qpat_x_assum `st1 = _` kall_tac >>
  first_x_assum drule_all >> strip_tac >>
  irule frag_exec_seq >>
  qexistsl_tac
    [`\s1. ?s. P s /\
           s1 = (if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
                  vs_inst_idx := LENGTH st1.cs_current_insts`, `st1`] >>
  simp[] >>
  qspecl_then
    [`ctx`, `nr`, `nkey`, `ut`, `iv`, `st`, `st1`, `P`,
     `\s1. ?s. P s /\
           s1 = (if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
                  vs_inst_idx := LENGTH st1.cs_current_insts`,
     `R`] mp_tac optional_unlock_frag >>
  impl_tac >- (simp[] >> metis_tac[]) >> simp[]
QED

(* Returning a static complex value, with the optional unlock first. *)
Theorem compile_external_return_copy_unlock_frag:
  !ctx op m msz nr nkey ut iv st x st' P Q R.
    compile_external_return (SOME op) F F (AbiCopy m) msz nr nkey ut iv st =
      (x, st') /\
    (nr /\ ~iv ==> ut) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    m < dimword(:256) /\
    (!s. P s ==>
         ?p. eval_operand op s = SOME p /\
             !ss. ss.vs_returndata = mem_bytes_at (w2n p) m s.vs_memory /\
                  ss.vs_accounts = s.vs_accounts /\
                  ss.vs_transient =
                    (if nr /\ ~iv then (tstore (n2w nkey) 0w s).vs_transient
                     else s.vs_transient) /\
                  ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
                  ss.vs_pending_deletions = s.vs_pending_deletions ==>
                  R (Halt ss)) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `SOME op`, `F`, `F`, `AbiCopy m`, `msz`, `nr`, `nkey`,
               `ut`, `iv`, `st`, `x`, `st'`, `P`, `Q`, `R`] mp_tac
    compile_external_return_unlock_seq >>
  impl_tac >> simp[] >> gen_tac >> strip_tac >> conj_tac
  >- (drule compile_external_return_copy_parts >> simp[] >> strip_tac >>
      irule cs_extends_same_block >> simp[] >>
      qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[compile_external_return_def, compile_alloc_buffer_def,
           Once compile_abi_encode_child_def, emit_op_def, emit_void_def,
           emit_inst_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
      rpt strip_tac >> gvs[]) >>
  qspecl_then [`ctx`, `op`, `m`, `msz`, `F`, `nkey`, `ut`, `iv`, `st1`, `()`,
               `st'`] mp_tac compile_external_return_copy_frag >>
  asm_rewrite_tac[] >> disch_then irule >> conj_tac
  >- (rpt strip_tac >> gvs[not_fresh_at_def]) >>
  rpt strip_tac >>
  qpat_x_assum `(\s1. _) _` (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `_ = (if _ then _ else _) with vs_inst_idx := _`
    SUBST_ALL_TAC >>
  rename1 `P s` >>
  qpat_x_assum `!s. P s ==> _` drule >> strip_tac >>
  qspecl_then [`nr`, `iv`, `nkey`, `LENGTH st1.cs_current_insts`, `s`,
    `(if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
       vs_inst_idx := LENGTH st1.cs_current_insts`]
    mp_tac optional_unlock_state >>
  REWRITE_TAC[] >> strip_tac >>
  qexists_tac `p` >> asm_rewrite_tac[]
QED

(* Returning a value through the ABI encoder, with the optional unlock
   first.  The unlock's TSTORE takes an instruction id below the
   encoder's, so the hypotheses at st cover the sequence after it. *)
Theorem compile_external_return_abi_unlock_frag:
  !ctx op ei msz nr nkey ut iv st x st' env ty tv v av P Q R.
    compile_external_return (SOME op) F F ei msz nr nkey ut iv st =
      (x, st') /\
    (nr /\ ~iv ==> ut) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
    LENGTH (enc (vyper_to_abi_type env ty) av) <= msz /\
    (!s. P s ==>
         ?p. eval_operand op s = SOME p /\
             val_in_memory tv v (w2n p) s.vs_memory /\
             w2n p + type_memory_size tv <= s.vs_alloca_next /\
             alloca_inv s /\
             (!i. i IN frag_ids st st' ==> FLOOKUP s.vs_allocas i = NONE) /\
             s.vs_alloca_next + msz + 32 * (st'.cs_next_id - st.cs_next_id) <
               dimword (:256) /\
             !ss. ss.vs_returndata = enc (vyper_to_abi_type env ty) av /\
                  ss.vs_accounts = s.vs_accounts /\
                  ss.vs_transient =
                    (if nr /\ ~iv then (tstore (n2w nkey) 0w s).vs_transient
                     else s.vs_transient) /\
                  ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
                  ss.vs_pending_deletions = s.vs_pending_deletions ==>
                  R (Halt ss)) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `SOME op`, `F`, `F`, `ei`, `msz`, `nr`, `nkey`,
               `ut`, `iv`, `st`, `x`, `st'`, `P`, `Q`, `R`] mp_tac
    compile_external_return_unlock_seq >>
  impl_tac >> simp[] >> gen_tac >> strip_tac >> conj_tac
  >- (drule compile_external_return_abi_parts >> simp[] >> strip_tac >>
      imp_res_tac compile_alloc_buffer_extends >>
      imp_res_tac compile_abi_encode_to_buf_extends >>
      imp_res_tac emit_inst_metadata >>
      metis_tac[cs_extends_trans]) >>
  qspecl_then [`ctx`, `op`, `ei`, `msz`, `F`, `nkey`, `ut`, `iv`, `st1`, `()`,
               `st'`, `env`, `ty`, `tv`, `v`, `av`] mp_tac
    compile_external_return_abi_frag >>
  asm_rewrite_tac[] >> disch_then irule >> conj_tac
  >- (rpt strip_tac >> gvs[not_fresh_at_def]) >>
  rpt strip_tac >>
  qpat_x_assum `(\s1. _) _` (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `_ = (if _ then _ else _) with vs_inst_idx := _`
    SUBST_ALL_TAC >>
  rename1 `P s` >>
  qpat_x_assum `!s. P s ==> _` drule >> strip_tac >>
  qspecl_then [`nr`, `iv`, `nkey`, `LENGTH st1.cs_current_insts`, `s`,
    `(if nr /\ ~iv then tstore (n2w nkey) 0w s else s) with
       vs_inst_idx := LENGTH st1.cs_current_insts`]
    mp_tac optional_unlock_state >>
  REWRITE_TAC[] >> strip_tac >>
  qexists_tac `p` >> asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i. i IN frag_ids st st' ==> _` irule >>
      gvs[frag_ids_def]) >>
  decide_tac
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
            ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
            ss.vs_pending_deletions = s.vs_pending_deletions ==>
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
            ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
            ss.vs_pending_deletions = s.vs_pending_deletions ==>
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

(* With state_rel at the return, a Halt preserves the raw accounts and
   pending deletions, except for the optional unlock's TSTORE.  Finalize
   the accounts only at the success boundary, just as the source does
   after releasing the lock at the same key. *)
Theorem external_halt_success_unlock:
  !func cenv cx es es' s ss nr nkey iv tops tx srcs exps layouts.
    state_rel func cenv cx es s /\
    s.vs_accounts = es.accounts /\ s.vs_transient = es.tStorage /\
    (if nr /\ ~iv then release_nonreentrant_lock cx.txn.target nkey
     else vyperState$return ()) es = (INL (), es') /\
    ss.vs_accounts = s.vs_accounts /\
    ss.vs_transient =
      (if nr /\ ~iv then (tstore (n2w nkey) 0w s).vs_transient
       else s.vs_transient) /\
    ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
    ss.vs_pending_deletions = s.vs_pending_deletions ==>
    process_deletions ss.vs_pending_deletions ss.vs_accounts =
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

(* With state_rel at the return, a Halt that leaves the effects and pending
   deletions unchanged gives the finalized effects compared on success. *)
Theorem external_halt_success:
  !func cenv cx es s ss tops tx srcs exps layouts.
    state_rel func cenv cx es s /\
    s.vs_accounts = es.accounts /\ s.vs_transient = es.tStorage /\
    ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
    ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
    ss.vs_pending_deletions = s.vs_pending_deletions ==>
    process_deletions ss.vs_pending_deletions ss.vs_accounts =
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
