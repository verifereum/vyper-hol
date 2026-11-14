(* Dynamic SHA input preparation and bounded call outcomes. *)
Theory bodyFullHashShaBytesSuccess
Ancestors
  bodyFullHashShaPrefix bodyFullHashShaSuccess bodyFullHashShaAbort bodyFullHashKeccakBytes
  bodyPtrHashBuiltinsShaBytes bodyPtrHashBuiltinsShaEndpoint
  bodyPtrHashBuiltinsShaPrefix bodyPtrHashBuiltinsShaAlloc
  bodyPtrHashBuiltinsGhostFrame bodyPtrDefs
  ghostPcTransportPtr instIdxIndep
  fragExec fragExecMem fragGasSeqPtr instSeqComposePtr
  exprSimHash exprLoweringProps loweringHalt loweringStateRelDefs
  arithmeticProps freshWrites
  compileEnv context emitHelper venomState venomInst venomExecSemantics
  ptrDiscipline finite_map pred_set words list rich_list arithmetic

Theorem bytes_prefix_mem_ok[local]:
  !xs ys s. run_inst_seq_mem_ok (xs ++ ys) s ==> run_inst_seq_mem_ok xs s
Proof
  Induct >> simp[run_inst_seq_mem_ok_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> fs[] >> metis_tac[]
QED

Theorem bytes_allocation_code[local]:
  emit_op MLOAD [x] sa = (len_op,sl) /\
  emit_op ADD [x;Lit 32w] sl = (data_op,sm) /\
  compile_alloc_buffer 32 sm = (buf,sn) /\
  emit_op GAS [] sn = (gas_op,sg) /\
  emit_op STATICCALL [gas_op;Lit 2w;data_op;len_op;buf.buf_operand;Lit 32w] sg = (success_op,sc) /\
  emit_void ASSERT [success_op] sc = ((),sh) /\
  emit_op MLOAD [buf.buf_operand] sh = (op,sb) /\ fn_has_code sa sb fn ==>
  fn_has_code sm sn fn
Proof
  strip_tac >> mp_tac cs_appends_emit_helpers >>
  simp[cs_appends_def] >> strip_tac >>
  `cs_extends sa sl /\ cs_extends sl sm /\ cs_extends sm sn /\
   cs_extends sn sg /\ cs_extends sg sc /\ cs_extends sc sh /\ cs_extends sh sb` by
    metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sa sm /\ cs_extends sn sb /\ cs_extends sm sb` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sm sb fn` by metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED

Theorem bytes_kept_then_at[local]:
  ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
  ghost_kept_at lo cenv es sm G1 tn1 a Gf tf /\
  local_ptrs_reserved cenv sa /\
  (!z. not_fresh_at sa z ==> not_fresh_at sm z) /\
  (!z. not_fresh_at sa z ==> lookup_var z a = lookup_var z s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP a.vs_allocas aid = SOME entry) /\ sa.cs_next_id <= sm.cs_next_id ==>
  ghost_kept_at lo cenv es sa G tn s Gf tf
Proof
  strip_tac >>
  `ghost_kept cenv es sa G tn s G1 tn1 /\
   ghost_kept cenv es sm G1 tn1 a Gf tf` by
    (fs[ghost_kept_at_def, ghost_kept_def] >> metis_tac[]) >>
  drule_all hash_ghost_kept_then >>
  fs[ghost_kept_at_def, ghost_kept_def] >> metis_tac[]
QED

Theorem sha_bytes_success_frame_at:
  !D lo H ctx fn PG G tn s bb x sa op sb b rootbase cap n d cenv cx es outcome rest bs.
  compile_sha256_bytes (Var x) sa = (op,sb) /\ not_fresh_at sa x /\
  eval_operand (Var x) s = SOME (n2w b) /\
  FLOOKUP G x = SOME (rootbase,cap) /\ rootbase <= b /\ b+32+n <= rootbase+cap /\
  b+32 < dimword (:256) /\ n < dimword (:256) /\ op_taint tn (Var x) = {} /\
  (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w n /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list)
    ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ghost_inv_at D lo d cenv cx es G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  MEM (mk_inst (sa.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var+2))]) (fn_insts fn) /\
  (n = 0 \/
   (?aid a k. FLOOKUP s.vs_allocas aid = SOME (a,k) /\
      aid < sa.cs_next_id /\ a <= b+32 /\ b+32+n <= a+k) \/
   (?name a k. local_region cenv es.scopes s name a k /\
      a <= b+32 /\ b+32+n <= a+k)) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  fn_has_code sa sb fn /\ run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success /\
  mem_bytes_at (b+32) n s.vs_memory = bs ==>
  ?t Gf tf. run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tf /\
    eval_operand op t = SOME (SHA_256_bytes bs) /\
    ghost_inv_at D lo d cenv cx (es with outcomes := SOME rest) Gf tf
      (t with vs_inst_idx := s.vs_inst_idx+7) /\
    ghost_kept_at lo cenv es sa G tn s Gf tf /\ op_taint tf op = {} /\
    op_prov Gf op = NONE
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule hash_sha256_bytes_parts >> strip_tac >>
  drule_all hash_bytes_prepare_emission >> strip_tac >>
  drule_all hash_sha256_alloc_tail_layout >> strip_tac >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   LENGTH (emitted_insts sa sm) = 2` by
    (qpat_x_assum `emit_op MLOAD [Var x] sa = _` mp_tac >>
     qpat_x_assum `emit_op ADD [Var x;Lit 32w] _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >>
     gvs[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_prefix_split >> metis_tac[]) >>
  `isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) /\
   isPREFIX (emitted_insts sm sb) (DROP (s.vs_inst_idx+2) bb.bb_instructions)` by
    (`isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
        (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
     drule hash_code_prefix_split >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (irule bytes_prefix_mem_ok >> qexists_tac `emitted_insts sm sb` >> metis_tac[]) >>
  drule_all sha_bytes_prepare_frame_at >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qabbrev_tac `a = t with vs_inst_idx := s.vs_inst_idx+2` >>
  `stmt_state_rel H ctx fn cenv cx es a /\ ghost_inv_at D lo d cenv cx es G1 tn1 a` by
    simp[Abbr `a`, stmt_state_rel_inst_idx, bytes_ghost_cursor] >>
  `a.vs_memory = s.vs_memory /\ a.vs_allocas = s.vs_allocas /\
   a.vs_outcomes = s.vs_outcomes /\ ~a.vs_halted /\
   lookup_block a.vs_current_bb fn.fn_blocks = SOME bb /\
   a.vs_inst_idx = s.vs_inst_idx+2 /\
   (!z. not_fresh_at sa z ==> lookup_var z a = lookup_var z s)` by
    (qpat_x_assum `(t with vs_vars := s.vs_vars) = s` mp_tac >>
     simp[venom_state_component_equality] >> strip_tac >>
     fs[Abbr `a`, lookup_var_def]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `(!z k. cenv.ce_return_buf = SOME (PtrVar (Var z) k) ==> not_fresh_at sm z) /\
   (!z k. cenv.ce_return_pc = SOME (PtrVar (Var z) k) ==> not_fresh_at sm z)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  suspend "call"
QED

Resume sha_bytes_success_frame_at[call]:
  qpat_x_assum `data_op = Var p` SUBST_ALL_TAC >>
  `ptr_covers G1 tn1 p a (w2n (n2w n:bytes32)) /\
   eval_operand (Var p) a = SOME (n2w (b+32)) /\
   eval_operand len_op a = SOME (n2w n) /\
   isPREFIX (emitted_insts sm sb) (DROP a.vs_inst_idx bb.bb_instructions)` by
    simp[Abbr `a`] >>
  `!z. z=p \/ len_op=Var z ==> not_fresh_at sm z` by metis_tac[] >>
  `!i. w2n (n2w (b+32):bytes32) <= i /\
       i < w2n (n2w (b+32):bytes32)+w2n (n2w n:bytes32) ==> i NOTIN tn1.t_mem` by simp[] >>
  `a.vs_outcomes = outcome::rest /\
   mem_bytes_at (w2n (n2w (b+32):bytes32)) (w2n (n2w n:bytes32)) a.vs_memory = bs` by simp[] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sm.cs_next_var)]) (fn_insts fn)` by simp[] >>
  `fn_has_code sm sn fn` by (drule_all bytes_allocation_code >> simp[]) >>
  Q.SUBGOAL_THEN `n = 0 \/
   (?aid lb k. FLOOKUP t.vs_allocas aid = SOME (lb,k) /\
      aid < sm.cs_next_id /\ lb <= b+32 /\ b+32+n <= lb+k) \/
   (?name lb k. local_region cenv es.scopes t name lb k /\
      lb <= b+32 /\ b+32+n <= lb+k)` assume_tac >-
    (mp_tac (Q.INST [`s` |-> `s`, `t` |-> `t`, `sa` |-> `sa`,
       `sb` |-> `sm`, `a` |-> `b+32`, `n` |-> `n`,
       `cenv` |-> `cenv`, `es` |-> `es`] hash_readonly_input_window) >>
     simp[] >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD_COMM]) >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_assum `(t with vs_vars := s.vs_vars) = s`
       (mp_tac o Q.AP_TERM `\v. v.vs_allocas`) >> simp[]) >>
  Q.SUBGOAL_THEN `(w2n (n2w n:bytes32) = 0 \/
   (?aid lb k. FLOOKUP a.vs_allocas aid = SOME (lb,k) /\
      aid < sm.cs_next_id /\ lb <= w2n (n2w (b+32):bytes32) /\
      w2n (n2w (b+32):bytes32)+w2n (n2w n:bytes32) <= lb+k) \/
   (?name lb k. local_region cenv es.scopes a name lb k /\
      lb <= w2n (n2w (b+32):bytes32) /\
      w2n (n2w (b+32):bytes32)+w2n (n2w n:bytes32) <= lb+k))` assume_tac >-
    (qpat_x_assum `n = 0 \/ (?aid lb k. FLOOKUP t.vs_allocas aid = _ /\ _) \/ _`
       mp_tac >>
     simp[Abbr `a`, local_region_def, lookup_var_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD_COMM]) >>
  drule_all sha_alloc_success_frame_at >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `run_inst_seq (emitted_insts sm sb) a = OK tail` >>
  suspend "compose"
QED

Resume sha_bytes_success_frame_at[compose]:
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    simp[mk_inst_def, is_terminator_def] >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tf` by
    (qpat_assum `emitted_insts sa sb = _` SUBST1_TAC >>
     irule inst_seq_ptr_append_ok >> simp[] >>
     qexistsl_tac [`G1`, `tn1`] >>
     qpat_assum `inst_seq_ptr _ _ _ _ _ _ _ (emitted_insts sa sm) _ _ _` mp_tac >>
     qpat_assum `inst_seq_ptr _ _ _ _ _ _ _ (emitted_insts sm sb) _ _ _` mp_tac >>
     qpat_assum `Abbrev (a = _)` mp_tac >>
     qpat_assum `emitted_insts sa sm = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[markerTheory.Abbrev_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (drule_all hash_sha256_alloc_tail_nonterminators >> simp[]) >>
  `?u. run_inst_seq (emitted_insts sm sb) t = OK u /\
       tail = u with vs_inst_idx := s.vs_inst_idx+2` by
    (qpat_x_assum `run_inst_seq (emitted_insts sm sb) a = _` mp_tac >>
     simp[Abbr `a`, run_inst_seq_inst_idx] >>
     Cases_on `run_inst_seq (emitted_insts sm sb) t` >> simp[exec_result_map_def]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at sm z` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `sa.cs_next_id <= sm.cs_next_id` by simp[] >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP a.vs_allocas aid = SOME entry` by simp[] >>
  drule_all bytes_kept_then_at >> strip_tac >>
  qpat_x_assum `tail = u with vs_inst_idx := _` SUBST_ALL_TAC >>
  qexistsl_tac [`u`, `Gf`, `tf`] >> conj_tac
  >- (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK t`
        (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> simp[]) >>
  fs[bytes_ghost_cursor, eval_operand_inst_idx]
QED

Finalise sha_bytes_success_frame_at


Theorem sha_bytes_abort_ptr_at:
  !D lo H ctx fn PG G tn s bb x sa op sb b rootbase cap n d cenv cx es.
  compile_sha256_bytes (Var x) sa = (op,sb) /\ not_fresh_at sa x /\
  eval_operand (Var x) s = SOME (n2w b) /\
  FLOOKUP G x = SOME (rootbase,cap) /\ rootbase <= b /\ b+32+n <= rootbase+cap /\
  b+32 < dimword (:256) /\ n < dimword (:256) /\ op_taint tn (Var x) = {} /\
  (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w n /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list)
    ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ghost_inv_at D lo d cenv cx es G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  MEM (mk_inst (sa.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var+2))]) (fn_insts fn) /\
  (n = 0 \/
   (?aid a k. FLOOKUP s.vs_allocas aid = SOME (a,k) /\
      aid < sa.cs_next_id /\ a <= b+32 /\ b+32+n <= a+k) \/
   (?name a k. local_region cenv es.scopes s name a k /\
      a <= b+32 /\ b+32+n <= a+k)) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  fn_has_code sa sb fn /\ run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
  ?t Gf tf. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tf
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule hash_sha256_bytes_parts >> strip_tac >>
  drule_all hash_bytes_prepare_emission >> strip_tac >>
  drule_all hash_sha256_alloc_tail_layout >> strip_tac >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   LENGTH (emitted_insts sa sm) = 2` by
    (qpat_x_assum `emit_op MLOAD [Var x] sa = _` mp_tac >>
     qpat_x_assum `emit_op ADD [Var x;Lit 32w] _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >>
     gvs[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_prefix_split >> metis_tac[]) >>
  `isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) /\
   isPREFIX (emitted_insts sm sb) (DROP (s.vs_inst_idx+2) bb.bb_instructions)` by
    (`isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
        (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
     drule hash_code_prefix_split >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (irule bytes_prefix_mem_ok >> qexists_tac `emitted_insts sm sb` >> metis_tac[]) >>
  drule_all sha_bytes_prepare_frame_at >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qabbrev_tac `a = t with vs_inst_idx := s.vs_inst_idx+2` >>
  `stmt_state_rel H ctx fn cenv cx es a /\ ghost_inv_at D lo d cenv cx es G1 tn1 a` by
    simp[Abbr `a`, stmt_state_rel_inst_idx, bytes_ghost_cursor] >>
  `a.vs_memory = s.vs_memory /\ a.vs_allocas = s.vs_allocas /\
   a.vs_outcomes = s.vs_outcomes /\ ~a.vs_halted /\
   lookup_block a.vs_current_bb fn.fn_blocks = SOME bb /\
   a.vs_inst_idx = s.vs_inst_idx+2 /\
   (!z. not_fresh_at sa z ==> lookup_var z a = lookup_var z s)` by
    (qpat_x_assum `(t with vs_vars := s.vs_vars) = s` mp_tac >>
     simp[venom_state_component_equality] >> strip_tac >>
     fs[Abbr `a`, lookup_var_def]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `(!z k. cenv.ce_return_buf = SOME (PtrVar (Var z) k) ==> not_fresh_at sm z) /\
   (!z k. cenv.ce_return_pc = SOME (PtrVar (Var z) k) ==> not_fresh_at sm z)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  suspend "call"
QED

Resume sha_bytes_abort_ptr_at[call]:
  qpat_x_assum `data_op = Var p` SUBST_ALL_TAC >>
  `ptr_covers G1 tn1 p a (w2n (n2w n:bytes32)) /\
   eval_operand (Var p) a = SOME (n2w (b+32)) /\
   eval_operand len_op a = SOME (n2w n) /\
   isPREFIX (emitted_insts sm sb) (DROP a.vs_inst_idx bb.bb_instructions)` by
    simp[Abbr `a`] >>
  `!z. z=p \/ len_op=Var z ==> not_fresh_at sm z` by metis_tac[] >>
  `!i. w2n (n2w (b+32):bytes32) <= i /\
       i < w2n (n2w (b+32):bytes32)+w2n (n2w n:bytes32) ==> i NOTIN tn1.t_mem` by simp[] >>
  `~(?outcome rest. a.vs_outcomes = outcome::rest /\ outcome.co_success)` by
    (qpat_assum `~(?outcome rest. s.vs_outcomes = _ /\ _)` mp_tac >> simp[]) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sm.cs_next_var)]) (fn_insts fn)` by simp[] >>
  `fn_has_code sm sn fn` by (drule_all bytes_allocation_code >> simp[]) >>
  Q.SUBGOAL_THEN `n = 0 \/
   (?aid lb k. FLOOKUP t.vs_allocas aid = SOME (lb,k) /\
      aid < sm.cs_next_id /\ lb <= b+32 /\ b+32+n <= lb+k) \/
   (?name lb k. local_region cenv es.scopes t name lb k /\
      lb <= b+32 /\ b+32+n <= lb+k)` assume_tac >-
    (mp_tac (Q.INST [`s` |-> `s`, `t` |-> `t`, `sa` |-> `sa`,
       `sb` |-> `sm`, `a` |-> `b+32`, `n` |-> `n`,
       `cenv` |-> `cenv`, `es` |-> `es`] hash_readonly_input_window) >>
     simp[] >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD_COMM]) >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_assum `(t with vs_vars := s.vs_vars) = s`
       (mp_tac o Q.AP_TERM `\v. v.vs_allocas`) >> simp[]) >>
  Q.SUBGOAL_THEN `(w2n (n2w n:bytes32) = 0 \/
   (?aid lb k. FLOOKUP a.vs_allocas aid = SOME (lb,k) /\
      aid < sm.cs_next_id /\ lb <= w2n (n2w (b+32):bytes32) /\
      w2n (n2w (b+32):bytes32)+w2n (n2w n:bytes32) <= lb+k) \/
   (?name lb k. local_region cenv es.scopes a name lb k /\
      lb <= w2n (n2w (b+32):bytes32) /\
      w2n (n2w (b+32):bytes32)+w2n (n2w n:bytes32) <= lb+k))` assume_tac >-
    (qpat_x_assum `n = 0 \/ (?aid lb k. FLOOKUP t.vs_allocas aid = _ /\ _) \/ _`
       mp_tac >>
     simp[Abbr `a`, local_region_def, lookup_var_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD_COMM]) >>
  drule_all sha_alloc_abort_ptr_at >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  rename1 `run_inst_seq (emitted_insts sm sb) a = Abort Revert_abort tail` >>
  suspend "compose"
QED

Resume sha_bytes_abort_ptr_at[compose]:
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    simp[mk_inst_def, is_terminator_def] >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tf` by
    (qpat_assum `emitted_insts sa sb = _` SUBST1_TAC >>
     irule inst_seq_ptr_append_ok >> simp[] >>
     qexistsl_tac [`G1`, `tn1`] >>
     qpat_assum `inst_seq_ptr _ _ _ _ _ _ _ (emitted_insts sa sm) _ _ _` mp_tac >>
     qpat_assum `inst_seq_ptr _ _ _ _ _ _ _ (emitted_insts sm sb) _ _ _` mp_tac >>
     qpat_assum `Abbrev (a = _)` mp_tac >>
     qpat_assum `emitted_insts sa sm = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[markerTheory.Abbrev_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (drule_all hash_sha256_alloc_tail_nonterminators >> simp[]) >>
  `?u. run_inst_seq (emitted_insts sm sb) t = Abort Revert_abort u /\
       tail = u with vs_inst_idx := s.vs_inst_idx+2` by
    (qpat_x_assum `run_inst_seq (emitted_insts sm sb) a = _` mp_tac >>
     simp[Abbr `a`, run_inst_seq_inst_idx] >>
     Cases_on `run_inst_seq (emitted_insts sm sb) t` >> simp[exec_result_map_def]) >>
  qpat_x_assum `tail = u with vs_inst_idx := _` SUBST_ALL_TAC >>
  qexistsl_tac [`u`, `Gf`, `tf`] >> conj_tac
  >- (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK t`
        (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> simp[]) >>
  simp[]
QED

Finalise sha_bytes_abort_ptr_at
