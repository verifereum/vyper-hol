(* Counted memory-header prefix with an interface for subsequent guard code. *)
Theory bodyPtrPopLocalRootPath
Ancestors
  bodyPtrPopLocalRootEntry bodyPtrPopLengthGuard bodyPtrPopMemoryHeader
  bodyPtrPopMemoryStore bodyPtrPopInteriorPointer
  emitHelperProps emitHelper compileEnv loweringStateRelDefs venomState ptrDiscipline
  finite_map words list fragGasPathPtr bodyPtrBopCompareCompile storageCopyBodyPtr

Theorem pop_local_header_path_frame:
  emit_op MLOAD [Var src] sa = (op,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn src s bytes /\ 32 <= bytes /\
  lookup_var src s = SOME a /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
      (w2n a) mem) ==>
  ?out t G' tn'. op = Var out /\ not_fresh_at sb out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    eval_operand op t = SOME (mem_word_at (w2n a) s.vs_memory) /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_labels = s.vs_labels /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all pop_memory_header_load >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`out`, `(update_var out (mload (w2n a) s) s) with
    vs_inst_idx := SUC s.vs_inst_idx`, `G'`, `tn'`] >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   not_fresh_at sb out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def]) >>
  simp[update_var_def, lookup_var_def, eval_operand_def, FLOOKUP_UPDATE,
       GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >> metis_tac[]
QED

Theorem pop_local_empty_prefix_path:
  emit_op MLOAD [Var src] sa = (len,sb) /\ fn_has_code sa sb fn /\
  emit_op ISZERO [len] sb = (nz,sc) /\
  emit_op ISZERO [nz] sc = (valid,sd) /\
  emit_void ASSERT [valid] sd = ((),se) /\
  emit_op SUB [len; Lit 1w] se = (new_len,sf) /\
  fn_has_code sb sf fn /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn src s bytes /\ 32 <= bytes /\
  lookup_var src s = SOME a /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  mem_word_at (w2n a) s.vs_memory = 0w /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV []))
      (w2n a) mem) ==>
  ?t G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (Abort Revert_abort (revert_state (set_returndata [] t))) /\
    t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts
Proof
  strip_tac >> drule_all pop_local_header_path_frame >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `?u G2 tn2. gas_path_ptr D 0 ctx fn PG G' tn' t 0 G2 tn2
    (Abort Revert_abort (revert_state (set_returndata [] u))) /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts` by
    (irule pop_length_guard_empty_path >> metis_tac[]) >>
  qexistsl_tac [`u`, `G2`, `tn2`] >> simp[] >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem pop_local_compile_cuts:
  compile_dynarray_pop root_op 32 esz ctor imm LocMemory sa = (res,sj) ==>
  ?len nz valid new_len data offset sb sc sd se sf sg sh si.
    emit_op MLOAD [root_op] sa = (len,sb) /\
    emit_op ISZERO [len] sb = (nz,sc) /\
    emit_op ISZERO [nz] sc = (valid,sd) /\
    emit_void ASSERT [valid] sd = ((),se) /\
    emit_op SUB [len; Lit 1w] se = (new_len,sf) /\
    emit_void MSTORE [root_op;new_len] sf = ((),sg) /\
    emit_op ADD [root_op; Lit 32w] sg = (data,sh) /\
    emit_op MUL [new_len; Lit (n2w esz)] sh = (offset,si) /\
    emit_op ADD [data;offset] si = (res,sj)
Proof
  simp[exprLoweringTheory.compile_dynarray_pop_def,
       contextTheory.compile_ptr_load_def, contextTheory.compile_ptr_store_def,
       comp_bind_def, comp_ignore_bind_def, AllCaseEqs()] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem pop_local_guard_store_path:
  emit_op ISZERO [len] sa = (nz,sb) /\
  emit_op ISZERO [nz] sb = (valid,sc) /\
  emit_void ASSERT [valid] sc = ((),sd) /\
  emit_op SUB [len; Lit 1w] sd = (new_len,se) /\
  emit_void MSTORE [Var root;new_len] se = ((),sf) /\
  fn_has_code sa se fn /\ fn_has_code se sf fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand len s = SOME w /\ op_taint tn len = {} /\
  op_prov G len = NONE /\ (!v. len = Var v ==> not_fresh_at sa v) /\ w <> 0w /\
  not_fresh_at sa root /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s bytes /\ 32 <= bytes /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?t G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    t.vs_memory = (mstore (w2n a) (w-1w) s).vs_memory /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_labels = s.vs_labels /\
    (!v. new_len = Var v ==> not_fresh_at sf v) /\
    eval_operand new_len t = SOME (w-1w) /\
    op_taint tn' new_len = {} /\ op_prov G' new_len = NONE /\
    ptr_covers G' tn' root t bytes /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all pop_length_guard_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var root t = SOME a /\ ptr_covers G' tn' root t bytes` by
    (gvs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  `ptr_covers G' tn' root t 32` by
    (gvs[bodyPtrDefsTheory.ptr_covers_def] >> decide_tac) >>
  `?u. gas_path_ptr D 0 ctx fn PG G' tn' t 0 G' tn' (OK u) /\
    u = ((mstore (w2n a) (w-1w) t) with vs_inst_idx := SUC t.vs_inst_idx) /\
    ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
    u.vs_inst_idx = LENGTH sf.cs_current_insts /\
    (!v. lookup_var v u = lookup_var v t) /\
    mem_agree_outside {i | w2n a <= i /\ i < w2n a + 32}
      u.vs_memory t.vs_memory /\
    (!k. ptr_covers G' tn' root t k ==> ptr_covers G' tn' root u k)` by
    (irule pop_clean_header_store_path >> metis_tac[]) >>
  `!v. new_len = Var v ==> not_fresh_at sf v` by
    (gvs[emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
         comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
         comp_return_def, not_fresh_at_def]) >>
  qexistsl_tac [`u`, `G'`, `tn'`] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  simp[] >> gvs[mstore_def, eval_operand_def, lookup_var_def, update_var_def]
QED

Theorem pop_emit_mul_path_frame:
  emit_op MUL [left;right] sa = (dst,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  ?out t G' tn'. dst = Var out /\ not_fresh_at sb out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    eval_operand dst t = SOME (a*b) /\
    op_taint tn' dst = {} /\ op_prov G' dst = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_labels = s.vs_labels /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all bop_compare_emit_placement >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  `dst = Var out /\ sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   not_fresh_at sb out /\ (!v. not_fresh_at sa v ==> v <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def, Abbr `out`]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out (a*b) s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule storage_copy_mul_path_ptr >> metis_tac[]) >>
  qexistsl_tac [`out`, `(update_var out (a*b) s) with
      vs_inst_idx := SUC s.vs_inst_idx`,
    `DRESTRICT G (COMPL {out})`, `tn with t_var := tn.t_var |+ (out,{})`] >>
  simp[eval_operand_def, update_var_def, lookup_var_def, op_taint_def,
       op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

