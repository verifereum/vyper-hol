Theory bodyPtrCodeSliceExternalTail
Ancestors
  bodyPtrCodeSliceExternalContinue exprSimSliceExtcodeContinue
  bodyPtrCodeSliceSelfContinue bodyPtrDefs loweringPosts
  exprSimSliceExtcode venomExecSemantics venomState words list finite_map
  vyperValue vyperTyping compileEnv valueEncodingDefs memLocDefs valueEncoding
  loweringStateRelDefs exprSimProps fragGasSeqPtr gasSummaryComposePtr
  bodyPtrHashBuiltinsGhostFrame vyperState exprSimSliceSource
  fragGasPathPtr stmtAppendStoragePathPtr fragExec

Theorem external_code_tail_result_ptr:
  compile_slice_extcode addr src len (Var out) (Var dst) sa = (r,sb) /\
  eval_operand addr s = SOME av /\ eval_operand src s = SOME a /\
  eval_operand len s = SOME n /\ lookup_var out s = SOME p /\
  lookup_var dst s = SOME (p+32w) /\
  (!x. MEM (Var x) [addr;src;len;Var out;Var dst] ==> not_fresh_at sa x) /\
  LENGTH (lookup_account (w2w av) s.vs_accounts).code < dimword (:256) /\
  w2n a+w2n n <= LENGTH (lookup_account (w2w av) s.vs_accounts).code /\
  w2n p+32 < dimword (:256) /\
  ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn out s cap /\ 32 <= cap /\
  op_taint tn addr = {} /\ op_taint tn src = {} /\ op_taint tn len = {} /\
  op_prov G src = NONE /\ op_prov G len = NONE /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\ stmt_state_rel ctx fn cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!name off sz. local_region cenv es.scopes s name off sz ==>
    off+sz <= w2n p \/ w2n p+32+w2n n <= off) /\
  run_inst_seq (emitted_insts sa sb) s = OK z /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic bound))) /\
  vv_holds cenv cx ty
    (Value (BytesV (TAKE (w2n n) (DROP (w2n a)
      (lookup_account (w2w av) s.vs_accounts).code))))
    (LocatedValue ty (mk_ptr (Var out) LocMemory)) es z /\
  val_wf (BaseTV (BytesT (Dynamic bound)))
    (BytesV (TAKE (w2n n) (DROP (w2n a)
      (lookup_account (w2w av) s.vs_accounts).code))) /\
  val_store_size (BaseTV (BytesT (Dynamic bound)))
    (BytesV (TAKE (w2n n) (DROP (w2n a)
      (lookup_account (w2w av) s.vs_accounts).code))) <= cap /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= cap ==>
  ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    ghost_inv d cenv cx es Gf tnf z /\ ghost_kept cenv es sa G tn s Gf tnf /\
    ptr_vv_ok cx ty
      (Value (BytesV (TAKE (w2n n) (DROP (w2n a)
        (lookup_account (w2w av) s.vs_accounts).code))))
      (LocatedValue ty (mk_ptr (Var out) LocMemory)) es Gf tnf z /\
    ptr_buf_ok cenv e (Var out) Gf z
Proof
  strip_tac >> drule_all external_code_tail_success_checked >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `z' = z` by gvs[] >> gvs[] >>
  qexistsl_tac [`Gf`,`tn0 with t_mem := (tn0.t_mem DIFF
    {j | w2n p+32 <= j /\ j < w2n p+32+w2n n}) DIFF
    {j | w2n p <= j /\ j < w2n p+32}`] >> simp[] >>
  irule self_code_covered_result >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`bound`,`p`,`cap`,`tn0`] >> simp[]
QED

Theorem external_code_tail_semantic_ptr:
  compile_slice_extcode addr sop lop (Var out) (Var dst) sa = (r,sb) /\
  eval_operand addr s = SOME av /\ eval_operand sop s = SOME a /\
  eval_operand lop s = SOME nw /\ lookup_var out s = SOME p /\
  lookup_var dst s = SOME (p+32w) /\
  (!x. MEM (Var x) [addr;sop;lop;Var out;Var dst] ==> not_fresh_at sa x) /\
  LENGTH (lookup_account (w2w av) s.vs_accounts).code < dimword (:256) /\
  w2n a+w2n nw <= LENGTH (lookup_account (w2w av) s.vs_accounts).code /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sbase.cs_next_var <= sa.cs_next_var /\ sbase.cs_next_id <= aid /\
  aid < sa.cs_next_id /\ aid < sb.cs_next_id /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
  FLOOKUP s.vs_allocas aid = SOME (w2n p,cap) /\
  w2n p+cap < dimword (:256) /\ 32+w2n nw <= cap /\
  (!nm off sz. local_region cenv es.scopes s nm off sz ==>
    regions_disjoint (w2n p) cap off sz) /\
  (!j off sz. FLOOKUP s.vs_allocas j = SOME (off,sz) /\ j < sbase.cs_next_id ==>
    regions_disjoint (w2n p) cap off sz) /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ w2n nw <= n /\
  ghost_inv d cenv cx es G tn s /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn out s cap /\ ptr_covers G tn dst s (w2n nw) /\
  op_taint tn addr = {} /\ op_taint tn sop = {} /\ op_taint tn lop = {} /\
  op_prov G sop = NONE /\ op_prov G lop = NONE /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= cap /\
  32+32*word_size n <= cap ==>
  ?z Gf tnf. run_inst_seq (emitted_insts sa sb) s = OK z /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    ghost_inv d cenv cx es Gf tnf z /\ ghost_kept cenv es sa G tn s Gf tnf /\
    ptr_vv_ok cx (expr_type e)
      (Value (BytesV (TAKE (w2n nw) (DROP (w2n a)
        (lookup_account (w2w av) s.vs_accounts).code))))
      (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory)) es Gf tnf z /\
    ptr_buf_ok cenv e (Var out) Gf z /\
    !idx. vv_post ctx fn cenv cx e es sbase sb s es
      (Value (BytesV (TAKE (w2n nw) (DROP (w2n a)
        (lookup_account (w2w av) s.vs_accounts).code))))
      (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory))
      (z with vs_inst_idx := idx)
Proof
  strip_tac >>
  `eval_operand (Var out) s = SOME p /\
   eval_operand (Var dst) s = SOME (p+32w)` by simp[eval_operand_def] >>
  drule_all slice_extcode_tail_vv_post >> strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
  `vv_holds cenv cx (expr_type e)
    (Value (BytesV (TAKE (w2n nw) (DROP (w2n a)
      (lookup_account (w2w av) s.vs_accounts).code))))
    (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory)) es t` by
    (qpat_x_assum `!idx. vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `t.vs_inst_idx` mp_tac) >> simp[vv_post_def]) >>
  suspend "result"
QED

Resume external_code_tail_semantic_ptr[result]:
  `LENGTH (TAKE (w2n nw) (DROP (w2n a)
    (lookup_account (w2w av) s.vs_accounts).code)) = w2n nw` by simp[] >>
  `val_wf (BaseTV (BytesT (Dynamic n)))
    (BytesV (TAKE (w2n nw) (DROP (w2n a)
      (lookup_account (w2w av) s.vs_accounts).code)))` by
    (simp[val_wf_def, type_memory_size_def] >>
     qspec_then `n` mp_tac le_word_size_mul >> decide_tac) >>
  `val_store_size (BaseTV (BytesT (Dynamic n)))
    (BytesV (TAKE (w2n nw) (DROP (w2n a)
      (lookup_account (w2w av) s.vs_accounts).code))) <= cap` by
    (drule val_store_size_le >> simp[type_memory_size_def] >> decide_tac) >>
  `!nm off sz. local_region cenv es.scopes s nm off sz ==>
    off+sz <= w2n p \/ w2n p+32+w2n nw <= off` by
    (fs[regions_disjoint_def] >> rpt strip_tac >>
     qpat_x_assum `!nm off sz. local_region _ _ _ _ _ _ ==> _`
       drule >> decide_tac) >>
  `w2n p+32 < dimword (:256) /\ 32 <= cap /\
   evaluate_type (get_tenv cx) (expr_type e) =
     SOME (BaseTV (BytesT (Dynamic n)))` by
    (qspec_then `n` mp_tac le_word_size_mul >>
     simp[evaluate_type_def, type_slot_size_def] >> decide_tac) >>
  drule_all external_code_tail_result_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[]
QED

Finalise external_code_tail_semantic_ptr

Theorem external_code_tail_outcome_ptr:
  compile_slice_extcode addr sop lop (Var out) (Var dst) sa = (r,sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand addr s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  eval_operand sop s = SOME (n2w i) /\ eval_operand lop s = SOME (n2w k) /\
  lookup_var out s = SOME p /\ lookup_var dst s = SOME (p+32w) /\
  (!x. MEM (Var x) [addr;sop;lop;Var out;Var dst] ==> not_fresh_at sa x) /\
  accounts_agree cx es.accounts s.vs_accounts /\ accounts_well_typed es.accounts /\
  LENGTH bs = 20 /\ i < dimword (:256) /\ k < dimword (:256) /\ k <= n /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sbase.cs_next_var <= sa.cs_next_var /\ sbase.cs_next_id <= aid /\
  aid < sa.cs_next_id /\ aid < sb.cs_next_id /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
  FLOOKUP s.vs_allocas aid = SOME (w2n p,cap) /\
  w2n p+cap < dimword (:256) /\ 32+n <= cap /\
  (!nm off sz. local_region cenv es.scopes s nm off sz ==>
    regions_disjoint (w2n p) cap off sz) /\
  (!j off sz. FLOOKUP s.vs_allocas j = SOME (off,sz) /\ j < sbase.cs_next_id ==>
    regions_disjoint (w2n p) cap off sz) /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ es.gas_obs = [] /\
  ghost_inv d cenv cx es G tn s /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn out s cap /\ ptr_covers G tn dst s k /\
  op_taint tn addr = {} /\ op_taint tn sop = {} /\ op_taint tn lop = {} /\
  op_prov G sop = NONE /\ op_prov G lop = NONE /\
  (!x j. cenv.ce_return_buf = SOME (PtrVar (Var x) j) ==> not_fresh_at sa x) /\
  (!x j. cenv.ce_return_pc = SOME (PtrVar (Var x) j) ==> not_fresh_at sa x) /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= cap /\
  32+32*word_size n <= cap ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (do acc <- get_accounts;
        v <- lift_sum (evaluate_slice
          (BytesV (lookup_account (word_of_bytes_be bs) acc).code)
          (IntV (&i)) (IntV (&k)) n);
        return (Value v) od) (es,s,G,tn)
    (\res ee Gf tnf t. ?tv. res = INL tv /\
      vv_post ctx fn cenv cx e es sbase sb s ee tv
        (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory)) t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee Gf tnf t /\ ghost_kept cenv es sa G tn s Gf tnf /\
      ptr_vv_ok cx (expr_type e) tv
        (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory)) ee Gf tnf t /\
      ptr_buf_ok cenv e (Var out) Gf t)
    (\res ee ghosts r. expr_exit res r)
Proof
  strip_tac >> drule_all slice_extcode_account >> strip_tac >>
  `LENGTH (lookup_account (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)))
    s.vs_accounts).code < dimword (:256)` by
    (simp[dimword_def] >> decide_tac) >>
  `EVERY (\inst. inst.inst_opcode <> INVOKE /\
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> GAS)
    (emitted_insts sa sb)` by metis_tac[slice_extcode_zero_code] >>
  Cases_on `i+k <= LENGTH (lookup_account (word_of_bytes_be bs) es.accounts).code`
  >- suspend "success"
  >> suspend "range"
QED

Resume external_code_tail_outcome_ptr[success]:
  `w2n (n2w i : bytes32) + w2n (n2w k : bytes32) <=
    LENGTH (lookup_account (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)))
      s.vs_accounts).code /\ 32+w2n (n2w k : bytes32) <= cap /\
    w2n (n2w k : bytes32) <= n /\
    ptr_covers G tn dst s (w2n (n2w k : bytes32))` by simp[] >>
  drule_all external_code_tail_semantic_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  suspend "count"
QED

Resume external_code_tail_outcome_ptr[count]:
  `EVERY (\inst. inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode)
    (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `FILTER (\inst. inst.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  `es with gas_obs := [] = es` by
    (qpat_x_assum `es.gas_obs = []` (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (Value (BytesV (TAKE k (DROP i
    (lookup_account (word_of_bytes_be bs) es.accounts).code))))`,
    `es`,`Gf`,`tnf`,`OK (z with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))`] >>
  simp[get_accounts_def, bind_def, lift_sum_def, return_def, slice_bytes_nat] >>
  suspend "endpoint"
QED

Resume external_code_tail_outcome_ptr[range]:
  `LENGTH (lookup_account (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)))
    s.vs_accounts).code < w2n (n2w i : bytes32)+w2n (n2w k : bytes32)` by
    (simp[] >> decide_tac) >>
  `!x. MEM (Var x) [addr;sop;lop] ==> not_fresh_at sa x` by metis_tac[MEM] >>
  drule_all external_code_tail_abort_checked >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `EVERY (\inst. inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
    ~is_terminator inst.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_abort_zero_path_ptr >> strip_tac >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "evaluate_slice range"))`,
    `es`,`Gf`,`tnf`,`Abort Revert_abort (t with vs_inst_idx := j)`] >>
  simp[get_accounts_def, bind_def, lift_sum_def, return_def, raise_def,
    slice_bytes_nat, exit_result_def, exprSimDefsTheory.expr_exit_def]
QED

Resume external_code_tail_outcome_ptr[endpoint]:
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[slice_extcode_tail_control] >>
  `z.vs_current_bb = s.vs_current_bb` by
    (drule_all (cj 1 fragExecTheory.exec_block_run_inst_seq) >> simp[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (qpat_x_assum `sb.cs_current_insts = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  gvs[hash_ghost_inv_inst_idx, ptr_vv_ok_def, ptr_mem_ok_def, ptr_buf_ok_def,
    eval_operand_def, lookup_var_def]
QED

Finalise external_code_tail_outcome_ptr
