Theory bodyPtrIfExpBytesConsumer
Ancestors
  bodyPtrIfExpBytesEndpoint bodyPtrIfExpBytesPost bodyPtrIfExpBytesCallerFrame
  bodyPtrIfExpBytesFrame bodyPtrDefs appendStorageGhostPtr loweringPosts
  exprSimProps exprSimDefs compileEnv venomState venomInst finite_map words
  exprSimBufferStore vyperTyping valueCopyBytes exprLoweringProps valueEncodingTyping

Theorem ifexp_allocated_bytes_writer:
  post_value_type ce result = expr_type result /\
  vv_post ctx fn ce cx arm es sa sc s0 ee raw vv t /\
  (~expr_has_effect result ==> ~expr_has_effect arm) /\
  stmt_state_rel ctx fn ce cx es s0 /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sc.cs_next_var /\
  MEM (mk_inst aid ALLOCA [Lit (n2w capacity)] [out]) (fn_insts fn) /\
  not_local_ptr ce ee.scopes out /\
  FLOOKUP t.vs_allocas aid = SOME (w2n b,capacity) /\
  sa.cs_next_id <= aid /\ aid < sd.cs_next_id /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    off+sz <= w2n b \/ w2n b+capacity <= off) /\
  (!name p sz. local_region ce es.scopes s0 name p sz ==>
    p+sz <= w2n b \/ w2n b+capacity <= p) /\
  ghost_inv d ce cx ee G tn t /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  compile_store_bytestring (Var src) (Var out) sc = ((),sd) /\
  not_fresh_at sc src /\ not_fresh_at sc out /\
  lookup_var src t = SOME a /\ lookup_var out t = SOME b /\
  ptr_covers G tn src t n /\ ptr_covers G tn out t capacity /\
  n = 32 + 32 * ((len+31) DIV 32) /\ n <= capacity /\
  len+31 < dimword(:256) /\ n < dimword(:256) /\
  is_bytestring_type sty /\ is_bytestring_type (expr_type result) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) (expr_type result) = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_footprint dtv v <= capacity /\ val_store_size dtv v <= capacity /\
  type_memory_bytes ce (lowered_value_type ce result) <= capacity /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory stv v (w2n a) m) /\
  ~ctx_has_dalloca ctx /\ ~t.vs_halted /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sc sd) (DROP t.vs_inst_idx bb.bb_instructions) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn t 0 Gf tnf
      (OK (sf with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts sc sd))) /\
    expr_post ctx fn ce cx result es sa sd s0 ee v (Var out)
      (sf with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts sc sd)) /\
    ghost_inv d ce cx ee Gf tnf
      (sf with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts sc sd)) /\
    ghost_kept ce es sa G0 tn0 s0 Gf tnf /\
    ptr_val_ok cx (expr_type result) v (Var out) Gf tnf
      (sf with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts sc sd)) /\
    ptr_buf_ok ce result (Var out) Gf
      (sf with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts sc sd)) /\
    (sf with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>) = t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_covers G tn out t n` by
    (gvs[ptr_covers_def] >> qexistsl_tac [`b'`, `sz'`] >> simp[] >> decide_tac) >>
  drule_all compile_store_bytestring_robust_gas_path_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `local_ptrs_reserved ce sc` by metis_tac[local_ptrs_reserved_next_var] >>
  `lookup_var out sf = SOME b /\ ptr_covers Gf tnf out sf capacity` by
    (conj_tac >- metis_tac[] >> irule ptr_covers_old_transport >> metis_tac[]) >>
  `~is_word_type (expr_type result)` by metis_tac[is_bytestring_word_type] >>
  `val_wf dtv v` by metis_tac[value_has_type_val_wf] >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  conj_tac >- suspend "semantic" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "kept" >>
  suspend "pointer"
QED

Resume ifexp_allocated_bytes_writer[semantic]:
  `eval_operand (Var out) sf = SOME b` by simp[eval_operand_def] >>
  `val_in_memory dtv v (w2n b) sf.vs_memory` by
    metis_tac[mem_agree_outside_def] >>
  `!x. not_fresh_at sc x ==> lookup_var x sf = lookup_var x t` by metis_tac[] >>
  drule_all ifexp_bytes_destination_expr_post >> simp[]
QED

Resume ifexp_allocated_bytes_writer[ghost]:
  `stor_taint_ok cx tn t` by gvs[ghost_inv_def] >>
  `stor_taint_ok cx tnf sf` by
    (irule bytes_writer_stor_taint_ok >> qexistsl_tac [`t`, `tn`] >> simp[]) >>
  `!x. not_fresh_at sc x ==>
     FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x) /\
     lookup_var x sf = lookup_var x t` by metis_tac[] >>
  drule_all ifexp_bytes_caller_ghost_inv >> simp[]
QED

Resume ifexp_allocated_bytes_writer[kept]:
  `!x. not_fresh_at sc x ==>
     FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)`
    by metis_tac[] >>
  drule_all ifexp_bytes_caller_ghost_kept >> simp[]
QED

Resume ifexp_allocated_bytes_writer[pointer]:
  irule ifexp_bytes_destination_ptr_post >> simp[] >>
  qexistsl_tac [`capacity`, `b`] >> simp[eval_operand_def]
QED

Finalise ifexp_allocated_bytes_writer
