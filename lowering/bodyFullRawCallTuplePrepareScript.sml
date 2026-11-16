(* Conditional assembly of the tuple suffix.  The four closed antecedents are
   discharged by the actual finite and spatial producers at publication. *)
Theory bodyFullRawCallTuplePrepare
Ancestors
  bodyFullRawCallTupleAllocFrame bodyFullAllocGeneric rawCallBufferPtr
  exprSimRawCall exprSimRawCallCalldata fragGasSeqPtr instSeqComposePtr
  loweringStateRelDefs ptrDiscipline venomState bodyPtrDefs
  exprLoweringProps venomMemDefs

Theorem raw_call_tuple_suffix_prepared:
  (!z sa s1 cmp n s2 cap s3 sb x s b G tn lo ctx func PG t.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
    emit_void MSTORE [Var x;cap] s3 = ((),sb) /\
    0 < n /\ n < dimword (:256) /\
    64 + ((n+31) DIV 32)*32 < dimword (:256) /\
    safe_operand sa (Var x) /\ lookup_var x s = SOME (n2w b) /\
    b + (32 + ((n+31) DIV 32)*32) < dimword (:256) /\
    ptr_covers G tn x s (32 + ((n+31) DIV 32)*32) /\
    LENGTH s.vs_returndata < dimword (:256) /\
    mem_bytes_at (b+32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
      TAKE n s.vs_returndata /\
    (!i. b+32 <= i /\ i < b+32+LENGTH (TAKE n s.vs_returndata) ==>
      i NOTIN tn.t_mem) /\
    allocas_from lo s /\ ~ctx_has_dalloca ctx /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    ?Gf tnf.
      (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf) /\
      ptr_covers Gf tnf x t (32 + ((n+31) DIV 32)*32) /\
      (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
        val_in_memory (BaseTV (BytesT (Dynamic n)))
          (BytesV (TAKE n s.vs_returndata)) b mem) /\
      tnf.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      (!v. not_fresh_at sa v ==>
        lookup_var v t = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
        op_taint tnf (Var v) = op_taint tn (Var v)) /\
      (t with vs_vars := s.vs_vars) =
        mstore b (n2w (LENGTH (TAKE n s.vs_returndata))) s) ==>
  (!p ok sa s1 dst s2 x n sb bs a b s G tn success lo ctx func PG t.
    emit_void MSTORE [Var p;ok] sa = ((),s1) /\
    emit_op ADD [Var p;Lit 32w] s1 = (dst,s2) /\
    emit_void MCOPY [dst;Var x;Lit (n2w (32 + ((n+31) DIV 32)*32))]
      s2 = ((),sb) /\
    safe_operand sa (Var p) /\ safe_operand sa (Var x) /\ safe_operand sa ok /\
    0 < n /\ LENGTH bs <= n /\
    64 + ((n+31) DIV 32)*32 < dimword (:256) /\
    a + (32 + ((n+31) DIV 32)*32) < dimword (:256) /\
    b + (64 + ((n+31) DIV 32)*32) < dimword (:256) /\
    lookup_var x s = SOME (n2w a) /\ lookup_var p s = SOME (n2w b) /\
    ptr_covers G tn x s (32 + ((n+31) DIV 32)*32) /\
    ptr_covers G tn p s (64 + ((n+31) DIV 32)*32) /\
    eval_operand ok s = SOME (if success then 1w else 0w) /\ op_taint tn ok = {} /\
    (a+32+LENGTH bs <= b \/ b+32 <= a) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) a mem) /\
    allocas_from lo s /\ ~ctx_has_dalloca ctx /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    let count = 32 + ((n+31) DIV 32)*32;
        dirty = tn.t_mem DIFF {i | b <= i /\ i < b+32}
    in ?Gf tnf.
      (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf) /\
      ptr_covers Gf tnf p t (64 + ((n+31) DIV 32)*32) /\
      (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
        val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
          (ArrayV (TupleV [BoolV success;BytesV bs])) b mem) /\
      tnf.t_mem =
        ((dirty DIFF {i | b+32 <= i /\ i < b+32+count}) UNION
          {b+32+i | i < count /\ a+i IN dirty}) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      (!v. not_fresh_at sa v ==>
        lookup_var v t = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
        op_taint tnf (Var v) = op_taint tn (Var v)) /\
      (t with vs_vars := s.vs_vars) =
        mcopy (b+32) a count (mstore b (val_to_w256 (BoolV success)) s)) ==>
  (!H ctx func cenv cx es s inst q b k sf es0 s0 lo.
    stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
      ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
    sf.cs_next_id <= inst.inst_id /\ local_ptrs_reserved cenv sf /\
    MAP FDOM es0.scopes = MAP FDOM es.scopes /\
    (!x. not_fresh_at sf x ==> lookup_var x s = lookup_var x s0) /\
    (!aid row. FLOOKUP s0.vs_allocas aid = SOME row ==>
      FLOOKUP s.vs_allocas aid = SOME row) /\ allocas_from lo s ==>
    lo <= b /\
    (!aid a m. FLOOKUP s.vs_allocas aid = SOME (a,m) /\ aid < inst.inst_id ==>
      a+m <= b \/ b+k <= a) /\
    (!name a m i. local_region cenv es.scopes s name a m /\
      a <= i /\ i < a+m ==> ~(b <= i /\ i < b+k)) /\
    (!aid a m i. FLOOKUP s0.vs_allocas aid = SOME (a,m) /\
      aid < sf.cs_next_id /\ a <= i /\ i < a+m ==> ~(b <= i /\ i < b+k)) /\
    (!name a m i. local_region cenv es0.scopes s0 name a m /\
      a <= i /\ i < a+m ==> ~(b <= i /\ i < b+k))) ==>
  (!H ctx func cenv cx es s sf t Gf G tnf tn R lo s0 es0 G0 tn0 dep.
    stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
      ctx func cenv cx es s /\
    local_ptrs_reserved cenv sf /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
    (!x. not_fresh_at sf x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!i. i NOTIN R ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i NOTIN R /\ i IN tnf.t_mem ==> i IN tn.t_mem) /\
    (!i. i < lo ==> i NOTIN R) /\
    (!name a m i. local_region cenv es.scopes s name a m /\
      a <= i /\ i < a+m ==> i NOTIN R) /\
    (!aid a m i. FLOOKUP s0.vs_allocas aid = SOME (a,m) /\
      aid < sf.cs_next_id /\ a <= i /\ i < a+m ==> i NOTIN R) /\
    (!name a m i. local_region cenv es0.scopes s0 name a m /\
      a <= i /\ i < a+m ==> i NOTIN R) /\
    ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn ==>
    ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
    (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
      ghost_inv_at D lo dep cenv cx es Gf tnf t)) ==>
  !n sa result sb cenv e cx H0 ctx func es s es0 sf s0 alloc q w ov ok
    ovx G tn success lo G0 tn0 explicit PG t dep.
  (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sa = (result,sb) /\
  0 < n /\
  post_value_type cenv e = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))] /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) /\
  type_memory_bytes cenv (lowered_value_type cenv e) <=
    64 + ((n + 31) DIV 32) * 32 /\
  stmt_state_rel (H0 : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\
  wb_frame cenv es0 es sf s0 s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id =
    SOME (w2n w,32 + ((n + 31) DIV 32) * 32) /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
  alloc.inst_id < sa.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sf x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sf x) /\
  safe_operand sa ov /\ safe_operand sa ok /\
  ov = Var ovx /\
  FLOOKUP G ovx = SOME (w2n w,32 + ((n + 31) DIV 32) * 32) /\
  op_taint tn ov = {} /\ op_taint tn ok = {} /\
  eval_operand ov s = SOME w /\
  eval_operand ok s = SOME (if success then 1w else 0w) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata /\
  (!i. w2n w + 32 <= i /\
       i < w2n w + 32 + LENGTH (TAKE n s.vs_returndata) ==>
       i NOTIN tn.t_mem) /\
  64 + ((n + 31) DIV 32) * 32 < dimword (:256) /\
  n < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?Gf tnf p.
    result = Var p /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)) /\
    ptr_covers Gf tnf p t (64 + ((n + 31) DIV 32) * 32) /\
    (!tw mem. eval_operand result t = SOME tw /\
       mem_agree_outside tnf.t_mem t.vs_memory mem ==>
       val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
         (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)]))
         (w2n tw) mem) /\
    ptr_vv_ok cx (post_value_type cenv e)
      (Value (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])))
      (LocatedValue (expr_type e) (mk_ptr result LocMemory)) es Gf tnf
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ptr_buf_ok cenv e result Gf
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
    (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
       ghost_inv_at D lo dep cenv cx es Gf tnf
         (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  disch_then (mk_asm "length") >>
  disch_then (mk_asm "copy") >>
  disch_then (mk_asm "separation") >>
  disch_then (mk_asm "frame") >>
  rpt gen_tac >> strip_tac >>
  drule_all raw_call_nonrevert_suffix_code >> strip_tac >>
  suspend "assemble"
QED

Resume raw_call_tuple_suffix_prepared[assemble]:
  qpat_x_assum `(if _ then _ else _) _ = _` kall_tac >>
  `stmt_state_rel H0 ctx func cenv cx es (s with vs_fmp := s.vs_fmp)` by simp[] >>
  qpat_assum `stmt_state_rel H0 _ _ _ _ _ (s with vs_fmp := _)`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac
      raw_call_output_prefix_ready) >>
  disch_then (drule_at (Pat `emit_op RETURNDATASIZE _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op LT _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_select _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_void MSTORE _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >> simp[] >>
  disch_then drule_all >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa s4) s = OK u` >>
  `u with vs_fmp := s.vs_fmp = u` by
    (qpat_assum `u.vs_fmp = _` (SUBST1_TAC o SYM) >> simp[]) >> fs[] >>
  `w2n w + (32 + ((n+31) DIV 32)*32) < dimword (:256)` by
    (gvs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `ptr_covers G tn ovx s (32 + ((n+31) DIV 32)*32)` by
    (gvs[ptr_covers_def, eval_operand_def]) >>
  asm "length" drule_all >> strip_tac >>
  suspend "length_frame"
QED

Resume raw_call_tuple_suffix_prepared[length_frame]:
  cheat
QED

Finalise raw_call_tuple_suffix_prepared
