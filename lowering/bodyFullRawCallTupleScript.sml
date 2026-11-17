(* Publish the tuple boundary using the four actual producer certificates. *)
Theory bodyFullRawCallTuple
Ancestors
  bodyFullRawCallTuplePrepare bodyFullRawCallTupleLength
  bodyFullRawCallTupleCopy bodyFullRawCallTupleWriteSeparation
  bodyFullRawCallTupleWriteFrame

Theorem raw_call_tuple_suffix_origin_at:
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
  mp_tac raw_call_tuple_suffix_prepared >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC raw_call_tuple_length_checked)) >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC raw_call_tuple_copy_checked)) >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC raw_call_tuple_write_separation)) >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC raw_call_tuple_write_frame)) >>
  disch_then MATCH_ACCEPT_TAC
QED
