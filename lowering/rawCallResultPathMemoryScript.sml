(* Result execution with the counted memory path for nonreverting raw_call. *)
Theory rawCallResultPathMemory
Ancestors
  rawCallSuffixMemory exprSimRawCall rawCallTupleMemory
  bodyMemAggregateBounds exprSimVVFrame exprSimMemDefs valueEncoding
  exprSimDefs exprLoweringProps venomState venomInst compileEnv context
  finite_map words
Libs
  monadsyntax

Theorem raw_call_nonrevert_positive_path_mem:
  expr_type e = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))] /\
  lowered_value_type cenv e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) /\
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
     else return ok) sa = (result,sb) /\ 0 < n /\
  stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 es sf s0 s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n + 31) DIV 32) * 32) /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
  alloc.inst_id < sa.cs_next_id /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sa ov /\ safe_operand sa ok /\
  eval_operand ov s = SOME w /\ eval_operand ok s = SOME (if success then 1w else 0w) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata /\
  64 + ((n + 31) DIV 32) * 32 < dimword (:256) /\ n < dimword (:256) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t tw ti. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es0 es sf s0 t /\
    t.vs_fmp = s.vs_fmp /\
    (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s) /\
    sf.cs_next_id <= ti /\ ti < sb.cs_next_id /\
    eval_operand result t = SOME tw /\
    FLOOKUP t.vs_allocas ti = SOME (w2n tw,64 + ((n + 31) DIV 32) * 32) /\
    w2n tw + (64 + ((n + 31) DIV 32) * 32) < dimword (:256) /\
    val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
      (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)]))
      (w2n tw) t.vs_memory /\
    (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
      w2n tw + (64 + ((n + 31) DIV 32) * 32) <= lb \/ lb + lsz <= w2n tw) /\
    gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_current_bb = sb.cs_current_bb /\
    vv_post ctx func cenv cx e es0 sf sb s0 es
      (Value (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])))
      (LocatedValue (expr_type e) (mk_ptr result LocMemory))
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) es
      (Value (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])))
      (LocatedValue (expr_type e) (mk_ptr result LocMemory))
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  drule_all raw_call_nonrevert_positive_run >> strip_tac >>
  drule_all raw_call_nonrevert_positive_mem_ok >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all raw_call_nonrevert_suffix_counted_mem >> strip_tac >>
  `vv_post ctx func cenv cx e es0 sf sb s0 es
    (Value (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])))
    (LocatedValue (expr_type e) (mk_ptr result LocMemory)) t` by
    (qpat_assum `lowered_value_type _ _ = _`
       (assume_tac o MATCH_MP loweringPostsTheory.post_value_type_lowered) >>
     irule raw_call_tuple_post >> simp[] >> qexists_tac `ti` >>
     fs[arithmeticTheory.MULT_COMM] >> metis_tac[]) >>
  `vv_store_bound cx (expr_type e) (lowered_value_type cenv e) es
    (Value (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])))
    (LocatedValue (expr_type e) (mk_ptr result LocMemory)) t` by
    (irule aggregate_allocated_result_store_bound_mem >>
     conj_tac >- fs[stmt_state_rel_def] >>
     conj_tac
     >- (qexistsl_tac [`ti`,`w2n tw`,
           `TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]`,
           `64 + ((n+31) DIV 32)*32`] >>
         pure_rewrite_tac[mk_ptr_def, type_memory_size_def,
           vfmConstantsTheory.word_size_def] >> simp[arithmeticTheory.MULT_COMM]) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`t`,`tw`,`ti`] >>
  fs[arithmeticTheory.MULT_COMM, vv_store_bound_def, mk_ptr_def,
     eval_operand_def, lookup_var_def] >> metis_tac[]
QED
