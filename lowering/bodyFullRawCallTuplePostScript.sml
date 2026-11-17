Theory bodyFullRawCallTuplePost
Ancestors
  bodyFullRawCallTuple exprSimRawCall exprSimMemDefs
  bodyDeclMemoryCore bodyMemBiSha256Compose entrySinkExtraction
  exprLoweringProps exprSimRawCallCalldata venomState loweringStateRelDefs
  venomMemDefs valueEncoding exprSimProps exprLowering loweringPosts compileEnv vyperValue
  typeLayoutProps vfmConstants context vyperState
Libs
  monadsyntax

Theorem raw_call_tuple_suffix_full_post:
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
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  expr_has_effect e /\ post_value_type cenv e = expr_type e /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next ==>
  ?Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)) /\
    !H D. stmt_state_rel H ctx func cenv cx es s /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at D lo dep cenv cx es G tn s ==>
      vv_post H ctx func cenv cx e es0 sf sb s0 es
        (Value (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])))
        (LocatedValue (expr_type e) (mk_ptr result LocMemory))
        (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) es
        (Value (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])))
        (LocatedValue (expr_type e) (mk_ptr result LocMemory))
        (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb = sb.cs_current_bb /\
      (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
      s0.vs_alloca_next <= (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_alloca_next /\
      ghost_inv_at D lo dep cenv cx es Gf tnf (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      ptr_vv_ok cx (post_value_type cenv e)
        (Value (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])))
        (LocatedValue (expr_type e) (mk_ptr result LocMemory)) es Gf tnf
        (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      (cenv.ce_is_ctor /\ vv_location (LocatedValue (expr_type e) (mk_ptr result LocMemory)) = SOME LocCode ==>
        ?val. read_result cx (Value (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)]))) es = (INL val,es) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
            eval_operand (vv_operand (LocatedValue (expr_type e) (mk_ptr result LocMemory)))
              (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tnf.t_mem (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
      (!t' op. LocatedValue (expr_type e) (mk_ptr result LocMemory) = StackValue t' op /\
        ~is_word_type (post_value_type cenv e) ==>
        ptr_buf_ok cenv e op Gf (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
      (!t' p. LocatedValue (expr_type e) (mk_ptr result LocMemory) = LocatedValue t' p /\
        p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand Gf (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
      ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf
Proof
  strip_tac >>
  drule_all raw_call_tuple_suffix_origin_at >>
  disch_then (qspecl_then [`explicit`,`dep`,`PG`]
    (qx_choose_then `Gf` (qx_choose_then `tnf` (qx_choose_then `p` strip_assume_tac)))) >>
  qexistsl_tac [`Gf`,`tnf`] >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `stmt_state_rel H ctx func cenv cx es s`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac raw_call_nonrevert_positive_run) >>
  disch_then drule_all >> strip_tac >> gvs[] >>
  suspend "post"
QED

Resume raw_call_tuple_suffix_full_post[post]:
  `vv_post H ctx func cenv cx e es0 sf sb s0 es
    (Value (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])))
    (LocatedValue (expr_type e) (mk_ptr (Var p) LocMemory))
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule raw_call_tuple_post >>
     simp[stmt_state_rel_inst_idx, raw_call_wb_frame_inst_idx,
       eval_operand_def, lookup_var_def] >>
     qexistsl_tac [`ti`,`tw`] >>
     fs[eval_operand_def, lookup_var_def] >>
     rpt strip_tac >>
     qpat_x_assum `!name lb lsz. local_region cenv es.scopes t name lb lsz ==> _` irule >>
     fs[local_region_def, lookup_var_def] >> metis_tac[]) >>
  suspend "store"
QED

Resume raw_call_tuple_suffix_full_post[store]:
  `w2n tw + (32 * ((n + 31) DIV 32) + 64) <= t.vs_alloca_next` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es t` mp_tac >>
     qpat_assum `FLOOKUP t.vs_allocas ti = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     metis_tac[]) >>
  `!rt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt ==>
    type_memory_size rt = type_memory_bytes cenv (lowered_value_type cenv e)` by
    (qsuff_tac `(?bt. lowered_value_type cenv e = BaseT bt) \/
       lowered_value_type cenv e = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))]`
     >- (strip_tac >> gvs[]
         >- metis_tac[type_memory_bytes_base_evaluated] >>
         simp[evaluate_type_def, type_memory_size_def, type_memory_bytes_def, word_size_def]) >>
     qpat_assum `post_value_type cenv e = _` mp_tac >>
     qpat_assum `expr_type e = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `e` >> simp[vyperASTTheory.expr_type_def] >>
     rpt strip_tac >> gvs[] >>
     simp[lowered_value_type_def, post_value_type_def, vyperASTTheory.expr_type_def] >>
     TRY (rename1 `lowered_value_type _ (Builtin _ b _)` >>
       Cases_on `b` >> simp[lowered_value_type_def, concat_buffer_type_def,
         vyperASTTheory.expr_type_def] >> NO_TAC) >>
     TRY (rename1 `lowered_value_type _ (TypeBuiltin _ tb _ _)` >>
       Cases_on `tb` >> simp[lowered_value_type_def, vyperASTTheory.expr_type_def] >> NO_TAC) >>
     rename1 `lowered_value_type _ (Call _ target _ _)` >>
     Cases_on `target` >>
     gvs[post_value_type_def, lowered_value_type_def, is_word_type_def,
       is_bytestring_type_def, vyperASTTheory.expr_type_def]) >>
  suspend "capacity"
QED

Resume raw_call_tuple_suffix_full_post[capacity]:
  `vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) es
    (Value (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])))
    (LocatedValue (expr_type e) (mk_ptr (Var p) LocMemory))
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_assum `w2n tw + _ <= t.vs_alloca_next` mp_tac >>
     qpat_assum `eval_operand (Var p) t = SOME tw` mp_tac >>
     qpat_assum `type_memory_bytes cenv _ <= _` mp_tac >>
     qpat_assum `!rt. evaluate_type _ (lowered_value_type cenv e) = _ ==> _` mp_tac >>
     qpat_assum `expr_type e = _` mp_tac >>
     qpat_assum `post_value_type cenv e = _` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) (TupleT _) = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[vv_store_bound_def, mk_ptr_def, read_result_def, vyperStateTheory.return_def,
       eval_operand_def, lookup_var_def,
       val_store_size_def, type_memory_size_def, word_size_def] >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  suspend "control"
QED

Resume raw_call_tuple_suffix_full_post[control]:
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\ same_blocks sa sb /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (qpat_assum `do _ od sa = _` mp_tac >>
     qpat_assum `0 < n` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     qpat_assum `0 < n`
       (mp_then (Pat `0 < _`) mp_tac exprSimRawCallTheory.raw_call_nonrevert_suffix_code) >>
     simp[] >> disch_then drule_all >> strip_tac >>
     gvs[same_blocks_def, emitted_insts_def, rich_listTheory.IS_PREFIX_APPEND,
       rich_listTheory.DROP_APPEND]) >>
  `alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s`,`sa`] >> simp[] >>
     fs[stmt_state_rel_def]) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (irule sha256_run_inst_seq_alloca_next_mono >>
     goal_assum (drule_at Any) >> simp[]) >>
  `t.vs_current_bb = sb.cs_current_bb` by
    (drule_all run_inst_seq_preserves_entry_control >> simp[]) >>
  gvs[mk_ptr_def,vv_location_def]
QED

Finalise raw_call_tuple_suffix_full_post
