Theory bodyPtrIfExpStorageSingle
Ancestors bodyPtrIfExpMaterializeSingle bodyPtrIfExpStorageSupplier
  bodyPtrIfExpStorageAllocation bodyPtrIfExpStorageSource pred_set
  context compileEnv loweringStateRelDefs emitHelper fragExec loweringHalt bodyPtrIfExpStorageAllocationFrame
  bodyPtrIfExpSingleCopyPost bodyPtrIfExpActiveCopyPost bodyPtrIfExpAllocSource exprSimStorageCopy valueEncodingTyping
  bodyPtrIfExpBytesInputs loweringPosts venomState finite_map valueEncodingProps

(* One-slot representations need not be word types.  Use source decoding
   and translated taint, exactly as for the nonsingleton loop. *)
Theorem ifexp_storage_single_robust:
  type_slot_size ty = 1 /\ well_formed_type_value ty /\
  slots_in_range st (w2n p) ty /\ decode_value st (w2n p) ty = SOME v /\
  storage_range_agree st rt p ty /\
  u = mstore b (lookup_storage p rt) s /\
  dest_taint = (old_taint DIFF {i | b <= i /\ i < b+32}) UNION
    {b+i | i IN key_taint source_taint p} /\
  (!k j. w2n p <= w2n k /\ w2n k < w2n p+type_slot_size ty /\
    j < 32 /\ (k,j) IN source_taint ==> dead_bytes rt (w2n p) ty (w2n k) j) ==>
  !m. mem_agree_outside dest_taint u.vs_memory m ==> val_in_memory ty v b m
Proof
  rpt strip_tac >> irule ifexp_range_storage_decode_robust >>
  conj_tac >- simp[] >>
  qexistsl_tac [`dest_taint`, `u.vs_memory`, `rt`, `source_taint`, `st`, `p`] >>
  simp[valueEncodingPropsTheory.mstore_mem_word_at_same,
       ptrDisciplineTheory.key_taint_def] >>
  simp[wordsTheory.WORD_ADD_0] >> metis_tac[]
QED

Theorem ifexp_storage_single_code:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc bytes 1 ctor imm sb = (dst,sd) /\
  fn_has_code sb sd fn ==>
  ?buf cs.
    compile_alloc_buffer bytes sb = (buf,cs) /\ dst = buf.buf_operand /\
    (do loaded <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [buf.buf_operand;loaded] od) cs = ((),sd) /\
    fn_has_code sb cs fn /\ fn_has_code cs sd fn /\
    sb.cs_next_var <= cs.cs_next_var /\ sb.cs_next_id <= cs.cs_next_id
Proof
  strip_tac >>
  drule_at (Pat `compile_ensure_in_memory _ _ _ _ _ _ _ = _`) ifexp_ensure_single_stages >>
  simp[] >> strip_tac >>
  rename1 `compile_alloc_buffer bytes sb = (buf,cs)` >>
  `cs_extends cs sd` by
    (gvs[compileEnvTheory.cs_extends_def,
      emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def,
      fresh_id_def, emit_def] >> simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  qexistsl_tac [`buf`, `cs`] >> simp[]
QED

Theorem ifexp_storage_load_step:
  (opc = SLOAD \/ opc = TLOAD) /\ eval_operand src s = SOME p ==>
  step_inst_base (mk_inst id opc [src] [out]) s =
    OK (update_var out (if opc = SLOAD then sload p s else tload p s) s)
Proof
  strip_tac >> gvs[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
    venomExecSemanticsTheory.exec_read1_def, venomInstTheory.mk_inst_def]
QED

Theorem ifexp_ensure_memory_storage_single:
  post_value_type ce e = expr_type e /\
  expr_body_pre ce cx env e es /\ eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx e es sa sb s0 ee raw (LocatedValue tag pp) s /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue tag pp) ee G tn s /\
  (pp.ptr_location = LocStorage \/ pp.ptr_location = LocTransient) /\
  (type_memory_bytes ce (expr_type e)+31) DIV 32 = 1 /\
  compile_ensure_in_memory pp.ptr_operand pp.ptr_location
    (type_memory_bytes ce (expr_type e)) 1 is_ctor imm sb = (dst,sd) /\
  fn_has_code sb sd fn /\
  ghost_inv rty ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_inst_ids_distinct fn /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  type_memory_bytes ce (expr_type e) < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  fresh_vars_wrt sb s ==>
  ?out d ty t G' tn'.
    dst = Var out /\ eval_operand dst t = SOME d /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~t.vs_halted /\
    (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==> val_in_memory ty v (w2n d) m) /\
    ptr_covers G' tn' out t (type_memory_bytes ce (expr_type e)) /\
    ghost_inv rty ce cx ee G' tn' t /\ ghost_kept ce es sa G0 tn0 s0 G' tn' /\
    (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
      off+sz <= w2n d \/ w2n d+type_memory_bytes ce (expr_type e) <= off) /\
    (!name pos len. local_region ce es.scopes s0 name pos len ==>
      pos+len <= w2n d \/ w2n d+type_memory_bytes ce (expr_type e) <= pos) /\
    (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!b len. b+len <= w2n d \/ w2n d+type_memory_bytes ce (expr_type e) <= b ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_transient = s.vs_transient /\ t.vs_data_section = s.vs_data_section /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (~is_word_type (expr_type e) ==> expr_post ctx fn ce cx e es sa sd s0 ee v dst t)
Proof
  bodyPtrStorageSingleProofLib.start ifexp_storage_single_code >>
  suspend "execute"
QED

Resume ifexp_ensure_memory_storage_single[execute]:
  bodyPtrStorageSingleProofLib.execute ifexp_storage_load_step >> suspend "finish"
QED

Resume ifexp_ensure_memory_storage_single[finish]:
  bodyPtrStorageSingleProofLib.frames >> suspend "post"
QED

Resume ifexp_ensure_memory_storage_single[post]:
  bodyPtrStorageSingleProofLib.robust ifexp_storage_single_robust >> suspend "ordinary"
QED

Resume ifexp_ensure_memory_storage_single[ordinary]:
  bodyPtrStorageSingleProofLib.ordinary >> suspend "semantic"
QED

Resume ifexp_ensure_memory_storage_single[semantic]:
  markerLib.RESUME_TAC >> bodyPtrStorageSingleProofLib.semantic >> suspend "expr_post"
QED

Resume ifexp_ensure_memory_storage_single[expr_post]:
  markerLib.RESUME_TAC >> bodyPtrStorageSingleProofLib.post >>
  bodyPtrStorageSingleProofLib.assemble
QED

Finalise ifexp_ensure_memory_storage_single
