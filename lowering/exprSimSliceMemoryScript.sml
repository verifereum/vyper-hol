(* Source capture boundaries for ordinary slices. *)
Theory exprSimSliceMemory
Ancestors
  builtinBytes emitHelperProps freshWrites fragExec exprLoweringProps
  compileEnv emitHelper context venomInst venomState venomExecSemantics
  venomMemDefs words arithmetic list finite_map loweringPosts valueEncodingProps
  exprSimLiteralBuffer exprSimHash stmtSimLogArgs stmtSimReturn exprSimTypedAlloc

Theorem slice_bytestring_src_shape:
  compile_bytestring_src src sa = ((len,data),sb) ==>
  len = Var (STRING #"%" (toString sa.cs_next_var)) /\
  data = Var (STRING #"%" (toString (sa.cs_next_var + 1))) /\
  sb.cs_next_var = sa.cs_next_var + 2 /\
  sb.cs_next_id = sa.cs_next_id + 2 /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id MLOAD [src]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) ADD [src; Lit 32w]
       [STRING #"%" (toString (sa.cs_next_var + 1))]]
Proof
  simp[compile_bytestring_src_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]
QED

Theorem slice_bytestring_src_run:
  compile_bytestring_src src sa = ((len,data),sb) /\
  eval_operand src s = SOME p /\
  (!z. src = Var z ==> not_fresh_at sa z) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand len t = SOME (mload (w2n p) s) /\
      eval_operand data t = SOME (p + 32w) /\
      t = s with vs_vars := t.vs_vars /\
      (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> drule slice_bytestring_src_shape >> strip_tac >>
  `eval_operand src
     (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n p) s) s) =
     eval_operand src s` by
    (Cases_on `src` >> gvs[eval_operand_def, lookup_var_update_var,
                            not_fresh_at_def] >> metis_tac[]) >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_read1_def, exec_pure2_def, eval_operand_def, lookup_var_update_var] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE, not_fresh_at_def] >>
  rpt strip_tac >> gvs[]
QED

(* Later operands preserve windows inside earlier non-local allocations.
   The frame is independent of nocalls, so internal calls are covered too. *)
Theorem slice_allocated_window_preserved:
  wb_frame cenv es sa s t /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  (!name off len. local_region cenv es.scopes s name off len ==>
                  b + sz <= off \/ off + len <= b) /\
  i + n <= sz ==>
  mem_bytes_at (b+i) n t.vs_memory = mem_bytes_at (b+i) n s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (fs[wb_frame_def] >> first_x_assum irule >>
     conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[ADD_COMM]) >>
     qexists_tac `aid` >> simp[]) >>
  irule mem_bytes_at_translated_window >>
  qexists_tac `sz` >> simp[]
QED

Theorem slice_bytestring_capture:
  compile_bytestring_src src sa = ((len,data),sb) /\
  eval_operand src s = SOME p /\
  (!z. src = Var z ==> not_fresh_at sa z) /\
  mload (w2n p) s = n2w (LENGTH bs) /\
  mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs /\
  w2n p + 32 < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand len t = SOME (n2w (LENGTH bs)) /\
      eval_operand data t = SOME (n2w (w2n p + 32)) /\
      mem_bytes_at (w2n p + 32) (LENGTH bs) t.vs_memory = bs /\
      t = s with vs_vars := t.vs_vars /\
      (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> drule_all slice_bytestring_src_run >> strip_tac >>
  qexists_tac `t` >> simp[GSYM word_add_n2w] >>
  qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]
QED

(* Fixed bytes are staged without a length header: the scratch word starts
   at the allocation's base, unlike a dynamic bytestring's payload. *)
Theorem slice_fixed_scratch_store:
  emit_void MSTORE [ptr_op; value] sa = ((),sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand value s = SOME w /\
  LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be w) = bs ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      mem_bytes_at (w2n p) (LENGTH bs) t.vs_memory = bs /\
      t = mstore (w2n p) w s /\
      t.vs_allocas = s.vs_allocas /\ t.vs_vars = s.vs_vars /\
      (!off len. regions_disjoint (w2n p) 32 off len ==>
        mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >> drule_all literal_emit_mstore_run >> strip_tac >>
  qexists_tac `mstore (w2n p) w s` >> simp[] >>
  conj_tac >- (irule hash_mstore_prefix >> simp[]) >>
  conj_tac >- simp[mstore_def] >> rpt strip_tac >>
  irule mstore_region_frame >> qexistsl_tac [`w2n p`, `32`] >> simp[]
QED

Theorem slice_fixed_scratch_alloc:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; val_op] sm = ((),sb) /\
  eval_operand val_op s = SOME w /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\ (!l. val_op <> Label l) /\
  LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be w) = bs /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t p. run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t /\
    eval_operand buf.buf_operand t = SOME p /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n p,32) /\
    w2n p + 32 < dimword (:256) /\ sa.cs_next_id < sm.cs_next_id /\
    mem_bytes_at (w2n p) (LENGTH bs) t.vs_memory = bs /\
    (!name off len. local_region cenv es.scopes s name off len ==>
       regions_disjoint (w2n p) 32 off len) /\
    stmt_state_rel ctx func cenv cx es t /\
    (!name off len. local_region cenv es.scopes t name off len ==>
       regions_disjoint (w2n p) 32 off len) /\
    sa.cs_next_id < sb.cs_next_id /\
    (?x. buf.buf_operand = Var x /\ not_fresh_at sb x)
Proof
  strip_tac >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  `eval_operand val_op u = SOME w` by
    (drule_all log_frame_operand >> simp[]) >>
  drule_all slice_fixed_scratch_store >> strip_tac >>
  qexistsl_tac [`t`, `w'`] >>
  conj_tac >- (qpat_assum `run_inst_seq _ s = OK u`
    (mp_then Any mp_tac run_inst_seq_append) >> simp[]) >> simp[] >>
  conj_tac >- gvs[eval_operand_def, lookup_var_def] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> qexists_tac `name` >>
      irule exprSimPropsTheory.local_region_frame_fwd >>
      qexistsl_tac [`s`, `sa`, `es.scopes`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `t = mstore _ _ _` SUBST1_TAC >>
      irule exprSimAllocTheory.literal_mstore_state_rel >>
      reverse conj_tac >- simp[] >>
      qexistsl_tac [`w2n w'`, `mk_inst sa.cs_next_id ALLOCA [Lit 32w]
        [STRING #"%" (toString sa.cs_next_var)]`, `32`] >>
      simp[mk_inst_def] >> rpt strip_tac >>
      first_x_assum drule >> simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> qexists_tac `name` >>
      fs[local_region_def, lookup_var_def]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  gvs[not_fresh_at_def]
QED

Theorem slice_out_buf_decompose:
  compile_slice_out_buf sz sa = ((out,data),sb) ==>
  ?buf sm. compile_alloc_buffer sz sa = (buf,sm) /\
    out = buf.buf_operand /\ emit_op ADD [out; Lit 32w] sm = (data,sb) /\
    sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
    sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb
Proof
  simp[compile_slice_out_buf_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >> simp[] >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> simp[]
QED

Theorem slice_out_data_run[local]:
  emit_op ADD [out; Lit 32w] sa = (data,sb) /\
  eval_operand out s = SOME p /\
  (!z. out = Var z ==> not_fresh_at sa z) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand out t = SOME p /\ eval_operand data t = SOME (p + 32w) /\
      t = s with vs_vars := t.vs_vars /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def,
       mk_inst_def, eval_operand_def] >>
  conj_tac
  >- (Cases_on `out` >> gvs[eval_operand_def, lookup_var_update_var,
                             not_fresh_at_def] >> metis_tac[]) >>
  simp[lookup_var_update_var, update_var_def] >>
  rpt strip_tac >> gvs[lookup_var_def, FLOOKUP_UPDATE, not_fresh_at_def]
QED

Theorem slice_out_buf_run:
  compile_slice_out_buf sz sa = ((out,data),sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t p. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand out t = SOME p /\ eval_operand data t = SOME (p + 32w) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n p,sz) /\
    w2n p + sz < dimword (:256) /\ sa.cs_next_id < sb.cs_next_id /\
    (!name off len. local_region cenv es.scopes s name off len ==>
       regions_disjoint (w2n p) sz off len) /\
    (!name off len. local_region cenv es.scopes t name off len ==>
       regions_disjoint (w2n p) sz off len) /\
    (?x. out = Var x /\ not_fresh_at sb x) /\
    (?x. data = Var x /\ not_fresh_at sb x) /\
    stmt_state_rel ctx func cenv cx es t /\
    t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n p) sz b len) /\
    wb_frame cenv es sa s t
Proof
  strip_tac >> drule slice_out_buf_decompose >> strip_tac >> gvs[] >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  `local_ptrs_reserved cenv sm` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
     drule emitted_insts_emit_op >> strip_tac >>
     gvs[local_ptrs_reserved_def, not_fresh_at_def] >>
     metis_tac[DECIDE ``a + 1 <= n ==> a <= n``]) >>
  `!z. buf.buf_operand = Var z ==> not_fresh_at sm z` by simp[] >>
  drule_all slice_out_data_run >> strip_tac >>
  qexistsl_tac [`t`, `w`] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  conj_tac >- (simp[] >> qpat_assum `run_inst_seq _ s = OK u`
    (mp_then Any mp_tac run_inst_seq_append) >> simp[]) >>
  `t.vs_allocas = u.vs_allocas` by
    (qpat_x_assum `t = u with vs_vars := _` SUBST1_TAC >> simp[]) >>
  drule emitted_insts_emit_op >> strip_tac >> simp[ADD_COMM] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> qexists_tac `name` >>
      irule exprSimPropsTheory.local_region_frame_fwd >>
      qexistsl_tac [`s`, `sa`, `es.scopes`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> qexists_tac `name` >>
      irule exprSimPropsTheory.local_region_frame >>
      conj_tac
      >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
      qexistsl_tac [`sm`, `es.scopes`, `t`] >>
      simp[]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (qpat_x_assum `t = u with vs_vars := _` SUBST1_TAC >>
     irule exprSimPropsTheory.stmt_state_rel_vars_frame >>
     simp[] >> rpt strip_tac >>
     fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, emitHelperTheory.emit_op_def,
          fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels` by
    (qpat_x_assum `t = u with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by
       (qpat_x_assum `not_fresh_at sa x` mp_tac >>
        simp[not_fresh_at_def] >> rpt strip_tac >>
        first_x_assum irule >> decide_tac) >> metis_tac[]) >>
  `wb_frame cenv es sa s t` by
    (simp[wb_frame_def] >>
     irule exprSimPropsTheory.locals_kept_mem >>
     simp[] >> rpt strip_tac >> metis_tac[]) >>
  gvs[not_fresh_at_def] >>
  rpt strip_tac >>
  qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _` irule >>
  qexists_tac `aid` >> simp[]
QED

(* The operand post, including when nocalls is false, carries the memory
   frame needed by a source captured before that operand is evaluated. *)
Theorem slice_payload_after_operand:
  expr_sim_inv cenv cx env es /\
  expr_val_at cenv cx (BaseT bt) sa sm es v op s /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME vt /\
  ~is_word_type (BaseT bt) /\ eval_operand op s = SOME p /\
  32 + LENGTH bs <= val_footprint vt v /\
  mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs /\
  expr_post ctx func cenv cx e es sm sb s es' v' op' t ==>
  mem_bytes_at (w2n p + 32) (LENGTH bs) t.vs_memory = bs
Proof
  strip_tac >>
  `wb_frame cenv es sm s t` by (drule exprSimWordArgsTheory.expr_post_frame >> simp[]) >>
  `log_arg_clear cenv cx (BaseT bt) v` by
    (irule log_arg_clear_base >> goal_assum (drule_at Any)) >>
  drule_all log_argument_footprint_kept >> strip_tac >>
  `mem_bytes_at (w2n p + 32) (LENGTH bs) t.vs_memory =
   mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory` by
    (irule mem_bytes_at_translated_window >>
     qexists_tac `val_footprint vt v` >> simp[]) >> simp[]
QED

(* Dynamic source posts provide the exact no-wrap layout used by the
   two-instruction capture; bytes and strings share the same payload. *)
Theorem slice_dynamic_value_capture:
  compile_bytestring_src src sm = ((len,data),sb) /\
  stmt_state_rel ctx func cenv cx es s /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME (BaseTV bt) /\
  expr_val_rel cx (BaseT bt) v src s /\
  expr_val_at cenv cx (BaseT bt) sa sm es v src s /\
  ((bt = BytesT (Dynamic cap) /\ v = BytesV bs) \/
   (?str. bt = StringT cap /\ v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
  (!z. src = Var z ==> not_fresh_at sm z) ==>
  ?t p. run_inst_seq (emitted_insts sm sb) s = OK t /\
    eval_operand len t = SOME (n2w (LENGTH bs)) /\
    eval_operand data t = SOME (n2w (w2n p + 32)) /\
    eval_operand src s = SOME p /\ w2n p + 32 < dimword (:256) /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) t.vs_memory = bs /\
    t = s with vs_vars := t.vs_vars /\
    (!x. not_fresh_at sm x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> fs[expr_val_rel_def] >>
  `~is_word_type (BaseT bt)` by
    (fs[is_word_type_def] >> metis_tac[]) >>
  `w2n w + val_footprint (BaseTV bt) v < dimword (:256)` by
    (irule expr_val_at_bound >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  gs[vyperValueTheory.evaluate_type_def, is_word_type_def,
     valueEncodingDefsTheory.val_in_memory_def, val_footprint_def] >>
  `w2n w + 32 < dimword (:256)` by decide_tac >>
  `mload (w2n w) s = n2w (LENGTH bs)` by
    gvs[mload_def, valueEncodingDefsTheory.mem_word_at_def] >>
  drule slice_bytestring_capture >>
  disch_then (qspecl_then [`s`, `w`, `bs`] mp_tac) >>
  simp[]
QED

(* This boundary deliberately has no nocalls restriction: a later operand
   may make internal calls, provided its usual expression post holds. *)
Theorem slice_dynamic_capture_continue:
  compile_bytestring_src src sm = ((len,data),sb) /\
  stmt_state_rel ctx func cenv cx es s /\ expr_sim_inv cenv cx env es /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME (BaseTV bt) /\
  expr_val_rel cx (BaseT bt) v src s /\
  expr_val_at cenv cx (BaseT bt) sa sm es v src s /\
  ((bt = BytesT (Dynamic cap) /\ v = BytesV bs) \/
   (?str. bt = StringT cap /\ v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
  (!z. src = Var z ==> not_fresh_at sm z) /\ (!l. src <> Label l) /\
  local_ptrs_reserved cenv sm /\
  32 + LENGTH bs <= val_footprint (BaseTV bt) v ==>
  ?t (p:bytes32). run_inst_seq (emitted_insts sm sb) s = OK t /\
    eval_operand len t = SOME (n2w (LENGTH bs)) /\
    eval_operand data t = SOME (n2w (w2n p + 32)) /\
    expr_val_at cenv cx (BaseT bt) sa sb es v src t /\
    eval_operand src t = SOME p /\ w2n p + 32 < dimword (:256) /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) t.vs_memory = bs /\
    t = s with vs_vars := t.vs_vars /\
    (!x. not_fresh_at sm x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x) /\
    (!e sc es' v' op' u.
      expr_post ctx func cenv cx e es sb sc t es' v' op' u ==>
      mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all slice_dynamic_value_capture >> strip_tac >>
  `wb_frame cenv es sm s t` by
    (simp[wb_frame_def] >>
     qpat_assum `t = s with vs_vars := _` SUBST1_TAC >>
     simp[exprSimPropsTheory.locals_kept_mem, lookup_var_def] >> metis_tac[]) >>
  `expr_val_at cenv cx (BaseT bt) sa sb es v src t` by
    (`sm.cs_next_id <= sb.cs_next_id` by
       (drule slice_bytestring_src_shape >> simp[]) >>
     irule log_frame_placement >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  `eval_operand src t = SOME p` by
    (drule_all log_frame_operand >> simp[]) >>
  `~is_word_type (BaseT bt)` by (fs[is_word_type_def] >> metis_tac[]) >>
  qexistsl_tac [`t`, `p`] >> simp[] >> rpt strip_tac >>
  irule slice_payload_after_operand >> goal_assum (drule_at Any) >>
  metis_tac[]
QED
