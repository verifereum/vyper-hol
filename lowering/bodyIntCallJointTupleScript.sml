Theory bodyIntCallJointTuple
Ancestors
  bodyIntCallJointWrite exprLowering context compileEnv emitHelperProps
  fragGasSeq fragGasPath list rich_list vyperAST exprCallBounds
  exprLoweringProps fragExec venomInst venomInstProofs venomExecSemantics
  emitHelper venomState

(* Isolate the actual singleton compiler before its execution proof. *)
Theorem joint_singleton_tuple_compile:
  compile_alloc_buffer (type_memory_bytes ce (expr_type e)) sa = (buf,sm) /\
  compile_expr ce (expr_type e) e sm = (StackValue et src,sn) /\
  emit_op ADD [buf.buf_operand; Lit 0w] sn = (dst,sp) /\
  compile_store_memory ce src dst (expr_type e) (lowered_value_type ce e) sp =
    ((),sb) ==>
  compile_expr ce ty (Builtin ann (MakeArray NONE bnd) [e]) sa =
    (LocatedValue ann (mk_ptr buf.buf_operand LocMemory),sb)
Proof
  strip_tac >> Cases_on `e` >>
  once_rewrite_tac[compile_expr_raw_def] >>
  simp[compile_expr_body_def, builtin_child_callback_def,
       expr_builtin_dispatch_bound, expr_type_def] >>
  once_rewrite_tac[compile_expr_raw_def] >>
  simp[compile_builtin_dispatch_body_def, as_ptr_val_def] >>
  simp[compile_make_tuple_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, unwrap_value_def, as_ptr_val_def]
QED

(* The allocation prefix contributes no gas reads, at its actual endpoint. *)
Theorem joint_tuple_alloc_prefix_path:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sm) s = OK t ==>
  gas_path ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sm.cs_current_insts)) /\
  sm.cs_current_bb = sa.cs_current_bb
Proof
  strip_tac >>
  `?op. emit_op ALLOCA [Lit (n2w sz)] sa = (op,sm)` by
    (gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sm)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all tuple_run_inst_seq_gas_path >> simp[mk_inst_def]
QED

(* Exit propagation does not impose a successful-value frame on the child. *)
Theorem joint_singleton_tuple_exit_path:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ sz < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (~?u. r = OK u) /\
  (!t. run_inst_seq (emitted_insts sa sm) s = OK t ==>
    gas_path ctx func (t with vs_inst_idx := LENGTH sm.cs_current_insts) n r) ==>
  gas_path ctx func s n r
Proof
  strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all exprSimAllocTheory.literal_alloc_buffer_run >> strip_tac >>
  drule_all joint_tuple_alloc_prefix_path >> strip_tac >>
  qpat_x_assum `!t. run_inst_seq _ _ = _ ==> _` drule >> strip_tac >>
  qpat_x_assum `!ctx. _` (qspec_then `ctx` strip_assume_tac) >>
  drule_all gas_path_then >> simp[]
QED

(* The real singleton suffix is ADD followed by the word store. *)
Theorem joint_tuple_word_suffix_run:
  emit_op ADD [pop; Lit 0w] sn = (dst,sp) /\
  compile_store_memory ce src dst ty sty sp = ((),sb) /\
  is_word_type ty /\ eval_operand pop s = SOME p /\
  eval_operand src s = SOME w /\
  (!x. src = Var x ==> x <> STRING #"%" (toString sn.cs_next_var)) ==>
  run_inst_seq (emitted_insts sn sb) s =
    OK (mstore (w2n p) w
      (update_var (STRING #"%" (toString sn.cs_next_var)) p s)) /\
  sb.cs_current_bb = sn.cs_current_bb /\
  sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> GAS) (emitted_insts sn sb)
Proof
  strip_tac >>
  `eval_operand src
    (update_var (STRING #"%" (toString sn.cs_next_var)) p s) = SOME w` by
    (irule eval_operand_update_other_local >> simp[] >> metis_tac[]) >>
  gvs[compile_store_memory_def] >>
  gvs[emit_op_def, fresh_var_def, fresh_id_def, emit_void_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_def, mk_inst_def, is_terminator_def] >>
  simp[step_inst_base_opcode_eqs, exec_read1_def, exec_write2_def, eval_operand_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def,
       exec_pure2_def] >>
  gvs[update_var_def, eval_operand_def, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE, wordsTheory.WORD_ADD_0]
QED

Theorem joint_tuple_word_suffix_path:
  emit_op ADD [pop; Lit 0w] sn = (dst,sp) /\
  compile_store_memory ce src dst ty sty sp = ((),sb) /\
  is_word_type ty /\ eval_operand pop s = SOME p /\
  eval_operand src s = SOME w /\
  (!x. src = Var x ==> x <> STRING #"%" (toString sn.cs_next_var)) /\
  fn_has_code sn sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  gas_path ctx func s 0
    (OK ((mstore (w2n p) w
      (update_var (STRING #"%" (toString sn.cs_next_var)) p s))
      with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule_all joint_tuple_word_suffix_run >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sn sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sn sb)` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sn sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all tuple_run_inst_seq_gas_path >> simp[]
QED

(* Assignment of the generated address temporary is invisible to live regions. *)
Theorem joint_tuple_local_region_update:
  not_local_ptr ce scopes x ==>
  (local_region ce scopes (update_var x w s) name b sz <=>
   local_region ce scopes s name b sz)
Proof
  simp[not_local_ptr_def, local_region_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> eq_tac >> strip_tac >>
  qexistsl_tac [`entry`, `p`, `w'`] >> gvs[] >> metis_tac[]
QED

Theorem joint_tuple_word_suffix_frame:
  stmt_state_rel ctx func ce cx es s /\ not_local_ptr ce es.scopes x /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\ 32 <= sz /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
     regions_disjoint b sz lb len) /\
  EVERY (\(off,len). regions_disjoint b sz off len) hs ==>
  stmt_state_rel ctx func ce cx es
    ((mstore b w (update_var x p s)) with vs_inst_idx := ix) /\
  EVERY (\(off,len).
    mem_bytes_at off len
      ((mstore b w (update_var x p s)) with vs_inst_idx := ix).vs_memory =
    mem_bytes_at off len s.vs_memory) hs /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
      NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms)
      name = SOME (tv,v) ==>
    mem_bytes_at off (type_memory_size tv)
      ((mstore b w (update_var x p s)) with vs_inst_idx := ix).vs_memory =
    mem_bytes_at off (type_memory_size tv) s.vs_memory)
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx es (update_var x p s)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  `FLOOKUP (update_var x p s).vs_allocas inst.inst_id = SOME (b,sz)` by
    simp[update_var_def] >>
  `!name lb len. local_region ce es.scopes (update_var x p s) name lb len ==>
     regions_disjoint b sz lb len` by
    (simp[joint_tuple_local_region_update] >> metis_tac[]) >>
  `b <= b /\ b + 32 <= b + sz` by decide_tac >>
  drule_all joint_alloca_write_frame >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  simp[stmt_state_rel_inst_idx, update_var_def] >>
  gvs[update_var_def] >> first_assum ACCEPT_TAC
QED

(* The supplied child producer runs at the allocation's actual endpoint.
   Its allocation, local-separation and protected-window clauses are stronger
   than the existing unframed body_expr_ok judgment. This bounded composition
   does not identify the child's pointer with the allocation endpoint's pointer,
   prove final operand liveness, or frame constructor capacities from entry.
   Such capacities can be included in hs only with the stated child clauses;
   the suffix frame above separately preserves them from the child endpoint. *)
Theorem joint_singleton_tuple_path:
  compile_alloc_buffer (type_memory_bytes ce (expr_type e)) sa = (buf,sm) /\
  compile_expr ce (expr_type e) e sm = (StackValue et src,sn) /\
  emit_op ADD [buf.buf_operand; Lit 0w] sn = (dst,sp) /\
  compile_store_memory ce src dst (expr_type e) (lowered_value_type ce e) sp =
    ((),sb) /\ is_word_type (expr_type e) /\
  fn_has_code sa sm func /\ fn_has_code sn sb func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  32 <= type_memory_bytes ce (expr_type e) /\
  type_memory_bytes ce (expr_type e) < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!t. run_inst_seq (emitted_insts sa sm) s = OK t ==>
    ?u p.
      gas_path ctx func (t with vs_inst_idx := LENGTH sm.cs_current_insts)
        n (OK u) /\
      ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
      u.vs_inst_idx = LENGTH sn.cs_current_insts /\
      eval_operand buf.buf_operand u = SOME p /\
      eval_operand src u = SOME w /\
      (!x. src = Var x ==> x <> STRING #"%" (toString sn.cs_next_var)) /\
      not_local_ptr ce es'.scopes (STRING #"%" (toString sn.cs_next_var)) /\
      stmt_state_rel ctx func ce cx es' u /\
      FLOOKUP u.vs_allocas sa.cs_next_id =
        SOME (w2n p,type_memory_bytes ce (expr_type e)) /\
      (!name lb len. local_region ce es'.scopes u name lb len ==>
        regions_disjoint (w2n p) (type_memory_bytes ce (expr_type e)) lb len) /\
      EVERY (\(off,len).
        regions_disjoint (w2n p) (type_memory_bytes ce (expr_type e)) off len /\
        mem_bytes_at off len u.vs_memory = mem_bytes_at off len s.vs_memory) hs) ==>
  compile_expr ce ty (Builtin ann (MakeArray NONE bnd) [e]) sa =
    (LocatedValue ann (mk_ptr buf.buf_operand LocMemory),sb) /\
  ?u p.
    gas_path ctx func s n
      (OK ((mstore (w2n p) w
        (update_var (STRING #"%" (toString sn.cs_next_var)) p u))
        with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    stmt_state_rel ctx func ce cx es'
      ((mstore (w2n p) w
        (update_var (STRING #"%" (toString sn.cs_next_var)) p u))
        with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    EVERY (\(off,len).
      mem_bytes_at off len
        (mstore (w2n p) w
          (update_var (STRING #"%" (toString sn.cs_next_var)) p u)).vs_memory =
      mem_bytes_at off len s.vs_memory) hs
Proof
  strip_tac >> conj_tac
  >- (irule joint_singleton_tuple_compile >> metis_tac[]) >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all exprSimAllocTheory.literal_alloc_buffer_run >> strip_tac >>
  qpat_x_assum `!t. run_inst_seq _ _ = _ ==> _` drule >> strip_tac >>
  rename1 `eval_operand buf.buf_operand u = SOME wp` >>
  `EVERY (\(off,len).
     regions_disjoint (w2n wp) (type_memory_bytes ce (expr_type e)) off len) hs`
    by (gvs[EVERY_MEM] >> rpt strip_tac >> PairCases_on `e'` >>
        qpat_x_assum `!e'. MEM e' hs ==> _` drule >> simp[]) >>
  drule_all joint_tuple_alloc_prefix_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all joint_tuple_word_suffix_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `gas_path ctx func s n (OK u)` by
    (drule_all gas_path_then >> simp[]) >>
  `gas_path ctx func s n
    (OK ((mstore (w2n wp) w
      (update_var (STRING #"%" (toString sn.cs_next_var)) wp u))
      with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_all gas_path_then >> simp[]) >>
  ` (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce (expr_type e)))]
       [STRING #"%" (toString sa.cs_next_var)]).inst_opcode = ALLOCA` by
    simp[mk_inst_def] >>
  `FLOOKUP u.vs_allocas
    (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce (expr_type e)))]
       [STRING #"%" (toString sa.cs_next_var)]).inst_id =
     SOME (w2n wp,type_memory_bytes ce (expr_type e))` by simp[mk_inst_def] >>
  drule_all joint_tuple_word_suffix_frame >>
  disch_then (qspecl_then [`w`, `wp`, `LENGTH sb.cs_current_insts`]
    strip_assume_tac) >>
  qexistsl_tac [`u`, `wp`] >> simp[] >>
  qpat_x_assum `EVERY (\(off,len). _ /\ _) hs` mp_tac >>
  qpat_x_assum `EVERY (\(off,len). mem_bytes_at _ _ _ = _) hs` mp_tac >>
  rpt (first_x_assum kall_tac) >>
  simp[EVERY_MEM] >> rpt strip_tac >> PairCases_on `e'` >>
  rpt (first_x_assum drule) >> simp[]
QED
