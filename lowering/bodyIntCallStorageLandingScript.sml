(* Joint counted storage/transient copy at its actual protected landing. *)
Theory bodyIntCallStorageLanding
Ancestors
  bodyIntCallMaterializeLanding storageCopyGasPath exprSimStorageCopy exprSimCopy
  intCallFrame compileEnv finite_map list rich_list words exprSimMemUnwrap
  emitHelperProps venomInst venomState placeMemoryPrimitiveForward exprLoweringProps
  loweringPosts context valueCopy fragGasMode exprSimAlloc

Theorem protected_storage_loop_landing:
  compile_word_copy_loop src dst n loc LocMemory F sa = (result,sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\ fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  n = type_slot_size tv /\ n < 2**256 /\ b+32*n < 2**256 /\
  stmt_state_rel ctx func ce cx es s /\
  storage_holds cx (loc = LocTransient) ty (Value v) a es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ 32*n <= sz /\ allocas_above lo s /\
  (!p k. P p k ==> regions_disjoint p k b (32*n)) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    val_wf tv v /\ val_in_memory tv v b u.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\
    FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    allocas_above lo u /\ copy_static u = copy_static s /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  mp_tac (Q.INST [`sbase` |-> `s`, `u` |-> `result`]
    (SPEC_ALL (SRULE [] (compile_storage_copy_content_capacity_path
      |> Q.SPEC `F`
      |> CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX)))
      |> Q.SPEC `(ctx,func)`)))) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  `copy_static t = copy_static s` by fs[copy_prefix_def] >>
  drule copy_static_fields >> strip_tac >>
  `copy_prefix (if loc = LocTransient then LocTransient else LocStorage)
     a b (type_slot_size tv) s (type_slot_size tv) t` by
    (Cases_on `loc = LocTransient` >> gvs[]) >>
  drule_all copy_buffer_storage_contents >> strip_tac >>
  `!p k. P p k ==> mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory` by
    (rpt strip_tac >> irule copy_prefix_bytes >>
     fs[regions_disjoint_def] >> metis_tac[]) >>
  `!q. reserved q ==> eval_operand q t = eval_operand q s` by
    (rpt strip_tac >> irule storage_copy_operand_preserved >> metis_tac[]) >>
  qexists_tac `t` >> fs[allocas_above_def] >> gvs[]
QED

(* Count the public operational word run; no separate semantic endpoint. *)
Theorem protected_storage_word_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [dst; v] od sa = (result,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  b+32 < 2**256 /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    copy_prefix loc a b 1 s 1 u /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all storage_unwrap_word_run >> strip_tac >>
  drule storage_copy_word_layout >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (fs[same_blocks_def] >>
     `?l. sb.cs_current_insts = sa.cs_current_insts ++ l` by
       metis_tac[IS_PREFIX_APPEND] >>
     gvs[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (gvs[mk_inst_def, is_terminator_def] >> Cases_on `loc = LocStorage` >> simp[]) >>
  `gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >> metis_tac[]) >>
  `~t.vs_halted` by (fs[copy_prefix_def] >> drule copy_static_fields >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[copy_prefix_idx, lookup_var_def]
QED

Theorem protected_storage_word_landing:
  (loc = LocStorage \/ loc = LocTransient) /\
  do value <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [dst; value] od sa = (result,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  type_slot_size tv = 1 /\ b+32 < 2**256 /\
  stmt_state_rel ctx func ce cx es s /\
  storage_holds cx (loc = LocTransient) ty (Value v) a es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ allocas_above lo s /\
  (!p k. P p k ==> regions_disjoint p k b 32) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    val_wf tv v /\ val_in_memory tv v b u.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\
    FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    allocas_above lo u /\ copy_static u = copy_static s /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all protected_storage_word_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `copy_static u = copy_static s` by fs[copy_prefix_def] >>
  drule copy_static_fields >> strip_tac >>
  `copy_prefix (if loc = LocTransient then LocTransient else LocStorage)
     a b (type_slot_size tv) s (type_slot_size tv) u` by
    (Cases_on `loc = LocTransient` >> gvs[]) >>
  drule_all copy_buffer_storage_contents >> strip_tac >>
  `!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory` by
    (rpt strip_tac >> irule copy_prefix_bytes >>
     qexistsl_tac [`a`, `b`, `1`, `loc`, `1`] >>
     fs[regions_disjoint_def]) >>
  `!q. reserved q ==> eval_operand q u = eval_operand q s` by
    (rpt strip_tac >> irule storage_copy_operand_preserved >> metis_tac[]) >>
  qexists_tac `u` >> fs[allocas_above_def] >> gvs[]
QED

Theorem protected_storage_suffix_landing:
  (loc = LocStorage \/ loc = LocTransient) /\
  (if n = 1 then
     do value <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [dst; value] od
   else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
    sa = (result,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  n = type_slot_size tv /\ n < 2**256 /\ b+32*n < 2**256 /\
  stmt_state_rel ctx func ce cx es s /\
  storage_holds cx (loc = LocTransient) ty (Value v) a es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ 32*n <= sz /\ allocas_above lo s /\
  (!p k. P p k ==> regions_disjoint p k b (32*n)) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    val_wf tv v /\ val_in_memory tv v b u.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\
    FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    allocas_above lo u /\ copy_static u = copy_static s /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  Cases_on `n = 1`
  >- (fs[] >> irule protected_storage_word_landing >> simp[] >>
      metis_tac[]) >>
  `?r. compile_word_copy_loop src dst n loc LocMemory F sa = (r,sb)` by
    (qpat_x_assum `_ sa = (result,sb)` mp_tac >>
     simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> simp[]) >>
  drule_all protected_storage_loop_landing >> simp[]
QED

Theorem storage_alloc_materialization_landing:
  compile_alloc_buffer sz sa = (buf,sm) /\
  (if n = 1 then
     do value <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [buf.buf_operand; value] od
   else do compile_word_copy_loop src buf.buf_operand n loc LocMemory F; return () od)
    sm = (result,sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ fresh_vars_wrt sa s /\
  sz < dimword (:256) /\ 32*n <= sz /\ n = type_slot_size tv /\ n < 2**256 /\
  allocas_above lo s /\ copy_old_operand sa src /\ eval_operand src s = SOME a /\
  storage_holds cx (loc = LocTransient) ty (Value v) a es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. P p k ==> p+k <= lo) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx es u /\
    eval_operand buf.buf_operand u = SOME w /\ val_wf tv v /\
    val_in_memory tv v (w2n w) u.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    lo <= w2n w /\ w2n w+sz < dimword (:256) /\ allocas_above lo u /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!q x. (reserved q \/ q = src) /\ q = Var x ==> not_fresh_at sa x` by
    (fs[copy_old_operand_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`reserved` |-> `\q. reserved q \/ q = src`]
    (SPEC_ALL materialization_alloc_landing)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK mid)` >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `local_ptrs_reserved ce sm` by (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
  `!x. src = Var x \/ buf.buf_operand = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> fs[copy_old_operand_def] >>
     gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `storage_holds cx (loc = LocTransient) ty (Value v) a es mid` by
    gvs[storage_holds_def, contract_storage_def, contract_transient_def] >>
  `eval_operand src mid = SOME a /\
   eval_operand buf.buf_operand mid = SOME (n2w (w2n w)) /\
   w2n w+32*n < 2**256` by (fs[dimword_def] >> metis_tac[]) >>
  `!q x. (reserved q \/ q = buf.buf_operand) /\ q = Var x ==>
     not_fresh_at sm x` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  mp_tac (Q.INST [`s` |-> `mid`, `sa` |-> `sm`, `b` |-> `w2n (w:bytes32)`,
      `dst` |-> `buf.buf_operand`, `aid` |-> `sa.cs_next_id`,
      `P` |-> `\p k. regions_disjoint p k (w2n (w:bytes32)) (32*n)`,
      `reserved` |-> `\q. reserved q \/ q = buf.buf_operand`]
    (SPEC_ALL protected_storage_suffix_landing)) >>
  (impl_tac >- (simp[] >> gvs[] >> metis_tac[])) >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  `stmt_state_rel ctx func ce cx es u` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl_tac [`w2n w`,
       `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
          [STRING #"%" (toString sa.cs_next_var)]`, `mid`, `sm`, `sz`] >>
     simp[mk_inst_def] >> gvs[regions_disjoint_def] >>
     rpt strip_tac >> first_assum irule >> fs[] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_LESS_EQ_MONO]) >>
  `gas_marked_path F ctx func s 0 (OK u)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexistsl_tac [`u`, `w`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  qx_gen_tac `protected_addr` >> qx_gen_tac `protected_len` >> strip_tac >>
  `protected_addr + protected_len <= lo` by metis_tac[] >>
  `regions_disjoint protected_addr protected_len (w2n w) (32*n)` by
    (simp[regions_disjoint_def] >> decide_tac) >>
  metis_tac[]
QED
