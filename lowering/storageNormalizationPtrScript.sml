(* Semantic resources at the actual checked storage-normalization endpoint. *)
Theory storageNormalizationPtr
Ancestors
  storageNormalizationBranchPtr storageUnwrapSizingPtr storageLocatedResourcesPtr
  storageCopyContentsPtr storageCopyRepresentationPtr bodyPtrDefs exprSimProps
  exprSimStorageCopy venomState ptrDiscipline words arithmetic
  reasonStoragePrefixPtr reasonPrefixPtr ghostPcTransportPtr allocationPtr
  exprSimAlloc exprLoweringProps loweringHalt venomExecSemantics venomInstProofs
  context emitHelper compileEnv venomInst loweringPosts fragGasPathPtr

Theorem storage_normalization_endpoint_resources:
  stmt_state_rel ctx func cenv cx es u /\
  ptr_vv_ok cx ty tv (LocatedValue ann p) es G tn u /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  eval_operand p.ptr_operand u = SOME a /\
  storage_holds cx tr ty tv a es u /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT max)) /\
  read_result cx tv es = (INL (StringV str),es) /\
  n = type_slot_size (BaseTV (StringT max)) /\
  copy_prefix p.ptr_location a b n u n z /\
  ptr_covers Gf tnf root z (32*n) /\
  lookup_var root z = SOME (n2w b) /\ b < dimword(:256) /\
  tnf.t_mem = (tn.t_mem DIFF {x | b <= x /\ x < b+32*n}) UNION
    {b+32*i+r | i < n /\ r < 32 /\
      (a+n2w i,r) IN (if tr then tn.t_trans else tn.t_stor)} ==>
  val_wf (BaseTV (StringT max)) (StringV str) /\
  ptr_mem_ok cx ty (StringV str) (Var root) Gf tnf z /\
  ptr_covers Gf tnf root z (32+32*word_size (LENGTH str)) /\
  val_store_size (BaseTV (StringT max)) (StringV str) =
    32+32*word_size (LENGTH str)
Proof
  strip_tac >>
  drule_all located_storage_string_source_resources >> strip_tac >>
  `copy_prefix (if tr then LocTransient else LocStorage) a b
     (type_slot_size (BaseTV (StringT max))) u
     (type_slot_size (BaseTV (StringT max))) z` by metis_tac[] >>
  drule_all completed_storage_copy_contents >> strip_tac >>
  drule_all storage_string_runtime_copy_capacity >> strip_tac >>
  `!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
     val_in_memory (BaseTV (StringT max)) (StringV str) b mem` by
    (gen_tac >> strip_tac >> irule copied_storage_string_robust_memory >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`tn.t_mem`, `if tr then tn.t_trans else tn.t_stor`, `a`,
       `z.vs_memory`, `n`, `if tr then contract_transient u else contract_storage u`] >>
     simp[] >>
     qpat_x_assum `mem_agree_outside tnf.t_mem _ _` mp_tac >>
     qpat_x_assum `tnf.t_mem = _` (fn th => pure_rewrite_tac[th]) >>
     simp[GSYM ADD_ASSOC]) >>
  simp[val_store_size_def] >> conj_tac
  >- (simp[ptr_mem_ok_def, eval_operand_def] >>
      qpat_x_assum `ptr_covers Gf tnf root z _` mp_tac >>
      simp[ptr_covers_def, eval_operand_def] >> rpt strip_tac >>
      goal_assum (drule_at Any) >> simp[val_store_size_def] >> decide_tac) >>
  qpat_x_assum `ptr_covers Gf tnf root z _` mp_tac >>
  simp[ptr_covers_def] >> rpt strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

(* Both compiler branches expose identical suffix resources, at their own
   checked endpoint rather than at a separately chosen ordinary run. *)
Theorem compile_storage_normalization_resources_path_ptr:
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  (if n = 1 then
     do v <- emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD)
               [p.ptr_operand]; emit_void MSTORE [Var root;v] od
   else do compile_word_copy_loop p.ptr_operand (Var root) n p.ptr_location LocMemory F;
           return () od) sa = (result,sb) /\
  fn_has_code sa sb func /\
  (!x. p.ptr_operand = Var x \/ root = x ==> not_fresh_at sa x) /\
  eval_operand p.ptr_operand u = SOME a /\ lookup_var root u = SOME (n2w b) /\
  op_taint tn p.ptr_operand = {} /\ ptr_covers G tn root u (32*n) /\
  n < dimword(:256) /\ b+32*n < dimword(:256) /\
  ~u.vs_halted /\ ~ctx_has_dalloca ctx /\
  u.vs_current_bb = sa.cs_current_bb /\ u.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es u /\ local_ptrs_reserved cenv sa /\
  MEM (mk_inst aid ALLOCA operands outputs) (fn_insts func) /\
  FLOOKUP u.vs_allocas aid = SOME (b,32*n) /\
  (!name lb len. local_region cenv es.scopes u name lb len ==>
    regions_disjoint b (32*n) lb len) /\
  ptr_vv_ok cx ty tv (LocatedValue ann p) es G tn u /\
  storage_holds cx tr ty tv a es u /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT max)) /\
  read_result cx tv es = (INL (StringV str),es) /\
  n = type_slot_size (BaseTV (StringT max)) ==>
  ?Gf tnf z.
    gas_path_ptr D 0 ctx func PG G tn u 0 Gf tnf (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~z.vs_halted /\
    stmt_state_rel ctx func cenv cx es z /\ z.vs_allocas = u.vs_allocas /\
    lookup_var root z = SOME (n2w b) /\
    ptr_mem_ok cx ty (StringV str) (Var root) Gf tnf z /\
    val_wf (BaseTV (StringT max)) (StringV str) /\
    ptr_covers Gf tnf root z (32+32*word_size (LENGTH str)) /\
    val_store_size (BaseTV (StringT max)) (StringV str) =
      32+32*word_size (LENGTH str) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x z = lookup_var x u /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!old sz. not_fresh_at sa old /\ ptr_covers G tn old u sz ==>
      ptr_covers Gf tnf old z sz)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `tr` >> gvs[] >>
  `type_slot_size (BaseTV (StringT max)) < dimword(:256)` by decide_tac >>
  FIRST [drule_all (Q.INST [`loc` |-> `LocTransient`]
           compile_storage_normalization_branch_path_ptr |> SRULE []),
         drule_all (Q.INST [`loc` |-> `LocStorage`]
           compile_storage_normalization_branch_path_ptr |> SRULE [])] >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `not_fresh_at sa root` by metis_tac[] >>
  `lookup_var root t = SOME (n2w b)` by metis_tac[] >>
  `stmt_state_rel ctx func cenv cx es t /\ t.vs_allocas = u.vs_allocas` by
    (first_x_assum (qspecl_then [`cenv`, `cx`, `es`, `mk_inst aid ALLOCA operands outputs`] mp_tac) >>
     simp[mk_inst_def] >> impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  `b < dimword(:256)` by decide_tac >>
  `copy_prefix p.ptr_location a b (type_slot_size (BaseTV (StringT max))) u
     (type_slot_size (BaseTV (StringT max))) t` by simp[] >>
  FIRST [drule_all (Q.INST [`tr` |-> `T`,
      `n` |-> `type_slot_size (BaseTV (StringT max))`]
      storage_normalization_endpoint_resources |> SRULE []),
    drule_all (Q.INST [`tr` |-> `F`,
      `n` |-> `type_slot_size (BaseTV (StringT max))`]
      storage_normalization_endpoint_resources |> SRULE [])] >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> simp[] >>
  qpat_x_assum `ptr_covers G' tn' root t (32 + _)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV arithmeticTheory.ADD_COMM))) >>
  rewrite_tac[]
QED

(* ALLOCA resources at the counted-path cursor, ready for either copy branch. *)
Theorem storage_normalization_alloc_path_ptr:
  stmt_state_rel ctx func cenv cx es s /\
  compile_alloc_buffer n cc = (buf,cd) /\ fn_has_code cc cd func /\
  local_ptrs_reserved cenv cc /\ fn_inst_ids_distinct func /\
  n < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = cc.cs_current_bb /\
  s.vs_inst_idx = LENGTH cc.cs_current_insts /\ ~s.vs_halted /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at cc x) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ptr_vv_ok cx ty tv (LocatedValue ann p) es G tn s ==>
  ?u root b G1 tn1.
    buf.buf_operand = Var root /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK u) /\
    u.vs_current_bb = cd.cs_current_bb /\
    u.vs_inst_idx = LENGTH cd.cs_current_insts /\ ~u.vs_halted /\
    stmt_state_rel ctx func cenv cx es u /\ local_ptrs_reserved cenv cd /\
    FLOOKUP u.vs_allocas cc.cs_next_id = SOME (b,n) /\
    b+n < dimword(:256) /\ lookup_var root u = SOME (n2w b) /\
    ptr_covers G1 tn1 root u n /\
    eval_operand p.ptr_operand u = eval_operand p.ptr_operand s /\
    ptr_vv_ok cx ty tv (LocatedValue ann p) es G1 tn1 u /\
    (!tr sty stv a. storage_holds cx tr sty stv a es s ==>
      storage_holds cx tr sty stv a es u) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!name lb len. local_region cenv es.scopes u name lb len ==>
      regions_disjoint b n lb len) /\
    MEM (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func) /\
    not_local_ptr cenv es.scopes root /\
    (!old. not_fresh_at cc old ==>
      lookup_var old u = lookup_var old s /\ FLOOKUP G1 old = FLOOKUP G old /\
      op_taint tn1 (Var old) = op_taint tn (Var old)) /\
    (!old k. not_fresh_at cc old /\ ptr_covers G tn old s k ==>
      ptr_covers G1 tn1 old u k)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all reason_storage_alloc_buffer_resources >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all reason_encoder_alloc_path_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] assume_tac) >>
  `cd.cs_current_bb = cc.cs_current_bb /\
   LENGTH cd.cs_current_insts = SUC (LENGTH cc.cs_current_insts)` by
    (qpat_x_assum `compile_alloc_buffer n cc = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_halted = s.vs_halted` by
    suspend "control" >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1
     (OK (s1 with vs_inst_idx := SUC (LENGTH cc.cs_current_insts)))` by metis_tac[] >>
  qexistsl_tac [`s1 with vs_inst_idx := SUC s.vs_inst_idx`, `out`,
    `w2n w`, `G1`, `tn1`] >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- metis_tac[]
  >- gvs[eval_operand_def, lookup_var_def]
  >- suspend "source" >- suspend "holds" >- suspend "locals" >>
  suspend "old"
QED

Resume storage_normalization_alloc_path_ptr[control]:
  `step_inst 0 ctx (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK s1` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  conj_tac
  >- (drule step_preserves_control_flow >> simp[mk_inst_def, is_terminator_def]) >>
  drule step_preserves_halted >> simp[mk_inst_def, is_terminator_def]
QED

Resume storage_normalization_alloc_path_ptr[source]:
  qpat_x_assum `ptr_vv_ok _ _ _ _ _ G1 tn1 s1` mp_tac >>
  asm_rewrite_tac[] >> POP_ASSUM_LIST (K all_tac) >>
  simp[ptr_vv_ok_def, ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def, lookup_var_def]
QED

Resume storage_normalization_alloc_path_ptr[holds]:
  rpt strip_tac >>
  `storage_holds cx tr sty stv a es s1` by metis_tac[] >>
  pop_assum mp_tac >> POP_ASSUM_LIST (K all_tac) >>
  simp[storage_holds_def, contract_storage_def, contract_transient_def]
QED

Resume storage_normalization_alloc_path_ptr[locals]:
  qpat_x_assum `!name b len. local_region _ _ s1 _ _ _ ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[local_region_def, lookup_var_def]
QED

Resume storage_normalization_alloc_path_ptr[old]:
  rpt strip_tac >>
  `old <> out` by
    (drule compile_alloc_buffer_parts >> strip_tac >> gvs[not_fresh_at_def] >> metis_tac[]) >>
  `eval_operand (Var old) s1 = eval_operand (Var old) s` by
    (irule alloca_step_operand_preserved >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[eval_operand_def, lookup_var_def]
QED

Finalise storage_normalization_alloc_path_ptr

Theorem storage_normalization_alloc_copy_path_ptr:
  compile_alloc_buffer (32*n) cc = (buf,ca) /\ buf.buf_operand = Var root /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  (if n = 1 then
     do v <- emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD)
               [p.ptr_operand]; emit_void MSTORE [Var root;v] od
   else do compile_word_copy_loop p.ptr_operand (Var root) n p.ptr_location LocMemory F;
           return () od) ca = (result,cb) /\
  fn_has_code cc ca func /\ fn_has_code ca cb func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv cc /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  32*n < dimword(:256) /\ n < dimword(:256) /\
  s.vs_current_bb = cc.cs_current_bb /\
  s.vs_inst_idx = LENGTH cc.cs_current_insts /\ ~s.vs_halted /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at cc x) /\
  ptr_vv_ok cx ty tv (LocatedValue ann p) es G tn s /\
  eval_operand p.ptr_operand s = SOME a /\ storage_holds cx tr ty tv a es s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT max)) /\
  read_result cx tv es = (INL (StringV str),es) /\
  n = type_slot_size (BaseTV (StringT max)) ==>
  ?Gf tnf z b.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK z) /\
    z.vs_current_bb = cb.cs_current_bb /\
    z.vs_inst_idx = LENGTH cb.cs_current_insts /\ ~z.vs_halted /\
    stmt_state_rel ctx func cenv cx es z /\
    lookup_var root z = SOME (n2w b) /\
    ptr_mem_ok cx ty (StringV str) (Var root) Gf tnf z /\
    val_wf (BaseTV (StringT max)) (StringV str) /\
    ptr_covers Gf tnf root z (32+32*word_size (LENGTH str)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP z.vs_allocas aid = SOME entry) /\
    (!old. not_fresh_at cc old ==>
      lookup_var old z = lookup_var old s /\ FLOOKUP Gf old = FLOOKUP G old /\
      op_taint tnf (Var old) = op_taint tn (Var old)) /\
    (!old k. not_fresh_at cc old /\ ptr_covers G tn old s k ==>
      ptr_covers Gf tnf old z k)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Q.SUBGOAL_THEN `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient`
    assume_tac >- (Cases_on `tr` >> gvs[]) >>
  drule_all storage_normalization_alloc_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `root' = root` by metis_tac[operand_11] >>
  qpat_x_assum `root' = root` SUBST_ALL_TAC >>
  `(!x. p.ptr_operand = Var x \/ root = x ==> not_fresh_at ca x)` by
    suspend "fresh" >>
  `eval_operand p.ptr_operand u = SOME a /\ storage_holds cx tr ty tv a es u` by metis_tac[] >>
  `op_taint tn1 p.ptr_operand = {}` by
    (qpat_x_assum `ptr_vv_ok _ _ _ _ _ G1 tn1 u` mp_tac >> simp[ptr_vv_ok_def]) >>
  drule_all compile_storage_normalization_resources_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `z`, `b`] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- suspend "path" >- suspend "old" >> suspend "covers"
QED

Resume storage_normalization_alloc_copy_path_ptr[fresh]:
  drule compile_alloc_buffer_parts >> strip_tac >>
  map_every (fn q => qpat_assum q mp_tac)
    [`buf.buf_operand = Var root`, `buf.buf_operand = Var (STRING _ _)`,
     `!y. not_fresh_at cc y ==> not_fresh_at ca y`,
     `not_fresh_at ca (STRING _ _)`,
     `!x. p.ptr_operand = Var x ==> not_fresh_at cc x`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Resume storage_normalization_alloc_copy_path_ptr[path]:
  qpat_x_assum `gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK u)` mp_tac >>
  qpat_x_assum `gas_path_ptr D 0 ctx func PG G1 tn1 u 0 Gf tnf (OK z)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_path_ptr_then, ADD_CLAUSES]
QED

Resume storage_normalization_alloc_copy_path_ptr[old]:
  rpt strip_tac >>
  `not_fresh_at ca old` by
    (drule compile_alloc_buffer_parts >> strip_tac >> metis_tac[]) >>
  metis_tac[]
QED

Resume storage_normalization_alloc_copy_path_ptr[covers]:
  rpt strip_tac >>
  `not_fresh_at ca old` by
    (drule compile_alloc_buffer_parts >> strip_tac >> metis_tac[]) >>
  metis_tac[]
QED

Finalise storage_normalization_alloc_copy_path_ptr

(* Expose only the two compiler phases of actual located unwrap. *)
Theorem storage_unwrap_compile_parts:
  vv_holds cenv cx ty tv (LocatedValue ann p) es s /\
  ~is_word_type ty /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  type_memory_bytes cenv ann = 32*n /\
  (type_memory_bytes cenv ann+31) DIV 32 = n /\
  unwrap_value cenv (LocatedValue ann p) cc = (op,cb) ==>
  ?buf ca root result.
    compile_alloc_buffer (32*n) cc = (buf,ca) /\
    buf.buf_operand = Var root /\ op = Var root /\
    (if n = 1 then
       do v <- emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD)
                 [p.ptr_operand]; emit_void MSTORE [Var root;v] od
     else do compile_word_copy_loop p.ptr_operand (Var root) n p.ptr_location LocMemory F;
             return () od) ca = (result,cb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all located_storage_unwrap_layout >> disch_tac >>
  qpat_x_assum `unwrap_value _ _ cc = _` mp_tac >>
  asm_rewrite_tac[] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `_ = (op,cb)` mp_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
