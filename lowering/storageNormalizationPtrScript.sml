(* Semantic resources at the actual checked storage-normalization endpoint. *)
Theory storageNormalizationPtr
Ancestors
  storageNormalizationBranchPtr storageUnwrapSizingPtr storageLocatedResourcesPtr
  storageCopyContentsPtr storageCopyRepresentationPtr bodyPtrDefs exprSimProps
  exprSimStorageCopy venomState ptrDiscipline words arithmetic

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
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (b,32*n) /\
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
    (first_x_assum (qspecl_then [`cenv`, `cx`, `es`, `inst`] mp_tac) >>
     simp[] >> impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
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
