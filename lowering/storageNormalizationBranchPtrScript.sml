(* The actual singleton/loop storage normalization suffix, shared by reasons. *)
Theory storageNormalizationBranchPtr
Ancestors
  storageSingleWordPtr storageNormalizationCopyPtr exprSimStorageCopy
  fragGasPathPtr bodyPtrDefs compileEnv exprLoweringProps context
  ptrDiscipline ptrSafeRun venomState finite_map pred_set words
  emitHelper storageNormalizationOwnershipPtr

Theorem compile_storage_normalization_branch_path_ptr:
  (loc = LocStorage \/ loc = LocTransient) /\
  (if n = 1 then
     do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [Var root;v] od
   else do compile_word_copy_loop src (Var root) n loc LocMemory F;
           return () od) sa = (result,sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ root = x ==> not_fresh_at sa x) /\
  eval_operand src sbase = SOME a /\ lookup_var root sbase = SOME (n2w b) /\
  op_taint tn src = {} /\ ptr_covers G tn root sbase (32*n) /\
  n < dimword(:256) /\ b+32*n < dimword(:256) /\
  ~sbase.vs_halted /\ ~ctx_has_dalloca ctx /\
  sbase.vs_current_bb = sa.cs_current_bb /\
  sbase.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn sbase 0 G' tn' (OK t) /\
    copy_prefix loc a b n sbase n t /\ ptr_covers G' tn' root t (32*n) /\
    copy_static t = copy_static sbase /\
    LENGTH sbase.vs_memory <= LENGTH t.vs_memory /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    tn'.t_mem = (tn.t_mem DIFF {x | b <= x /\ x < b+32*n}) UNION
      {b+32*i+r | i < n /\ r < 32 /\
        (a+n2w i,r) IN (if loc = LocStorage then tn.t_stor else tn.t_trans)} /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x sbase /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    (!p sz. not_fresh_at sa p /\ ptr_covers G tn p sbase sz ==>
      ptr_covers G' tn' p t sz) /\
    (!off len. off+len <= b \/ b+32*n <= off ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len sbase.vs_memory) /\
    (!x. ~(b <= x /\ x < b+32*n) ==>
      (x IN tn'.t_mem <=> x IN tn.t_mem)) /\
    (!cenv cx es inst.
      stmt_state_rel ctx fn cenv cx es sbase /\ local_ptrs_reserved cenv sa /\
      MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
      FLOOKUP sbase.vs_allocas inst.inst_id = SOME (b,32*n) /\
      (!name lb len. local_region cenv es.scopes sbase name lb len ==>
        regions_disjoint b (32*n) lb len) ==>
      stmt_state_rel ctx fn cenv cx es t /\ t.vs_allocas = sbase.vs_allocas /\
      (!tr ty tv w. storage_holds cx tr ty tv w es sbase ==>
        storage_holds cx tr ty tv w es t) /\
      (!aid off len. aid <> inst.inst_id /\
        FLOOKUP sbase.vs_allocas aid = SOME (off,len) ==>
        mem_bytes_at off len t.vs_memory = mem_bytes_at off len sbase.vs_memory))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `n = 1` >- suspend "singleton" >>
  qpat_x_assum `(if _ then _ else _) sa = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [] >> disch_then SUBST_ALL_TAC >>
  drule_all compile_storage_copy_framed_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `copy_static t = copy_static sbase` by
    (qpat_assum `copy_prefix _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[copy_prefix_def]) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >>
  simp_tac (srw_ss()) [arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM] >>
  rule_assum_tac (SIMP_RULE (srw_ss()) [arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, suspend "ownership_loop"]
QED

Resume compile_storage_normalization_branch_path_ptr[singleton]:
  qpat_x_assum `n = 1` SUBST_ALL_TAC >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >> simp[] >>
  `not_fresh_at sa root` by metis_tac[] >>
  `!X : (bytes32 # num) set.
    {b+32*i+r | i < 1 /\ r < 32 /\ (a+n2w i,r) IN X} =
    {b+r | r < 32 /\ (a,r) IN X}` by
    (`!i:num. i < 1 <=> i = 0` by decide_tac >> simp[EXTENSION, wordsTheory.WORD_ADD_0]) >>
  Cases_on `loc = LocStorage`
  >- (gvs[] >>
      `not_fresh_at sa root` by metis_tac[] >>
      drule_all (SRULE [] (Q.INST [`tr` |-> `F`] compile_storage_single_word_path_ptr)) >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      qexistsl_tac [`G'`, `tn'`, `t`] >>
      simp_tac (srw_ss()) [arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM] >>
      rule_assum_tac (SIMP_RULE (srw_ss()) [arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
      rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, suspend "ownership_single"]) >>
  gvs[] >>
  `not_fresh_at sa root` by metis_tac[] >>
  drule_all (SRULE [] (Q.INST [`tr` |-> `T`] compile_storage_single_word_path_ptr)) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >>
      simp_tac (srw_ss()) [arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM] >>
      rule_assum_tac (SIMP_RULE (srw_ss()) [arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
      rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, suspend "ownership_single"]
QED

Resume compile_storage_normalization_branch_path_ptr[ownership_loop]:
  rpt gen_tac >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sbase` by metis_tac[] >>
  drule_all (SRULE [arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]
    normalization_copy_ownership_frame) >> simp[]
QED

Resume compile_storage_normalization_branch_path_ptr[ownership_single]:
  markerLib.RESUME_TAC >> rpt gen_tac >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sbase` by metis_tac[] >>
  drule_all (SRULE [arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]
    normalization_copy_ownership_frame) >> simp[]
QED

Finalise compile_storage_normalization_branch_path_ptr
