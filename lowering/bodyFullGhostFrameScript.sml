(*
 * The pointer ghost invariant at any dead mask and bound survives a step
 * that leaves memory, allocations, storage, transient storage, the
 * immutables and every reserved variable alone: the (D, lo) twin of
 * bodyPtrHashBuiltinsGhostFrame's hash_ghost_inv_exterior_frame, for
 * steps that write no memory.
 *
 * TOP-LEVEL:
 *   ghost_inv_at_exterior_frame
 *)
Theory bodyFullGhostFrame
Ancestors
  bodyPtrDefs loweringStateRelDefs ptrDiscipline venomState

Theorem ghost_inv_at_exterior_frame:
  !D lo d cenv cx es es' G G' tn tn' s s' sa.
    ghost_inv_at D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x. not_fresh_at sa x ==>
         lookup_var x s' = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    es'.scopes = es.scopes /\ s'.vs_memory = s.vs_memory /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    s'.vs_call_ctx = s.vs_call_ctx /\ s'.vs_accounts = s.vs_accounts /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_immutables = s.vs_immutables ==>
    ghost_inv_at D lo d cenv cx es' G' tn' s'
Proof
  rpt gen_tac >> strip_tac >>
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
          ptr_covers G' tn' p s' sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_at_def, stor_taint_ok_at_def, allocas_from_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum drule_all >> metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[])
  >- (rpt strip_tac >> gvs[local_ptrs_reserved_def] >> metis_tac[])
  >- metis_tac[]
QED
