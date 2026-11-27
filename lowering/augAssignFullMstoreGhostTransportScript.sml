(* Ghost transport across a clean word replacement.  The changed local's
   representation and the immutable prefix mask are supplied separately. *)
Theory augAssignFullMstoreGhostTransport
Ancestors
  bodyPtrDefs ptrDiscipline venomState
  finite_map pred_set words

Theorem augassign_mstore_ghost_transport:
  u = (mstore a w s with vs_inst_idx := pc) /\
  tn' = (tn with t_mem := tn.t_mem DIFF {q | a <= q /\ q < a + 32}) /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  (!name entry p sz.
    lookup_scopes name es'.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ptr_covers G tn p s sz /\
    !v mem. lookup_var p s = SOME v /\
      mem_agree_outside tn'.t_mem u.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n v) mem) /\
  (!q. q < lo /\ q IN tn'.t_mem ==>
    imm_section_dead_mods cenv (mem_bytes_at 0 lo u.vs_memory) q) ==>
  ghost_inv_at D lo d cenv cx es' G tn' u
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      first_assum (drule_all_then strip_assume_tac) >>
      gvs[ptr_covers_def, op_taint_def, lookup_var_def, mstore_def]) >>
  conj_tac
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      PairCases_on `x` >>
      gvs[return_buf_ptr_def, ptr_covers_def, op_taint_def,
          lookup_var_def, mstore_def] >> metis_tac[]) >>
  gvs[op_taint_def, stor_taint_ok_at_def, allocas_from_def, mstore_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
