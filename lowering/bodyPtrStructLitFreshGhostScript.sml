(* Selective live-register frames: non-live registers may change freely. *)
Theory bodyPtrStructLitFreshGhost
Ancestors
  wordLoadStorePtr
  bodyPtrStructLitGhostFrame decoderGhostFramePtr bodyPtrDefs venomState
  finite_map typedCopyPtr venomInst

Theorem ghost_inv_selective_frame:
  ghost_inv d cenv cx es G tn s /\
  (!x.
    ((?name entry sz. lookup_scopes name es.scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var x) sz)) \/
     (?sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz)) \/
     (?sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz))) ==>
    lookup_var x s' = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  s'.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
  s'.vs_accounts = s.vs_accounts /\ s'.vs_transient = s.vs_transient /\
  s'.vs_call_ctx = s.vs_call_ctx /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  tn'.t_imm = tn.t_imm ==>
  ghost_inv d cenv cx es G' tn' s'
Proof
  strip_tac >> rewrite_tac[ghost_inv_def] >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_inv_def] >> strip_tac >>
  rpt conj_tac
  >- (rpt strip_tac >>
      `lookup_var p s' = lookup_var p s /\
       FLOOKUP G' p = FLOOKUP G p /\
       op_taint tn' (Var p) = op_taint tn (Var p)` by
        (first_x_assum irule >> metis_tac[]) >>
      first_x_assum drule_all >>
      simp[ptr_covers_def] >> metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      PairCases_on `x` >> gvs[return_buf_ptr_def] >>
      `lookup_var x s' = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)` by
        (first_x_assum irule >> metis_tac[]) >>
      gvs[ptr_covers_def] >> metis_tac[])
  >- (rpt strip_tac >>
      `op_taint tn' (Var x) = op_taint tn (Var x)` by
        (first_x_assum (qspec_then `x` mp_tac) >> simp[] >> metis_tac[]) >>
      metis_tac[])
  >> gvs[stor_taint_ok_def]
QED

Theorem ghost_inv_update_var_pc:
  ghost_inv d cenv cx es G tn s /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm ==>
  ghost_inv d cenv cx es G' tn'
    (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> irule ghost_inv_selective_frame >>
  qexistsl [`G`, `s`, `tn`] >> simp[update_var_def] >>
  rpt strip_tac >>
  `x <> out` by metis_tac[] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem ghost_inv_fresh_add_pc:
  ghost_inv d cenv cx es G tn s /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> out) ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id ADD [left; right] [out]) (update_var out w s))
    (step_taint (mk_inst id ADD [left; right] [out]) s (update_var out w s) tn)
    (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> irule ghost_inv_update_var_pc >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`G`, `tn`] >>
  simp[copy_len_binop_ghost_frame, step_taint_nonmemory_frame, mk_inst_def]
QED

Theorem ghost_inv_clean_mload_pc:
  ghost_inv d cenv cx es G tn s /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  eval_operand src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id MLOAD [src] [out])
      (update_var out (mload (w2n a) s) s))
    (step_taint (mk_inst id MLOAD [src] [out]) s
      (update_var out (mload (w2n a) s) s) tn)
    (update_var out (mload (w2n a) s) s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> irule ghost_inv_update_var_pc >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`G`, `tn`] >>
  drule_all mload_ghost_clean >> strip_tac >>
  simp[] >> conj_tac
  >- (gen_tac >> disch_tac >> conj_tac
      >- (irule step_prov_other_output >> simp[mk_inst_def]) >>
      irule step_taint_other_output >> simp[mk_inst_def]) >>
  irule (cj 3 step_taint_nonmemory_frame) >> simp[mk_inst_def]
QED
