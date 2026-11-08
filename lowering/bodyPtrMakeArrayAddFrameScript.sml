(* Judgment transport across the fresh destination offset instruction. *)
Theory bodyPtrMakeArrayAddFrame
Ancestors
  bodyPtrMakeArrayAdd exprSimVVFrame context compileEnv exprLoweringProps
  bodyPtrDefs freshWrites loweringPosts emitHelper ptrDiscipline venomState
  finite_map venomExecSemantics

Theorem emit_binop_vv_post:
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) /\
  emit_op opc [left;right] sm = (Var out,sn) ==>
  vv_post ctx func cenv cx e es sa sn s0 es' tv vv
    ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> simp[] >> irule vv_post_update_var >> simp[] >>
  qexists_tac `sm` >> simp[] >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def, not_fresh_at_def]
QED

Theorem ghost_kept_frame:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  tn'.t_mem = tn.t_mem /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) ==>
  ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  simp[ghost_kept_def] >> metis_tac[]
QED

Theorem emit_binop_ghost_kept:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  sa.cs_next_var <= sm.cs_next_var /\
  (opc = ADD \/ opc = AND) /\
  emit_op opc [left;right] sm = (Var out,sn) ==>
  ghost_kept cenv es sa G0 tn0 s0
    (step_prov PG G (mk_inst sm.cs_next_id opc [left;right] [out])
      (update_var out w s))
    (step_taint (mk_inst sm.cs_next_id opc [left;right] [out]) s
      (update_var out w s) tn)
Proof
  strip_tac >>
  `!p. not_fresh_at sa p ==> p <> out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     rpt strip_tac >> decide_tac) >>
  irule ghost_kept_frame >> qexistsl_tac [`G`, `tn`] >>
  simp[typedCopyPtrTheory.copy_len_binop_ghost_frame]
QED

Theorem binop_source_ptr_mem_ok:
  ptr_mem_ok cx t v op G tn s /\
  (!p. op = Var p ==> p <> out) /\ (opc = ADD \/ opc = AND) ==>
  ptr_mem_ok cx t v op
    (step_prov PG G (mk_inst id opc [left;right] [out])
      (update_var out w s))
    (step_taint (mk_inst id opc [left;right] [out]) s
      (update_var out w s) tn)
    ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  Cases_on `op` >>
  gvs[] >>
  simp[ptr_mem_ok_def, typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
  gvs[ptr_mem_ok_def, eval_operand_def, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE]
QED

Theorem binop_source_ptr_buf_ok:
  ptr_buf_ok cenv e op G s /\
  (!p. op = Var p ==> p <> out) /\ (opc = ADD \/ opc = AND) ==>
  ptr_buf_ok cenv e op
    (step_prov PG G (mk_inst id opc [left;right] [out])
      (update_var out w s))
    ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> Cases_on `op` >>
  gvs[] >>
  simp[ptr_buf_ok_def, typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
  gvs[ptr_buf_ok_def, eval_operand_def, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE]
QED

Theorem binop_source_op_taint:
  (!p. op = Var p ==> p <> out) /\ (opc = ADD \/ opc = AND) ==>
  op_taint (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn) op = op_taint tn op
Proof
  strip_tac >> Cases_on `op` >>
  gvs[typedCopyPtrTheory.copy_len_binop_ghost_frame, op_taint_def]
QED

Theorem binop_source_ptr_val_ok:
  ptr_val_ok cx t v op G tn s /\
  (!p. op = Var p ==> p <> out) /\ (opc = ADD \/ opc = AND) ==>
  ptr_val_ok cx t v op
    (step_prov PG G (mk_inst id opc [left;right] [out])
      (update_var out w s))
    (step_taint (mk_inst id opc [left;right] [out]) s
      (update_var out w s) tn)
    ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `op_taint (step_taint (mk_inst id opc [left;right] [out]) s
     (update_var out w s) tn) op = op_taint tn op` by
    (irule binop_source_op_taint >> metis_tac[]) >>
  `op_prov (step_prov PG G (mk_inst id opc [left;right] [out])
     (update_var out w s)) op = op_prov G op` by
    (Cases_on `op` >>
     gvs[op_prov_def, typedCopyPtrTheory.copy_len_binop_ghost_frame]) >>
  gvs[ptr_val_ok_def] >> strip_tac >>
  irule binop_source_ptr_mem_ok >> simp[]
QED

Theorem binop_source_ptr_vv_ok:
  ptr_vv_ok cx t tv vv es G tn s /\
  (!p. vv_operand vv = Var p ==> p <> out) /\
  (opc = ADD \/ opc = AND) ==>
  ptr_vv_ok cx t tv vv es
    (step_prov PG G (mk_inst id opc [left;right] [out])
      (update_var out w s))
    (step_taint (mk_inst id opc [left;right] [out]) s
      (update_var out w s) tn)
    ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `vv`
  >- (gvs[ptr_vv_ok_def, vv_operand_def] >>
      irule binop_source_ptr_val_ok >> simp[]) >>
  gvs[ptr_vv_ok_def, vv_operand_def] >>
  (conj_tac >- metis_tac[binop_source_op_taint] >>
  conj_tac
  >- (strip_tac >> Cases_on `p.ptr_operand` >>
      gvs[op_prov_def, typedCopyPtrTheory.copy_len_binop_ghost_frame]) >>
  conj_tac
  >- (strip_tac >> gvs[] >>
      irule binop_source_ptr_mem_ok >> simp[]) >>
  Cases_on `p.ptr_operand` >>
  gvs[eval_operand_def, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE, typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
  metis_tac[])
QED

Theorem emit_binop_ghost_inv:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sm x) /\
  (opc = ADD \/ opc = AND) /\
  emit_op opc [left;right] sm = (Var out,sn) ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst sm.cs_next_id opc [left;right] [out])
      (update_var out w s))
    (step_taint (mk_inst sm.cs_next_id opc [left;right] [out]) s
      (update_var out w s) tn)
    ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `!x. not_fresh_at sm x ==> x <> out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     rpt strip_tac >> decide_tac) >>
  `!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     p <> out` by
    (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> out`
    by metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> out`
    by metis_tac[] >>
  gvs[ghost_inv_def] >> (
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `p <> out` by metis_tac[] >>
      simp[ptr_covers_def, typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
      gvs[ptr_covers_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  conj_tac
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >> PairCases_on `x` >>
      gvs[return_buf_ptr_def] >>
      simp[ptr_covers_def, typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
      gvs[ptr_covers_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `x <> out` by metis_tac[] >>
      simp[typedCopyPtrTheory.copy_len_binop_ghost_frame] >> metis_tac[]) >>
  gvs[stor_taint_ok_def, typedCopyPtrTheory.copy_len_binop_ghost_frame,
      step_taint_def, venomInstTheory.mk_inst_def, store_taint_def, set_var_taint_def,
      update_var_def, imm_taint_def])
QED
