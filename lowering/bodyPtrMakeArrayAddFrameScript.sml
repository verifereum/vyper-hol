(* Judgment transport across the fresh destination offset instruction. *)
Theory bodyPtrMakeArrayAddFrame
Ancestors
  bodyPtrMakeArrayAdd exprSimVVFrame context compileEnv loweringStateRelDefs exprLoweringProps
  bodyPtrDefs freshWrites loweringPosts emitHelper ptrDiscipline venomState
  finite_map venomExecSemantics

Theorem emit_binop_vv_post:
  vv_post H ctx func cenv cx e es sa sm s0 es' tv vv s /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) /\
  emit_op opc [left;right] sm = (Var out,sn) ==>
  vv_post H ctx func cenv cx e es sa sn s0 es' tv vv
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

Theorem emit_binop_ghost_inv:
  ghost_inv H d cenv cx es G tn s /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sm x) /\
  (opc = ADD \/ opc = AND) /\
  emit_op opc [left;right] sm = (Var out,sn) ==>
  ghost_inv H d cenv cx es
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
