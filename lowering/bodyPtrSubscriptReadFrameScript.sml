(* Read-only suffixes preserve the original expression's ghost frame. *)
Theory bodyPtrSubscriptReadFrame
Ancestors
  bodyPtrSubscriptNamedScalar bodyPtrDefs exprLoweringProps ptrDiscipline
  emitHelper compileEnv venomState venomInst finite_map stmtFragPtr

Theorem ghost_kept_read_suffix:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  sa.cs_next_var <= sm.cs_next_var /\ tnf.t_mem = tn.t_mem /\
  (!p. not_fresh_at sm p ==>
    FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p)) ==>
  ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
  rw[ghost_kept_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem mload_read_suffix_frame:
  ghost_inv d cenv cx ee G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved cenv sm /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  sf = (update_var out (mload (w2n a) s) s with
          vs_inst_idx := SUC s.vs_inst_idx) /\
  tnf = step_taint (mk_inst sm.cs_next_id MLOAD [Var src] [out]) s
          (update_var out (mload (w2n a) s) s) tn /\
  (!p. not_fresh_at sm p ==>
    lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p)) ==>
  ghost_inv d cenv cx (ee with gas_obs := []) Gf tnf sf /\
  ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >>
  `tnf.t_imm = tn.t_imm` by
    simp[step_taint_def, mk_inst_def, imm_taint_def] >>
  conj_tac
  >- (irule (cj 1 named_read_ghost_frame) >>
      qexistsl_tac [`G`, `s`, `sm`, `tn`] >> simp[update_var_def]) >>
  irule ghost_kept_read_suffix >> metis_tac[]
QED
