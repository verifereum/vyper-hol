(* A finite separated write preserves the outer invariant. This is not a
   frame requirement on an arbitrary body callback. *)
Theory forPtrWriteScope
Ancestors bodyPtrDefs forPtrElement forPtrBytes robustCopyTransportPtr
  finite_map pred_set

Theorem ghost_local_after_separated_write:
  ghost_inv d cenv cx es G tn s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
  op_taint tf (Var p) = op_taint tn (Var p) /\
  val_wf entry.type entry.value /\
  (!w i. lookup_var p s = SOME w /\
    w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
    i NOTIN writes) /\
  mem_agree_outside writes sf.vs_memory s.vs_memory /\
  (!i. i NOTIN writes ==> (i IN tf.t_mem <=> i IN tn.t_mem)) ==>
  ptr_covers gf tf p sf sz /\
  !w mem. lookup_var p sf = SOME w /\
    mem_agree_outside tf.t_mem sf.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n w) mem
Proof
  strip_tac >> drule_all ghost_inv_local_ptr >> strip_tac >>
  conj_tac >- metis_tac[for_ptr_covers_transport] >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tf.t_mem`, `writes`] >>
  gvs[mem_agree_outside_def] >> metis_tac[]
QED

Theorem ghost_inv_after_separated_write:
  ghost_inv d cenv cx es G tn s /\
  mem_agree_outside writes sf.vs_memory s.vs_memory /\
  (!i. i NOTIN writes ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  (!p. p IN kept ==>
    lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
    op_taint tf (Var p) = op_taint tn (Var p)) /\
  (!name entry p sz.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    p IN kept /\ val_wf entry.type entry.value /\
    !w i. lookup_var p s = SOME w /\
      w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
      i NOTIN writes) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) \/
    cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p IN kept) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
  sf.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es gf tf sf
Proof
  strip_tac >> simp[ghost_inv_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >>
      qpat_x_assum `!p. p IN kept ==> _` drule >> strip_tac >>
      drule_all ghost_local_after_separated_write >> simp[])
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
      fs[ghost_inv_def, return_buf_ptr_def] >>
      metis_tac[for_ptr_covers_transport])
  >- (fs[ghost_inv_def] >> metis_tac[])
  >> fs[ghost_inv_def, stor_taint_ok_def]
QED
