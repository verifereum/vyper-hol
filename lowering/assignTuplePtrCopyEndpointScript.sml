(* Natural-address boundary for staging into an allocated buffer. *)
Theory assignTuplePtrCopyEndpoint
Ancestors
  assignTuplePtrStageFrame robustCopyTransportPtr typedCopyPtr venomMemProofs
  valueEncodingProps exprSimBufferStore exprSimProps compileEnv
  venomState venomInst venomExecSemantics bodyPtrDefs ptrDiscipline
  ghostPcTransportPtr stmtFragPtr emitHelper emitHelperProps exprLoweringProps

(* Copy taint with bytes; padding need not be clean. *)
Theorem mcopy_staged_robust_ptr:
  eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
  eval_operand count_op s = SOME n /\ val_wf tv v /\
  val_footprint tv v <= w2n n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory tv v (w2n a) m) ==>
  !m. mem_agree_outside
    (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_mem
    (mcopy (w2n b) (w2n a) (w2n n) s).vs_memory m ==>
    val_in_memory tv v (w2n b) m
Proof
  strip_tac >>
  qpat_assum `eval_operand dst s = SOME b`
    (mp_then Any mp_tac mcopy_operand_ghost_frame) >>
  disch_then (fn th => qpat_assum `eval_operand src s = SOME a`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_operand count_op s = SOME n`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`ARB`, `ARB`, `tn`, `id`] strip_assume_tac) >>
  rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`,
    `(mcopy (w2n b) (w2n a) (w2n n) s).vs_memory`,
    `w2n n`, `w2n a`, `tn.t_mem`,
    `(step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_mem`] >>
  simp[mcopy_mem_bytes_at_same]
QED

Theorem ghost_inv_inst_idx:
  ghost_inv d cenv cx es G tn (s with vs_inst_idx := k) <=>
  ghost_inv d cenv cx es G tn s
Proof
  simp[ghost_inv_def, ptr_covers_def, stor_taint_ok_def, lookup_var_def] >>
  Cases_on `d` >> simp[return_buf_ptr_def] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem emit_allocated_mcopy_endpoint_ptr:
  emit_inst MCOPY [Var p; Var q; Lit (n2w n)] [] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var p s = SOME (n2w b) /\ lookup_var q s = SOME a /\
  b < dimword (:256) /\ n < dimword (:256) /\
  ptr_covers G tn p s n /\ ptr_covers G tn q s n /\
  ghost_inv d cenv cx es G tn s /\ stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  not_local_ptr cenv es.scopes p /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,alloc_sz) /\ n <= alloc_sz /\
  (!name entry r sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var r) sz) /\
    lookup_var r s = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w + val_footprint entry.type entry.value <= b \/ b+n <= w2n w)) /\
  val_wf tv v /\ val_footprint tv v <= n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory tv v (w2n a) m) ==>
  ?u G' tn'.
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK u) /\
    ghost_inv d cenv cx es G' tn' u /\
    stmt_state_rel ctx func cenv cx es u /\
    (!m. mem_agree_outside tn'.t_mem u.vs_memory m ==> val_in_memory tv v b m) /\
    u = (mcopy b (w2n a) n s with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!x. lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    u.vs_allocas = s.vs_allocas /\ ptr_covers G' tn' p u n /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `eval_operand (Var p) s = SOME (n2w b)` by simp[eval_operand_def] >>
  `eval_operand (Var q) s = SOME a` by simp[eval_operand_def] >>
  `eval_operand (Lit (n2w n)) s = SOME (n2w n : bytes32)` by simp[eval_operand_def] >>
  suspend "endpoint"
QED

Resume emit_allocated_mcopy_endpoint_ptr[endpoint]:
  drule emit_mcopy_zero_path_ptr >>
  simp[eval_operand_def, op_taint_def] >>
  disch_then drule_all >>
  simp[] >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  qpat_assum `eval_operand (Var p) s = SOME _`
    (mp_then (Pat `eval_operand dst _ = _`) mp_tac mcopy_exterior_ghost_inv) >>
  disch_then (fn th => qpat_assum `eval_operand (Var q) s = SOME _`
    (mp_then (Pat `eval_operand src _ = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_operand (Lit _) s = SOME _`
    (mp_then (Pat `eval_operand count_op _ = _`) mp_tac th)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`sa.cs_next_id`, `PG`] assume_tac) >>
  qpat_assum `eval_operand (Var p) s = SOME _`
    (mp_then (Pat `eval_operand dst _ = _`) mp_tac mcopy_staged_robust_ptr) >>
  disch_then (fn th => qpat_assum `eval_operand (Var q) s = SOME _`
    (mp_then (Pat `eval_operand src _ = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_operand (Lit _) s = SOME _`
    (mp_then (Pat `eval_operand count_op _ = _`) mp_tac th)) >>
  simp[] >>
  disch_then (qspecl_then [`v`, `tv`, `tn`, `sa.cs_next_id`] mp_tac) >>
  simp[] >> disch_tac >>
  drule_all stmt_state_rel_mcopy_alloca >>
  disch_then (qspec_then `w2n a` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf _` >>
  qexistsl_tac [`Gf`, `tf`] >>
  simp[ghost_inv_inst_idx, stmt_state_rel_inst_idx] >>
  suspend "frames"
QED

Resume emit_allocated_mcopy_endpoint_ptr[frames]:
  qpat_assum `eval_operand (Var p) s = SOME _`
    (mp_then (Pat `eval_operand dst _ = _`) mp_tac mcopy_operand_ghost_frame) >>
  disch_then (fn th => qpat_assum `eval_operand (Var q) s = SOME _`
    (mp_then (Pat `eval_operand src _ = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_operand (Lit _) s = SOME _`
    (mp_then (Pat `eval_operand count_op _ = _`) mp_tac th)) >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `sa.cs_next_id`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[Abbr `Gf`, Abbr `tf`] >>
  simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def,
       ptr_covers_def, op_taint_def] >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, emit_def, fresh_id_def, comp_bind_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  gvs[ptr_covers_def, op_taint_def, lookup_var_def]
QED

Finalise emit_allocated_mcopy_endpoint_ptr
