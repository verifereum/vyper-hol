(* Allocation-to-loop interface: the allocated capacity is not the copy size. *)
Theory exprPtrUnwrapLoopEntry
Ancestors
  exprPtrUnwrapAllocEntry exprPtrUnwrapCompiledLoop exprPtrUnwrapAllocationFrame
  exprPtrUnwrapAllocSeparation exprSimAlloc exprPtrUnwrapAllocation
  slotCopyExecution copyExecution bodyPtrDefs context compileEnv
  exprLoweringProps emitHelper ASCIInumbers words arithmetic
  venomState bufferAllocationExecution finite_map

Theorem unwrap_slot_external_old:
  (!x. op = Var x ==> not_fresh_at cs x) ==>
  slot_copy_external cs op
Proof
  simp[slot_copy_external_def, slot_copy_var_def] >> rpt strip_tac >>
  spose_not_then assume_tac >> gvs[not_fresh_at_def] >>
  metis_tac[LESS_EQ_REFL, DECIDE ``n <= n+k``]
QED

Theorem unwrap_alloc_loop_external:
  compile_alloc_buffer nb sa = (buf,sm) /\
  (!x. src = Var x ==> not_fresh_at sa x) ==>
  slot_copy_external sm src /\ slot_copy_external sm buf.buf_operand
Proof
  strip_tac >>
  gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
  conj_tac >> irule unwrap_slot_external_old >>
  gvs[not_fresh_at_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> decide_tac
QED

Theorem unwrap_alloc_loop_entry:
  compile_alloc_buffer nb sa = (buf,sm) /\ fn_has_code sa sm func /\
  stmt_state_rel ctx func cenv cx es s /\ nb < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} /\ 32*n <= nb ==>
  ?root d a G0 tn0 u.
    u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    buf.buf_operand = Var root /\
    d = n2w (buffer_allocation_base s sa.cs_next_id) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G0 tn0 (OK a) /\
    a.vs_current_bb = sm.cs_current_bb /\
    a.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~a.vs_halted /\
    slot_copy_external sm src /\ slot_copy_external sm (Var root) /\
    eval_operand src a = SOME p /\ lookup_var root a = SOME d /\
    op_taint tn0 src = {} /\
    ptr_covers G0 tn0 root a (32*n) /\ ptr_covers G0 tn0 root a nb /\
    w2n d+32*n < 2**256 /\
    a.vs_memory = s.vs_memory /\ a.vs_accounts = s.vs_accounts /\
    a.vs_transient = s.vs_transient /\ a.vs_call_ctx = s.vs_call_ctx /\
    a.vs_immutables = s.vs_immutables /\
    tn0.t_stor = tn.t_stor /\ tn0.t_trans = tn.t_trans /\ tn0.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all unwrap_alloc_entry >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `!x. src = Var x ==> x <> out` by
    metis_tac[unwrap_alloc_old_operand_distinct] >>
  drule_all unwrap_alloc_old_operand_ghost >>
  disch_then (qspecl_then [`tn`, `SUC s.vs_inst_idx`, `PG`, `G`] strip_assume_tac) >>
  drule_all unwrap_alloc_loop_external >> strip_tac >>
  drule_all unwrap_alloc_site_bound >> strip_tac >>
  drule unwrap_alloc_runtime_frame >>
  disch_then (qspec_then `SUC s.vs_inst_idx` strip_assume_tac) >>
  drule_all buffer_alloc_code >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [out]) (fn_insts func)` by simp[] >>
  drule_all unwrap_alloc_taint_frame >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  qexistsl [`out`, `n2w (buffer_allocation_base s sa.cs_next_id)`,
    `a`, `Gf`, `tnf`, `u`] >>
  gvs[eval_operand_def] >>
  conj_tac
  >- (simp[update_var_def, buffer_allocation_fields_def] >>
      Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >> simp[]) >>
  conj_tac
  >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (gvs[ptr_covers_def] >> metis_tac[LESS_EQ_LESS_EQ_MONO]) >>
  gvs[dimword_def] >> decide_tac
QED
