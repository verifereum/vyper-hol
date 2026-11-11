(* PC-independent ghost frames for the two readonly raw-call header steps. *)
Theory rawCallHeaderFramePtr
Ancestors ghostPcTransportPtr typedCopyAmbientFramePtr decoderGhostFramePtr
  rawCallShapePtr

Theorem ghost_inv_inst_idx[simp]:
  ghost_inv dep cenv cx es G tn (s with vs_inst_idx := k) <=>
  ghost_inv dep cenv cx es G tn s
Proof
  Cases_on `dep` >>
  simp[bodyPtrDefsTheory.ghost_inv_def, bodyPtrDefsTheory.return_buf_ptr_def,
    bodyPtrDefsTheory.ptr_covers_def, bodyPtrDefsTheory.stor_taint_ok_def,
    venomStateTheory.lookup_var_def] >>
  PairCases_on `x` >>
  simp[bodyPtrDefsTheory.return_buf_ptr_def, bodyPtrDefsTheory.ptr_covers_def,
    venomStateTheory.lookup_var_def]
QED

Theorem raw_call_header_ghost_frame:
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint un (Var x) = op_taint tn (Var x)) /\
  t.vs_memory = s.vs_memory /\ un.t_mem = tn.t_mem /\
  un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient ==>
  ghost_inv dep cenv cx es H un t /\
  ghost_kept cenv es sa G tn s H un
Proof
  strip_tac >> conj_tac
  >- (fs[bodyPtrDefsTheory.ghost_inv_def,
         bodyPtrDefsTheory.return_buf_ptr_def,
         bodyPtrDefsTheory.stor_taint_ok_def,
         loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
      rpt conj_tac >> rpt strip_tac
      >- (fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[])
      >- metis_tac[]
      >- (Cases_on `dep` >>
          fs[bodyPtrDefsTheory.return_buf_ptr_def] >>
          PairCases_on `x` >>
          fs[bodyPtrDefsTheory.return_buf_ptr_def] >>
          `not_fresh_at sa x` by metis_tac[] >>
          first_x_assum drule >> strip_tac >>
          fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[])
      >> metis_tac[]) >>
  simp[bodyPtrDefsTheory.ghost_kept_def]
QED

Theorem raw_call_header_fresh_step_frame:
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa out /\ (opc = MLOAD \/ opc = ADD) /\
  H = step_prov PG G (mk_inst id opc ops [out]) (update_var out w s) /\
  un = step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn ==>
  ghost_inv dep cenv cx es H un (update_var out w s) /\
  ghost_kept cenv es sa G tn s H un
Proof
  strip_tac >> (irule raw_call_header_ghost_frame >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `x <> out` by metis_tac[] >>
      gvs[] >>
      simp[decoderGhostFramePtrTheory.step_prov_other_output,
        decoderGhostFramePtrTheory.step_taint_other_output,
        venomInstTheory.mk_inst_def, venomStateTheory.update_var_def,
        venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  gvs[ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.mem_taint_def,
    ptrDisciplineTheory.new_site_bytes_def, ptrDisciplineTheory.step_writes_def,
    ptrDisciplineTheory.written_taint_def, ptrDisciplineTheory.adopt_reset_def,
    ptrDisciplineTheory.store_taint_def, ptrDisciplineTheory.imm_taint_def,
    ptrDisciplineTheory.range_bytes_def, venomStateTheory.update_var_def,
    venomInstTheory.mk_inst_def,
    codegenRelTheory.source_memory_write_ranges_def,
    finite_mapTheory.FLOOKUP_DEF] >>
  rpt (CASE_TAC >> gvs[]) >> simp[SF CONJ_ss])
QED

Theorem raw_call_emit_mload_ghost_frame:
  emit_op MLOAD [Var src] sa = (Var out,sb) /\
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  H = step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [out])
        (update_var out (mload (w2n w) s) s) /\
  un = step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s
        (update_var out (mload (w2n w) s) s) tn ==>
  ghost_inv dep cenv cx es H un
    ((update_var out (mload (w2n w) s) s) with
      vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ghost_kept cenv es sa G tn s H un
Proof
  strip_tac >>
  `~not_fresh_at sa out` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
       compileEnvTheory.comp_return_def] >> rpt strip_tac >> gvs[] >>
     fs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  simp[ghost_inv_inst_idx] >> irule raw_call_header_fresh_step_frame >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`PG`, `sa.cs_next_id`, `MLOAD`, `[Var src]`] >> simp[]
QED

Theorem raw_call_emit_add_ghost_frame:
  emit_op ADD [left;right] sa = (Var out,sb) /\
  ghost_inv dep cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  H = step_prov PG G (mk_inst sa.cs_next_id ADD [left;right] [out])
        (update_var out (a+b) s) /\
  un = step_taint (mk_inst sa.cs_next_id ADD [left;right] [out]) s
        (update_var out (a+b) s) tn ==>
  ghost_inv dep cenv cx es H un
    ((update_var out (a+b) s) with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ghost_kept cenv es sa G tn s H un
Proof
  strip_tac >>
  `~not_fresh_at sa out` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
       compileEnvTheory.comp_return_def] >> rpt strip_tac >> gvs[] >>
     fs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  simp[ghost_inv_inst_idx] >> irule raw_call_header_fresh_step_frame >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`PG`, `sa.cs_next_id`, `ADD`, `[left;right]`] >> simp[]
QED
