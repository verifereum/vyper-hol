(* Footprint-safe staging, including copies shorter than their allocation. *)
Theory annassignRelayoutStage
Ancestors
  stmtSimDeclPath stmtSimProps exprSimBufferStore valueCopy stmtSimDefs loweringPosts
  fragGasMode fragGasSeq fragGasPath compileEnv emitHelper emitHelperProps exprLoweringProps
  venomExecSemantics venomInst venomState valueEncoding
Libs monadsyntax

Theorem alloc_copy_memory_framed_capacity_path:
  !ctx func cenv cx es sa sm sb s0 p src capacity nbytes sw tv v.
    emit_inst ALLOCA [Lit (n2w capacity)] [p] sa = ((),sm) /\
    emit_void MCOPY [Var p;src;Lit (n2w nbytes)] sm = ((),sb) /\
    stmt_state_rel ctx func cenv cx es s0 /\ fn_inst_ids_distinct func /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w capacity)] [p]) (fn_insts func) /\
    not_local_ptr cenv es.scopes p /\ nbytes <= capacity /\ capacity < dimword (:256) /\
    src <> Var p /\ eval_operand src s0 = SOME sw /\
    val_in_memory tv v (w2n sw) s0.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= nbytes /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t w. gas_marked_path F ctx func s0 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es t /\
      val_in_memory tv v (w2n w) t.vs_memory /\ lookup_var p t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,capacity) /\
      (!x. x <> p ==> lookup_var x t = lookup_var x s0) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                   FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!off len. off + len <= w2n w \/ w2n w + capacity <= off ==>
        mem_bytes_at off len t.vs_memory = mem_bytes_at off len s0.vs_memory) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt strip_tac >> drule_all annassign_alloca_operand_framed_path >>
  disch_then (qx_choosel_then [`s1`,`w`] strip_assume_tac) >>
  `eval_operand src s1 = SOME sw` by simp[] >>
  `val_in_memory tv v (w2n sw) s1.vs_memory` by simp[] >>
  `stmt_state_rel ctx func cenv cx es (mcopy (w2n w) (w2n sw) nbytes s1)` by
    (irule stmt_state_rel_mcopy_alloca >> simp[] >>
     qexistsl_tac [`capacity`, `mk_inst sa.cs_next_id ALLOCA [Lit (n2w capacity)] [p]`, `p`] >>
     simp[mk_inst_def]) >>
  `val_in_memory tv v (w2n w) (mcopy (w2n w) (w2n sw) nbytes s1).vs_memory` by
    (irule mcopy_val_in_memory >> simp[]) >>
  `step_inst_base (mk_inst sm.cs_next_id MCOPY [Var p;src;Lit (n2w nbytes)] []) s1 =
     OK (mcopy (w2n w) (w2n sw) nbytes s1)` by
    simp[step_inst_base_def, eval_operand_def] >>
  `gas_marked_path F ctx func s1 0
    (OK (mcopy (w2n w) (w2n sw) nbytes s1 with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (irule emit_inst_zero_marked_path >> simp[] >>
     qexistsl_tac [`[Var p;src;Lit (n2w nbytes)]`, `MCOPY`, `[]`, `sm`, `sb`] >>
     fs[emit_void_def, emit_inst_def, is_terminator_def]) >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sm.cs_current_insts)` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qexistsl_tac [`mcopy (w2n w) (w2n sw) nbytes s1 with vs_inst_idx := SUC s1.vs_inst_idx`, `w`] >>
  reverse conj_tac
  >- (simp[stmt_state_rel_inst_idx] >>
      `(!x. lookup_var x (mcopy (w2n w) (w2n sw) nbytes s1) = lookup_var x s1) /\
       (mcopy (w2n w) (w2n sw) nbytes s1).vs_allocas = s1.vs_allocas /\
       (mcopy (w2n w) (w2n sw) nbytes s1).vs_halted = s1.vs_halted /\
       (mcopy (w2n w) (w2n sw) nbytes s1).vs_current_bb = s1.vs_current_bb` by
        simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def, LET_THM] >>
      `!q z i. lookup_var q (z with vs_inst_idx := i) = lookup_var q z` by
        simp[lookup_var_def] >>
      simp[] >> rpt strip_tac >>
      `off + len <= w2n w \/ w2n w + nbytes <= off` by decide_tac >>
      metis_tac[mem_bytes_at_mcopy_disjoint]) >>
  `gas_marked_path F ctx func s0 (0 + 0)
    (OK (mcopy (w2n w) (w2n sw) nbytes s1 with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (irule gas_marked_path_then >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[]
QED
