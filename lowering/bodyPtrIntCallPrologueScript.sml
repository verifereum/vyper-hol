Theory bodyPtrIntCallPrologue
Ancestors
  bodyPtrIntCallEntryMaterialize bodyPtrIntCallMaterializeList allocationPtr robustCopyTransportPtr
  fragGasSeqPtr intCallCallee venomState venomExecSemantics ptrDiscipline
  finite_map words exprLoweringProps bodyPtrDefs pred_set loweringHalt
  fragExecPtr venomInst arithmetic emitHelper exprLowering compileEnv context rich_list list

(* Scratch allocation taints only bytes above the completed locals. *)
Theorem intcall_scratch_old_robust:
  FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  val_wf ty v /\ p + val_footprint ty v <= s.vs_alloca_next /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ty v p m) ==>
  !m. mem_agree_outside
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem
    u.vs_memory m ==> val_in_memory ty v p m
Proof
  rpt gen_tac >> strip_tac >>
  `u.vs_memory = s.vs_memory` by
    (drule_all step_alloca_fresh >> disch_then (qspec_then `out` mp_tac) >>
     gvs[update_var_def]) >>
  drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`[]`,`FEMPTY`,`tn`] strip_assume_tac) >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  simp[] >>
  qexistsl_tac [`s.vs_memory`,`u.vs_memory`,`tn.t_mem`,
    `(step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem`,
    `{i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+n}`] >>
  simp[mem_agree_outside_def] >> rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem intcall_scratch_local_value:
  intcall_local_value entry p sz G tn s /\ p <> out /\
  FLOOKUP s.vs_allocas id = NONE /\ s.vs_alloca_next + n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  intcall_local_value entry p sz
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) u
Proof
  strip_tac >>
  `n < dimword (:256)` by decide_tac >>
  fs[intcall_local_value_def] >>
  `lookup_var p u = lookup_var p s /\ s.vs_alloca_next <= u.vs_alloca_next` by
    (drule_all step_alloca_fresh >> disch_then (qspec_then `out` mp_tac) >>
     gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) p u sz` by
    (irule (cj 2 fresh_alloca_ptr_covers) >> asm_rewrite_tac[] >> simp[]) >>
  asm_rewrite_tac[] >> qexists_tac `w` >> asm_rewrite_tac[] >>
  conj_tac >- decide_tac >>
  metis_tac[intcall_scratch_old_robust]
QED

Theorem intcall_scratch_completed:
  intcall_completed env ce G tn s /\
  lookup_var out s = NONE /\
  FLOOKUP s.vs_allocas id = NONE /\ s.vs_alloca_next + n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  intcall_completed env ce
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) u
Proof
  simp[intcall_completed_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`p`,`sz`] >> asm_rewrite_tac[] >>
  irule intcall_scratch_local_value >> asm_rewrite_tac[] >>
  conj_tac >- (strip_tac >> gvs[intcall_local_value_def]) >> decide_tac
QED

Theorem intcall_scratch_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ALLOCA [Lit (n2w n)] [out]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id ALLOCA [Lit (n2w n)] [out]] s
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)` by
    (simp[inst_seq_ptr_def] >> irule ptr_inst_ok_alloca >> simp[]) >>
  `run_inst_seq [mk_inst id ALLOCA [Lit (n2w n)] [out]] s = OK u` by
    simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    [mk_inst id ALLOCA [Lit (n2w n)] [out]]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[mk_inst_def, is_terminator_def, ADD1]
QED

Theorem intcall_prologue_factor:
  compile_internal_prologue ce params has_rb ret_type st0 = ((ce2,rpc),st1) ==>
  ?ce1 caps stm st2.
    compile_internal_entry_prefix ce params has_rb st0 = ((ce1,caps,rpc),stm) /\
    materialize_internal_params ce1 caps stm = (ce2,st2) /\
    (case ret_type of
       SOME ty => if ce.ce_returns_count > 0 then
         do compile_alloc_buffer (type_memory_bytes ce ty); return () od
         else return ()
     | NONE => return ()) st2 = ((),st1)
Proof
  simp[compile_internal_prologue_def, compile_internal_entry_prefix_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_scratch_metadata:
  FLOOKUP s.vs_allocas id = NONE /\ s.vs_alloca_next + n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  (!k. ce.ce_return_buf <> SOME (PtrVar (Var out) k)) /\
  (!k. ce.ce_return_pc <> SOME (PtrVar (Var out) k)) /\
  return_buf_ptr d ce G tn s /\
  (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> op_taint tn (Var x) = {}) /\
  stor_taint_ok cx tn s ==>
  return_buf_ptr d ce
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) u /\
  (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==>
    op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) (Var x) = {}) /\
  stor_taint_ok cx
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) u
Proof
  strip_tac >>
  `n < dimword (:256)` by decide_tac >>
  `!p sz. p <> out /\ ptr_covers G tn p s sz ==>
    ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) p u sz` by
    (rpt strip_tac >> irule (cj 2 fresh_alloca_ptr_covers) >>
     asm_rewrite_tac[] >> simp[]) >>
  drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`PG`,`G`,`tn`] strip_assume_tac) >>
  drule_all step_alloca_fresh >> disch_then (qspec_then `out` assume_tac) >>
  conj_tac >-
    (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
     gvs[return_buf_ptr_def] >>
     gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  conj_tac >-
    (simp[op_taint_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
     `x <> out` by metis_tac[] >> gvs[op_taint_def]) >>
  gvs[stor_taint_ok_def, update_var_def]
QED

Theorem intcall_compile_scratch_path:
  compile_alloc_buffer n st = (buf,st') /\
  intcall_completed src ce G tn s /\ return_buf_ptr d ce G tn s /\
  stor_taint_ok cx tn s /\
  (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> op_taint tn (Var x) = {}) /\
  (!x k. ce.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at st x) /\
  (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at st x) /\
  fresh_vars_wrt st s /\
  (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
  s.vs_alloca_next + n < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!name. lookup_scopes name es.scopes = FLOOKUP src name) ==>
  ?t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d ce cx es G' tn' t /\
    intcall_completed src ce G' tn' t /\
    fresh_vars_wrt st' t /\
    (!aid. aid IN FDOM t.vs_allocas ==> aid < st'.cs_next_id) /\
    t.vs_inst_idx = s.vs_inst_idx +
      LENGTH (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    run_inst_seq (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts) s =
      OK (t with vs_inst_idx := s.vs_inst_idx)
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
    comp_return_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  qabbrev_tac `out = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `u = update_var out (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+ (st.cs_next_id,(s.vs_alloca_next,n));
              vs_alloca_next := s.vs_alloca_next+n|>)` >>
  `n < dimword (:256)` by decide_tac >>
  `FLOOKUP s.vs_allocas st.cs_next_id = NONE` by
    (simp[FLOOKUP_DEF] >> strip_tac >> res_tac >> decide_tac) >>
  `lookup_var out s = NONE` by
    (simp[Abbr `out`, lookup_var_def, FLOOKUP_DEF] >>
     fs[fresh_vars_wrt_def]) >>
  `(!k. ce.ce_return_buf <> SOME (PtrVar (Var out) k)) /\
   (!k. ce.ce_return_pc <> SOME (PtrVar (Var out) k))` by
    (simp[Abbr `out`] >> rpt strip_tac >> res_tac >>
     fs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
  `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u`
    by (simp[step_alloca_fresh, Abbr `u`]) >>
  `intcall_completed src ce
    (step_prov PG G (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn) u`
    by (irule intcall_scratch_completed >> asm_rewrite_tac[] >> simp[ADD_COMM]) >>
  `s.vs_alloca_next + n < dimword (:256)` by decide_tac >>
  drule_all intcall_scratch_metadata >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [out]) u`,
    `step_taint (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn`] >>
  conj_tac >- suspend "path" >>
  suspend "endpoint"
QED

Resume intcall_compile_scratch_path[path]:
  irule intcall_scratch_path >> asm_rewrite_tac[] >>
  qexists_tac `bb` >> asm_rewrite_tac[] >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  simp[DROP_LENGTH_APPEND, Abbr `out`]
QED

Resume intcall_compile_scratch_path[endpoint]:
  `ghost_inv d ce cx es
    (step_prov PG G (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn) u` by
    (irule intcall_completed_ghost_inv >> asm_rewrite_tac[] >>
     qexists_tac `src` >> asm_rewrite_tac[]) >>
  conj_tac >-
    (qpat_x_assum `ghost_inv _ _ _ _ _ _ u` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[ghost_inv_def, oneline return_buf_ptr_def, ptr_covers_def,
          lookup_var_def, stor_taint_ok_def] >> strip_tac >> asm_rewrite_tac[]) >>
  conj_tac >-
    (qpat_x_assum `intcall_completed _ _ _ _ u` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[intcall_completed_def, intcall_local_value_def, ptr_covers_def, lookup_var_def]) >>
  drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`PG`,`G`,`tn`] strip_assume_tac) >>
  simp[Abbr `u`, update_var_def] >>
  conj_tac >- suspend "fresh" >>
  conj_tac >- (simp[FDOM_FUPDATE] >> rpt strip_tac >> res_tac >> decide_tac) >>
  simp[ADD1] >> conj_tac >- suspend "oldvars" >>
  simp[DROP_LENGTH_APPEND, run_inst_seq_def, step_alloca_fresh, update_var_def,
       venom_state_component_equality]
QED

Resume intcall_compile_scratch_path[oldvars]:
  rpt strip_tac >>
  `x <> out` by
    (gvs[Abbr `out`, not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def]
QED
Resume intcall_compile_scratch_path[fresh]:
  qpat_x_assum `fresh_vars_wrt st s` mp_tac >>
  qpat_x_assum `Abbrev (out = _)` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[fresh_vars_wrt_def, FDOM_FUPDATE] >>
  rpt strip_tac >> gvs[] >>
  rename1 `k >= st.cs_next_var + 1` >>
  `k <> st.cs_next_var` by decide_tac >>
  gvs[ASCIInumbersTheory.toString_inj] >>
  first_x_assum drule >> decide_tac
QED
Finalise intcall_compile_scratch_path
