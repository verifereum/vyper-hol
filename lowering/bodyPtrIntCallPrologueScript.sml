Theory bodyPtrIntCallPrologue
Ancestors
  bodyPtrIntCallEntryMaterialize bodyPtrIntCallMaterializeList allocationPtr robustCopyTransportPtr
  fragGasSeqPtr intCallCallee venomState venomExecSemantics ptrDiscipline
  finite_map words exprLoweringProps bodyPtrDefs pred_set loweringHalt
  fragExecPtr venomInst arithmetic emitHelper exprLowering compileEnv context rich_list list
  bodyPtrIntCallRoom bodyPtrIntCallJoint fragGasPathPtr vyperState venomMemDefs fragExec

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

(* Deterministic raw execution aligns the semantic and constructive witnesses. *)
Theorem intcall_runtime_prologue_raw_post:
  compile_internal_prologue ce params has_rb ret_type st0 = ((ce2,rpc),st1) /\
  fn_has_code st0 st1 fn /\ fn_inst_ids_distinct fn /\
  setup_callee fn args caller = SOME s0 /\
  state_rel f ce cx (vs with scopes := []) caller /\
  internal_immutable_regions ce cx vs caller.vs_alloca_next /\
  internal_args_rel ce params src (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\ ~ce.ce_is_ctor /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK u ==>
  state_rel fn (ce2 with ce_alloca_locals := T) cx (vs with scopes := [src]) u /\
  immutable_alloca_sep fn (ce2 with ce_alloca_locals := T) cx
    (vs with scopes := [src]) u /\ alloca_inv u /\
  fresh_vars_wrt st1 u /\ mat_frame st0 s0 u /\
  (!inst n base sz. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\ FLOOKUP u.vs_allocas inst.inst_id = SOME (base,sz) ==>
    sz = w2n n) /\
  (?x. rpc = Var x /\ not_fresh_at st1 x /\
       lookup_var x u = SOME s0.vs_return_pc_token) /\
  (has_rb ==> ?rb. not_fresh_at st1 rb /\ lookup_var rb u = SOME (HD args) /\
    !off sz. ce.ce_return_buf = SOME (MemLoc off sz) ==>
       ce2.ce_return_buf = SOME (PtrVar (Var rb) sz))
Proof
  strip_tac >> drule internal_prologue_run >> simp[] >>
  disch_then drule_all >> strip_tac >> gvs[] >> first_assum ACCEPT_TAC
QED

Theorem intcall_ghost_inv_alloca_locals:
  ghost_inv d (ce with ce_alloca_locals := flag) cx es G tn s <=>
  ghost_inv d ce cx es G tn s
Proof
  Cases_on `d` >- simp[ghost_inv_def, return_buf_ptr_def] >>
  PairCases_on `x` >> simp[ghost_inv_def, return_buf_ptr_def]
QED

(* The optional suffix retains the raw witness needed for semantic alignment. *)
Theorem intcall_optional_scratch_path:
  (case ret_type of
     SOME ty => if ce0.ce_returns_count > 0 then
       do compile_alloc_buffer (type_memory_bytes ce0 ty); return () od
       else return ()
   | NONE => return ()) st = ((),st') /\
  (case ret_type of NONE => T | SOME ty =>
    type_memory_bytes ce0 ty < dimword (:256)) /\
  fn_has_code st st' fn /\ alloca_room ctx fn s /\
  intcall_completed src ce G tn s /\ ghost_inv d ce cx es G tn s /\
  (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> op_taint tn (Var x) = {}) /\
  (!x k. ce.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at st x) /\
  (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at st x) /\
  fresh_vars_wrt st s /\
  (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!name. lookup_scopes name es.scopes = FLOOKUP src name) ==>
  ?t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d ce cx es G' tn' t /\
    intcall_completed src ce G' tn' t /\ fresh_vars_wrt st' t /\
    (!aid. aid IN FDOM t.vs_allocas ==> aid < st'.cs_next_id) /\
    t.vs_inst_idx = s.vs_inst_idx +
      LENGTH (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
    run_inst_seq (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts) s =
      OK (t with vs_inst_idx := s.vs_inst_idx)
Proof
  Cases_on `ret_type`
  >- (simp[comp_return_def] >> strip_tac >> gvs[] >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[gas_path_ptr_rules, run_inst_seq_def]) >>
  rename1 `SOME ty` >> reverse (Cases_on `ce0.ce_returns_count > 0`)
  >- (simp[comp_return_def] >> strip_tac >> gvs[] >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[gas_path_ptr_rules, run_inst_seq_def]) >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_all intcall_compile_scratch_room >> strip_tac >>
  `return_buf_ptr d ce G tn s /\ stor_taint_ok cx tn s` by
    fs[ghost_inv_def] >>
  drule_all intcall_compile_scratch_path >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> asm_rewrite_tac[] >> simp[]
QED

Theorem intcall_optional_scratch_append:
  (case ret_type of
     SOME ty => if ce.ce_returns_count > 0 then
       do compile_alloc_buffer (type_memory_bytes ce ty); return () od
       else return ()
   | NONE => return ()) st = ((),st') ==>
  ?code. st'.cs_current_insts = st.cs_current_insts ++ code /\
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    EVERY (\i. i.inst_opcode <> INVOKE) code /\
    EVERY (\i. ~is_terminator i.inst_opcode) code
Proof
  Cases_on `ret_type`
  >- (simp[comp_return_def] >> strip_tac >> gvs[]) >>
  rename1 `SOME ty` >> reverse (Cases_on `ce.ce_returns_count > 0`)
  >- (simp[comp_return_def] >> strip_tac >> gvs[]) >>
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
    comp_return_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[mk_inst_def, is_terminator_def]
QED

Theorem intcall_prologue_joint_path:
  compile_internal_entry_prefix ce params has_rb st = ((ce1,caps,rpc),stm) /\
  materialize_internal_params ce1 caps stm = (ce2,st2) /\
  (case ret_type of
     SOME ty => if ce.ce_returns_count > 0 then
       do compile_alloc_buffer (type_memory_bytes ce ty); return () od
       else return ()
   | NONE => return ()) st2 = ((),st1) /\
  (case ret_type of NONE => T | SOME ty =>
    type_memory_bytes ce ty < dimword (:256)) /\
  fn_has_code st2 st1 fn /\ alloca_room ctx fn s /\
  EVERY (\i. MEM i (fn_insts fn) /\ i.inst_opcode <> INVOKE)
    (DROP (LENGTH st.cs_current_insts) st2.cs_current_insts) /\
  internal_args_rel ce params src (if has_rb then 1 else 0)
    s.vs_params s.vs_alloca_next s.vs_memory /\
  intcall_entry_memory ce params src (if has_rb then 1 else 0) PG tn s /\
  intcall_entry_return ce has_rb d PG s /\
  (!name entry off sz. FLOOKUP src name = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (MemLoc off sz) ==>
    val_footprint entry.type entry.value <= sz) /\
  (if has_rb then 1 else 0) + LENGTH params <= LENGTH s.vs_params /\
  (if has_rb then 1 else 0) + LENGTH params <= LENGTH PG /\
  (if has_rb then 1 else 0) + LENGTH params < dimword (:256) /\
  fresh_vars_wrt st s /\
  (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (DROP (LENGTH st.cs_current_insts) st1.cs_current_insts)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  stor_taint_ok cx tn s /\
  (!name. lookup_scopes name es.scopes = FLOOKUP src name) ==>
  ?t G' tn' u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d ce2 cx es G' tn' t /\
    fresh_vars_wrt st1 t /\
    t.vs_inst_idx = s.vs_inst_idx +
      LENGTH (DROP (LENGTH st.cs_current_insts) st1.cs_current_insts) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
    run_inst_seq (DROP (LENGTH st.cs_current_insts) st1.cs_current_insts) s = OK u /\
    t = u with vs_inst_idx := s.vs_inst_idx +
      LENGTH (DROP (LENGTH st.cs_current_insts) st1.cs_current_insts)
Proof
  strip_tac >> drule_all intcall_optional_scratch_append >> strip_tac >>
  `DROP (LENGTH st.cs_current_insts) st1.cs_current_insts =
    DROP (LENGTH st.cs_current_insts) st2.cs_current_insts ++
    DROP (LENGTH st2.cs_current_insts) st1.cs_current_insts` by suspend "split" >>
  `isPREFIX (DROP (LENGTH st.cs_current_insts) st2.cs_current_insts)
    (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     asm_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >>
     strip_tac >> metis_tac[APPEND_ASSOC]) >>
  drule_all intcall_entry_materialize_path >>
  disch_then (qspecl_then [`G`,`D`] strip_assume_tac) >>
  `alloca_room ctx fn t` by suspend "room" >>
  `isPREFIX (DROP (LENGTH st2.cs_current_insts) st1.cs_current_insts)
    (DROP t.vs_inst_idx bb.bb_instructions)` by suspend "suffix" >>
  `(!x k. ce2.ce_return_pc = SOME (PtrVar (Var x) k) ==>
      op_taint tn' (Var x) = {})` by suspend "retpc" >>
  `lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\ ~t.vs_halted` by
    asm_rewrite_tac[] >>
  drule_all intcall_optional_scratch_path >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `run_inst_seq (DROP (LENGTH st.cs_current_insts) st1.cs_current_insts) s =
    OK (t' with vs_inst_idx := s.vs_inst_idx)` by
    (qpat_assum `DROP _ _ = _ ++ _` (fn th => pure_once_rewrite_tac[th]) >>
     irule intcall_run_cursor_append >> conj_tac
     >- (qexists_tac `t` >> asm_rewrite_tac[]) >>
     asm_rewrite_tac[] >> simp[DROP_LENGTH_APPEND]) >>
  qexistsl_tac [`t'`,`G''`,`tn''`,`t' with vs_inst_idx := s.vs_inst_idx`] >>
  conj_tac >- suspend "path" >> suspend "endpoint"
QED

Resume intcall_prologue_joint_path[split]:
  drule intcall_entry_prefix_code >> strip_tac >>
  drule intcall_materialize_append >> strip_tac >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Resume intcall_prologue_joint_path[room]:
  drule_all intcall_run_inst_seq_alloca_room >>
  simp[alloca_room_def, pending_alloca_size_def]
QED

Resume intcall_prologue_joint_path[suffix]:
  qpat_x_assum `isPREFIX (DROP (LENGTH st.cs_current_insts) st1.cs_current_insts) _` mp_tac >>
  qpat_assum `DROP _ _ = _ ++ _` (fn th => pure_once_rewrite_tac[th]) >>
  pure_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  qexists_tac `l` >>
  `DROP t.vs_inst_idx bb.bb_instructions =
    DROP (LENGTH (DROP (LENGTH st.cs_current_insts) st2.cs_current_insts))
      (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `t.vs_inst_idx = _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, DROP_DROP_T, ADD_COMM]) >>
  qpat_x_assum `DROP t.vs_inst_idx _ = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `DROP _ _ = _ ++ _ ++ l` (fn th => pure_rewrite_tac[th]) >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Resume intcall_prologue_joint_path[retpc]:
  drule_all intcall_entry_materialize_code >> strip_tac >>
  rpt strip_tac >> gvs[]
QED

Resume intcall_prologue_joint_path[path]:
  qpat_assum `gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t)`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[]
QED

Resume intcall_prologue_joint_path[endpoint]:
  asm_rewrite_tac[] >>
  `t'.vs_inst_idx = s.vs_inst_idx +
    LENGTH (DROP (LENGTH st.cs_current_insts) st1.cs_current_insts)` by
    (asm_rewrite_tac[] >> simp[NoAsms, LENGTH_APPEND] >>
     CONV_TAC (AC_CONV (ADD_ASSOC, ADD_COMM))) >>
  simp[venom_state_component_equality] >>
  drule intcall_entry_prefix_code >> strip_tac >>
  drule intcall_materialize_append >> strip_tac >>
  asm_rewrite_tac[] >> simp[LENGTH_APPEND]
QED
Finalise intcall_prologue_joint_path

Theorem intcall_prologue_assemble:
  compile_internal_entry_prefix ce params has_rb st = ((ce1,caps,rpc),stm) /\
  materialize_internal_params ce1 caps stm = (ce2,st2) /\
  (case ret_type of
     SOME ty => if ce.ce_returns_count > 0 then
       do compile_alloc_buffer (type_memory_bytes ce ty); return () od
       else return ()
   | NONE => return ()) st2 = ((),st1) ==>
  compile_internal_prologue ce params has_rb ret_type st = ((ce2,rpc),st1)
Proof
  strip_tac >> drule intcall_entry_prefix_split >> strip_tac >>
  Cases_on `rb` >> Cases_on `ce.ce_return_buf` >>
  TRY (rename1 `ce.ce_return_buf = SOME loc` >> Cases_on `loc`) >>
  gvs[] >>
  simp[compile_internal_prologue_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  qpat_x_assum `_ st2 = ((),st1)` mp_tac >>
  pure_rewrite_tac[comp_ignore_bind_def] >>
  disch_then SUBST1_TAC >> simp[]
QED

Theorem intcall_entry_semantic_cursor:
  (state_rel fn ce cx es (s with vs_inst_idx := idx) <=> state_rel fn ce cx es s) /\
  (immutable_alloca_sep fn ce cx es (s with vs_inst_idx := idx) <=>
    immutable_alloca_sep fn ce cx es s) /\
  (alloca_inv (s with vs_inst_idx := idx) <=> alloca_inv s)
Proof
  simp[state_rel_def, local_ptrs_rel_def, local_region_def, local_backed_def,
    lookup_var_def, storage_rel_def, transient_rel_def, immutables_rel_def,
    logs_rel_def, call_ctx_rel_def, contract_storage_def, contract_transient_def,
    alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
    immutable_alloca_sep_def, immutable_base_zero_alt]
QED

(* One endpoint for the semantic entry and the complete pointer prologue.
   The compile equations are its three constructive factors. *)
Theorem intcall_runtime_prologue_entry_ptr:
  compile_internal_entry_prefix ce params has_rb st = ((ce1,caps,rpc),stm) /\
  materialize_internal_params ce1 caps stm = (ce2,st2) /\
  (case ret_type of
     SOME ty => if ce.ce_returns_count > 0 then
       do compile_alloc_buffer (type_memory_bytes ce ty); return () od
       else return ()
   | NONE => return ()) st2 = ((),st1) /\
  (case ret_type of NONE => T | SOME ty =>
    type_memory_bytes ce ty < dimword (:256)) /\
  fn_has_code st st1 fn /\ fn_inst_ids_distinct fn /\
  setup_callee fn args caller = SOME s /\
  state_rel f ce cx (vs with scopes := []) caller /\
  internal_immutable_regions ce cx vs caller.vs_alloca_next /\
  internal_args_rel ce params src (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\ ~ce.ce_is_ctor /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  fn_has_code st2 st1 fn /\ alloca_room ctx fn s /\
  EVERY (\i. MEM i (fn_insts fn) /\ i.inst_opcode <> INVOKE)
    (DROP (LENGTH st.cs_current_insts) st2.cs_current_insts) /\
  intcall_entry_memory ce params src (if has_rb then 1 else 0) PG tn s /\
  intcall_entry_return ce has_rb d PG s /\
  (!name entry off sz. FLOOKUP src name = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (MemLoc off sz) ==>
    val_footprint entry.type entry.value <= sz) /\
  (if has_rb then 1 else 0) + LENGTH params <= LENGTH args /\
  (if has_rb then 1 else 0) + LENGTH params <= LENGTH PG /\
  (if has_rb then 1 else 0) + LENGTH params < dimword (:256) /\
  fresh_vars_wrt st s /\
  (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
  ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (DROP (LENGTH st.cs_current_insts) st1.cs_current_insts)
    (DROP s.vs_inst_idx bb.bb_instructions) /\ stor_taint_ok cx tn s ==>
  ?t G' tn' u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d (ce2 with ce_alloca_locals := T) cx
      (vs with scopes := [src]) G' tn' t /\
    state_rel fn (ce2 with ce_alloca_locals := T) cx (vs with scopes := [src]) t /\
    immutable_alloca_sep fn (ce2 with ce_alloca_locals := T) cx
      (vs with scopes := [src]) t /\ alloca_inv t /\
    fresh_vars_wrt st1 t /\
    (?x. rpc = Var x /\ not_fresh_at st1 x /\
      lookup_var x t = SOME s.vs_return_pc_token) /\
    (has_rb ==> ?rb. not_fresh_at st1 rb /\ lookup_var rb t = SOME (HD args) /\
      !off sz. ce.ce_return_buf = SOME (MemLoc off sz) ==>
        ce2.ce_return_buf = SOME (PtrVar (Var rb) sz)) /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts st st1) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
    run_inst_seq (emitted_insts st st1) s = OK u /\
    t = u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st1)
Proof
  strip_tac >>
  `s.vs_params = args /\ s.vs_alloca_next = caller.vs_alloca_next /\
   s.vs_memory = caller.vs_memory /\ ~s.vs_halted` by
    (fs[setup_callee_def, AllCaseEqs()] >> gvs[]) >>
  `internal_args_rel ce params src (if has_rb then 1 else 0)
     s.vs_params s.vs_alloca_next s.vs_memory /\
   s.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
   (if has_rb then 1 else 0) + LENGTH params <= LENGTH s.vs_params` by
    asm_rewrite_tac[] >>
  `!name. lookup_scopes name (vs with scopes := [src]).scopes = FLOOKUP src name` by
    (gen_tac >> simp[lookup_scopes_def] >>
     Cases_on `FLOOKUP src name` >> simp[]) >>
  drule_all intcall_prologue_joint_path >>
  disch_then (qspecl_then [`G`,`D`] strip_assume_tac) >>
  drule_all intcall_prologue_assemble >> strip_tac >>
  `run_inst_seq (emitted_insts st st1) s = OK u` by
    simp[emitted_insts_def] >>
  drule_all intcall_runtime_prologue_raw_post >> strip_tac >>
  qexistsl_tac [`t`,`G'`,`tn'`,`u`] >>
  asm_rewrite_tac[intcall_ghost_inv_alloca_locals] >>
  suspend "cursor"
QED

Resume intcall_runtime_prologue_entry_ptr[cursor]:
  simp[intcall_entry_semantic_cursor, emitted_insts_def, lookup_var_def] >>
  fs[lookup_var_def]
QED
Finalise intcall_runtime_prologue_entry_ptr

Theorem intcall_prologue_code_suppliers:
  compile_internal_entry_prefix ce params has_rb st = ((ce1,caps,rpc),stm) /\
  materialize_internal_params ce1 caps stm = (ce2,st2) /\
  (case ret_type of
     SOME ty => if ce.ce_returns_count > 0 then
       do compile_alloc_buffer (type_memory_bytes ce ty); return () od
       else return ()
   | NONE => return ()) st2 = ((),st1) /\ fn_has_code st st1 fn ==>
  fn_has_code st2 st1 fn /\
  EVERY (\i. MEM i (fn_insts fn) /\ i.inst_opcode <> INVOKE)
    (emitted_insts st st1) /\
  EVERY (\i. MEM i (fn_insts fn) /\ i.inst_opcode <> INVOKE)
    (emitted_insts st st2) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st1)
Proof
  strip_tac >> drule intcall_entry_prefix_code >> strip_tac >>
  drule intcall_materialize_append >> strip_tac >>
  drule_all intcall_optional_scratch_append >> strip_tac >>
  conj_tac >- (fs[fn_has_code_def, emitted_blocks_def]) >>
  `EVERY (\i. MEM i (fn_insts fn)) (emitted_insts st st1)` by suspend "members" >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st1)` by suspend "opcodes" >>
  `isPREFIX (emitted_insts st st2) (emitted_insts st st1)` by
    (asm_rewrite_tac[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  fs[EVERY_MEM, rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[MEM_APPEND]
QED

Resume intcall_prologue_code_suppliers[members]:
  qpat_x_assum `fn_has_code st st1 fn` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  simp[EVERY_MEM, emitted_insts_def] >> rpt strip_tac >>
  irule lookup_block_fn_insts >>
  qexistsl_tac [`bb`,`st1.cs_current_bb`] >> simp[] >>
  metis_tac[MEM_DROP_IMP, MEM_APPEND]
QED

Resume intcall_prologue_code_suppliers[opcodes]:
  asm_rewrite_tac[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[EVERY_APPEND, EVERY_GENLIST, mk_inst_def, is_terminator_def] >>
  fs[EVERY_MEM]
QED
Finalise intcall_prologue_code_suppliers


Theorem intcall_prologue_immutable_fields:
  compile_internal_prologue ce params has_rb ret_type st0 = ((ce2,rpc),st1) ==>
  ce2.ce_imm_alloca = ce.ce_imm_alloca /\ ce2.ce_is_ctor = ce.ce_is_ctor
Proof
  strip_tac >> drule intcall_prologue_factor >> strip_tac >>
  drule intcall_entry_prefix_code >> strip_tac >>
  drule intcall_materialize_return_metadata >> simp[]
QED

Theorem intcall_runtime_raw_stmt_post:
  compile_internal_prologue ce params has_rb ret_type st0 = ((ce2,rpc),st1) /\
  fn_has_code st0 st1 fn /\ fn_inst_ids_distinct fn /\
  setup_callee fn args caller = SOME s0 /\
  state_rel f ce cx (vs with scopes := []) caller /\
  internal_immutable_regions ce cx vs caller.vs_alloca_next /\
  internal_args_rel ce params src (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK u /\
  EVERY (\i. MEM i (fn_insts fn) /\ i.inst_opcode <> INVOKE) (emitted_insts st0 st1) /\
  alloca_room ctx fn s0 /\ fmp_room ctx fn s0 ==>
  stmt_state_rel ctx fn (ce2 with ce_alloca_locals := T) cx (vs with scopes := [src]) u
Proof
  strip_tac >> drule_all intcall_runtime_prologue_raw_post >> strip_tac >>
  `u.vs_fmp = s0.vs_fmp` by
    (qpat_x_assum `mat_frame _ _ _` mp_tac >>
     simp[mat_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  `alloca_room ctx fn u` by
    (drule_all intcall_run_inst_seq_alloca_room >> simp[]) >>
  `fmp_room ctx fn u` by
    (drule_all run_inst_seq_fmp_room >> simp[]) >>
  drule intcall_prologue_immutable_fields >> strip_tac >>
  simp[stmt_state_rel_def, immutable_base_zero_alt] >> first_assum ACCEPT_TAC
QED

Theorem intcall_runtime_prologue_stmt_entry_ptr:
  compile_internal_entry_prefix ce params has_rb st = ((ce1,caps,rpc),stm) /\
  materialize_internal_params ce1 caps stm = (ce2,st2) /\
  (case ret_type of
     SOME ty => if ce.ce_returns_count > 0 then
       do compile_alloc_buffer (type_memory_bytes ce ty); return () od
       else return ()
   | NONE => return ()) st2 = ((),st1) /\
  (case ret_type of NONE => T | SOME ty =>
    type_memory_bytes ce ty < dimword (:256)) /\
  fn_has_code st st1 fn /\ fn_inst_ids_distinct fn /\
  setup_callee fn args caller = SOME s /\
  state_rel f ce cx (vs with scopes := []) caller /\
  internal_immutable_regions ce cx vs caller.vs_alloca_next /\
  internal_args_rel ce params src (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  alloca_room ctx fn s /\ fmp_room ctx fn s /\
  intcall_entry_memory ce params src (if has_rb then 1 else 0) PG tn s /\
  intcall_entry_return ce has_rb d PG s /\
  (!name entry off sz. FLOOKUP src name = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (MemLoc off sz) ==>
    val_footprint entry.type entry.value <= sz) /\
  (if has_rb then 1 else 0) + LENGTH params <= LENGTH args /\
  (if has_rb then 1 else 0) + LENGTH params <= LENGTH PG /\
  (if has_rb then 1 else 0) + LENGTH params < dimword (:256) /\
  fresh_vars_wrt st s /\
  (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
  ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (DROP (LENGTH st.cs_current_insts) st1.cs_current_insts)
    (DROP s.vs_inst_idx bb.bb_instructions) /\ stor_taint_ok cx tn s ==>
  ?t G' tn' u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d (ce2 with ce_alloca_locals := T) cx
      (vs with scopes := [src]) G' tn' t /\
    stmt_state_rel ctx fn (ce2 with ce_alloca_locals := T) cx (vs with scopes := [src]) t /\
    fresh_vars_wrt st1 t /\
    (?x. rpc = Var x /\ not_fresh_at st1 x /\
      lookup_var x t = SOME s.vs_return_pc_token) /\
    (has_rb ==> ?rb. not_fresh_at st1 rb /\ lookup_var rb t = SOME (HD args) /\
      !off sz. ce.ce_return_buf = SOME (MemLoc off sz) ==>
        ce2.ce_return_buf = SOME (PtrVar (Var rb) sz)) /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts st st1) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
    run_inst_seq (emitted_insts st st1) s = OK u /\
    t = u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st1)
Proof
  strip_tac >> drule_all intcall_prologue_code_suppliers >> strip_tac >>
  `EVERY (\i. MEM i (fn_insts fn) /\ i.inst_opcode <> INVOKE)
    (DROP (LENGTH st.cs_current_insts) st2.cs_current_insts)` by
    fs[emitted_insts_def] >>
  drule_all intcall_runtime_prologue_entry_ptr >>
  disch_then (qspecl_then [`G`,`D`] strip_assume_tac) >>
  drule_all intcall_prologue_assemble >> strip_tac >>
  drule_all intcall_runtime_raw_stmt_post >> strip_tac >>
  qexistsl_tac [`t`,`G'`,`tn'`,`u`] >> asm_rewrite_tac[] >>
  qpat_x_assum `t = u with vs_inst_idx := _` SUBST_ALL_TAC >>
  fs[stmt_state_rel_inst_idx, lookup_var_def]
QED
