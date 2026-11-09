(*
 * Two runs that agree modulo taint, without relocation
 *
 * Passes that leave some memory of the target unwritten (copy forwarding,
 * dead-store elimination) run on states where the source and target
 * differ only where the pointer discipline lets nothing observe it: at
 * tainted bytes (fresh allocations' unwritten bytes and what was copied
 * from them), at a pass-given dead set X of memory bytes, and in memory
 * at or above the bump allocator, where a returned callee's frames were.
 * Unlike LowerDload and ConcretizeMemLoc no site moves: allocations,
 * the bump pointer and every other frame field are equal, and an
 * operand with no taint evaluates to the same word in both runs.
 *
 * TOP-LEVEL:
 *   taint_agree           — the state relation
 *   taint_agree_step_base — one non-INVOKE step from a reachable state
 *)

Theory taintAgree
Ancestors
  o1LowerDloadRelocationKernel o1LowerDloadShared o1PassContract ptrDiscipline codegenRel contextCodegenRel
  venomExecSemantics venomState finite_map pred_set list

(* s and t agree except at the taint tn, the dead bytes X, and memory at
   or above the bump allocator; call requests agree outside D (their
   snapshots may hold tainted storage).  The fields not listed are
   equal. *)
Definition taint_agree_def:
  taint_agree D X tn s t <=>
    ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
    t with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_accounts := s.vs_accounts; vs_transient := s.vs_transient;
              vs_immutables := s.vs_immutables;
              vs_requests := s.vs_requests |> = s /\
    FDOM t.vs_vars = FDOM s.vs_vars /\
    (!v. v IN FDOM s.vs_vars ==>
         word_agree_except (op_taint tn (Var v))
           (s.vs_vars ' v) (t.vs_vars ' v)) /\
    (!i. i NOTIN X /\ i NOTIN tn.t_mem /\ i < s.vs_alloca_next ==>
         read_byte i s.vs_memory = read_byte i t.vs_memory)
End

Theorem taint_agree_shared:
  taint_agree D X tn s t ==>
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t
Proof
  simp[taint_agree_def]
QED

Theorem taint_agree_frame:
  taint_agree D X tn s t ==>
  t with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_accounts := s.vs_accounts; vs_transient := s.vs_transient;
            vs_immutables := s.vs_immutables;
            vs_requests := s.vs_requests |> = s
Proof
  simp[taint_agree_def]
QED

Theorem taint_agree_labels:
  taint_agree D X tn s t ==> s.vs_labels = t.vs_labels
Proof
  simp[taint_agree_def] >> rpt strip_tac >>
  qpat_x_assum `_ = s`
    (mp_tac o Q.AP_TERM `\u. u.vs_labels`) >> simp[]
QED

Theorem taint_agree_var_domain:
  taint_agree D X tn s t ==> FDOM s.vs_vars = FDOM t.vs_vars
Proof
  simp[taint_agree_def]
QED

Theorem taint_agree_memory:
  taint_agree D X tn s t /\ i NOTIN X /\ i NOTIN tn.t_mem /\
  i < s.vs_alloca_next ==>
  read_byte i s.vs_memory = read_byte i t.vs_memory
Proof
  simp[taint_agree_def]
QED

Theorem taint_agree_operand_defined:
  taint_agree D X tn s t ==>
  (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))
Proof
  strip_tac >>
  drule taint_agree_labels >> drule taint_agree_var_domain >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def, FLOOKUP_DEF] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem taint_agree_operand_value:
  taint_agree D X tn s t /\ eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\
      word_agree_except (op_taint tn op) x y
Proof
  Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, op_taint_def]
  >- (rpt strip_tac >> gvs[] >> simp[word_agree_except_def])
  >- (simp[taint_agree_def, FLOOKUP_DEF] >> rpt strip_tac >>
      gvs[op_taint_def, FLOOKUP_DEF]) >>
  strip_tac >> drule taint_agree_labels >>
  disch_tac >> qexists_tac `x` >> gvs[word_agree_except_def]
QED

Theorem taint_agree_operand_clean:
  taint_agree D X tn s t /\ op_taint tn op = {} ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule taint_agree_operand_defined >>
  disch_then (qspec_then `op` assume_tac) >>
  Cases_on `eval_operand op s`
  >- (Cases_on `eval_operand op t` >> gvs[]) >>
  drule_all taint_agree_operand_value >> strip_tac >> gvs[] >>
  `x = y` by
    (irule ld_value_agree_clean >>
     simp[ld_value_agree_scalar] >> goal_assum (drule_at Any)) >>
  simp[]
QED

Theorem taint_agree_update_var:
  taint_agree D X tn s t /\ word_agree_except m x y ==>
  taint_agree D X
    (tn with t_var := set_var_taint tn.t_var [out] m)
    (update_var out x s) (update_var out y t)
Proof
  simp[taint_agree_def, update_var_def, set_var_taint_def,
       ld_shared_agree_def, op_taint_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> simp[]
  >- gvs[venom_state_component_equality] >>
  Cases_on `v = out` >> gvs[FAPPLY_FUPDATE_THM]
QED

Theorem taint_agree_bind_output:
  taint_agree D X tn s t /\ word_agree_except m x y /\
  bind_outputs [out] [x] s = SOME s' ==>
  ?t'. bind_outputs [out] [y] t = SOME t' /\
       taint_agree D X
         (tn with t_var := set_var_taint tn.t_var [out] m) s' t'
Proof
  simp[bind_outputs_def] >> rpt strip_tac >> gvs[] >>
  irule taint_agree_update_var >> goal_assum (drule_at Any) >> simp[]
QED

Theorem taint_agree_exec_pure1:
  taint_agree D X tn s t /\
  (!op x y. MEM op inst.inst_operands /\
     word_agree_except (op_taint tn op) x y ==>
     word_agree_except m (f x) (f y)) /\
  exec_pure1 f inst s = OK s' ==>
  ?t'. exec_pure1 f inst t = OK t' /\
       taint_agree D X
         (tn with t_var := set_var_taint tn.t_var inst.inst_outputs m) s' t'
Proof
  simp[exec_pure1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all taint_agree_operand_value >> strip_tac >>
  qexists_tac `update_var out (f y) t` >> simp[] >>
  irule taint_agree_update_var >> simp[] >>
  first_x_assum irule >> simp[] >> goal_assum (drule_at Any)
QED

Theorem taint_agree_exec_pure2_clean:
  taint_agree D X tn s t /\
  (!op. MEM op inst.inst_operands ==> op_taint tn op = {}) /\
  exec_pure2 f inst s = OK s' ==>
  ?t'. exec_pure2 f inst t = OK t' /\
       taint_agree D X
         (tn with t_var := set_var_taint tn.t_var inst.inst_outputs {}) s' t'
Proof
  simp[exec_pure2_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `eval_operand op1 s = eval_operand op1 t` by
    (irule taint_agree_operand_clean >> goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand op2 s = eval_operand op2 t` by
    (irule taint_agree_operand_clean >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> irule taint_agree_update_var >>
  simp[word_agree_except_def]
QED

Theorem taint_agree_exec_pure3_clean:
  taint_agree D X tn s t /\
  (!op. MEM op inst.inst_operands ==> op_taint tn op = {}) /\
  exec_pure3 f inst s = OK s' ==>
  ?t'. exec_pure3 f inst t = OK t' /\
       taint_agree D X
         (tn with t_var := set_var_taint tn.t_var inst.inst_outputs {}) s' t'
Proof
  simp[exec_pure3_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `eval_operand op1 s = eval_operand op1 t` by
    (irule taint_agree_operand_clean >> goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand op2 s = eval_operand op2 t` by
    (irule taint_agree_operand_clean >> goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand op3 s = eval_operand op3 t` by
    (irule taint_agree_operand_clean >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> irule taint_agree_update_var >>
  simp[word_agree_except_def]
QED

Theorem taint_agree_assign:
  taint_agree D X tn s t /\ inst.inst_opcode = ASSIGN /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  drule_all taint_agree_operand_value >> strip_tac >>
  qexists_tac `update_var out y t` >> simp[] >>
  `step_taint inst s (update_var out v s) tn =
     tn with t_var := set_var_taint tn.t_var [out] (op_taint tn op1)` by
    (Cases_on `tn` >>
     simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
          imm_taint_def, adopt_reset_def, new_site_bytes_def, update_var_def,
          step_writes_def, source_memory_write_ranges_def, written_taint_def,
          range_bytes_def, FLOOKUP_DEF, SF CONJ_ss,
          taint_component_equality]) >>
  simp[] >> irule taint_agree_update_var >> simp[]
QED

Theorem taint_agree_pure2:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode
    [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; EQ; LT; GT; SLT; SGT;
     AND; OR; XOR; SIGNEXTEND; BYTE; OFFSET] /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  fs[MEM] >> gvs[step_inst_base_opcode_eqs] >>
  drule_all taint_agree_exec_pure2_clean >> strip_tac >>
  qexists_tac `t'` >> simp[] >>
  qpat_x_assum `exec_pure2 _ inst s = _` mp_tac >>
  simp[exec_pure2_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `taint_agree _ _ _ _ _` mp_tac >>
  simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, new_site_bytes_def, update_var_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, FLOOKUP_DEF, SF CONJ_ss, taint_component_equality] >>
  strip_tac >> qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  `mask = tn with t_var := mask.t_var` by
    simp[Abbr `mask`, taint_component_equality] >>
  pop_assum SUBST1_TAC >> simp[Abbr `mask`]
QED

Theorem taint_agree_exec_pure1_clean:
  taint_agree D X tn s t /\
  (!op. MEM op inst.inst_operands ==> op_taint tn op = {}) /\
  exec_pure1 f inst s = OK s' ==>
  ?t'. exec_pure1 f inst t = OK t' /\
       taint_agree D X
         (tn with t_var := set_var_taint tn.t_var inst.inst_outputs {}) s' t'
Proof
  simp[exec_pure1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `eval_operand op1 s = eval_operand op1 t` by
    (drule_all taint_agree_operand_clean >> simp[]) >>
  gvs[] >> irule taint_agree_update_var >>
  simp[word_agree_except_def]
QED

Theorem taint_agree_pure1:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode [ISZERO; NOT] /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  fs[MEM] >> gvs[step_inst_base_opcode_eqs] >>
  drule_all taint_agree_exec_pure1_clean >> strip_tac >>
  qexists_tac `t'` >> simp[] >>
  qpat_x_assum `exec_pure1 _ inst s = _` mp_tac >>
  simp[exec_pure1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `taint_agree _ _ _ _ _` mp_tac >>
  simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, new_site_bytes_def, update_var_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, FLOOKUP_DEF, SF CONJ_ss] >>
  strip_tac >> qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  `mask = tn with t_var := mask.t_var` by
    simp[Abbr `mask`, taint_component_equality] >>
  pop_assum SUBST1_TAC >> simp[Abbr `mask`]
QED

Theorem taint_agree_pure3:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode [ADDMOD; MULMOD] /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  fs[MEM] >> gvs[step_inst_base_opcode_eqs] >>
  drule_all taint_agree_exec_pure3_clean >> strip_tac >>
  qexists_tac `t'` >> simp[] >>
  qpat_x_assum `exec_pure3 _ inst s = _` mp_tac >>
  simp[exec_pure3_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `taint_agree _ _ _ _ _` mp_tac >>
  simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, new_site_bytes_def, update_var_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, FLOOKUP_DEF, SF CONJ_ss,
       taint_fn_updates] >>
  strip_tac >> qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  `mask = tn with t_var := mask.t_var` by
    simp[Abbr `mask`, taint_component_equality] >>
  pop_assum SUBST1_TAC >> simp[Abbr `mask`]
QED

Theorem taint_agree_shift:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode [SHL; SHR; SAR] /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >> fs[MEM] >>
  gvs[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()] >>
  `op_taint tn op1 = {}` by
    (fs[taint_ok_def] >> spose_not_then assume_tac >>
     first_x_assum (qspec_then `op1` mp_tac) >> simp[]) >>
  `eval_operand op1 s = eval_operand op1 t` by
    (drule_all taint_agree_operand_clean >> simp[]) >>
  drule_all taint_agree_operand_value >> strip_tac >>
  gvs[] >>
  (imp_res_tac word_agree_except_shl >>
   imp_res_tac word_agree_except_shr >>
   imp_res_tac word_agree_except_sar) >>
  simp[step_taint_def, mem_taint_def, out_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def, new_site_bytes_def,
       update_var_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, FLOOKUP_DEF, SF CONJ_ss] >>
  qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  `mask = tn with t_var := mask.t_var` by
    simp[Abbr `mask`, taint_component_equality] >>
  pop_assum SUBST1_TAC >>
  rewrite_tac[GSYM update_var_def] >>
  simp[Abbr `mask`] >> irule taint_agree_update_var >> simp[]
QED

(* Why it holds: taint_ok gives each operand of a non-propagating opcode
   no taint, so taint_agree evaluates it equally in t; access_ok puts
   each read ending above lo inside a site, below the bump pointer since
   the root starts with no allocations
   (o1LowerDloadOccurrenceTheory.frame_reachable_occurrence_annotation),
   and distinct block labels (o1_ctx_shape) keep in_revert_forward from
   switching access_ok off except at REVERT and its RETURNDATACOPY;
   taint_ok keeps tainted bytes away from reads other than MLOAD, ILOAD,
   MCOPY and RETURN; the read premise keeps X away.  The propagating
   opcodes (ASSIGN, shifts, MLOAD/ILOAD, MSTORE/ISTORE, MCOPY,
   SLOAD/TLOAD, SSTORE/TSTORE) move taint exactly as step_taint says:
   word_agree_except_shl/shr/sar, ld_mload_masked_bytes, ld_mstore_bytes,
   ld_shared_sstore/tstore.  A step that records a call request needs
   taint_within's first clause for the request's snapshot.  A fresh ALLOCA lands at the same offset in
   both runs and new_site_bytes taints what it claims above the old bump
   pointer.  RET's operands carry no taint, so the returned values are
   equal.  At a halt, taint_within puts the remaining taint (and RETURN's
   tainted bytes, ret_taint) inside D: ld_shared_halt_result. *)
Theorem taint_agree_step_base:
  !vs C stk PG G tn fn inst s t D X lo r.
    frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
    o1_ctx_shape C /\ MEM fn C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
    ptr_discipline lo C vs /\ ~ctx_has_dalloca C /\
    taint_within D C vs /\ dead_wf D /\
    inst.inst_opcode <> INVOKE /\
    taint_agree D X tn s t /\
    (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
                 off <= i /\ i < off + len ==> i NOTIN X) /\
    step_inst_base inst s = r /\ terminates r ==>
    (!s'. r = OK s' ==>
          ?t'. step_inst_base inst t = OK t' /\
               taint_agree D X (step_taint inst s s' tn) s' t') /\
    (!v s'. r = IntRet v s' ==>
          ?t'. step_inst_base inst t = IntRet v t' /\
               taint_agree D X tn s' t') /\
    (!s'. r = Halt s' ==>
          ?t'. step_inst_base inst t = Halt t' /\
               dead_result_rel D (Halt s') (Halt t')) /\
    (!a s'. r = Abort a s' ==>
          ?t'. step_inst_base inst t = Abort a t')
Proof
  cheat
QED
