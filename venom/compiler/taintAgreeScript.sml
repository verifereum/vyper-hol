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
  o1LowerDloadJointExternal
  o1LowerDloadConcreteExternal o1LowerDloadExternalEffects o1LowerDloadExternalOracle
  o1LowerDloadPrecompileEffects extCallOracle
  o1LowerDloadHaltResult o1LowerDloadJointStorageWrite o1LowerDloadStackFrontier
  o1LowerDloadRangeTransport o1LowerDloadJointMemoryRead o1LowerDloadJointRead1
  o1LowerDloadMemoryConsumer o1LowerDloadJointInternalEffects
  o1LowerDloadRelocationKernel o1LowerDloadShared o1PassContract ptrDiscipline codegenRel contextCodegenRel
  venomExecSemantics venomCallOracleDefs venomState finite_map pred_set list

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

Theorem taint_agree_call_ctx:
  taint_agree D X tn s t ==> s.vs_call_ctx = t.vs_call_ctx
Proof
  strip_tac >> drule taint_agree_frame >>
  disch_then (mp_tac o Q.AP_TERM `\u. u.vs_call_ctx`) >> simp[]
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

Theorem taint_agree_reachable_read_byte:
  frame_reachable vs C stk PG G tn fn inst s /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  taint_agree D X tn s t /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN X) /\
  MEM (off,len) (source_memory_read_ranges inst s) /\
  off <= i /\ i < off + len /\ i NOTIN tn.t_mem ==>
  read_byte i s.vs_memory = read_byte i t.vs_memory
Proof
  strip_tac >> irule taint_agree_memory >>
  `i < s.vs_alloca_next` by
    (irule ld_frame_reachable_read_byte_bound >> metis_tac[]) >>
  metis_tac[]
QED

Theorem taint_agree_reachable_clean_read:
  frame_reachable vs C stk PG G tn fn inst s /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  taint_agree D X tn s t /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN X) /\
  MEM (off,len) (source_memory_read_ranges inst s) /\
  (!i. off <= i /\ i < off + len ==> i NOTIN tn.t_mem) ==>
  read_memory off len s = read_memory off len t
Proof
  strip_tac >> irule LIST_EQ >> simp[ld_read_memory_length] >>
  rpt strip_tac >> simp[ld_read_memory_element] >>
  irule taint_agree_reachable_read_byte >>
  qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
  qpat_assum `ptr_discipline _ _ _` (irule_at Any) >>
  qexistsl_tac [`off`, `len`] >> simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem taint_agree_request_snapshots:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode <> INVOKE /\ taint_within D C vs /\
  taint_agree D X tn s t /\ step_inst_base inst s = OK s' /\
  LENGTH s.vs_requests < LENGTH s'.vs_requests ==>
  accounts_agree_except D s.vs_accounts t.vs_accounts /\
  transient_agree_except D s.vs_transient t.vs_transient
Proof
  strip_tac >>
  `step_inst 0 C inst s = OK s'` by simp[step_inst_non_invoke] >>
  `tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
   tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address)` by
    (fs[taint_within_def] >> metis_tac[]) >>
  drule taint_agree_shared >>
  metis_tac[ld_shared_accounts_observe, ld_shared_transient_observe]
QED

Theorem taint_agree_external_clean_shared:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ptr_discipline lo C vs /\
  MEM inst.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
  taint_agree D X tn s t ==>
  tn.t_stor = {} /\ tn.t_trans = {} /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `tn.t_stor = {} /\ tn.t_trans = {}` by
    (fs[taint_ok_def, MEM] >> metis_tac[]) >>
  drule taint_agree_shared >>
  metis_tac[ld_shared_clean_accounts, ld_shared_clean_transient]
QED

Theorem taint_agree_external_update:
  taint_agree D X tn s t /\ tn'.t_var = tn.t_var /\
  r1 = s with <|vs_memory := m1; vs_accounts := a1; vs_transient := tr1;
    vs_logs := l1; vs_outcomes := o1; vs_requests := q1;
    vs_pending_deletions := p1; vs_returndata := rd|> /\
  r2 = t with <|vs_memory := m2; vs_accounts := a2; vs_transient := tr2;
    vs_logs := l2; vs_outcomes := o2; vs_requests := q2;
    vs_pending_deletions := p2; vs_returndata := rd|> /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn' r1 r2 /\
  (!i. i NOTIN X /\ i NOTIN tn'.t_mem /\ i < s.vs_alloca_next ==>
     read_byte i m1 = read_byte i m2) ==>
  taint_agree D X tn' r1 r2
Proof
  strip_tac >>
  `l1 = l2 /\ o1 = o2 /\ p1 = p2` by gvs[ld_shared_agree_def] >>
  gvs[taint_agree_def, op_taint_def] >>
  qpat_x_assum `_ = s` (mp_tac o Q.AP_TERM
    `\u. u with <|vs_memory := m1; vs_accounts := a1; vs_transient := tr1;
      vs_logs := l1; vs_outcomes := o1; vs_requests := q1;
      vs_pending_deletions := p1; vs_returndata := rd|>`) >>
  simp[venom_state_fupdcanon]
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

Theorem taint_agree_jump_to:
  taint_agree D X tn s t ==>
  taint_agree D X tn (jump_to lbl s) (jump_to lbl t)
Proof
  simp[taint_agree_def, jump_to_def, ld_shared_agree_def] >>
  rpt strip_tac >> simp[] >> gvs[venom_state_component_equality]
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

Theorem taint_agree_update_two_clean:
  taint_agree D X tn s t ==>
  taint_agree D X
    (tn with t_var := set_var_taint tn.t_var [p;q] {})
    (update_var q y (update_var p x s))
    (update_var q y (update_var p x t))
Proof
  simp[taint_agree_def, update_var_def, set_var_taint_def,
       ld_shared_agree_def, op_taint_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> simp[]
  >- gvs[venom_state_component_equality] >>
  Cases_on `v = q` >> gvs[FAPPLY_FUPDATE_THM, word_agree_except_def] >>
  Cases_on `v = p` >> gvs[FAPPLY_FUPDATE_THM, word_agree_except_def]
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

Theorem taint_agree_external_operands:
  taint_ok fn tn inst s /\ taint_agree D X tn s t /\
  MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
  !op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t
Proof
  rpt strip_tac >> irule taint_agree_operand_clean >>
  gvs[taint_ok_def, MEM] >> metis_tac[]
QED

Theorem taint_agree_external_read:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  taint_agree D X tn s t /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN X) /\
  MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  MEM (off,len) (source_memory_read_ranges inst s) ==>
  read_memory off len s = read_memory off len t
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `wf_function fn /\ fn_inst_wf fn` by
    (gvs[o1PassContractTheory.o1_ctx_shape_def, listTheory.EVERY_MEM] >>
     metis_tac[o1PassContractTheory.o1_fn_shape_def]) >>
  `~in_revert_forward fn s` by
    (spose_not_then assume_tac >>
     gvs[in_revert_forward_def, active_inst_def] >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
       (irule venomExecPropsTheory.MEM_lookup_block >>
        gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]) >>
     gvs[] >>
     `get_instruction bb s.vs_inst_idx = SOME (EL s.vs_inst_idx bb.bb_instructions)` by
       simp[venomInstTheory.get_instruction_def] >>
     drule_all memSafeRunTheory.revert_forward_at_opcode >> fs[MEM]) >>
  irule taint_agree_reachable_clean_read >>
  qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
  qpat_assum `ptr_discipline _ _ _` (irule_at Any) >> simp[] >>
  gvs[taint_ok_def, about_to_revert_def, MEM] >> metis_tac[]
QED

Theorem taint_agree_read_fields:
  taint_agree D X tn s t ==>
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_tx_ctx = t.vs_tx_ctx /\
  s.vs_block_ctx = t.vs_block_ctx /\ s.vs_code = t.vs_code /\
  s.vs_returndata = t.vs_returndata
Proof
  strip_tac >> drule taint_agree_frame >>
  simp[venom_state_component_equality]
QED

Theorem taint_agree_scalar_fields:
  taint_agree D X tn s t ==>
  s.vs_params = t.vs_params /\
  s.vs_return_pc_token = t.vs_return_pc_token /\
  s.vs_initial_fmp = t.vs_initial_fmp
Proof
  strip_tac >> drule taint_agree_frame >>
  simp[venom_state_component_equality]
QED

Theorem taint_agree_gas_readings_update:
  taint_agree D X tn s t ==>
  taint_agree D X tn (s with vs_gas_readings := rs)
    (t with vs_gas_readings := rs)
Proof
  simp[taint_agree_def] >> strip_tac >>
  conj_tac >- metis_tac[ld_shared_agree_gas_readings_update] >>
  gvs[venom_state_component_equality]
QED

Theorem taint_agree_exec_read0_clean:
  taint_agree D X tn s t /\ f s = f t /\
  exec_read0 f inst s = OK s' ==>
  ?t'. exec_read0 f inst t = OK t' /\
       taint_agree D X
         (tn with t_var := set_var_taint tn.t_var inst.inst_outputs {}) s' t'
Proof
  simp[exec_read0_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  irule taint_agree_update_var >> simp[word_agree_except_def]
QED

Theorem taint_agree_exec_read1_clean:
  taint_agree D X tn s t /\ (!v. f v s = f v t) /\
  (!op. MEM op inst.inst_operands ==> op_taint tn op = {}) /\
  exec_read1 f inst s = OK s' ==>
  ?t'. exec_read1 f inst t = OK t' /\
       taint_agree D X
         (tn with t_var := set_var_taint tn.t_var inst.inst_outputs {}) s' t'
Proof
  simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `eval_operand op1 s = eval_operand op1 t` by
    (drule_all taint_agree_operand_clean >> simp[]) >>
  gvs[] >> irule taint_agree_update_var >> simp[word_agree_except_def]
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

Theorem taint_agree_allocation_fields:
  taint_agree D X tn s t ==>
  s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next
Proof
  disch_then (mp_tac o MATCH_MP taint_agree_frame) >>
  simp[venom_state_component_equality]
QED

Theorem taint_agree_alloca_fresh:
  taint_agree D X tn s t /\ s.vs_allocas = t.vs_allocas /\
  s.vs_alloca_next = t.vs_alloca_next ==>
  taint_agree D X
    (tn with t_mem := tn.t_mem UNION
      {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+sz})
    (s with <|vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,sz));
              vs_alloca_next := s.vs_alloca_next+sz|>)
    (t with <|vs_allocas := t.vs_allocas |+ (id,(t.vs_alloca_next,sz));
              vs_alloca_next := t.vs_alloca_next+sz|>)
Proof
  simp[taint_agree_def, ld_shared_agree_def, op_taint_def] >>
  rpt strip_tac >> simp[]
  >- (qpat_x_assum `_ = s`
        (mp_tac o Q.AP_TERM `\u. u with
          <|vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,sz));
            vs_alloca_next := s.vs_alloca_next+sz|>`) >> simp[]) >>
  first_x_assum irule >> simp[] >> decide_tac
QED

Theorem taint_agree_alloca_step:
  taint_agree D X tn s t /\ inst.inst_opcode = ALLOCA /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next` by
    metis_tac[taint_agree_allocation_fields] >>
  gvs[step_inst_base_opcode_eqs, exec_alloca_def, AllCaseEqs()] >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  qabbrev_tac `mask0 = tn with t_mem := mask.t_mem` >>
  `mask = mask0 with t_var := set_var_taint mask0.t_var [out] {}` by
    simp[Abbr `mask0`, Abbr `mask`, step_taint_def, out_taint_def, store_taint_def,
         imm_taint_def, adopt_reset_def, eval_operand_def,
         taint_component_equality] >>
  pop_assum SUBST1_TAC >>
  irule taint_agree_update_var >> simp[word_agree_except_def] >>
  simp[Abbr `mask0`, Abbr `mask`, step_taint_def, mem_taint_def, new_site_bytes_def,
       update_var_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, FLOOKUP_DEF, SF CONJ_ss] >>
  `inst.inst_id NOTIN FDOM t.vs_allocas` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  simp[] >> drule_all taint_agree_alloca_fresh >>
  disch_then (qspecl_then [`w2n alloc_size`, `inst.inst_id`] mp_tac) >> simp[]
QED

Theorem taint_agree_allocation_step:
  taint_agree D X tn s t /\ active_inst fn inst s /\
  MEM fn C.ctx_functions /\ ~ctx_has_dalloca C /\
  MEM inst.inst_opcode [ALLOCA; DALLOCA] ==>
  (!s'. step_inst_base inst s = OK s' ==>
    ?t'. step_inst_base inst t = OK t' /\
         taint_agree D X (step_taint inst s s' tn) s' t') /\
  (!v s'. step_inst_base inst s = IntRet v s' ==>
    ?t'. step_inst_base inst t = IntRet v t' /\ taint_agree D X tn s' t') /\
  (!s'. step_inst_base inst s = Halt s' ==>
    ?t'. step_inst_base inst t = Halt t' /\ dead_result_rel D (Halt s') (Halt t')) /\
  (!a s'. step_inst_base inst s = Abort a s' ==>
    ?t'. step_inst_base inst t = Abort a t')
Proof
  strip_tac >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, venomInstTheory.fn_insts_def,
        o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `inst.inst_opcode <> DALLOCA` by
    (fs[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]) >>
  gvs[MEM] >> conj_tac
  >- metis_tac[taint_agree_alloca_step] >>
  rpt conj_tac >> rpt strip_tac >>
  gvs[step_inst_base_opcode_eqs, exec_alloca_def, AllCaseEqs()]
QED

Theorem taint_agree_memory_update:
  taint_agree D X tn s t /\
  (!i. i NOTIN X /\ i NOTIN M /\ i < s.vs_alloca_next ==>
       read_byte i ms = read_byte i mt) ==>
  taint_agree D X (tn with t_mem := M)
    (s with vs_memory := ms) (t with vs_memory := mt)
Proof
  simp[taint_agree_def, ld_shared_agree_def, op_taint_def] >>
  rpt strip_tac >> simp[] >>
  qpat_x_assum `_ = s` (mp_tac o Q.AP_TERM `\u. u with vs_memory := ms`) >>
  simp[]
QED

Theorem taint_agree_write_memory:
  taint_agree D X tn s t /\ LENGTH xs = len /\ LENGTH ys = len /\
  (tn.t_mem DIFF {i | a <= i /\ i < a+len}) SUBSET M /\
  (!k. k < len /\ a+k NOTIN M ==> EL k xs = EL k ys) ==>
  taint_agree D X (tn with t_mem := M)
    (write_memory_with_expansion a xs s) (write_memory_with_expansion a ys t)
Proof
  strip_tac >>
  `write_memory_with_expansion a xs s =
     s with vs_memory := (write_memory_with_expansion a xs s).vs_memory` by
    simp[write_memory_with_expansion_def] >>
  `write_memory_with_expansion a ys t =
     t with vs_memory := (write_memory_with_expansion a ys t).vs_memory` by
    simp[write_memory_with_expansion_def] >>
  pop_assum SUBST1_TAC >> pop_assum SUBST1_TAC >>
  irule taint_agree_memory_update >>
  qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
  gen_tac >> disch_tac >>
  simp[regularCallEmitSimTheory.read_byte_write_memory_with_expansion] >>
  Cases_on `a <= i /\ i < a+len` >> simp[] >>
  irule taint_agree_memory >>
  qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
  gvs[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem taint_agree_consume_call_memory:
  taint_agree D X tn s t /\ tn'.t_var = tn.t_var /\
  consume_call_outcome rq1 ro rs s = (w1,r1) /\
  consume_call_outcome rq2 ro rs t = (w2,r2) /\
  r1.vs_returndata = r2.vs_returndata /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn' r1 r2 /\
  (tn.t_mem DIFF {i | ro <= i /\
       i < ro + LENGTH (TAKE rs r1.vs_returndata)}) SUBSET tn'.t_mem ==>
  taint_agree D X tn' r1 r2
Proof
  strip_tac >>
  `r1 = s with <|vs_memory :=
      (write_memory_with_expansion ro (TAKE rs r1.vs_returndata) s).vs_memory;
    vs_accounts := r1.vs_accounts; vs_transient := r1.vs_transient;
    vs_logs := r1.vs_logs; vs_outcomes := r1.vs_outcomes;
    vs_requests := r1.vs_requests; vs_pending_deletions := r1.vs_pending_deletions;
    vs_returndata := r1.vs_returndata|>` by
    (qpat_x_assum `consume_call_outcome _ _ _ s = _` mp_tac >>
     pure_rewrite_tac[consume_call_outcome_eq, pairTheory.PAIR_EQ] >>
     strip_tac >> gvs[]) >>
  `r2 = t with <|vs_memory :=
      (write_memory_with_expansion ro (TAKE rs r1.vs_returndata) t).vs_memory;
    vs_accounts := r2.vs_accounts; vs_transient := r2.vs_transient;
    vs_logs := r2.vs_logs; vs_outcomes := r2.vs_outcomes;
    vs_requests := r2.vs_requests; vs_pending_deletions := r2.vs_pending_deletions;
    vs_returndata := r1.vs_returndata|>` by
    (qpat_x_assum `consume_call_outcome _ _ _ t = _` mp_tac >>
     pure_rewrite_tac[consume_call_outcome_eq, pairTheory.PAIR_EQ] >>
     strip_tac >> gvs[]) >>
  `taint_agree D X (tn with t_mem := tn'.t_mem)
     (write_memory_with_expansion ro (TAKE rs r1.vs_returndata) s)
     (write_memory_with_expansion ro (TAKE rs r1.vs_returndata) t)` by
    (irule taint_agree_write_memory >> simp[] >> metis_tac[]) >>
  irule taint_agree_external_update >>
  qpat_assum `taint_agree D X tn s t` (irule_at Any) >>
  qpat_assum `r1 = _` (irule_at Any) >>
  qpat_assum `r2 = _` (irule_at Any) >>
  simp[] >> rpt strip_tac >>
  drule taint_agree_memory >> simp[] >> disch_then irule >> simp[]
QED

Theorem taint_agree_consume_call:
  taint_agree D X tn s t /\
  ((computed_precompile rq1 /\ computed_precompile rq2 /\
    rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data) \/
   request_agree_except D rq1 rq2) /\
  rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
  rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
  consume_call_outcome rq1 ro rs s = (w1,r1) /\
  consume_call_outcome rq2 ro rs t = (w2,r2) ==>
  w1 = w2 /\
  taint_agree D X
    (tn with <|t_mem := tn.t_mem DIFF
        {i | ro <= i /\ i < ro + LENGTH (TAKE rs r1.vs_returndata)};
      t_stor := if ~rq1.cr_static /\ r1.vs_requests <> s.vs_requests /\
        r1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
        then {} else tn.t_stor;
      t_trans := if ~rq1.cr_static /\ r1.vs_requests <> s.vs_requests /\
        r1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
        then {} else tn.t_trans|>) r1 r2
Proof
  strip_tac
  >- (`ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by
        metis_tac[taint_agree_shared] >>
      `r1.vs_requests = s.vs_requests` by
        (qpat_x_assum `consume_call_outcome rq1 _ _ s = _` mp_tac >>
         simp[consume_call_outcome_eq, record_request_def] >>
         strip_tac >> gvs[]) >>
      drule_all ld_consume_precompile_shared >> strip_tac >>
      simp[Excl "consume_call_outcome_eq"] >>
      irule taint_agree_consume_call_memory >>
      qpat_assum `taint_agree D X tn s t` (irule_at Any) >>
      qpat_assum `consume_call_outcome rq1 _ _ _ = _` (irule_at Any) >>
      qpat_assum `consume_call_outcome rq2 _ _ _ = _` (irule_at Any) >>
      simp[Excl "consume_call_outcome_eq"] >>
      fs[ld_shared_agree_def, Excl "consume_call_outcome_eq"]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by
    metis_tac[taint_agree_shared] >>
  `s.vs_outcomes = t.vs_outcomes /\
   LIST_REL (request_agree_except D) s.vs_requests t.vs_requests` by
    fs[ld_shared_agree_def] >>
  drule_all ld_consume_call_outcome_masked_observation >> strip_tac >>
  simp[Excl "consume_call_outcome_eq"] >>
  drule_all ld_consume_call_outcome_shared_effects >> strip_tac >>
  irule taint_agree_consume_call_memory >>
  qpat_assum `taint_agree D X tn s t` (irule_at Any) >>
  qpat_assum `consume_call_outcome rq1 _ _ _ = _` (irule_at Any) >>
  qpat_assum `consume_call_outcome rq2 _ _ _ = _` (irule_at Any) >>
  simp[Excl "consume_call_outcome_eq"] >>
  fs[ld_shared_agree_def, Excl "consume_call_outcome_eq"] >> metis_tac[]
QED

Theorem taint_agree_consume_call_request:
  taint_agree D X tn s t /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n ao) (w2n az) t /\
  (computed_precompile (venom_call_request s addr value ao az static) \/
   (accounts_agree_except D s.vs_accounts t.vs_accounts /\
    transient_agree_except D s.vs_transient t.vs_transient)) /\
  consume_call_outcome (venom_call_request s addr value ao az static) ro rs s = (w,r) ==>
  ?u. consume_call_outcome (venom_call_request t addr value ao az static) ro rs t = (w,u) /\
    taint_agree D X
      (tn with <|t_mem := tn.t_mem DIFF
        {i | ro <= i /\ i < ro + LENGTH (TAKE rs r.vs_returndata)};
       t_stor := if ~(static \/ s.vs_call_ctx.cc_static) /\
         r.vs_requests <> s.vs_requests /\ r.vs_outcomes <> s.vs_outcomes /\
         (HD s.vs_outcomes).co_success then {} else tn.t_stor;
       t_trans := if ~(static \/ s.vs_call_ctx.cc_static) /\
         r.vs_requests <> s.vs_requests /\ r.vs_outcomes <> s.vs_outcomes /\
         (HD s.vs_outcomes).co_success then {} else tn.t_trans|>) r u
Proof
  rpt gen_tac >> disch_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[taint_agree_call_ctx] >>
  `((computed_precompile (venom_call_request s addr value ao az static) /\
     computed_precompile (venom_call_request t addr value ao az static) /\
     (venom_call_request s addr value ao az static).cr_target =
       (venom_call_request t addr value ao az static).cr_target /\
     (venom_call_request s addr value ao az static).cr_data =
       (venom_call_request t addr value ao az static).cr_data) \/
    request_agree_except D (venom_call_request s addr value ao az static)
      (venom_call_request t addr value ao az static))` by
    (fs[Excl "consume_call_outcome_eq"]
     >- (disj1_tac >> gvs[computed_precompile_def, venom_call_request_def,
           Excl "consume_call_outcome_eq"]) >>
     disj2_tac >> irule ld_venom_call_request_masked >>
     simp[Excl "consume_call_outcome_eq"]) >>
  Cases_on `consume_call_outcome (venom_call_request t addr value ao az static) ro rs t` >>
  fs[Excl "consume_call_outcome_eq"] >>
  qpat_assum `consume_call_outcome _ _ _ s = _`
    (mp_then Any mp_tac taint_agree_consume_call) >>
  disch_then drule >>
  disch_then (drule_at (Pat `consume_call_outcome _ _ _ _ = _`)) >>
  (impl_tac >- simp[venom_call_request_def, Excl "consume_call_outcome_eq"]) >>
  strip_tac >>
  gvs[venom_call_request_def, Excl "consume_call_outcome_eq"]
QED

Theorem taint_agree_consume_create:
  taint_agree D X tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  consume_create_outcome rq s = (w,r) ==>
  ?u. consume_create_outcome rq t = (w,u) /\ taint_agree D X tn r u
Proof
  strip_tac >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by
    metis_tac[taint_agree_shared] >>
  `s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient` by
    metis_tac[ld_shared_clean_accounts, ld_shared_clean_transient] >>
  `s.vs_outcomes = t.vs_outcomes /\ s.vs_logs = t.vs_logs /\
   s.vs_pending_deletions = t.vs_pending_deletions` by fs[ld_shared_agree_def] >>
  drule_all ld_consume_create_outcome_transport >> strip_tac >>
  qmatch_asmsub_abbrev_tac `consume_create_outcome rq t = (w,u)` >>
  qexists_tac `u` >> simp[Excl "consume_create_outcome_eq"] >>
  qpat_assum `r = _` (fn th => once_rewrite_tac[th]) >>
  simp[Abbr `u`, taint_agree_def, ld_shared_agree_def, word_agree_except_def,
       Excl "consume_create_outcome_eq"] >>
  gvs[taint_agree_def, ld_shared_agree_def, word_agree_except_def,
      Excl "consume_create_outcome_eq"] >>
  conj_tac
  >- (Cases_on `computed_precompile rq` >>
      simp[record_request_def, LIST_REL_APPEND, request_agree_except_def,
        accounts_agree_except_def, transient_agree_except_def,
        storage_agree_except_def, word_agree_except_def]) >>
  qpat_x_assum `_ = s` (mp_tac o Q.AP_TERM
    `\v. v with <|vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
      vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
      vs_pending_deletions := r.vs_pending_deletions;
      vs_returndata := r.vs_returndata;
      vs_requests := record_request rq s.vs_requests|>`) >>
  simp[venom_state_fupdcanon]
QED

Theorem taint_agree_local_fields:
  taint_agree D X tn s t ==> ld_joint_local_fields s t
Proof
  simp[taint_agree_def, o1LowerDloadJointRelationTheory.ld_joint_local_fields_def] >>
  strip_tac >>
  qpat_x_assum `_ = s` (fn th => once_rewrite_tac[GSYM th]) >> simp[]
QED

Theorem taint_agree_extract_concrete:
  taint_agree D X tn s t /\
  extract_venom_result s v ro rs rr = SOME (w,r) ==>
  taint_agree D X
    (tn with t_mem := tn.t_mem DIFF
      {i | ro <= i /\ i < ro + LENGTH (TAKE rs r.vs_returndata)})
    r (t with <|vs_returndata := r.vs_returndata;
      vs_accounts := r.vs_accounts; vs_logs := r.vs_logs;
      vs_transient := r.vs_transient;
      vs_pending_deletions := r.vs_pending_deletions;
      vs_memory := (write_memory_with_expansion ro
        (TAKE rs r.vs_returndata) t).vs_memory|>)
Proof
  strip_tac >> drule ld_extract_concrete_shape >> strip_tac >>
  `taint_agree D X (tn with t_mem := tn.t_mem DIFF
      {i | ro <= i /\ i < ro + LENGTH (TAKE rs r.vs_returndata)})
    (write_memory_with_expansion ro (TAKE rs r.vs_returndata) s)
    (write_memory_with_expansion ro (TAKE rs r.vs_returndata) t)` by
    (irule taint_agree_write_memory >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >> simp[]) >>
  qpat_assum `r = _` (fn th => once_rewrite_tac[th]) >>
  gvs[taint_agree_def, ld_shared_agree_def, word_agree_except_def,
    op_taint_def, write_memory_with_expansion_def, write_memory_def] >>
  reverse conj_tac >- metis_tac[] >>
  qpat_x_assum `_ = s` (mp_tac o Q.AP_TERM
    `\z. z with <|vs_memory := (write_memory_with_expansion ro
       (TAKE rs r.vs_returndata) s).vs_memory;
      vs_transient := r.vs_transient; vs_returndata := r.vs_returndata;
      vs_accounts := r.vs_accounts; vs_logs := r.vs_logs;
      vs_pending_deletions := r.vs_pending_deletions|>`) >>
  simp[write_memory_with_expansion_def, write_memory_def, venom_state_fupdcanon]
QED

Theorem taint_agree_exec_delegatecall:
  taint_agree D X tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off) (w2n sz) t /\
  exec_delegatecall inst s (gas:256 word) (addr:256 word) (off:256 word)
    (sz:256 word) (ro:256 word) (rs:256 word) = OK s' ==>
  ?out w r u. inst.inst_outputs = [out] /\ s' = update_var out w r /\
    exec_delegatecall inst t gas addr off sz ro rs = OK (update_var out w u) /\
    r.vs_allocas = s.vs_allocas /\ r.vs_fmp = s.vs_fmp /\
    taint_agree D X
      ((tn with t_mem := tn.t_mem DIFF
        {i | w2n ro <= i /\ i < w2n ro + LENGTH (TAKE (w2n rs) r.vs_returndata)})
       with t_var := set_var_taint tn.t_var [out] {}) s' (update_var out w u)
Proof
  strip_tac >>
  `ld_joint_local_fields s t` by metis_tac[taint_agree_local_fields] >>
  `s.vs_logs = t.vs_logs /\ s.vs_pending_deletions = t.vs_pending_deletions` by
    fs[taint_agree_def, ld_shared_agree_def] >>
  drule_all (INST_TYPE
    (map (fn ty => ty |-> ``:256``)
      (type_vars_in_term (concl ld_exec_delegatecall_transport)))
    ld_exec_delegatecall_transport) >>
  disch_then (qspec_then `ro` strip_assume_tac) >>
  drule_all taint_agree_extract_concrete >> strip_tac >>
  drule ld_extract_concrete_shape >> strip_tac >>
  `r.vs_allocas = s.vs_allocas /\ r.vs_fmp = s.vs_fmp` by
    (qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  gvs[] >> qexistsl_tac [`w`, `r`] >>
  qmatch_asmsub_abbrev_tac `exec_delegatecall inst t gas addr off sz ro rs = OK (update_var out w u)` >>
  qexists_tac `u` >> simp[] >>
  qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  `mask = (tn with t_mem := mask.t_mem) with
     t_var := set_var_taint (tn with t_mem := mask.t_mem).t_var [out] {}` by
    simp[Abbr `mask`, taint_component_equality] >>
  pop_assum SUBST1_TAC >>
  irule taint_agree_update_var >>
  simp[Abbr `mask`, word_agree_except_def]
QED

Theorem taint_agree_delegatecall_mask:
  inst.inst_opcode = DELEGATECALL /\ inst.inst_outputs = [out] /\
  out_taint tn inst s = {} /\
  source_memory_write_ranges inst s = [(ro,rs)] /\
  r.vs_allocas = s.vs_allocas /\ r.vs_fmp = s.vs_fmp ==>
  step_taint inst s (update_var out w r) tn =
    (tn with t_mem := tn.t_mem DIFF
      {i | ro <= i /\ i < ro + LENGTH (TAKE rs r.vs_returndata)}) with
    t_var := set_var_taint tn.t_var [out] {}
Proof
  strip_tac >>
  `written_taint tn inst s = {}` by
    (simp[written_taint_def] >> rpt CASE_TAC >> simp[]) >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
    store_taint_def, imm_taint_def, adopt_reset_def,
    range_bytes_def, update_var_def, taint_component_equality,
    LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF, FLOOKUP_DEF, SF CONJ_ss] >>
  rpt IF_CASES_TAC >> gvs[arithmeticTheory.LESS_OR_EQ]
QED

Theorem taint_agree_delegatecall_ok:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ptr_discipline lo C vs /\ ~ctx_has_dalloca C /\
  taint_agree D X tn s t /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN X) /\
  inst.inst_opcode = DELEGATECALL /\ step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
    taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `tn.t_stor = {} /\ tn.t_trans = {} /\
   s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient` by
    (irule taint_agree_external_clean_shared >>
     qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ptr_discipline _ _ _` (irule_at Any) >> simp[]) >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_external_operands >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_ok _ _ _ _` (irule_at Any) >> simp[]) >>
  `!off len. MEM (off,len) (source_memory_read_ranges inst s) ==>
     read_memory off len s = read_memory off len t` by
    (rpt strip_tac >> irule taint_agree_external_read >>
     qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ptr_discipline _ _ _` (irule_at Any) >> simp[] >> gvs[]) >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  `read_memory (w2n ao) (w2n as_) s =
   read_memory (w2n ao) (w2n as_) t` by
    (first_x_assum irule >>
     gvs[source_memory_read_ranges_def, memory_range_of_operands_def]) >>
  drule_all taint_agree_exec_delegatecall >> strip_tac >> gvs[] >>
  `step_taint inst s (update_var out w r) tn =
     (tn with t_mem := tn.t_mem DIFF
       {i | w2n ro <= i /\ i < w2n ro + LENGTH (TAKE (w2n rs) r.vs_returndata)}) with
     t_var := set_var_taint tn.t_var [out] {}` by
    (irule taint_agree_delegatecall_mask >>
     simp[out_taint_def, source_memory_write_ranges_def,
       memory_range_of_operands_def] >> gvs[]) >> simp[]
QED

Theorem taint_agree_delegatecall_abort:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  inst.inst_opcode = DELEGATECALL /\ step_inst_base inst s = Abort a s' ==>
  ?t'. step_inst_base inst t = Abort a t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_external_operands >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_ok _ _ _ _` (irule_at Any) >> simp[]) >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs(), exec_delegatecall_def]
QED

Theorem taint_agree_delegatecall_not_terminal:
  inst.inst_opcode = DELEGATECALL ==>
  (!v s'. step_inst_base inst s <> IntRet v s') /\
  (!s'. step_inst_base inst s <> Halt s')
Proof
  rpt strip_tac >>
  gvs[step_inst_base_opcode_eqs, exec_delegatecall_def, AllCaseEqs()]
QED

Theorem taint_agree_exec_create:
  taint_agree D X tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off) (w2n sz) t /\
  exec_create inst s value off sz salt = OK s' ==>
  ?out w r u. inst.inst_outputs = [out] /\ s' = update_var out w r /\
    exec_create inst t value off sz salt = OK (update_var out w u) /\
    consume_create_outcome (venom_create_request s value off sz salt) s = (w,r) /\
    taint_agree D X (tn with t_var := set_var_taint tn.t_var [out] {})
      s' (update_var out w u)
Proof
  strip_tac >>
  `venom_create_request s value off sz salt =
   venom_create_request t value off sz salt` by simp[venom_create_request_def] >>
  qpat_x_assum `exec_create _ _ _ _ _ _ = _` mp_tac >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  simp[exec_create_def, Excl "consume_create_outcome_eq"] >>
  Cases_on `outs` >> simp[Excl "consume_create_outcome_eq"] >>
  IF_CASES_TAC >> simp[Excl "consume_create_outcome_eq"] >>
  pairarg_tac >> strip_tac >>
  drule_all taint_agree_consume_create >> strip_tac >>
  gvs[Excl "consume_create_outcome_eq"] >>
  qexists_tac `u` >> simp[] >>
  irule taint_agree_update_var >> simp[word_agree_except_def]
QED

Theorem taint_agree_create_mask:
  MEM inst.inst_opcode [CREATE; CREATE2] /\ inst.inst_outputs = [out] /\
  out_taint tn inst s = {} /\
  consume_create_outcome rq s = (w,r) ==>
  step_taint inst s (update_var out w r) tn =
    tn with t_var := set_var_taint tn.t_var [out] {}
Proof
  strip_tac >>
  `r.vs_allocas = s.vs_allocas /\ r.vs_fmp = s.vs_fmp` by
    (qpat_x_assum `consume_create_outcome _ _ = _` mp_tac >>
     simp[consume_create_outcome_eq] >> strip_tac >> gvs[]) >>
  `written_taint tn inst s = {}` by
    (fs[MEM] >> simp[written_taint_def] >> rpt CASE_TAC >> simp[]) >>
  fs[MEM] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
    store_taint_def, imm_taint_def, adopt_reset_def,
    source_memory_write_ranges_def, range_bytes_def, update_var_def,
    taint_component_equality, FLOOKUP_DEF, SF CONJ_ss,
    Excl "consume_create_outcome_eq"]
QED

Theorem taint_agree_create_ok:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ptr_discipline lo C vs /\ ~ctx_has_dalloca C /\
  taint_agree D X tn s t /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN X) /\
  MEM inst.inst_opcode [CREATE; CREATE2] /\ step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
    taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `tn.t_stor = {} /\ tn.t_trans = {} /\
   s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient` by
    (irule taint_agree_external_clean_shared >>
     qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ptr_discipline _ _ _` (irule_at Any) >> simp[] >> fs[MEM]) >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_external_operands >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_ok _ _ _ _` (irule_at Any) >> simp[] >> fs[MEM]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[taint_agree_call_ctx] >>
  `IS_SOME (eval_operands inst.inst_operands s) =
   IS_SOME (eval_operands inst.inst_operands t)` by
    (irule o1LowerDloadOpaqueTheory.eval_operands_defined_iff >> simp[]) >>
  `!off len. MEM (off,len) (source_memory_read_ranges inst s) ==>
     read_memory off len s = read_memory off len t` by
    (rpt strip_tac >> irule taint_agree_external_read >>
     qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ptr_discipline _ _ _` (irule_at Any) >> simp[] >> fs[MEM]) >>
  fs[MEM] >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  `read_memory (w2n offset) (w2n sz) s =
   read_memory (w2n offset) (w2n sz) t` by
    (first_x_assum irule >>
     gvs[source_memory_read_ranges_def, memory_range_of_operands_def]) >>
  drule_all taint_agree_exec_create >> strip_tac >>
  gvs[Excl "consume_create_outcome_eq"] >>
  `step_taint inst s (update_var out w r) tn =
     tn with t_var := set_var_taint tn.t_var [out] {}` by
    (irule taint_agree_create_mask >>
     qpat_assum `consume_create_outcome _ _ = _` (irule_at Any) >>
     simp[out_taint_def, MEM]) >> simp[]
QED

Theorem taint_agree_create_abort:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode [CREATE; CREATE2] /\
  step_inst_base inst s = Abort a s' ==>
  ?t'. step_inst_base inst t = Abort a t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_external_operands >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_ok _ _ _ _` (irule_at Any) >> simp[] >> fs[MEM]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[taint_agree_call_ctx] >>
  `IS_SOME (eval_operands inst.inst_operands s) =
   IS_SOME (eval_operands inst.inst_operands t)` by
    (irule o1LowerDloadOpaqueTheory.eval_operands_defined_iff >> simp[]) >>
  fs[MEM] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs(), exec_create_abort_iff] >>
  metis_tac[exec_create_abort_iff]
QED

Theorem taint_agree_call_mask:
  MEM inst.inst_opcode [CALL; STATICCALL] /\
  inst.inst_outputs = [out] /\ out_taint tn inst s = {} /\
  source_memory_write_ranges inst s = [(ro,rs)] /\
  rq.cr_static = (inst.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static) /\
  consume_call_outcome rq ro rs s = (w,r) ==>
  step_taint inst s (update_var out w r) tn =
    (tn with <|t_mem := tn.t_mem DIFF
       {i | ro <= i /\ i < ro + LENGTH (TAKE rs r.vs_returndata)};
      t_stor := if ~rq.cr_static /\ r.vs_requests <> s.vs_requests /\
        r.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
        then {} else tn.t_stor;
      t_trans := if ~rq.cr_static /\ r.vs_requests <> s.vs_requests /\
        r.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
        then {} else tn.t_trans|>) with
      t_var := set_var_taint tn.t_var [out] {}
Proof
  strip_tac >>
  `r.vs_allocas = s.vs_allocas /\ r.vs_fmp = s.vs_fmp` by
    (qpat_x_assum `consume_call_outcome _ _ _ _ = _` mp_tac >>
     simp[consume_call_outcome_eq] >> strip_tac >> gvs[]) >>
  `written_taint tn inst s = {}` by
    (fs[MEM] >> simp[written_taint_def] >> rpt CASE_TAC >> simp[]) >>
  fs[MEM] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
    store_taint_def, imm_taint_def, adopt_reset_def,
    range_bytes_def, update_var_def, taint_component_equality,
    LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF, FLOOKUP_DEF, SF CONJ_ss,
    Excl "consume_call_outcome_eq"] >>
  rpt IF_CASES_TAC >> gvs[arithmeticTheory.LESS_OR_EQ]
QED

Theorem taint_agree_exec_ext_call:
  taint_agree D X tn s t /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n ao) (w2n az) t /\
  (computed_precompile (venom_call_request s addr value ao az static) \/
   (accounts_agree_except D s.vs_accounts t.vs_accounts /\
    transient_agree_except D s.vs_transient t.vs_transient)) /\
  exec_ext_call inst s gas addr value ao az ro rs static = OK s' ==>
  ?out w r u. inst.inst_outputs = [out] /\ s' = update_var out w r /\
    exec_ext_call inst t gas addr value ao az ro rs static = OK (update_var out w u) /\
    consume_call_outcome (venom_call_request s addr value ao az static)
      (w2n ro) (w2n rs) s = (w,r) /\
    taint_agree D X
      ((tn with <|t_mem := tn.t_mem DIFF
        {i | w2n ro <= i /\ i < w2n ro + LENGTH (TAKE (w2n rs) r.vs_returndata)};
       t_stor := if ~(static \/ s.vs_call_ctx.cc_static) /\
         r.vs_requests <> s.vs_requests /\ r.vs_outcomes <> s.vs_outcomes /\
         (HD s.vs_outcomes).co_success then {} else tn.t_stor;
       t_trans := if ~(static \/ s.vs_call_ctx.cc_static) /\
         r.vs_requests <> s.vs_requests /\ r.vs_outcomes <> s.vs_outcomes /\
         (HD s.vs_outcomes).co_success then {} else tn.t_trans|>) with
       t_var := set_var_taint tn.t_var [out] {}) s' (update_var out w u)
Proof
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `_ /\ _` strip_assume_tac >>
  qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  simp[exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  Cases_on `outs` >> simp[Excl "consume_call_outcome_eq"] >>
  pairarg_tac >> strip_tac >>
  drule_at (Pat `consume_call_outcome _ _ _ _ = _`) taint_agree_consume_call_request >>
  disch_then drule >>
  (impl_tac >- simp[Excl "consume_call_outcome_eq"]) >> strip_tac >>
  gvs[Excl "consume_call_outcome_eq"] >>
  qexists_tac `u` >> simp[Excl "consume_call_outcome_eq"] >>
  qmatch_asmsub_abbrev_tac `taint_agree D X mask s'' u` >>
  qmatch_goalsub_abbrev_tac `taint_agree D X final` >>
  `final = mask with t_var := set_var_taint mask.t_var [out] {}` by
    simp[Abbr `final`, Abbr `mask`, taint_component_equality] >>
  pop_assum SUBST1_TAC >> irule taint_agree_update_var >>
  simp[word_agree_except_def, Excl "consume_call_outcome_eq"]
QED

Theorem taint_agree_call_abort:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode [CALL; STATICCALL] /\
  step_inst_base inst s = Abort a s' ==>
  ?t'. step_inst_base inst t = Abort a t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_external_operands >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_ok _ _ _ _` (irule_at Any) >> simp[] >> fs[MEM]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[taint_agree_call_ctx] >>
  fs[MEM] >> gvs[step_inst_base_opcode_eqs, AllCaseEqs(), exec_ext_call_def]
QED

Theorem taint_agree_call_ok:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ptr_discipline lo C vs /\ ~ctx_has_dalloca C /\ taint_within D C vs /\
  taint_agree D X tn s t /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN X) /\
  MEM inst.inst_opcode [CALL; STATICCALL] /\ step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
    taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_external_operands >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_ok _ _ _ _` (irule_at Any) >> simp[] >> fs[MEM]) >>
  `!off len. MEM (off,len) (source_memory_read_ranges inst s) ==>
     read_memory off len s = read_memory off len t` by
    (rpt strip_tac >> irule taint_agree_external_read >>
     qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ptr_discipline _ _ _` (irule_at Any) >> simp[] >> fs[MEM] >> gvs[]) >>
  `!(gas:256 word) addr value ao az (ro:256 word) (rs:256 word) static.
     exec_ext_call inst s gas addr value ao az ro rs static = OK s' ==>
     computed_precompile (venom_call_request s addr value ao az static) \/
       (accounts_agree_except D s.vs_accounts t.vs_accounts /\
        transient_agree_except D s.vs_transient t.vs_transient)` by
    (rpt strip_tac >>
     Cases_on `computed_precompile (venom_call_request s addr value ao az static)` >> simp[] >>
     irule taint_agree_request_snapshots >>
     qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >> simp[] >>
     qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
     pairarg_tac >> simp[AllCaseEqs(), update_var_def] >> strip_tac >>
     gvs[consume_call_outcome_eq, record_request_def, MEM]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[taint_agree_call_ctx] >>
  fs[MEM] >> gvs[step_inst_base_opcode_eqs, AllCaseEqs(),
    Excl "consume_call_outcome_eq"] >>
  `read_memory (w2n ao) (w2n as_) s = read_memory (w2n ao) (w2n as_) t` by
    (first_x_assum irule >>
     gvs[source_memory_read_ranges_def, memory_range_of_operands_def]) >>
  drule_at (Pat `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _`) taint_agree_exec_ext_call >>
  disch_then drule >>
  (impl_tac >- (simp[Excl "consume_call_outcome_eq"] >>
    first_x_assum irule >> goal_assum (drule_at Any))) >>
  strip_tac >> gvs[Excl "consume_call_outcome_eq"] >>
  drule_at (Pat `consume_call_outcome _ _ _ _ = _`) taint_agree_call_mask >>
  disch_then (qspecl_then [`tn`, `out`, `inst`] mp_tac) >>
  (impl_tac >- (simp[out_taint_def, source_memory_write_ranges_def,
    memory_range_of_operands_def, venom_call_request_def] >> gvs[])) >>
  disch_then SUBST1_TAC >> gvs[venom_call_request_def, Excl "consume_call_outcome_eq"]
QED

Theorem taint_agree_call_not_terminal:
  MEM inst.inst_opcode [CALL; STATICCALL] ==>
  (!v s'. step_inst_base inst s <> IntRet v s') /\
  (!s'. step_inst_base inst s <> Halt s')
Proof
  rpt strip_tac >> fs[MEM] >>
  gvs[step_inst_base_opcode_eqs, exec_ext_call_def, AllCaseEqs(),
    Excl "consume_call_outcome_eq"] >>
  pairarg_tac >> gvs[AllCaseEqs(), Excl "consume_call_outcome_eq"]
QED

Theorem taint_agree_mcopy:
  taint_agree D X tn s t /\
  (!k. k < len /\ src+k NOTIN tn.t_mem ==>
       src+k NOTIN X /\ src+k < s.vs_alloca_next) ==>
  taint_agree D X
    (tn with t_mem := (tn.t_mem DIFF {i | dst <= i /\ i < dst+len}) UNION
                       {dst+k | k < len /\ src+k IN tn.t_mem})
    (mcopy dst src len s) (mcopy dst src len t)
Proof
  strip_tac >>
  pure_rewrite_tac[mcopy_def, GSYM read_memory_def, LET_THM] >> BETA_TAC >>
  irule taint_agree_write_memory >>
  qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
  qexists_tac `len` >> simp[ld_read_memory_length] >>
  rpt strip_tac >> simp[ld_read_memory_element] >>
  irule taint_agree_memory >>
  qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
  gvs[] >> metis_tac[]
QED

Theorem taint_agree_mstore:
  taint_agree D X tn s t /\ word_agree_except m x y ==>
  taint_agree D X
    (tn with t_mem := (tn.t_mem DIFF {i | a <= i /\ i < a+32}) UNION
                         {a+k | k IN m})
    (mstore a x s) (mstore a y t)
Proof
  strip_tac >>
  `mstore a x s = s with vs_memory := (mstore a x s).vs_memory` by
    simp[mstore_def] >>
  `mstore a y t = t with vs_memory := (mstore a y t).vs_memory` by
    simp[mstore_def] >>
  pop_assum SUBST1_TAC >> pop_assum SUBST1_TAC >>
  irule taint_agree_memory_update >>
  qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
  gen_tac >> disch_tac >> simp[ld_mstore_bytes] >>
  Cases_on `a <= i /\ i < a+32` >> simp[]
  >- (gvs[word_agree_except_def] >>
      `i-a < 32 /\ a + (i-a) = i` by decide_tac >>
      first_x_assum irule >> simp[] >> metis_tac[]) >>
  irule taint_agree_memory >>
  qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >> gvs[]
QED

Theorem taint_agree_istore:
  taint_agree D X tn s t /\ word_agree_except m v w ==>
  taint_agree D X
    (tn with <|t_mem := (tn.t_mem DIFF {i | off <= i /\ i < off+32}) UNION
                         {off+k | k IN m};
               t_imm := key_update tn.t_imm off m|>)
    (istore off v s) (istore off w t)
Proof
  strip_tac >>
  drule_all taint_agree_mstore >>
  disch_then (qspec_then `off` assume_tac) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address
     (tn with t_imm := key_update tn.t_imm off m)
     (istore off v s) (istore off w t)` by
    (irule ld_shared_istore >> simp[] >> metis_tac[taint_agree_shared]) >>
  fs[taint_agree_def] >>
  simp[taint_agree_def, istore_def, mstore_def, op_taint_def] >>
  conj_tac >- (gvs[ld_shared_agree_def, istore_def, mstore_def] >> metis_tac[]) >>
  gvs[venom_state_component_equality, istore_def, mstore_def, op_taint_def] >>
  metis_tac[]
QED

Theorem taint_agree_word_store_step:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode [MSTORE; ISTORE] /\ inst.inst_outputs = [] /\ 
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >> fs[MEM] >>
  gvs[step_inst_base_opcode_eqs, exec_write2_def, AllCaseEqs()] >>
  rename1 `inst.inst_operands = [op1; op2]` >>
  rename1 `eval_operand op1 s = SOME addr` >>
  `op_taint tn op1 = {}` by (fs[taint_ok_def] >> metis_tac[]) >>
  `eval_operand op1 s = eval_operand op1 t` by
    (drule_all taint_agree_operand_clean >> simp[]) >>
  drule_all taint_agree_operand_value >> strip_tac >> gvs[] >>
  simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, new_site_bytes_def, mstore_def,
       set_var_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, FLOOKUP_DEF, SF CONJ_ss,
       DRESTRICT_UNIV] >>
  qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  Cases_on `inst.inst_opcode = MSTORE` >> gvs[]
  >- (`mask = tn with t_mem := mask.t_mem` by
        simp[Abbr `mask`, taint_component_equality] >>
      pop_assum SUBST1_TAC >> simp[Abbr `mask`] >>
      drule_all taint_agree_mstore >>
      disch_then (qspec_then `w2n addr` mp_tac) >>
      simp[mstore_def, fixed_source_write_range_def, arithmeticTheory.ADD_COMM]) >>
  `mask = tn with <|t_mem := mask.t_mem; t_imm := mask.t_imm|>` by
    simp[Abbr `mask`, taint_component_equality] >>
  pop_assum SUBST1_TAC >> simp[Abbr `mask`] >>
  drule_all taint_agree_istore >>
  disch_then (qspec_then `w2n addr` mp_tac) >>
  simp[istore_def, mstore_def, fixed_source_write_range_def,
       arithmeticTheory.ADD_COMM, SF CONJ_ss]
QED

Theorem taint_agree_byte_store_step:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  inst.inst_opcode = MSTORE8 /\ inst.inst_outputs = [] /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_operand_clean >>
     gvs[taint_ok_def] >> metis_tac[]) >>
  gvs[step_inst_base_opcode_eqs, exec_write2_def, AllCaseEqs()] >>
  simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, new_site_bytes_def,
       set_var_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, FLOOKUP_DEF, SF CONJ_ss,
       DRESTRICT_UNIV] >>
  qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  `mask = tn with t_mem := mask.t_mem` by
    simp[Abbr `mask`, taint_component_equality] >>
  pop_assum SUBST1_TAC >> simp[Abbr `mask`] >>
  simp[venomMemPropsTheory.mstore8_eq_write_mem] >>
  irule taint_agree_write_memory >>
  qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
  qexists_tac `1` >>
  simp[fixed_source_write_range_def, arithmeticTheory.ADD_COMM] >>
  pred_setLib.SET_TAC[]
QED

Theorem taint_agree_load_word:
  frame_reachable vs C stk PG G tn fn inst s /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN X) /\
  MEM inst.inst_opcode [MLOAD; ILOAD] /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (gvs[taint_ok_def, MEM] >> metis_tac[]) >>
  fs[MEM] >> gvs[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()] >>
  rename1 `eval_operand op1 s = SOME v` >>
  `eval_operand op1 t = SOME v` by
    (qsuff_tac `eval_operand op1 s = eval_operand op1 t` >- simp[] >>
     irule taint_agree_operand_clean >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >> simp[]) >>
  simp[] >>
  `word_agree_except (mem_word_taint tn.t_mem (w2n v))
     (mload (w2n v) s) (mload (w2n v) t)` by
    (irule ld_mload_masked_bytes >> simp[mem_word_taint_def] >>
     rpt strip_tac >> irule taint_agree_reachable_read_byte >>
     qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ptr_discipline _ _ _` (irule_at Any) >>
     qexistsl_tac [`w2n v`, `32`] >>
     simp[source_memory_read_ranges_def]) >>
  `step_taint inst s (update_var out (mload (w2n v) s) s) tn =
     tn with t_var := set_var_taint tn.t_var [out]
       (mem_word_taint tn.t_mem (w2n v))` by
    simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
         imm_taint_def, adopt_reset_def, new_site_bytes_def, update_var_def,
         step_writes_def, source_memory_write_ranges_def, written_taint_def,
         range_bytes_def, FLOOKUP_DEF, SF CONJ_ss, taint_component_equality] >>
  simp[] >> irule taint_agree_update_var >> simp[]
QED

Theorem taint_agree_mcopy_step:
  frame_reachable vs C stk PG G tn fn inst s /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN X) /\
  inst.inst_opcode = MCOPY /\ inst.inst_outputs = [] /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_operand_clean >>
     gvs[taint_ok_def] >> metis_tac[]) >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rename1 `frame_reachable vs C stk PG G tn fn inst s` >>
  rename1 `inst.inst_operands = [dop; rop; lop]` >>
  rename1 `eval_operand dop t = SOME d` >>
  rename1 `eval_operand rop t = SOME a` >>
  rename1 `eval_operand lop t = SOME n` >>
  simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, new_site_bytes_def,
       set_var_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, FLOOKUP_DEF, SF CONJ_ss,
       DRESTRICT_UNIV, mcopy_def, write_memory_with_expansion_def] >>
  qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  `mask = tn with t_mem := mask.t_mem` by
    simp[Abbr `mask`, taint_component_equality] >>
  pop_assum SUBST1_TAC >> simp[Abbr `mask`] >>
  drule taint_agree_mcopy >>
  disch_then (qspecl_then [`w2n a`, `w2n n`, `w2n d`] mp_tac) >>
  impl_tac
  >- (gen_tac >> strip_tac >> conj_tac
      >- (qpat_x_assum `!off len i. _ ==> i NOTIN X` irule >>
          qexistsl_tac [`w2n n`, `w2n a`] >>
          simp[source_memory_read_ranges_def]) >>
      irule ld_frame_reachable_read_byte_bound >>
      qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `ptr_discipline _ _ _` (irule_at Any) >>
      qexistsl_tac [`w2n a`, `w2n n`] >>
      simp[source_memory_read_ranges_def]) >>
  simp[mcopy_def, write_memory_with_expansion_def,
       sized_source_write_range_def, arithmeticTheory.ADD_COMM]
QED

Theorem taint_agree_source_copy_step:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY; EXTCODECOPY] /\
  inst.inst_outputs = [] /\ step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_operand_clean >>
     gvs[taint_ok_def] >> metis_tac[]) >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_code = t.vs_code /\
   s.vs_data_section = t.vs_data_section /\ s.vs_returndata = t.vs_returndata` by
    (drule taint_agree_frame >> simp[venom_state_component_equality]) >>
  `!addr. (lookup_account addr s.vs_accounts).code =
          (lookup_account addr t.vs_accounts).code` by
    metis_tac[taint_agree_shared, ld_shared_account_observations] >>
  `!a bs u. new_site_bytes u (write_memory_with_expansion a bs u) = {}` by
    simp[new_site_bytes_def, write_memory_with_expansion_def, FLOOKUP_DEF, SF CONJ_ss] >>
  fs[MEM] >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  simp[] >>
  simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, new_site_bytes_def,
       set_var_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, FLOOKUP_DEF, SF CONJ_ss,
       DRESTRICT_UNIV] >>
  qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  `mask = tn with t_mem := mask.t_mem` by
    simp[Abbr `mask`, taint_component_equality] >>
  pop_assum SUBST1_TAC >> simp[Abbr `mask`] >>
  rewrite_tac[GSYM write_memory_with_expansion_def] >>
  irule taint_agree_write_memory >>
  qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
  simp[sized_source_write_range_def, arithmeticTheory.ADD_COMM] >>
  pred_setLib.SET_TAC[]
QED

Theorem taint_agree_copy_abort:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode
    [MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY; EXTCODECOPY] /\
  step_inst_base inst s = Abort a s' ==>
  ?t'. step_inst_base inst t = Abort a t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_operand_clean >>
     gvs[taint_ok_def] >> metis_tac[]) >>
  `s.vs_returndata = t.vs_returndata` by
    (drule taint_agree_frame >> simp[venom_state_component_equality]) >>
  fs[MEM] >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >> simp[]
QED

Theorem taint_agree_copy_step:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  taint_agree D X tn s t /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN X) /\
  MEM inst.inst_opcode
    [MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY; EXTCODECOPY] ==>
  (!s'. step_inst_base inst s = OK s' ==>
    ?t'. step_inst_base inst t = OK t' /\
         taint_agree D X (step_taint inst s s' tn) s' t') /\
  (!v s'. step_inst_base inst s = IntRet v s' ==>
    ?t'. step_inst_base inst t = IntRet v t' /\ taint_agree D X tn s' t') /\
  (!s'. step_inst_base inst s = Halt s' ==>
    ?t'. step_inst_base inst t = Halt t' /\ dead_result_rel D (Halt s') (Halt t')) /\
  (!a s'. step_inst_base inst s = Abort a s' ==>
    ?t'. step_inst_base inst t = Abort a t')
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `wf_function fn /\ fn_inst_wf fn` by
    (gvs[o1PassContractTheory.o1_ctx_shape_def, listTheory.EVERY_MEM] >>
     metis_tac[o1PassContractTheory.o1_fn_shape_def]) >>
  `inst_wf inst` by
    (gvs[active_inst_def, venomWfTheory.fn_inst_wf_def] >>
     metis_tac[listTheory.MEM_EL]) >>
  conj_tac
  >- (rpt strip_tac >>
      `inst.inst_outputs = []` by
        (fs[MEM] >> gvs[venomWfTheory.inst_wf_def]) >>
      Cases_on `inst.inst_opcode = MCOPY`
      >- (`~in_revert_forward fn s` by
            (spose_not_then assume_tac >>
             gvs[in_revert_forward_def, active_inst_def] >>
             `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
               (irule venomExecPropsTheory.MEM_lookup_block >>
                gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]) >>
             gvs[] >>
             `get_instruction bb s.vs_inst_idx = SOME (EL s.vs_inst_idx bb.bb_instructions)` by
               simp[venomInstTheory.get_instruction_def] >>
             drule_all memSafeRunTheory.revert_forward_at_opcode >> fs[MEM]) >>
          irule taint_agree_mcopy_step >> metis_tac[]) >>
      irule taint_agree_source_copy_step >> fs[MEM] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> fs[MEM] >>
      gvs[step_inst_base_opcode_eqs, AllCaseEqs()]) >>
  reverse conj_tac
  >- (rpt strip_tac >> irule taint_agree_copy_abort >> metis_tac[]) >>
  rpt strip_tac >> fs[MEM] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Theorem taint_agree_hash_step:
  frame_reachable vs C stk PG G tn fn inst s /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN X) /\
  inst.inst_opcode = SHA3 /\ step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_operand_clean >>
     gvs[taint_ok_def] >> metis_tac[]) >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rename1 `inst.inst_operands = [op_off; op_len]` >>
  rename1 `eval_operand op_off t = SOME a` >>
  rename1 `eval_operand op_len t = SOME n` >>
  `read_memory (w2n a) (w2n n) s = read_memory (w2n a) (w2n n) t` by
    (irule taint_agree_reachable_clean_read >>
     qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ptr_discipline _ _ _` (irule_at Any) >>
     simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
     gvs[taint_ok_def, about_to_revert_def,
         source_memory_read_ranges_def, memory_range_of_operands_def] >> metis_tac[]) >>
  simp[GSYM read_memory_def] >>
  simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, new_site_bytes_def,
       set_var_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, FLOOKUP_DEF, SF CONJ_ss,
       update_var_def] >>
  qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  `mask = tn with t_var := mask.t_var` by
    simp[Abbr `mask`, taint_component_equality] >>
  pop_assum SUBST1_TAC >> simp[Abbr `mask`] >>
  rewrite_tac[GSYM update_var_def] >>
  irule (SRULE [set_var_taint_def] taint_agree_update_var) >>
  simp[word_agree_except_def]
QED

Theorem taint_agree_logs_append:
  taint_agree D X tn s t ==>
  taint_agree D X tn
    (s with vs_logs := s.vs_logs ++ [ev]) (t with vs_logs := t.vs_logs ++ [ev])
Proof
  strip_tac >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn
    (s with vs_logs := s.vs_logs ++ [ev]) (t with vs_logs := t.vs_logs ++ [ev])` by
    metis_tac[taint_agree_shared, ld_shared_logs_append] >>
  fs[taint_agree_def] >> simp[taint_agree_def] >>
  qpat_x_assum `_ = s` (mp_tac o Q.AP_TERM `\u. u with vs_logs := u.vs_logs ++ [ev]`) >>
  simp[]
QED

Theorem taint_agree_log_step:
  frame_reachable vs C stk PG G tn fn inst s /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN X) /\
  inst.inst_opcode = LOG /\ inst.inst_outputs = [] /\ step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_operand_clean >>
     gvs[taint_ok_def] >> metis_tac[]) >>
  `!ops. (!op. MEM op ops ==> MEM op inst.inst_operands) ==>
         eval_operands ops s = eval_operands ops t` by
    (Induct >> simp[eval_operands_def] >> rpt strip_tac >>
     `eval_operand h s = eval_operand h t` by metis_tac[MEM] >>
     `eval_operands ops s = eval_operands ops t` by
       (first_x_assum irule >> metis_tac[MEM]) >> simp[]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[taint_agree_call_ctx] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `REVERSE rest` >> gvs[] >> rename1 `REVERSE rest = p::rr` >>
  Cases_on `rr` >> gvs[] >> rename1 `REVERSE rest = p::szop::tops` >>
  `rest = REVERSE (p::szop::tops)` by metis_tac[REVERSE_REVERSE] >>
  `eval_operand p s = eval_operand p t /\ eval_operand szop s = eval_operand szop t /\
   eval_operands tops s = eval_operands tops t` by
    (rpt conj_tac >> first_x_assum irule >> simp[MEM_REVERSE] >> metis_tac[MEM]) >>
  `EVERY (\op. IS_SOME (eval_operand op s)) tops` by
    (qpat_assum `eval_operands tops s = SOME topics` mp_tac >>
     simp[GSYM ld_eval_operands_defined]) >>
  `IS_SOME (eval_operands inst.inst_operands s)` by
    (simp[ld_eval_operands_defined, eval_operand_def] >> metis_tac[optionTheory.IS_SOME_DEF]) >>
  gvs[] >>
  `read_memory (w2n off) (w2n sz) s = read_memory (w2n off) (w2n sz) t` by
    (irule taint_agree_reachable_clean_read >>
     qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ptr_discipline _ _ _` (irule_at Any) >>
     simp[source_memory_read_ranges_def, memory_range_of_operands_def, REVERSE_APPEND] >>
     gvs[taint_ok_def, about_to_revert_def,
         source_memory_read_ranges_def, memory_range_of_operands_def, REVERSE_APPEND] >> metis_tac[]) >>
  simp[GSYM read_memory_def] >>
  gvs[] >>
  `!ev. step_taint inst s (s with vs_logs := s.vs_logs ++ [ev]) tn = tn` by
    (simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
          imm_taint_def, adopt_reset_def, new_site_bytes_def,
          set_var_taint_def, step_writes_def, source_memory_write_ranges_def,
          range_bytes_def, FLOOKUP_DEF, SF CONJ_ss, DRESTRICT_UNIV,
          taint_component_equality] >>
     Cases_on `REVERSE tops` >> simp[written_taint_def] >>
     rename1 `REVERSE tops = h::tl` >>
     Cases_on `tl` >> simp[written_taint_def] >>
     rename1 `REVERSE tops = h::h2::tail` >>
     Cases_on `tail` >> simp[]) >>
  simp[] >> irule taint_agree_logs_append >> simp[]
QED

Theorem taint_agree_observation_abort:
  taint_agree D X tn s t /\ MEM inst.inst_opcode [SHA3; LOG] /\
  step_inst_base inst s = Abort a s' ==>
  ?t'. step_inst_base inst t = Abort a t'
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[taint_agree_call_ctx] >>
  `IS_SOME (eval_operands inst.inst_operands s) =
   IS_SOME (eval_operands inst.inst_operands t)` by
    (irule o1LowerDloadOpaqueTheory.eval_operands_defined_iff >>
     metis_tac[taint_agree_operand_defined]) >>
  fs[MEM] >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >> simp[]
QED

Theorem taint_agree_memory_observation_step:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  taint_agree D X tn s t /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN X) /\
  MEM inst.inst_opcode [SHA3; LOG] ==>
  (!s'. step_inst_base inst s = OK s' ==>
    ?t'. step_inst_base inst t = OK t' /\
         taint_agree D X (step_taint inst s s' tn) s' t') /\
  (!v s'. step_inst_base inst s = IntRet v s' ==>
    ?t'. step_inst_base inst t = IntRet v t' /\ taint_agree D X tn s' t') /\
  (!s'. step_inst_base inst s = Halt s' ==>
    ?t'. step_inst_base inst t = Halt t' /\ dead_result_rel D (Halt s') (Halt t')) /\
  (!a s'. step_inst_base inst s = Abort a s' ==>
    ?t'. step_inst_base inst t = Abort a t')
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `wf_function fn /\ fn_inst_wf fn` by
    (gvs[o1PassContractTheory.o1_ctx_shape_def, listTheory.EVERY_MEM] >>
     metis_tac[o1PassContractTheory.o1_fn_shape_def]) >>
  `inst_wf inst` by
    (gvs[active_inst_def, venomWfTheory.fn_inst_wf_def] >>
     metis_tac[listTheory.MEM_EL]) >>
  `~in_revert_forward fn s` by
    (spose_not_then assume_tac >>
     gvs[in_revert_forward_def, active_inst_def] >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
       (irule venomExecPropsTheory.MEM_lookup_block >>
        gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]) >>
     gvs[] >>
     `get_instruction bb s.vs_inst_idx = SOME (EL s.vs_inst_idx bb.bb_instructions)` by
       simp[venomInstTheory.get_instruction_def] >>
     drule_all memSafeRunTheory.revert_forward_at_opcode >> fs[MEM]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `inst.inst_opcode = SHA3`
      >- (irule taint_agree_hash_step >> metis_tac[]) >>
      irule taint_agree_log_step >> fs[MEM] >>
      gvs[venomWfTheory.inst_wf_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> fs[MEM] >>
      gvs[step_inst_base_opcode_eqs, AllCaseEqs()]) >>
  reverse conj_tac
  >- (rpt strip_tac >> irule taint_agree_observation_abort >> metis_tac[]) >>
  rpt strip_tac >> fs[MEM] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Theorem taint_agree_load_store_step:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  taint_agree D X tn s t /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN X) /\
  MEM inst.inst_opcode [MLOAD; ILOAD; MSTORE; ISTORE; MSTORE8] ==>
  (!s'. step_inst_base inst s = OK s' ==>
    ?t'. step_inst_base inst t = OK t' /\
         taint_agree D X (step_taint inst s s' tn) s' t') /\
  (!v s'. step_inst_base inst s = IntRet v s' ==>
    ?t'. step_inst_base inst t = IntRet v t' /\ taint_agree D X tn s' t') /\
  (!s'. step_inst_base inst s = Halt s' ==>
    ?t'. step_inst_base inst t = Halt t' /\ dead_result_rel D (Halt s') (Halt t')) /\
  (!a s'. step_inst_base inst s = Abort a s' ==>
    ?t'. step_inst_base inst t = Abort a t')
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `wf_function fn /\ fn_inst_wf fn` by
    (gvs[o1PassContractTheory.o1_ctx_shape_def, listTheory.EVERY_MEM] >>
     metis_tac[o1PassContractTheory.o1_fn_shape_def]) >>
  `inst_wf inst` by
    (gvs[active_inst_def, venomWfTheory.fn_inst_wf_def] >>
     metis_tac[listTheory.MEM_EL]) >>
  `~in_revert_forward fn s` by
    (spose_not_then assume_tac >>
     gvs[in_revert_forward_def, active_inst_def] >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
       (irule venomExecPropsTheory.MEM_lookup_block >>
        gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]) >>
     gvs[] >>
     `get_instruction bb s.vs_inst_idx = SOME (EL s.vs_inst_idx bb.bb_instructions)` by
       simp[venomInstTheory.get_instruction_def] >>
     drule_all memSafeRunTheory.revert_forward_at_opcode >> fs[MEM]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `MEM inst.inst_opcode [MLOAD; ILOAD]`
      >- (irule taint_agree_load_word >> metis_tac[]) >>
      Cases_on `inst.inst_opcode = MSTORE8`
      >- (irule taint_agree_byte_store_step >>
          gvs[venomWfTheory.inst_wf_def] >> metis_tac[]) >>
      irule taint_agree_word_store_step >> fs[MEM] >>
      gvs[venomWfTheory.inst_wf_def] >> metis_tac[]) >>
  rpt conj_tac >> rpt strip_tac >> fs[MEM] >>
  gvs[step_inst_base_opcode_eqs, exec_read1_def, exec_write2_def, AllCaseEqs()]
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

Theorem taint_agree_jump:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  inst.inst_outputs = [] /\ MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_operand_clean >>
     gvs[taint_ok_def, MEM] >> metis_tac[]) >>
  fs[MEM] >> qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `jump_to label s` >>
  `step_taint inst s (jump_to label s) tn = tn` by
    (simp[step_taint_def, mem_taint_def, store_taint_def, jump_to_def,
          imm_taint_def, adopt_reset_def, new_site_bytes_def,
          step_writes_def, source_memory_write_ranges_def, written_taint_def,
          range_bytes_def, FLOOKUP_DEF, SF CONJ_ss, set_var_taint_def,
          DRESTRICT_UNIV, taint_component_equality] >>
     rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  simp[step_inst_base_opcode_eqs, Abbr `label`] >>
  metis_tac[MEM, taint_agree_jump_to]
QED

Theorem taint_agree_identity:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\ inst_wf inst /\
  MEM inst.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE] /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `step_taint inst s s tn = tn` by
    metis_tac[o1LowerDloadJointIdentityTheory.ld_joint_identity_annotations] >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_operand_clean >>
     gvs[taint_ok_def, MEM] >> metis_tac[]) >>
  fs[MEM] >> qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[step_inst_base_opcode_eqs] >> metis_tac[MEM]
QED

Theorem taint_agree_phi_not_terminating:
  inst.inst_opcode = PHI ==> ~terminates (step_inst_base inst s)
Proof
  simp[step_inst_base_opcode_eqs, passSimulationDefsTheory.terminates_def]
QED

Theorem taint_agree_bump:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  inst.inst_opcode = BUMP /\ step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_operand_clean >>
     gvs[taint_ok_def] >> metis_tac[]) >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> strip_tac >> gvs[] >>
  `eval_operand base_op t = SOME base_val /\
   eval_operand size_op t = SOME sz` by metis_tac[MEM] >>
  simp[step_inst_base_opcode_eqs] >>
  `step_taint inst s
     (update_var next_out (word_add base_val sz) (update_var ptr_out base_val s)) tn =
   tn with t_var := set_var_taint tn.t_var [ptr_out;next_out] {}` by
    simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
         imm_taint_def, adopt_reset_def, new_site_bytes_def, update_var_def,
         step_writes_def, source_memory_write_ranges_def, written_taint_def,
         range_bytes_def, FLOOKUP_DEF, SF CONJ_ss, taint_component_equality] >>
  simp[] >> irule taint_agree_update_two_clean >> simp[]
QED

Theorem taint_agree_bump_not_terminal:
  inst.inst_opcode = BUMP ==>
  step_inst_base inst s <> IntRet v u /\
  step_inst_base inst s <> Halt u /\ step_inst_base inst s <> Abort a u
Proof
  simp[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Theorem taint_agree_gas:
  taint_agree D X tn s t /\ inst.inst_opcode = GAS /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `s.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[taint_agree_shared, ld_shared_gas_readings] >>
  `!u. out_taint tn inst u = {}` by
    (gen_tac >> irule o1LowerDloadJointRead0Theory.ld_out_taint_default >> simp[]) >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, exec_gas_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  simp[step_inst_base_opcode_eqs, exec_gas_def] >>
  qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  `mask = tn with t_var := set_var_taint tn.t_var [out] {}` by
    (simp[Abbr `mask`, step_taint_def, mem_taint_def, store_taint_def,
          imm_taint_def, adopt_reset_def, new_site_bytes_def, update_var_def,
          step_writes_def, source_memory_write_ranges_def, written_taint_def,
          range_bytes_def, FLOOKUP_DEF, SF CONJ_ss, taint_component_equality] >>
     rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  simp[] >> irule taint_agree_update_var >> simp[word_agree_except_def] >>
  irule taint_agree_gas_readings_update >> simp[]
QED

Theorem taint_agree_frame_scalar:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode [PARAM; RETPC_PARAM; INITIAL_FMP] /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >> drule taint_agree_scalar_fields >> strip_tac >>
  fs[MEM] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  simp[step_inst_base_opcode_eqs] >>
  qmatch_goalsub_abbrev_tac `update_var out value t` >>
  `step_taint inst s (update_var out value s) tn =
     tn with t_var := set_var_taint tn.t_var [out] {}` by
    simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
         imm_taint_def, adopt_reset_def, new_site_bytes_def, update_var_def,
         step_writes_def, source_memory_write_ranges_def, written_taint_def,
         range_bytes_def, FLOOKUP_DEF, SF CONJ_ss, taint_component_equality,
         eval_operand_def] >>
  simp[] >> irule taint_agree_update_var >> simp[word_agree_except_def]
QED

Theorem taint_agree_read0:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode
    [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
     COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
     BLOBBASEFEE; CALLDATASIZE; CODESIZE; RETURNDATASIZE; SELFBALANCE] /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  drule taint_agree_read_fields >> strip_tac >>
  drule taint_agree_shared >> strip_tac >>
  drule ld_shared_account_observations >> strip_tac >>
  fs[MEM] >>
  `!u. out_taint tn inst u = {}` by
    (gen_tac >> irule o1LowerDloadJointRead0Theory.ld_out_taint_default >> simp[]) >>
  gvs[step_inst_base_opcode_eqs] >>
  drule_at (Pat `exec_read0 _ _ _ = _`) taint_agree_exec_read0_clean >>
  simp[] >> disch_then drule >> simp[] >>
  disch_then (qx_choose_then `target` strip_assume_tac) >>
  qexists_tac `target` >> simp[] >>
  qpat_x_assum `exec_read0 _ inst s = _` mp_tac >>
  simp[exec_read0_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `taint_agree _ _ _ _ _` mp_tac >>
  simp[step_taint_def, mem_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, new_site_bytes_def, update_var_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, FLOOKUP_DEF, SF CONJ_ss] >>
  strip_tac >> qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  `mask = tn with t_var := mask.t_var` by
    (simp[Abbr `mask`, taint_component_equality] >>
     rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  pop_assum SUBST1_TAC >> simp[Abbr `mask`]
QED

Theorem taint_agree_read1:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode
    [BLOCKHASH; BLOBHASH; BALANCE; EXTCODESIZE; EXTCODEHASH; CALLDATALOAD] /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (gvs[taint_ok_def, MEM] >> metis_tac[]) >>
  drule taint_agree_read_fields >> strip_tac >>
  drule taint_agree_shared >> strip_tac >>
  drule ld_shared_account_observations >> strip_tac >>
  fs[MEM] >>
  `!u. out_taint tn inst u = {}` by
    (gen_tac >> irule o1LowerDloadJointRead0Theory.ld_out_taint_default >> simp[]) >>
  gvs[step_inst_base_opcode_eqs] >>
  drule_at (Pat `exec_read1 _ _ _ = _`) taint_agree_exec_read1_clean >>
  simp[] >> disch_then drule >> simp[] >>
  disch_then (qx_choose_then `target` strip_assume_tac) >>
  qexists_tac `target` >> simp[] >>
  qpat_x_assum `exec_read1 _ inst s = _` mp_tac >>
  simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `taint_agree _ _ _ _ _` mp_tac >>
  simp[step_taint_def, mem_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, new_site_bytes_def, update_var_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, FLOOKUP_DEF, SF CONJ_ss] >>
  strip_tac >> qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  `mask = tn with t_var := mask.t_var` by
    simp[Abbr `mask`, taint_component_equality] >>
  pop_assum SUBST1_TAC >> simp[Abbr `mask`]
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

Theorem taint_agree_sload:
  taint_agree D X tn s t ==>
  word_agree_except (key_taint tn.t_stor key) (sload key s) (sload key t)
Proof
  strip_tac >> drule taint_agree_call_ctx >> strip_tac >>
  drule taint_agree_shared >> disch_tac >> drule ld_shared_storage_word >>
  disch_then (qspecl_then [`key`, `s.vs_call_ctx.cc_address`] mp_tac) >>
  simp[sload_def, contract_storage_def, key_taint_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.lookup_storage_def,
       word_agree_except_def] >> metis_tac[]
QED

Theorem taint_agree_tload:
  taint_agree D X tn s t ==>
  word_agree_except (key_taint tn.t_trans key) (tload key s) (tload key t)
Proof
  strip_tac >> drule taint_agree_call_ctx >> strip_tac >>
  drule taint_agree_shared >> disch_tac >> drule ld_shared_transient_word >>
  disch_then (qspecl_then [`key`, `s.vs_call_ctx.cc_address`] mp_tac) >>
  simp[tload_def, contract_transient_def, key_taint_def,
       vfmStateTheory.lookup_storage_def, word_agree_except_def] >> metis_tac[]
QED

Theorem taint_agree_storage_load:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode [SLOAD; TLOAD] /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  fs[MEM] >>
  gvs[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()] >>
  `eval_operand op1 s = eval_operand op1 t` by
    (drule_all taint_agree_operand_clean >> simp[]) >>
  gvs[] >>
  simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, new_site_bytes_def, update_var_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, FLOOKUP_DEF, SF CONJ_ss] >>
  qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  `mask = tn with t_var := mask.t_var` by
    simp[Abbr `mask`, taint_component_equality] >>
  pop_assum SUBST1_TAC >> simp[Abbr `mask`] >>
  rewrite_tac[GSYM update_var_def] >>
  irule taint_agree_update_var >>
  metis_tac[taint_agree_sload, taint_agree_tload]
QED

Theorem taint_agree_sstore:
  taint_agree D X tn s t /\ word_agree_except m v w ==>
  taint_agree D X (tn with t_stor := key_update tn.t_stor key m)
    (sstore key v s) (sstore key w t)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[taint_agree_call_ctx] >>
  `ld_shared_agree D s.vs_call_ctx.cc_address
     (tn with t_stor := key_update tn.t_stor key m)
     (sstore key v s) (sstore key w t)` by
    (irule ld_shared_sstore >> simp[] >> metis_tac[taint_agree_shared]) >>
  fs[taint_agree_def] >>
  simp[taint_agree_def, sstore_def, op_taint_def] >>
  conj_tac >- gvs[sstore_def] >>
  gvs[venom_state_component_equality, op_taint_def]
QED

Theorem taint_agree_tstore:
  taint_agree D X tn s t /\ word_agree_except m v w ==>
  taint_agree D X (tn with t_trans := key_update tn.t_trans key m)
    (tstore key v s) (tstore key w t)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[taint_agree_call_ctx] >>
  `ld_shared_agree D s.vs_call_ctx.cc_address
     (tn with t_trans := key_update tn.t_trans key m)
     (tstore key v s) (tstore key w t)` by
    (irule ld_shared_tstore >> simp[] >> metis_tac[taint_agree_shared]) >>
  fs[taint_agree_def] >>
  simp[taint_agree_def, tstore_def, op_taint_def] >>
  conj_tac >- gvs[tstore_def] >>
  gvs[venom_state_component_equality, op_taint_def]
QED

Theorem taint_agree_storage_store:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode [SSTORE; TSTORE] /\ inst.inst_outputs = [] /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[taint_agree_call_ctx] >>
  fs[MEM] >>
  gvs[step_inst_base_opcode_eqs, exec_write2_def, AllCaseEqs()] >>
  `op_taint tn op1 = {}` by
    (fs[taint_ok_def] >> metis_tac[]) >>
  `eval_operand op1 s = eval_operand op1 t` by
    (drule_all taint_agree_operand_clean >> simp[]) >>
  drule_all taint_agree_operand_value >> strip_tac >>
  gvs[eval_operands_def] >>
  simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, new_site_bytes_def, sstore_def, tstore_def,
       set_var_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, FLOOKUP_DEF, SF CONJ_ss,
       DRESTRICT_UNIV] >>
  qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  Cases_on `inst.inst_opcode = SSTORE` >> gvs[]
  >- (`mask = tn with t_stor := mask.t_stor` by
        simp[Abbr `mask`, taint_component_equality] >>
      pop_assum SUBST1_TAC >> simp[Abbr `mask`] >>
      drule_all taint_agree_sstore >>
      disch_then (qspec_then `key` mp_tac) >> simp[sstore_def]) >>
  `mask = tn with t_trans := mask.t_trans` by
    simp[Abbr `mask`, taint_component_equality] >>
  pop_assum SUBST1_TAC >> simp[Abbr `mask`] >>
  drule_all taint_agree_tstore >>
  disch_then (qspec_then `key` mp_tac) >> simp[tstore_def]
QED

Theorem taint_agree_storage_abort:
  taint_agree D X tn s t /\
  MEM inst.inst_opcode [SSTORE; TSTORE] /\
  step_inst_base inst s = Abort a s' ==>
  ?t'. step_inst_base inst t = Abort a t'
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[taint_agree_call_ctx] >>
  `IS_SOME (eval_operands inst.inst_operands s) <=>
   IS_SOME (eval_operands inst.inst_operands t)` by
    (irule o1LowerDloadOpaqueTheory.eval_operands_defined_iff >>
     metis_tac[taint_agree_operand_defined]) >>
  fs[MEM] >>
  gvs[step_inst_base_opcode_eqs, exec_write2_def, AllCaseEqs()]
QED

Theorem taint_agree_storage_step:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\ inst_wf inst /\
  MEM inst.inst_opcode [SLOAD; TLOAD; SSTORE; TSTORE] ==>
  (!s'. step_inst_base inst s = OK s' ==>
    ?t'. step_inst_base inst t = OK t' /\
         taint_agree D X (step_taint inst s s' tn) s' t') /\
  (!v s'. step_inst_base inst s = IntRet v s' ==>
    ?t'. step_inst_base inst t = IntRet v t' /\ taint_agree D X tn s' t') /\
  (!s'. step_inst_base inst s = Halt s' ==>
    ?t'. step_inst_base inst t = Halt t' /\ dead_result_rel D (Halt s') (Halt t')) /\
  (!a s'. step_inst_base inst s = Abort a s' ==>
    ?t'. step_inst_base inst t = Abort a t')
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >>
      Cases_on `MEM inst.inst_opcode [SLOAD; TLOAD]`
      >- metis_tac[taint_agree_storage_load] >>
      irule taint_agree_storage_store >>
      fs[MEM] >> gvs[venomWfTheory.inst_wf_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> fs[MEM] >>
      gvs[step_inst_base_opcode_eqs, exec_read1_def, exec_write2_def, AllCaseEqs()]) >>
  conj_tac
  >- (rpt strip_tac >> fs[MEM] >>
      gvs[step_inst_base_opcode_eqs, exec_read1_def, exec_write2_def, AllCaseEqs()]) >>
  rpt strip_tac >> Cases_on `MEM inst.inst_opcode [SLOAD; TLOAD]`
  >- (fs[MEM] >> gvs[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()]) >>
  irule taint_agree_storage_abort >> fs[MEM] >> metis_tac[]
QED

Theorem taint_agree_final_taint:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode <> INVOKE /\ step_inst_base inst s = Halt sh ==>
  final_taint vs C sh (step_taint inst s sh tn) (ret_taint tn inst s)
Proof
  strip_tac >> simp[final_taint_def] >>
  qexistsl_tac [`stk`, `PG`, `G`, `tn`, `fn`, `inst`, `s`, `0`] >>
  simp[step_inst_non_invoke]
QED

Theorem taint_agree_ret:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  inst.inst_opcode = RET /\ step_inst_base inst s = IntRet v s' ==>
  ?t'. step_inst_base inst t = IntRet v t' /\ taint_agree D X tn s' t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_operand_clean >>
     gvs[taint_ok_def] >> metis_tac[]) >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  `inst.inst_operands <> []` by
    (Cases_on `inst.inst_operands` >> gvs[eval_operands_def]) >>
  drule o1LowerDloadOpaqueTheory.eval_operands_front_agree >>
  disch_then (qspecl_then [`s`, `t`, `v3::v4`] mp_tac) >>
  (impl_tac >- metis_tac[rich_listTheory.MEM_FRONT_NOT_NIL]) >> strip_tac >>
  qexists_tac `t` >> simp[] >> Cases_on `ys` >> gvs[]
QED

Theorem taint_agree_halt_result:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode <> INVOKE /\ step_inst_base inst s = Halt sh /\
  taint_within D C vs /\
  ld_shared_agree D sh.vs_call_ctx.cc_address (step_taint inst s sh tn) sh th /\
  LENGTH sh.vs_returndata = LENGTH th.vs_returndata /\
  (!i. i < LENGTH sh.vs_returndata /\ i NOTIN ret_taint tn inst s ==>
       EL i sh.vs_returndata = EL i th.vs_returndata) /\
  sh.vs_halted = th.vs_halted ==>
  dead_result_rel D (Halt sh) (Halt th)
Proof
  strip_tac >> drule_all taint_agree_final_taint >> strip_tac >>
  qpat_x_assum `taint_within _ _ _` mp_tac >>
  simp[taint_within_def] >> strip_tac >>
  irule ld_shared_halt_result >> metis_tac[]
QED

Theorem taint_agree_simple_halt:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  taint_within D C vs /\ taint_agree D X tn s t /\
  MEM inst.inst_opcode [STOP; SINK] /\ step_inst_base inst s = Halt sh ==>
  ?th. step_inst_base inst t = Halt th /\ dead_result_rel D (Halt sh) (Halt th)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by fs[MEM] >>
  drule_all taint_agree_final_taint >> strip_tac >>
  qpat_x_assum `taint_within _ _ _` mp_tac >>
  simp[taint_within_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  fs[MEM] >> (gvs[step_inst_base_opcode_eqs] >>
  irule ld_shared_halt_result >>
  gvs[taint_agree_def, ld_shared_agree_def, halt_state_def,
      step_inst_base_opcode_eqs, ret_taint_def, step_taint_def,
      mem_taint_def, out_taint_def, store_taint_def, imm_taint_def,
      adopt_reset_def, new_site_bytes_def, step_writes_def,
      source_memory_write_ranges_def, written_taint_def, range_bytes_def,
      FLOOKUP_DEF, taint_component_equality] >>
  qpat_x_assum `_ = s` (assume_tac o Q.AP_TERM `\u. u.vs_returndata`) >>
  gvs[] >> conj_tac
  >- (qexists_tac `{}` >> simp[]) >>
  qexistsl_tac [`s.vs_call_ctx.cc_address`, `tn`] >> simp[])
QED

Theorem taint_agree_assert_step:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\ inst_wf inst /\
  MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE; INVALID; REVERT] ==>
  (!s'. step_inst_base inst s = OK s' ==>
    ?t'. step_inst_base inst t = OK t' /\
         taint_agree D X (step_taint inst s s' tn) s' t') /\
  (!v s'. step_inst_base inst s = IntRet v s' ==>
    ?t'. step_inst_base inst t = IntRet v t' /\ taint_agree D X tn s' t') /\
  (!s'. step_inst_base inst s = Halt s' ==>
    ?t'. step_inst_base inst t = Halt t' /\ dead_result_rel D (Halt s') (Halt t')) /\
  (!a s'. step_inst_base inst s = Abort a s' ==>
    ?t'. step_inst_base inst t = Abort a t')
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_operand_clean >>
     gvs[taint_ok_def] >> fs[MEM] >> metis_tac[]) >>
  fs[MEM] >> (gvs[venomWfTheory.inst_wf_def, step_inst_base_opcode_eqs,
                    AllCaseEqs()] >>
    rpt conj_tac >> rpt strip_tac >>
    gvs[step_inst_base_opcode_eqs, AllCaseEqs(), MEM] >>
    qpat_x_assum `taint_agree _ _ _ _ _` mp_tac >>
    Cases_on `tn` >>
    simp[step_taint_def, mem_taint_def, out_taint_def, store_taint_def,
         imm_taint_def, adopt_reset_def, new_site_bytes_def,
         step_writes_def, source_memory_write_ranges_def, written_taint_def,
         range_bytes_def, FLOOKUP_DEF, SF CONJ_ss, set_var_taint_def,
         DRESTRICT_UNIV, taint_agree_def, ld_shared_agree_def, op_taint_def])
QED

Theorem taint_agree_return_slice:
  frame_reachable vs C stk PG G tn fn inst s /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  taint_agree D X tn s t /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN X) /\
  inst.inst_opcode = RETURN /\ inst.inst_operands = [addr;sz] /\
  eval_operand addr s = SOME p /\ eval_operand sz s = SOME len ==>
  !k. k < w2n len /\ k NOTIN ret_taint tn inst s ==>
    EL k (read_memory (w2n p) (w2n len) s) =
    EL k (read_memory (w2n p) (w2n len) t)
Proof
  rpt strip_tac >> simp[ld_read_memory_element] >>
  irule taint_agree_reachable_read_byte >>
  qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
  qpat_assum `ptr_discipline _ _ _` (irule_at Any) >>
  qexistsl_tac [`w2n p`, `w2n len`] >>
  gvs[ret_taint_def, source_memory_read_ranges_def, memory_range_of_operands_def] >>
  metis_tac[arithmeticTheory.ADD_COMM, arithmeticTheory.LESS_EQ_ADD]
QED

Theorem taint_agree_return_halt:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  taint_within D C vs /\ taint_agree D X tn s t /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN X) /\
  inst.inst_opcode = RETURN /\ step_inst_base inst s = Halt sh ==>
  ?th. step_inst_base inst t = Halt th /\ dead_result_rel D (Halt sh) (Halt th)
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_operand_clean >>
     gvs[taint_ok_def] >> metis_tac[]) >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  drule_all taint_agree_final_taint >> strip_tac >>
  qpat_x_assum `taint_within _ _ _` mp_tac >>
  simp[taint_within_def] >> strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rename1 `inst.inst_operands = [addr_op0;size_op0]` >>
  rename1 `eval_operand addr_op0 t = SOME p` >>
  rename1 `eval_operand size_op0 t = SOME len` >>
  `!k. k < w2n len /\ k NOTIN ret_taint tn inst s ==>
      EL k (read_memory (w2n p) (w2n len) s) =
      EL k (read_memory (w2n p) (w2n len) t)` by
    (rpt strip_tac >> irule taint_agree_return_slice >>
     simp[] >>
     qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_agree _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ptr_discipline _ _ _` (irule_at Any) >>
     qpat_assum `inst.inst_operands = _` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  irule ld_shared_halt_result >>
  gvs[halt_state_def, set_returndata_def, step_taint_def, store_taint_def,
      adopt_reset_def, imm_taint_def, ld_read_memory_length,
      GSYM read_memory_def] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`s.vs_call_ctx.cc_address`, `tn`] >>
  gvs[taint_agree_def, ld_shared_agree_def]
QED

Theorem taint_agree_selfdestruct_halt:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ptr_discipline lo C vs /\ taint_within D C vs /\
  taint_agree D X tn s t /\ inst.inst_opcode = SELFDESTRUCT /\
  step_inst_base inst s = Halt sh ==>
  ?th. step_inst_base inst t = Halt th /\ dead_result_rel D (Halt sh) (Halt th)
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_operand_clean >>
     gvs[taint_ok_def] >> metis_tac[]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
   s.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[taint_agree_call_ctx, taint_agree_def] >>
  `step_inst 0 C inst s = Halt sh` by simp[step_inst_non_invoke] >>
  drule_all ld_shared_selfdestruct_step >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  qexists_tac `t1` >> conj_tac
  >- gvs[step_inst_non_invoke] >>
  irule taint_agree_halt_result >>
  qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem taint_agree_terminal_step:
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  taint_within D C vs /\ taint_agree D X tn s t /\ inst_wf inst /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN X) /\
  MEM inst.inst_opcode [RET; STOP; SINK; RETURN; SELFDESTRUCT;
                       ASSERT; ASSERT_UNREACHABLE; INVALID; REVERT] ==>
  (!s'. step_inst_base inst s = OK s' ==>
    ?t'. step_inst_base inst t = OK t' /\
         taint_agree D X (step_taint inst s s' tn) s' t') /\
  (!v s'. step_inst_base inst s = IntRet v s' ==>
    ?t'. step_inst_base inst t = IntRet v t' /\ taint_agree D X tn s' t') /\
  (!s'. step_inst_base inst s = Halt s' ==>
    ?t'. step_inst_base inst t = Halt t' /\ dead_result_rel D (Halt s') (Halt t')) /\
  (!a s'. step_inst_base inst s = Abort a s' ==>
    ?t'. step_inst_base inst t = Abort a t')
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  Cases_on `MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE; INVALID; REVERT]`
  >- (irule taint_agree_assert_step >> metis_tac[]) >>
  `MEM inst.inst_opcode [RET; STOP; SINK; RETURN; SELFDESTRUCT]` by fs[MEM] >>
  conj_tac
  >- (rpt strip_tac >> fs[MEM] >>
      gvs[step_inst_base_opcode_eqs, AllCaseEqs()]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `inst.inst_opcode = RET`
      >- (irule taint_agree_ret >> metis_tac[]) >>
      fs[MEM] >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `inst.inst_opcode = RETURN`
      >- (irule taint_agree_return_halt >> metis_tac[]) >>
      Cases_on `inst.inst_opcode = SELFDESTRUCT`
      >- (irule taint_agree_selfdestruct_halt >> metis_tac[]) >>
      Cases_on `inst.inst_opcode = RET`
      >- gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
      irule taint_agree_simple_halt >> fs[MEM] >> metis_tac[]) >>
  rpt strip_tac >> fs[MEM] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[taint_agree_call_ctx] >>
  conj_tac >- metis_tac[] >>
  mp_tac o1LowerDloadOpaqueTheory.eval_operands_defined_iff >>
  disch_then (qspecl_then [`inst.inst_operands`, `s`, `t`] mp_tac) >>
  simp[] >> disch_then irule >> rpt strip_tac >>
  `eval_operand op s = eval_operand op t` by
    (irule taint_agree_operand_clean >> gvs[taint_ok_def] >> metis_tac[]) >>
  simp[]
QED

Theorem taint_agree_external_step:
  !vs C stk PG G tn fn inst s t D X lo r.
    frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
    o1_ctx_shape C /\ MEM fn C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
    ptr_discipline lo C vs /\ ~ctx_has_dalloca C /\
    taint_within D C vs /\ dead_wf D /\
    inst.inst_opcode <> INVOKE /\
    MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
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
  rpt gen_tac >> strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `MEM inst.inst_opcode [CALL; STATICCALL]`
      >- (irule taint_agree_call_ok >> metis_tac[]) >>
      Cases_on `inst.inst_opcode = DELEGATECALL`
      >- (irule taint_agree_delegatecall_ok >> metis_tac[]) >>
      irule taint_agree_create_ok >> fs[MEM] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `MEM inst.inst_opcode [CALL; STATICCALL]`
      >- metis_tac[taint_agree_call_not_terminal] >>
      Cases_on `inst.inst_opcode = DELEGATECALL`
      >- metis_tac[taint_agree_delegatecall_not_terminal] >>
      fs[MEM] >> gvs[step_inst_base_opcode_eqs, AllCaseEqs(), exec_create_not_IntRet]) >>
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `MEM inst.inst_opcode [CALL; STATICCALL]`
      >- metis_tac[taint_agree_call_not_terminal] >>
      Cases_on `inst.inst_opcode = DELEGATECALL`
      >- metis_tac[taint_agree_delegatecall_not_terminal] >>
      fs[MEM] >> gvs[step_inst_base_opcode_eqs, AllCaseEqs(), exec_create_not_Halt]) >>
  rpt strip_tac >>
  Cases_on `MEM inst.inst_opcode [CALL; STATICCALL]`
  >- (irule taint_agree_call_abort >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = DELEGATECALL`
  >- (irule taint_agree_delegatecall_abort >> metis_tac[]) >>
  irule taint_agree_create_abort >> fs[MEM] >> metis_tac[]
QED

Theorem taint_agree_dload:
  taint_agree D X tn s t /\ taint_ok fn tn inst s /\
  inst.inst_opcode = DLOAD /\ step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
       taint_agree D X (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  `s.vs_data_section = t.vs_data_section` by
    (drule taint_agree_frame >> simp[venomStateTheory.venom_state_component_equality]) >>
  `!u. out_taint tn inst u = {}` by
    (gen_tac >> irule o1LowerDloadJointRead0Theory.ld_out_taint_default >> simp[]) >>
  gvs[step_inst_base_opcode_eqs] >>
  drule_at (Pat `exec_read1 _ _ _ = _`) taint_agree_exec_read1_clean >>
  simp[] >> disch_then drule >> simp[] >>
  disch_then (qx_choose_then `target` strip_assume_tac) >>
  qexists_tac `target` >> simp[] >>
  qpat_x_assum `exec_read1 _ inst s = _` mp_tac >>
  simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `taint_agree _ _ _ _ _` mp_tac >>
  simp[step_taint_def, mem_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, new_site_bytes_def, update_var_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, FLOOKUP_DEF, SF CONJ_ss] >>
  strip_tac >> qmatch_goalsub_abbrev_tac `taint_agree D X mask` >>
  `mask = tn with t_var := mask.t_var` by
    simp[Abbr `mask`, taint_component_equality] >>
  pop_assum SUBST1_TAC >> simp[Abbr `mask`]
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
  rpt gen_tac >> strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `wf_function fn /\ fn_inst_wf fn` by
    (gvs[o1PassContractTheory.o1_ctx_shape_def, listTheory.EVERY_MEM] >>
     metis_tac[o1PassContractTheory.o1_fn_shape_def]) >>
  `inst_wf inst` by
    (gvs[active_inst_def, venomWfTheory.fn_inst_wf_def] >>
     metis_tac[listTheory.MEM_EL]) >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, venomInstTheory.fn_insts_def,
        o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  `inst.inst_opcode <> MEMTOP /\ inst.inst_opcode <> DRET /\
   inst.inst_opcode <> GETFMP /\ inst.inst_opcode <> SETFMP /\
   inst.inst_opcode <> RETFMP /\ inst.inst_opcode <> FMP_PARAM` by
    (drule o1LowerDloadPtrDisciplineTheory.ptr_discipline_fn_ptr_ok >>
     strip_tac >> fs[EVERY_MEM] >>
     `fn_ptr_ok P fn` by metis_tac[] >> fs[fn_ptr_ok_def]) >>
  Cases_on `MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]`
  >- (irule taint_agree_external_step >> metis_tac[]) >>
  qpat_x_assum `step_inst_base inst s = r` (SUBST_ALL_TAC o SYM) >>
  Cases_on `MEM inst.inst_opcode [ALLOCA; DALLOCA]`
  >- (irule taint_agree_allocation_step >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [MLOAD; ILOAD; MSTORE; ISTORE; MSTORE8]`
  >- (irule taint_agree_load_store_step >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode
    [MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY; EXTCODECOPY]`
  >- (irule taint_agree_copy_step >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [SHA3; LOG]`
  >- (irule taint_agree_memory_observation_step >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [SLOAD; TLOAD; SSTORE; TSTORE]`
  >- (irule taint_agree_storage_step >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE; INVALID; REVERT]`
  >- (irule taint_agree_assert_step >> metis_tac[]) >>
  `~in_revert_forward fn s` by
    (spose_not_then assume_tac >>
     gvs[in_revert_forward_def, active_inst_def] >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
       (irule venomExecPropsTheory.MEM_lookup_block >>
        gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]) >>
     gvs[] >>
     `get_instruction bb s.vs_inst_idx = SOME (EL s.vs_inst_idx bb.bb_instructions)` by
       simp[venomInstTheory.get_instruction_def] >>
     drule_all memSafeRunTheory.revert_forward_at_opcode >> fs[MEM]) >>
  Cases_on `MEM inst.inst_opcode [RET; STOP; SINK; RETURN; SELFDESTRUCT]`
  >- (irule taint_agree_terminal_step >> fs[MEM] >> metis_tac[]) >>
  suspend "ordinary"
QED

Resume taint_agree_step_base[ordinary]:
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `MEM inst.inst_opcode
        [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; EQ; LT; GT; SLT; SGT;
         AND; OR; XOR; SIGNEXTEND; BYTE; OFFSET]`
      >- (irule taint_agree_pure2 >> metis_tac[]) >>
      Cases_on `MEM inst.inst_opcode [ISZERO; NOT]`
      >- (irule taint_agree_pure1 >> metis_tac[]) >>
      Cases_on `MEM inst.inst_opcode [ADDMOD; MULMOD]`
      >- (irule taint_agree_pure3 >> metis_tac[]) >>
      Cases_on `MEM inst.inst_opcode [SHL; SHR; SAR]`
      >- (irule taint_agree_shift >> metis_tac[]) >>
      Cases_on `MEM inst.inst_opcode
        [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
         COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
         BLOBBASEFEE; CALLDATASIZE; CODESIZE; RETURNDATASIZE; SELFBALANCE]`
      >- (irule taint_agree_read0 >> metis_tac[]) >>
      Cases_on `MEM inst.inst_opcode
        [BLOCKHASH; BLOBHASH; BALANCE; EXTCODESIZE; EXTCODEHASH; CALLDATALOAD]`
      >- (irule taint_agree_read1 >> metis_tac[]) >>
      Cases_on `MEM inst.inst_opcode [PARAM; RETPC_PARAM; INITIAL_FMP]`
      >- (irule taint_agree_frame_scalar >> metis_tac[]) >>
      suspend "small_ok") >>
  suspend "ordinary_terminal"
QED

Resume taint_agree_step_base[small_ok]:
  Cases_on `inst.inst_opcode = DLOAD`
  >- (irule taint_agree_dload >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = ASSIGN`
  >- (irule taint_agree_assign >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = GAS`
  >- (irule taint_agree_gas >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = BUMP`
  >- (irule taint_agree_bump >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = NOP`
  >- (irule taint_agree_identity >> simp[] >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [JMP; JNZ; DJMP]`
  >- (irule taint_agree_jump >>
      `inst.inst_outputs = []` by
        (fs[MEM] >> gvs[venomWfTheory.inst_wf_def]) >> metis_tac[]) >>
  fs[MEM] >> Cases_on `inst.inst_opcode` >>
  TRY (qpat_x_assum `~(c = c)` mp_tac >> simp[] >> NO_TAC) >>
  gvs[step_inst_base_opcode_eqs]
QED

Resume taint_agree_step_base[ordinary_terminal]:
  fs[MEM] >> Cases_on `inst.inst_opcode` >>
  TRY (qpat_x_assum `~(c = c)` mp_tac >> simp[] >> NO_TAC) >>
  qpat_x_assum `inst.inst_opcode = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> strip_tac
  >~ [`inst.inst_opcode = ADD`] >- suspend "term_ADD"
  >~ [`inst.inst_opcode = SUB`] >- suspend "term_SUB"
  >~ [`inst.inst_opcode = MUL`] >- suspend "term_MUL"
  >~ [`inst.inst_opcode = Div`] >- suspend "term_Div"
  >~ [`inst.inst_opcode = Mod`] >- suspend "term_Mod"
  >~ [`inst.inst_opcode = SDIV`] >- suspend "term_SDIV"
  >~ [`inst.inst_opcode = SMOD`] >- suspend "term_SMOD"
  >~ [`inst.inst_opcode = Exp`] >- suspend "term_Exp"
  >~ [`inst.inst_opcode = EQ`] >- suspend "term_EQ"
  >~ [`inst.inst_opcode = LT`] >- suspend "term_LT"
  >~ [`inst.inst_opcode = GT`] >- suspend "term_GT"
  >~ [`inst.inst_opcode = SLT`] >- suspend "term_SLT"
  >~ [`inst.inst_opcode = SGT`] >- suspend "term_SGT"
  >~ [`inst.inst_opcode = AND`] >- suspend "term_AND"
  >~ [`inst.inst_opcode = OR`] >- suspend "term_OR"
  >~ [`inst.inst_opcode = XOR`] >- suspend "term_XOR"
  >~ [`inst.inst_opcode = SIGNEXTEND`] >- suspend "term_SIGNEXTEND"
  >~ [`inst.inst_opcode = BYTE`] >- suspend "term_BYTE"
  >~ [`inst.inst_opcode = OFFSET`] >- suspend "term_OFFSET"
  >~ [`inst.inst_opcode = ISZERO`] >- suspend "term_ISZERO"
  >~ [`inst.inst_opcode = NOT`] >- suspend "term_NOT"
  >~ [`inst.inst_opcode = ADDMOD`] >- suspend "term_ADDMOD"
  >~ [`inst.inst_opcode = MULMOD`] >- suspend "term_MULMOD"
  >~ [`inst.inst_opcode = SHL`] >- suspend "term_SHL"
  >~ [`inst.inst_opcode = SHR`] >- suspend "term_SHR"
  >~ [`inst.inst_opcode = SAR`] >- suspend "term_SAR"
  >~ [`inst.inst_opcode = CALLER`] >- suspend "term_CALLER"
  >~ [`inst.inst_opcode = ADDRESS`] >- suspend "term_ADDRESS"
  >~ [`inst.inst_opcode = CALLVALUE`] >- suspend "term_CALLVALUE"
  >~ [`inst.inst_opcode = ORIGIN`] >- suspend "term_ORIGIN"
  >~ [`inst.inst_opcode = GASPRICE`] >- suspend "term_GASPRICE"
  >~ [`inst.inst_opcode = CHAINID`] >- suspend "term_CHAINID"
  >~ [`inst.inst_opcode = COINBASE`] >- suspend "term_COINBASE"
  >~ [`inst.inst_opcode = TIMESTAMP`] >- suspend "term_TIMESTAMP"
  >~ [`inst.inst_opcode = NUMBER`] >- suspend "term_NUMBER"
  >~ [`inst.inst_opcode = PREVRANDAO`] >- suspend "term_PREVRANDAO"
  >~ [`inst.inst_opcode = GASLIMIT`] >- suspend "term_GASLIMIT"
  >~ [`inst.inst_opcode = BASEFEE`] >- suspend "term_BASEFEE"
  >~ [`inst.inst_opcode = BLOBBASEFEE`] >- suspend "term_BLOBBASEFEE"
  >~ [`inst.inst_opcode = CALLDATASIZE`] >- suspend "term_CALLDATASIZE"
  >~ [`inst.inst_opcode = CODESIZE`] >- suspend "term_CODESIZE"
  >~ [`inst.inst_opcode = RETURNDATASIZE`] >- suspend "term_RETURNDATASIZE"
  >~ [`inst.inst_opcode = SELFBALANCE`] >- suspend "term_SELFBALANCE"
  >~ [`inst.inst_opcode = BLOCKHASH`] >- suspend "term_BLOCKHASH"
  >~ [`inst.inst_opcode = BLOBHASH`] >- suspend "term_BLOBHASH"
  >~ [`inst.inst_opcode = BALANCE`] >- suspend "term_BALANCE"
  >~ [`inst.inst_opcode = EXTCODESIZE`] >- suspend "term_EXTCODESIZE"
  >~ [`inst.inst_opcode = EXTCODEHASH`] >- suspend "term_EXTCODEHASH"
  >~ [`inst.inst_opcode = CALLDATALOAD`] >- suspend "term_CALLDATALOAD"
  >~ [`inst.inst_opcode = DLOAD`] >- suspend "term_DLOAD"
  >~ [`inst.inst_opcode = PARAM`] >- suspend "term_PARAM"
  >~ [`inst.inst_opcode = RETPC_PARAM`] >- suspend "term_RETPC_PARAM"
  >~ [`inst.inst_opcode = INITIAL_FMP`] >- suspend "term_INITIAL_FMP"
  >~ [`inst.inst_opcode = ASSIGN`] >- suspend "term_ASSIGN"
  >~ [`inst.inst_opcode = GAS`] >- suspend "term_GAS"
  >~ [`inst.inst_opcode = BUMP`] >- suspend "term_BUMP"
  >~ [`inst.inst_opcode = NOP`] >- suspend "term_NOP"
  >~ [`inst.inst_opcode = JMP`] >- suspend "term_JMP"
  >~ [`inst.inst_opcode = JNZ`] >- suspend "term_JNZ"
  >~ [`inst.inst_opcode = DJMP`] >- suspend "term_DJMP"
  >~ [`inst.inst_opcode = PHI`] >- suspend "term_PHI"
QED

Resume taint_agree_step_base[term_ADD]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_SUB]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_MUL]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_Div]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_Mod]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_SDIV]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_SMOD]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_Exp]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_EQ]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_LT]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_GT]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_SLT]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_SGT]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_AND]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_OR]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_XOR]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_SIGNEXTEND]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_BYTE]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_OFFSET]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_ISZERO]: simp[step_inst_base_opcode_eqs, exec_pure1_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_NOT]: simp[step_inst_base_opcode_eqs, exec_pure1_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_ADDMOD]: simp[step_inst_base_opcode_eqs, exec_pure3_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_MULMOD]: simp[step_inst_base_opcode_eqs, exec_pure3_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_SHL]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_SHR]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_SAR]: simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_CALLER]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_ADDRESS]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_CALLVALUE]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_ORIGIN]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_GASPRICE]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_CHAINID]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_COINBASE]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_TIMESTAMP]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_NUMBER]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_PREVRANDAO]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_GASLIMIT]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_BASEFEE]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_BLOBBASEFEE]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_CALLDATASIZE]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_CODESIZE]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_RETURNDATASIZE]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_SELFBALANCE]: simp[step_inst_base_opcode_eqs, exec_read0_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_BLOCKHASH]: simp[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_BLOBHASH]: simp[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_BALANCE]: simp[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_EXTCODESIZE]: simp[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_EXTCODEHASH]: simp[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_CALLDATALOAD]: simp[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_DLOAD]: simp[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_PARAM]: simp[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_RETPC_PARAM]: simp[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_INITIAL_FMP]: simp[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_ASSIGN]: simp[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_GAS]: simp[step_inst_base_opcode_eqs, exec_gas_def, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_BUMP]: simp[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_NOP]: simp[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_JMP]: simp[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_JNZ]: simp[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_DJMP]: simp[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Resume taint_agree_step_base[term_PHI]: simp[step_inst_base_opcode_eqs, AllCaseEqs()]
QED


Finalise taint_agree_step_base
