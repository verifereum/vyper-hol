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
  o1LowerDloadHaltResult o1LowerDloadJointStorageWrite o1LowerDloadStackFrontier
  o1LowerDloadRangeTransport o1LowerDloadJointMemoryRead
  o1LowerDloadMemoryConsumer o1LowerDloadJointInternalEffects
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

Theorem taint_agree_call_ctx:
  taint_agree D X tn s t ==> s.vs_call_ctx = t.vs_call_ctx
Proof
  strip_tac >> drule taint_agree_frame >>
  disch_then (mp_tac o Q.AP_TERM `\u. u.vs_call_ctx`) >> simp[]
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
