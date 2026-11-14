Theory readonlyInvokeCopyFwdExecutionHalt
Ancestors
  allocaFrontierBound
  pointerConfinedDefs
  readonlyInvokeCopyFwdExecutionReadClassification readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdMapCoverage
  readonlyInvokeCopyFwdExecutionMemoryScalars
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdOperationalSupport
  o1LowerDloadOccurrence o1LowerDloadShared o1LowerDloadRangeTransport
  internalReturnCopyFwdSim frameViewFacts frameRel unitShapeDefs
  ptrDiscipline taintAgree venomExecSemantics venomState venomInst
  codegenRel contextCodegenRel finite_map list pred_set words

Theorem ricf_execution_return_halt:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_mapped_support a B E PG G sites /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ taint_within D C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = RETURN /\ inst.inst_operands = [addr;sizeop] /\
  eval_operand addr s = SOME p /\ eval_operand sizeop s = SOME len /\
  step_inst fuel C inst s = Halt sh ==>
  ?th. step_inst fuel Ct inst t = Halt th /\ dead_result_rel D (Halt sh) (Halt th)
Proof
  strip_tac >> rename1 `eval_operand sizeop s = SOME size_word` >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn addr = {}` by (gvs[taint_ok_def] >> metis_tac[]) >>
  `op_taint tn sizeop = {}` by (gvs[taint_ok_def] >> metis_tac[]) >>
  `eval_operand sizeop t = SOME size_word` by
    (mp_tac (Q.INST [`op` |-> `sizeop`, `x` |-> `size_word:256 word`, `rt` |-> `tn`]
       ricf_execution_nonaddress_operand) >>
     (impl_tac >- (simp[is_pointer_preserving_op_def, memLocDefsTheory.mem_read_ops_def,
       memLocDefsTheory.mem_write_ops_def] >>
       Cases_on `sizeop = addr` >> simp[FILTER])) >> simp[]) >>
  `!name. addr = Var name ==> ~retpc_var fn name` by
    (rpt gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> simp[] >> metis_tac[active_inst_mem_fn_insts]) >>
  `mem_read_ops inst = SOME <|iao_ofst := addr; iao_size := SOME sizeop;
      iao_max_size := SOME sizeop|> /\
   MEM (w2n p,w2n size_word) (source_memory_read_ranges inst s)` by
    simp[memLocDefsTheory.mem_read_ops_def, source_memory_read_ranges_def,
      memory_range_of_operands_def] >>
  `?q. eval_operand addr t = SOME q /\
    (!k. k < w2n size_word /\ w2n p+k NOTIN tn.t_mem ==>
      read_byte (w2n p+k) s.vs_memory = read_byte (w2n q+k) t.vs_memory)` by
    (mp_tac (Q.INST [`x` |-> `p:256 word`, `len` |-> `w2n (size_word:256 word)`,
       `ops` |-> `<|iao_ofst := addr; iao_size := SOME sizeop;
         iao_max_size := SOME sizeop|>`] ricf_execution_read_bytes) >>
     (impl_tac >- simp[]) >> simp[]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
   t.vs_call_ctx = s.vs_call_ctx` by
    (`ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
       sites (ricf_complete_params PG s.vs_params) G tn s t` by
       fs[ricf_execution_invariant_def] >>
     qpat_x_assum `ricf_opaque_frame_agree _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >> strip_tac >>
     drule taint_agree_shared >> drule taint_agree_call_ctx >>
     simp[ricf_opaque_view_def, ld_shared_agree_def]) >>
  `final_taint vs C sh (step_taint inst s sh tn) (ret_taint tn inst s)` by
    (simp[final_taint_def] >>
     qexistsl_tac [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`fuel`] >> simp[]) >>
  `ret_taint tn inst s =
    {i | i < w2n size_word /\ w2n p+i IN tn.t_mem}` by simp[ret_taint_def] >>
  `(step_taint inst s sh tn).t_stor SUBSET
      D.d_stor sh.vs_call_ctx.cc_address
        (sh.vs_accounts sh.vs_call_ctx.cc_address).storage /\
   (step_taint inst s sh tn).t_trans SUBSET
      D.d_trans sh.vs_call_ctx.cc_address (sh.vs_transient sh.vs_call_ctx.cc_address) /\
   (step_taint inst s sh tn).t_imm SUBSET D.d_imm sh.vs_immutables /\
   ret_taint tn inst s SUBSET D.d_ret sh.vs_returndata` by
    (fs[taint_within_def] >> metis_tac[]) >>
  qexists_tac `halt_state (set_returndata (read_memory (w2n q) (w2n size_word) t) t)` >>
  conj_tac
  >- simp[step_inst_non_invoke, step_inst_base_opcode_eqs, read_memory_def] >>
  qpat_x_assum `step_inst fuel C inst s = Halt sh` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, GSYM read_memory_def] >>
  strip_tac >> gvs[] >>
  mp_tac (Q.INST [`A` |-> `s.vs_call_ctx.cc_address`,
    `s` |-> `halt_state (set_returndata
      (read_memory (w2n (p:256 word)) (w2n (size_word:256 word)) s) s)`,
    `t` |-> `halt_state (set_returndata
      (read_memory (w2n (q:256 word)) (w2n (size_word:256 word)) t) t)`,
    `tn` |-> `step_taint inst s
      (halt_state (set_returndata
        (read_memory (w2n (p:256 word)) (w2n (size_word:256 word)) s) s)) tn`,
    `R` |-> `{i | i < w2n (size_word:256 word) /\
       w2n (p:256 word)+i IN tn.t_mem}`] ld_shared_halt_result) >>
  (impl_tac >- (gvs[halt_state_def, set_returndata_def, step_taint_def,
    store_taint_def, adopt_reset_def, imm_taint_def, ld_read_memory_length,
    ld_shared_agree_def] >>
  rpt strip_tac >> simp[ld_read_memory_element] >>
  fs[] >> metis_tac[])) >> simp[halt_state_def, set_returndata_def]
QED

Theorem ricf_execution_return_result:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_mapped_support a B E PG G sites /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_ssa C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ taint_within D C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = RETURN /\ step_inst fuel C inst s = Halt sh ==>
  ?th. step_inst fuel Ct inst t = Halt th /\ dead_result_rel D (Halt sh) (Halt th)
Proof
  strip_tac >>
  `?addr sizeop p len. inst.inst_operands = [addr;sizeop] /\
    eval_operand addr s = SOME p /\ eval_operand sizeop s = SOME len` by
    (qpat_x_assum `step_inst fuel C inst s = Halt sh` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
     gvs[AllCaseEqs()] >> metis_tac[]) >>
  mp_tac ricf_execution_return_halt >> (impl_tac >- simp[]) >> simp[]
QED
