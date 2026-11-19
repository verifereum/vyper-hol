Theory requestCutConcretizeVisit
Ancestors
  lowerDloadDefs unitTransformDefs
  requestCutConcretizeOperands requestCutReplayProofs requestCutOracleReplay
  concretizePtrPairedPrefix concretizePtrMloadRecovery concretizePtrRequestHistory
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrSourceOwnership concretizePtrParamSupport concretizePtrParamShape
  concretizePtrChronologicalDemand concretizePtrOperationalOpcodes
  concretizePtrOpaqueRetpc concretizePtrValueTransport
  lowerDloadExternalInputs lowerDloadRequestObservation lowerDloadPtrCall
  ptrDiscipline o1PassContract unitShapeDefs frameRawProjection
  venomExecSemantics venomInst venomWf venomState memLocDefs concretizeMemLocDefs
  codegenRel contextCodegenRel copyFwdEquiv allocaRemapDefs
  list rich_list arithmetic finite_map pred_set words

Theorem external_input_range[local]:
  ((i.inst_opcode = CALL /\ i.inst_operands = [g;addr;v;off;sz;ro;rs] /\
     scalars = [g;addr;v;sz;rs]) \/
   (MEM i.inst_opcode [STATICCALL;DELEGATECALL] /\
    i.inst_operands = [g;addr;off;sz;ro;rs] /\ scalars = [g;addr;sz;rs]) \/
   (i.inst_opcode = CREATE /\ i.inst_operands = [v;off;sz] /\ scalars = [v;sz]) \/
   (i.inst_opcode = CREATE2 /\ i.inst_operands = [v;off;sz;salt] /\
    scalars = [v;sz;salt])) /\
  (!op. MEM op i.inst_operands ==> ?x. eval_operand op s = SOME x) /\
  eval_operand off s = SOME p /\ eval_operand sz s = SOME bytes ==>
  mem_read_ops i = SOME (THE (mem_read_ops i)) /\
  (THE (mem_read_ops i)).iao_ofst = off /\
  inst_read_op i = SOME off /\
  MEM (w2n p,w2n bytes) (source_memory_read_ranges i s)
Proof
  simp[MEM] >> strip_tac >>
  qpat_x_assum `!op. _ ==> ?x. _` mp_tac >>
  simp[MEM, DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
  simp[mem_read_ops_def, inst_read_op_def, source_memory_read_ranges_def,
       memory_range_of_operands_def]
QED

Theorem request_cut_concretize_visit:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  ptr_paired_prefix R lp positions lo clip0 C CT
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C CT /\
  o1_ctx_shape C /\ o1_initial_state_ok clip0 /\ clip0.vs_fmp = clip0.vs_initial_fmp /\
  code_layout_valid clip0 /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C clip0 /\ fixed_region_reserved lo C /\ ptr_discipline lo C clip0 /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom CT = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n clip0.vs_initial_fmp) /\
  frame_reachable clip0 C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  a.po_state = (s with vs_outcomes := []) /\ at.po_state = (t with vs_outcomes := []) /\
  s.vs_outcomes = t.vs_outcomes /\ LENGTH s.vs_requests = k /\ LENGTH t.vs_requests = k /\
  MEM a.po_inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  step_inst fuel CT a.po_inst t = OK t' /\ k < LENGTH t'.vs_requests ==>
  ?s'. step_inst fuel C a.po_inst s = OK s' /\ k < LENGTH s'.vs_requests /\
    (a.po_taint.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
     a.po_taint.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address) ==>
     request_agree_except D (EL k s'.vs_requests) (EL k t'.vs_requests))
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    simp[o1_ctx_shape_instructions_wf] >>
  drule_all ptr_source_ownership_prov_erases >> strip_tac >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `FDOM a.po_prov SUBSET fn_pv P a.po_fn` by
    (fs[ptr_static_support_def, SUBSET_DEF, FLOOKUP_DEF] >>
     metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    metis_tac[ptr_frame_operand_instructions] >>
  `inst_wf a.po_inst` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `o1_fn_shape C a.po_fn` by (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `opaque_use_ok a.po_fn` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  `ptr_use_ok P (fn_pv P a.po_fn) a.po_inst` by
    (fs[fn_ptr_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> fs[MEM]) >>
  qpat_x_assum `ptr_paired_sample positions a at _`
    (strip_assume_tac o REWRITE_RULE [ptr_paired_sample_def]) >>
  `a.po_state.vs_labels = at.po_state.vs_labels` by
    metis_tac[ptr_history_content_labels] >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (drule ptr_history_content_call_ctx >> simp[]) >>
  mp_tac (Q.INST [`tn` |-> `a.po_taint`, `fn` |-> `a.po_fn`, `gn` |-> `at.po_fn`,
    `s` |-> `a.po_state`, `t` |-> `at.po_state`,
    `dyn` |-> `dyn_floor C clip0`, `G` |-> `a.po_prov`,
    `pv` |-> `fn_pv P a.po_fn`, `i` |-> `a.po_inst`] request_cut_concretize_operands) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  simp[] >> strip_tac >>
  qpat_assum `step_inst fuel CT a.po_inst t = OK t'` (fn step =>
    qpat_assum `MEM a.po_inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]`
      (fn external => assume_tac
        (MATCH_MP ld_external_target_operands_defined (CONJ external step)))) >>
  `!op. MEM op a.po_inst.inst_operands ==> ?x y.
    eval_operand op s = SOME x /\ eval_operand op t = SOME y` by
    (rpt strip_tac >>
     qpat_assum `!op. MEM op a.po_inst.inst_operands ==> _ /\ _`
       (qspec_then `op` (drule_then strip_assume_tac)) >>
     qpat_assum `!op. MEM op a.po_inst.inst_operands ==> ?w. eval_operand op t = SOME w`
       (qspec_then `op` (drule_then strip_assume_tac)) >>
     Cases_on `eval_operand op s` >> fs[]) >>
  Q.SUBGOAL_THEN `?g addr v off sz ro rs salt scalars.
     (a.po_inst.inst_opcode = CALL /\ a.po_inst.inst_operands = [g;addr;v;off;sz;ro;rs] /\
      scalars = [g;addr;v;sz;rs]) \/
     (MEM a.po_inst.inst_opcode [STATICCALL;DELEGATECALL] /\
      a.po_inst.inst_operands = [g;addr;off;sz;ro;rs] /\ scalars = [g;addr;sz;rs]) \/
     (a.po_inst.inst_opcode = CREATE /\ a.po_inst.inst_operands = [v;off;sz] /\
      scalars = [v;sz]) \/
     (a.po_inst.inst_opcode = CREATE2 /\ a.po_inst.inst_operands = [v;off;sz;salt] /\
      scalars = [v;sz;salt])`
    (qx_choosel_then [`g`,`addr`,`v`,`off`,`sz`,`ro`,`rs`,`salt`,`scalars`] assume_tac)
  >- (
    qpat_assum `MEM a.po_inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]`
      (strip_assume_tac o REWRITE_RULE [MEM]) >>
    fs[MEM,inst_wf_def,LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  `!op. MEM op scalars ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     drule ld_external_layout_scalars >>
     disch_then (qspec_then `op` mp_tac) >> simp[] >> metis_tac[]) >>
  `MEM off a.po_inst.inst_operands /\ MEM sz a.po_inst.inst_operands /\ MEM sz scalars` by
    gvs[MEM] >>
  `?p q bytes. eval_operand off s = SOME p /\ eval_operand off t = SOME q /\
    eval_operand sz s = SOME bytes /\ eval_operand sz t = SOME bytes` by metis_tac[] >>
  `mem_read_ops a.po_inst = SOME (THE (mem_read_ops a.po_inst)) /\
    (THE (mem_read_ops a.po_inst)).iao_ofst = off /\
    inst_read_op a.po_inst = SOME off /\
    MEM (w2n p,w2n bytes) (source_memory_read_ranges a.po_inst a.po_state)` by
    (mp_tac (Q.INST [`i` |-> `a.po_inst`,
        `s` |-> `s with vs_outcomes := []`] external_input_range) >>
     (impl_tac >- (simp[] >> metis_tac[])) >>
     simp[]) >>
  `ptr_lookup_transport births positions (op_prov TG off) {} (SOME p) (SOME q)` by
    metis_tac[] >>
  `!j. j < w2n bytes ==> w2n p + j NOTIN a.po_taint.t_mem` by
    (rpt strip_tac >>
     `w2n p <= w2n p + j /\ w2n p + j < w2n p + w2n bytes` by decide_tac >>
     `~about_to_revert a.po_fn a.po_inst a.po_state` by
       fs[MEM, about_to_revert_def] >>
     qpat_assum `taint_ok _ _ _ _`
       (fn taint =>
          qpat_assum `~about_to_revert _ _ _` (fn live =>
            mp_tac (MATCH_MP (CONJUNCT1 (CONJUNCT2 (REWRITE_RULE [taint_ok_def] taint))) live))) >>
     disch_then (qspecl_then [`w2n p`,`w2n bytes`,`w2n p + j`] mp_tac) >>
     simp[] >>
     qpat_assum `MEM a.po_inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]`
       (strip_assume_tac o REWRITE_RULE [MEM]) >> simp[]) >>
  `a.po_inst.inst_opcode <> ASSIGN` by fs[MEM] >>
  `read_memory (w2n p) (w2n bytes) s = read_memory (w2n q) (w2n bytes) t` by
    (`!j. j < w2n bytes ==> read_byte (w2n p + j) s.vs_memory =
                         read_byte (w2n q + j) t.vs_memory` by
      (mp_tac (Q.INST [`ops` |-> `THE (mem_read_ops a.po_inst)`,
        `x` |-> `p`, `y` |-> `q`, `n` |-> `w2n (bytes:256 word)`, `C'` |-> `CT`,
        `vs` |-> `clip0`] ptr_paired_read_range_masked_bytes_static) >>
       (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
       simp[] >> metis_tac[ADD_COMM]) >>
     irule LIST_EQ >> simp[read_memory_def, LENGTH_TAKE_EQ] >>
     rpt strip_tac >>
     simp[take_drop_replicate_el, GSYM read_byte_def, mem_byte_at_def]) >>
  `a.po_inst.inst_opcode <> INVOKE` by fs[MEM] >>
  qabbrev_tac `shell_scalars = if MEM a.po_inst.inst_opcode [CALL;STATICCALL;DELEGATECALL]
    then TAKE (PRE (LENGTH scalars)) scalars else scalars` >>
  `((a.po_inst.inst_opcode = CALL /\ a.po_inst.inst_operands = [g;addr;v;off;sz;ro;rs] /\
      shell_scalars = [g;addr;v;sz]) \/
    (MEM a.po_inst.inst_opcode [STATICCALL;DELEGATECALL] /\
     a.po_inst.inst_operands = [g;addr;off;sz;ro;rs] /\ shell_scalars = [g;addr;sz]) \/
    (a.po_inst.inst_opcode = CREATE /\ a.po_inst.inst_operands = [v;off;sz] /\
     shell_scalars = [v;sz]) \/
    (a.po_inst.inst_opcode = CREATE2 /\ a.po_inst.inst_operands = [v;off;sz;salt] /\
     shell_scalars = [v;sz;salt])) /\
    (!op. MEM op shell_scalars ==> MEM op scalars)` by
    (qpat_assum `(a.po_inst.inst_opcode = CALL /\ _) \/ _`
       (strip_assume_tac o REWRITE_RULE [MEM]) >>
     simp[Abbr `shell_scalars`, MEM, DISJ_IMP_THM, FORALL_AND_THM]) >>
  `!op. MEM op shell_scalars ==> eval_operand op s = eval_operand op t` by metis_tac[] >>
  `!op. MEM op a.po_inst.inst_operands ==> ?w. eval_operand op s = SOME w` by
    (rpt strip_tac >>
     qpat_assum `!op. _ ==> ?x y. _` (qspec_then `op` mp_tac) >> simp[] >> metis_tac[]) >>
  `?s'. step_inst fuel C a.po_inst s = OK s'` by
    (mp_tac (Q.INST [`inst` |-> `a.po_inst`, `CS` |-> `C`,
       `scalars` |-> `shell_scalars`]
       (Q.INST [`a` |-> `addr`] request_step_relocated_backward)) >>
     (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
     simp[]) >>
  `k < LENGTH s'.vs_requests` by metis_tac[external_ok_records_request, DECIDE ``k < SUC k``] >>
  qexists_tac `s'` >> simp[] >> strip_tac >>
  `ptr_request_shell (LAST s'.vs_requests) (LAST t'.vs_requests)` by
    (mp_tac (Q.INST [`inst` |-> `a.po_inst`, `C'` |-> `CT`, `fuel'` |-> `fuel`,
       `scalars` |-> `shell_scalars`, `n` |-> `bytes`, `u` |-> `s'`, `u'` |-> `t'`]
       (Q.INST [`a` |-> `addr`] request_step_relocated_shell)) >>
     simp[]) >>
  `dload_shared_store a.po_taint a.po_taint s t` by
    (qpat_assum `ptr_history_content _ _ _`
       (mp_tac o MATCH_MP request_cut_concretize_store) >>
     simp[lowerDloadPtrCallTheory.dload_shared_store_def]) >>
  irule relocated_request_agrees >> simp[] >>
  qexistsl_tac [`C`,`CT`,`fuel`,`fuel`,`a.po_inst`,`a.po_inst`,`s`,`t`,
    `a.po_taint`,`a.po_taint`] >> simp[]
QED
