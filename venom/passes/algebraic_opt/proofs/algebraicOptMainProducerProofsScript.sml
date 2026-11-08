Theory algebraicOptMainProducerProofs
Ancestors
  algebraicOptMainScalarProofs algebraicOptFreshnessProofs
  algebraicOptRangeConditionProofs algebraicOptRangeLocalProofs
  venomInst venomState venomExecSemantics venomExecProps algebraicOptDefs
  algebraicOptComposeProofs algebraicOptRelationProofs algebraicOptCmpChunkProofs
  algebraicOptTraceProofs
Libs
  listTheory

Theorem ao_source_signextend_absorbed:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
  ao_source_trace ctx fn trace /\ LAST trace = (h,F,s) /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  dfg_get_def (dfg_build_function fn) x = SOME prod /\
  prod.inst_opcode = SIGNEXTEND /\ prod.inst_operands = [Lit inner; a] /\
  inner <=+ outer /\ lookup_var x s = SOME value ==>
  sign_extend outer value = value
Proof
  strip_tac >>
  `prod.inst_opcode <> PHI /\ ~is_terminator prod.inst_opcode` by
    simp[is_terminator_def] >>
  drule_all ao_dfg_source_producer >> strip_tac >>
  `MEM prod (fn_insts fn)` by metis_tac[dfgAnalysisPropsTheory.dfg_build_function_correct] >>
  `lookup_var x (SND (SND (HD trace))) = NONE` by metis_tac[] >>
  drule_all ao_source_trace_last_output >> strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def,
      eval_operand_def, AllCaseEqs(), lookup_var_def, update_var_def] >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
  irule ao_sign_extend_absorb >> simp[]
QED

Theorem ao_main_signextend_producer_chunk:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
  ao_source_trace ctx fn trace /\ LAST trace = (h,F,s) /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  MEM inst (fn_insts fn) /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = SIGNEXTEND /\ step_inst_base inst s = OK t /\
  ao_main_observations fn V s r /\ s.vs_labels = r.vs_labels /\
  (!i x. MEM i (fn_insts fn) /\
     (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
  ao_opt_producer (dfg_build_function fn)
    (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst) = SOME outs ==>
  ?u. ao_cmp_exec_chunk fuel ctx
        (ao_transform_inst (dfg_build_function fn) ra lbl idx
          (ao_compute_fn_iszero_targets fn) fr inst) r = OK u /\
      ao_main_observations fn V t u /\
      (u with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
      u.vs_inst_idx = r.vs_inst_idx + LENGTH
        (ao_transform_inst (dfg_build_function fn) ra lbl idx
          (ao_compute_fn_iszero_targets fn) fr inst)
Proof
  strip_tac >>
  `MEM inst.inst_opcode
    [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
     Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT]` by simp[] >>
  drule_all ao_source_resolved_scalar_step >>
  strip_tac >>
  `ao_main_observations fn V s s` by simp[ao_main_observations_def] >>
  `?y z. inst.inst_outputs = [y] /\ t = update_var y z s /\
    step_inst_base (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst) s =
      OK (update_var y z s)` by
    (irule ao_source_resolved_scalar_step >> asm_rewrite_tac[] >> metis_tac[]) >>
  qpat_x_assum `ao_opt_producer _ _ = _` mp_tac >>
  simp[ao_opt_producer_def, ao_resolve_iszero_inst_def] >>
  simp[AllCaseEqs()] >> strip_tac >>
  gvs[] >>
  qpat_x_assum `step_inst_base _ r = _` mp_tac >>
  qpat_x_assum `step_inst_base _ s = OK (update_var _ _ s)` mp_tac >>
  simp[ao_resolve_iszero_inst_def, step_inst_base_opcode_eqs, exec_pure2_def] >>
  asm_rewrite_tac[] >>
  simp[eval_operand_def, AllCaseEqs()] >> rpt strip_tac >>
  `?a b wa wb. inst.inst_operands = [a;b] /\
    eval_operand a s = SOME wa /\ eval_operand b s = SOME wb` by
    (qpat_x_assum `step_inst_base inst s = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  `ao_resolve_iszero_op (ao_compute_fn_iszero_targets fn) SIGNEXTEND b = Var v'` by
    gvs[] >>
  `eval_operand (Var v') r = SOME wb /\ eval_operand (Var v') s = SOME wb` by
    (conj_tac >>
     qpat_assum `ao_resolve_iszero_op _ _ b = _` (fn th => rewrite_tac[GSYM th]) >>
     qpat_assum `inst.inst_opcode = SIGNEXTEND`
       (fn th => irule (SRULE [th] ao_source_resolved_operand_exact)) >>
     simp[MEM, is_truthy_inst_def] >> metis_tac[]) >>
  gvs[eval_operand_def] >>
  `sign_extend w v2 = v2` by
    (irule ao_source_signextend_absorbed >> asm_rewrite_tac[] >> metis_tac[]) >>
  qpat_x_assum `update_var x (sign_extend w v2) s = _`
    (fn th => rewrite_tac[GSYM th]) >>
  `ao_transform_inst (dfg_build_function fn) ra lbl idx
     (ao_compute_fn_iszero_targets fn) fr inst =
    [inst with <|inst_opcode := ASSIGN; inst_operands := [Var v']|>]` by
    simp[ao_transform_inst_def, ao_resolve_iszero_inst_def,
         ao_opt_producer_def, ao_post_flip_inst_def] >>
  gvs[] >>
  simp[ao_cmp_exec_chunk_single, step_inst_non_invoke,
       step_inst_base_opcode_eqs, eval_operand_def] >>
  qpat_x_assum `update_var x v2 r = _` (fn th => rewrite_tac[GSYM th]) >>
  reverse conj_tac >- simp[update_var_def] >>
  `ao_main_observations fn V (update_var x v2 s) (update_var x v2 r)` by
    (irule ao_main_observations_update >> simp[]) >>
  gvs[ao_main_observations_def, lookup_var_def, update_var_def]
QED

Theorem ao_source_step_call_ctx:
  !ctx fn a b. ao_source_step ctx fn a b ==>
    (SND (SND b)).vs_call_ctx = (SND (SND a)).vs_call_ctx
Proof
  ho_match_mp_tac ao_source_step_ind >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >> drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
      disch_then (fn th => once_rewrite_tac[th]) >> simp[])
  >- metis_tac[venomInstPropsTheory.step_preserves_call_ctx] >>
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
      AllCaseEqs(), jump_to_def] >>
  pairarg_tac >> gvs[]
QED

Theorem ao_source_trace_call_ctx:
  !trace ctx fn a b.
    ao_source_trace ctx fn trace /\ MEM a trace /\ MEM b trace ==>
    (SND (SND a)).vs_call_ctx = (SND (SND b)).vs_call_ctx
Proof
  Induct >> simp[ao_source_trace_def] >>
  rpt gen_tac >> Cases_on `trace` >> simp[ao_source_trace_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[ao_source_step_call_ctx, MEM]
QED

Theorem ao_source_address_value:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
  ao_source_trace ctx fn trace /\ LAST trace = (h,F,s) /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  dfg_get_def (dfg_build_function fn) x = SOME prod /\
  prod.inst_opcode = ADDRESS /\ lookup_var x s = SOME value ==>
  value = w2w s.vs_call_ctx.cc_address
Proof
  strip_tac >>
  `prod.inst_opcode <> PHI /\ ~is_terminator prod.inst_opcode` by
    simp[is_terminator_def] >>
  drule_all ao_dfg_source_producer >> strip_tac >>
  `MEM prod (fn_insts fn)` by metis_tac[dfgAnalysisPropsTheory.dfg_build_function_correct] >>
  `lookup_var x (SND (SND (HD trace))) = NONE` by metis_tac[] >>
  drule_all ao_source_trace_last_output >> strip_tac >>
  `u.vs_call_ctx = s.vs_call_ctx` by
    (qspecl_then [`trace`,`ctx`,`fn`,`(q,F,u)`,`(h,F,s)`]
       mp_tac ao_source_trace_call_ctx >>
     `MEM (h,F,s) trace` by
       metis_tac[rich_listTheory.MEM_LAST_NOT_NIL] >>
     impl_tac >- asm_rewrite_tac[MEM_APPEND, MEM] >> simp[]) >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
      eval_operand_def, AllCaseEqs(), lookup_var_def, update_var_def] >>
  gvs[exec_read0_def, AllCaseEqs(), update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem ao_main_environment_producer_chunk:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
  ao_source_trace ctx fn trace /\ LAST trace = (h,F,s) /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  MEM inst (fn_insts fn) /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  MEM inst.inst_opcode [BALANCE; EXTCODESIZE] /\ step_inst_base inst s = OK t /\
  ao_main_observations fn V s r /\ s.vs_labels = r.vs_labels /\
  s.vs_accounts = r.vs_accounts /\ s.vs_call_ctx = r.vs_call_ctx /\
  (!i x. MEM i (fn_insts fn) /\
     (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) ==>
  ?u. ao_cmp_exec_chunk fuel ctx
        (ao_transform_inst (dfg_build_function fn) ra lbl idx
          (ao_compute_fn_iszero_targets fn) fr inst) r = OK u /\
      ao_main_observations fn V t u /\
      (u with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
      u.vs_inst_idx = r.vs_inst_idx + LENGTH
        (ao_transform_inst (dfg_build_function fn) ra lbl idx
          (ao_compute_fn_iszero_targets fn) fr inst)
Proof
  let
    val finish =
      reverse conj_tac >- simp[update_var_def] >>
      qmatch_goalsub_abbrev_tac `update_var y z s` >>
      `ao_main_observations fn V (update_var y z s) (update_var y z r)` by
        (irule ao_main_observations_update >> simp[]) >>
      gvs[ao_main_observations_def, lookup_var_def, update_var_def]
    val unchanged =
      qpat_x_assum `step_inst_base inst s = _` mp_tac >>
      simp[step_inst_base_opcode_eqs, exec_read1_def] >> strip_tac >> gvs[] >>
      simp[ao_cmp_exec_chunk_single, ao_post_flip_inst_def, step_inst_non_invoke,
           step_inst_base_opcode_eqs, exec_read1_def] >> finish
    val address =
      `w = w2w s.vs_call_ctx.cc_address` by
        (irule ao_source_address_value >> asm_rewrite_tac[] >>
         gvs[eval_operand_def] >> metis_tac[]) >>
      qpat_x_assum `step_inst_base inst s = _` mp_tac >>
      simp[step_inst_base_opcode_eqs, exec_read1_def] >> strip_tac >> gvs[] >>
      simp[ao_cmp_exec_chunk_single, step_inst_non_invoke,
           step_inst_base_opcode_eqs, exec_read0_def] >>
      `w2w (w2w r.vs_call_ctx.cc_address : bytes32) = r.vs_call_ctx.cc_address` by
        wordsLib.WORD_DECIDE_TAC >> asm_rewrite_tac[] >> finish
  in
    strip_tac >>
    `?a w y. inst.inst_operands = [a] /\ eval_operand a s = SOME w /\
      inst.inst_outputs = [y]` by
      (qpat_x_assum `step_inst_base inst s = _` mp_tac >>
       gvs[MEM] >> simp[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()] >>
       metis_tac[]) >>
    `ao_main_observations fn V s s` by simp[ao_main_observations_def] >>
    `eval_operand (ao_resolve_iszero_op (ao_compute_fn_iszero_targets fn)
       inst.inst_opcode a) r = SOME w /\
     eval_operand (ao_resolve_iszero_op (ao_compute_fn_iszero_targets fn)
       inst.inst_opcode a) s = SOME w` by
      (conj_tac >> irule ao_source_resolved_operand_exact >>
       simp[is_truthy_inst_def] >> gvs[MEM] >> metis_tac[]) >>
    gvs[MEM] >>
    simp[ao_transform_inst_def, ao_resolve_iszero_inst_def,
         ao_opt_producer_def, ao_post_flip_inst_def]
    >~ [`inst.inst_opcode = EXTCODESIZE`] >- unchanged >>
    Cases_on `ao_resolve_iszero_op (ao_compute_fn_iszero_targets fn) BALANCE a` >>
    simp[ao_post_flip_inst_def]
    >~ [`ao_resolve_iszero_op _ BALANCE a = Var x`]
    >- (Cases_on `dfg_get_def (dfg_build_function fn) x` >>
        simp[ao_post_flip_inst_def]
        >~ [`dfg_get_def _ x = SOME producer`]
        >- (Cases_on `producer.inst_opcode = ADDRESS` >> simp[ao_post_flip_inst_def]
            >- address >> unchanged) >> unchanged) >> unchanged
  end
QED
