Theory o1LabelFlowMiddle
Ancestors
  o1LabelFlowLowerDload o1LabelFlowMiddleConcretize o1LabelFlowMiddleFmp
  o1LabelFlowMiddleSsaAssembly o1ContractMakeSsa lowerDloadMakeSsaInput
  concretizeMemLocDefs venomPassDispatcher o1PassContract venomInst codegenSymRel list

(* Package the exact repeated LowerDload lifetime interface for stage lifting;
   this abbreviation adds no condition to the established lifetime theorem. *)
Definition middle_code_end_lifetime_def:
  middle_code_end_lifetime f <=>
  !x. code_end_var f x ==>
    ?d op. MEM d (fn_insts f) /\ d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
      (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
         MEM (Var x) j.inst_operands ==>
         j.inst_opcode = CODECOPY /\
         (?dst sz. j.inst_operands = [dst; Var x; sz] /\
                   dst <> Var x /\ sz <> Var x) /\
         ?pre post. bb.bb_instructions = pre ++ d::j::post)
End

Theorem middle_code_end_lifetime_explicit[local]:
  middle_code_end_lifetime f <=>
  !x. code_end_var f x ==>
    ?d op. MEM d (fn_insts f) /\ d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
      (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
         MEM (Var x) j.inst_operands ==>
         j.inst_opcode = CODECOPY /\
         (?dst sz. j.inst_operands = [dst; Var x; sz] /\
                   dst <> Var x /\ sz <> Var x) /\
         ?pre post. bb.bb_instructions = pre ++ d::j::post)
Proof
  rewrite_tac[middle_code_end_lifetime_def]
QED

Theorem middle_lifetime_same_blocks[local]:
  f.fn_blocks = g.fn_blocks ==>
  (middle_code_end_lifetime f <=> middle_code_end_lifetime g)
Proof
  strip_tac >>
  `!x. code_end_var f x <=> code_end_var g x` by
    metis_tac[code_end_var_same_blocks] >>
  simp[middle_code_end_lifetime_def, fn_insts_def]
QED

Theorem middle_lower_dload_step[local]:
  fn_pass_step rpolicy (CFP_Simple VP_LowerDload) observed s f out /\
  (!i. MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands) /\
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  label_flow_ok (ctx with ctx_functions := [out.fpo_function]) /\
  middle_code_end_lifetime out.fpo_function
Proof
  strip_tac >> drule lower_dload_step_supply >> strip_tac >>
  conj_tac
  >- (irule lower_dload_function_label_flow_ok >> metis_tac[]) >>
  pure_rewrite_tac[middle_code_end_lifetime_def] >> rpt strip_tac >>
  irule lower_dload_function_code_end_lifetime >> metis_tac[]
QED

Theorem middle_concretize_positions[local]:
  label_flow_ok (ctx with ctx_functions := [f]) /\
  middle_code_end_lifetime f ==>
  label_flow_ok (ctx with ctx_functions := [concretize_function_with_positions p f]) /\
  middle_code_end_lifetime (concretize_function_with_positions p f)
Proof
  strip_tac >> conj_tac
  >- metis_tac[concretize_label_flow] >>
  drule (PURE_REWRITE_RULE [GSYM middle_code_end_lifetime_def]
    concretize_function_code_end_lifetime) >> simp[]
QED

Theorem middle_concretize_layout[local]:
  label_flow_ok (ctx with ctx_functions := [f]) /\
  middle_code_end_lifetime f ==>
  label_flow_ok (ctx with ctx_functions := [apply_context_concretize_layout C layout f]) /\
  middle_code_end_lifetime (apply_context_concretize_layout C layout f)
Proof
  strip_tac >> drule_all middle_concretize_positions >>
  disch_then (qspec_then `layout.cl_positions` strip_assume_tac) >>
  ` (apply_context_concretize_layout C layout f).fn_blocks =
    (concretize_function_with_positions layout.cl_positions f).fn_blocks` by
    simp[apply_context_concretize_layout_def, apply_concretize_layout_def] >>
  metis_tac[label_flow_ok_same_blocks, middle_lifetime_same_blocks]
QED

Theorem middle_concretize_step[local]:
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s f out /\
  label_flow_ok (ctx with ctx_functions := [f]) /\ middle_code_end_lifetime f ==>
  label_flow_ok (ctx with ctx_functions := [out.fpo_function]) /\
  middle_code_end_lifetime out.fpo_function
Proof
  strip_tac >>
  `execute_configured_fn_pass rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    observed s f = SOME out` by fs[fn_pass_step_def] >>
  gvs[execute_configured_fn_pass_concretize, AllCaseEqs()] >>
  gvs[concretize_function_fuel_in_context_def, AllCaseEqs()] >>
  metis_tac[middle_concretize_layout]
QED

Theorem middle_fmp_step[local]:
  fn_pass_step rpolicy (CFP_Simple VP_FmpLowering) observed s f out /\
  o1_fn_row 3 f /\ EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  label_flow_ok (ctx with ctx_functions := [f]) /\ middle_code_end_lifetime f ==>
  label_flow_ok (ctx with ctx_functions := [out.fpo_function]) /\
  middle_code_end_lifetime out.fpo_function
Proof
  strip_tac >> conj_tac
  >- metis_tac[fmp_row_label_flow_ok] >>
  irule (PURE_REWRITE_RULE [GSYM middle_code_end_lifetime_def]
    fmp_row_code_end_lifetime) >> metis_tac[]
QED

Theorem middle_make_ssa_function[local]:
  wf_function f /\ fn_inst_wf f /\ make_ssa_input_ok f /\
  ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  label_flow_ok (ctx with ctx_functions := [f]) /\ middle_code_end_lifetime f /\
  make_ssa_current_fn s f = (g,t) ==>
  label_flow_ok (ctx with ctx_functions := [g])
Proof
  strip_tac >> irule make_ssa_current_fn_label_flow >>
  goal_assum $ drule_at Any >>
  fs[middle_code_end_lifetime_def]
QED

Theorem middle_flow_functions[local]:
  label_flow_ok C <=>
  EVERY (\f. label_flow_ok (ctx with ctx_functions := [f])) C.ctx_functions
Proof
  simp[label_flow_ok_def, EVERY_MEM] >> metis_tac[]
QED

Theorem middle_stage_every[local]:
  ctx_pass_stage rpolicy pass view C C' /\ EVERY P C.ctx_functions /\
  (!f observed s out. MEM f C.ctx_functions /\
    fn_pass_step rpolicy pass observed s f out /\ view C' f observed /\ P f ==>
    Q out.fpo_function) ==>
  EVERY Q C'.ctx_functions
Proof
  simp[ctx_pass_stage_def, EVERY_MEM] >> rpt strip_tac >>
  drule_all LIST_REL_MEM_IMP_R >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem middle_lower_dload_stage:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  label_flow_ok C /\
  (!f i. MEM f C.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) ==>
  label_flow_ok C' /\ EVERY middle_code_end_lifetime C'.ctx_functions
Proof
  strip_tac >>
  `EVERY (\f. label_flow_ok (C with ctx_functions := [f]) /\
     middle_code_end_lifetime f) C'.ctx_functions` suffices_by
    (simp[EVERY_CONJ, GSYM middle_flow_functions]) >>
  irule middle_stage_every >> goal_assum $ drule_at Any >>
  qexists `\f. label_flow_ok (C with ctx_functions := [f]) /\
    (!i. MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands)` >>
  conj_tac
  >- (rpt strip_tac >> fs[] >> metis_tac[middle_lower_dload_step]) >>
  fs[EVERY_MEM, label_flow_ok_def] >> metis_tac[]
QED

Theorem middle_concretize_stage:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  label_flow_ok C /\ EVERY middle_code_end_lifetime C.ctx_functions ==>
  label_flow_ok C' /\ EVERY middle_code_end_lifetime C'.ctx_functions
Proof
  strip_tac >>
  `EVERY (\f. label_flow_ok (C with ctx_functions := [f]) /\
     middle_code_end_lifetime f) C'.ctx_functions` suffices_by
    (simp[EVERY_CONJ, GSYM middle_flow_functions]) >>
  irule middle_stage_every >> qexists `C` >>
  qexists `\f. label_flow_ok (C with ctx_functions := [f]) /\
    middle_code_end_lifetime f` >>
  goal_assum $ drule_at Any >>
  conj_tac
  >- (rpt strip_tac >> fs[] >> metis_tac[middle_concretize_step]) >>
  fs[EVERY_CONJ, GSYM middle_flow_functions]
QED

Theorem middle_fmp_stage:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering) view C C' /\
  EVERY (o1_fn_row 3) C.ctx_functions /\
  (!f observed. MEM f C.ctx_functions /\ view C' f observed ==>
    EVERY fmp_sig_no_param observed.cu_context.ctx_functions) /\
  label_flow_ok C /\ EVERY middle_code_end_lifetime C.ctx_functions ==>
  label_flow_ok C' /\ EVERY middle_code_end_lifetime C'.ctx_functions
Proof
  strip_tac >>
  `EVERY (\f. label_flow_ok (C with ctx_functions := [f]) /\
     middle_code_end_lifetime f) C'.ctx_functions` suffices_by
    (simp[EVERY_CONJ, GSYM middle_flow_functions]) >>
  irule middle_stage_every >> qexists `C` >>
  qexists `\f. label_flow_ok (C with ctx_functions := [f]) /\
    middle_code_end_lifetime f` >>
  goal_assum $ drule_at Any >>
  conj_tac
  >- (rpt strip_tac >> fs[] >>
      `o1_fn_row 3 f` by fs[EVERY_MEM] >>
      `EVERY fmp_sig_no_param observed.cu_context.ctx_functions` by metis_tac[] >>
      drule_all middle_fmp_step >> simp[]) >>
  fs[EVERY_CONJ, GSYM middle_flow_functions]
QED

Theorem middle_make_ssa_stage:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY (o1_fn_row 4) C.ctx_functions /\
  label_flow_ok C /\ EVERY middle_code_end_lifetime C.ctx_functions ==>
  label_flow_ok C'
Proof
  strip_tac >>
  `EVERY make_ssa_input_ok C.ctx_functions` by
    (fs[EVERY_MEM, o1_fn_row_def] >> metis_tac[]) >>
  `LENGTH C'.ctx_functions = LENGTH C.ctx_functions` by
    metis_tac[make_ssa_stage_length] >>
  `EVERY (\f. label_flow_ok (C with ctx_functions := [f])) C.ctx_functions` by
    metis_tac[middle_flow_functions] >>
  once_rewrite_tac[Q.INST [`ctx` |-> `C`] middle_flow_functions] >>
  simp[EVERY_EL] >> rpt strip_tac >>
  drule_all make_ssa_stage_el >> strip_tac >>
  irule middle_make_ssa_function >> goal_assum $ drule_at Any >>
  fs[EVERY_EL] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  simp[label_flow_ok_def]
QED

(* The scheduled interval generates its own lifetime witness at LowerDload;
   callers provide only the ordinary stage, row, and shape facts. *)
Theorem middle_interval_label_flow_ok:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) vd C0 C1 /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) vc C1 C2 /\
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering) vf C2 C3 /\
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) vs C3 C4 /\
  EVERY (o1_fn_row 3) C2.ctx_functions /\
  (!f observed. MEM f C2.ctx_functions /\ vf C3 f observed ==>
    EVERY fmp_sig_no_param observed.cu_context.ctx_functions) /\
  o1_ctx_shape C3 /\ EVERY (o1_fn_row 4) C3.ctx_functions /\
  label_flow_ok C0 /\
  (!f i. MEM f C0.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) ==>
  label_flow_ok C4
Proof
  strip_tac >>
  drule_all middle_lower_dload_stage >> strip_tac >>
  drule_all middle_concretize_stage >> strip_tac >>
  drule_all middle_fmp_stage >> strip_tac >>
  irule middle_make_ssa_stage >> metis_tac[]
QED
