(* Backward ASSIGN comparisons through FMP lowering prefixes. *)
Theory fmpStageCoverForwardPrefix
Ancestors
  fmpStageRel fmpStepBridge fmpStepLayout fmpStepRewrite
  fmpLowerDefs fmpLowerProps fmpLowerSequenceExec lowerDloadPtrForward contextCodegenRel
  irSupply venomFnScheduleRunner o1PassContract venomInst list pred_set

Theorem fmp_prefix_chunk_outputs[local]:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  MEM v s.irs_used_vars /\ v <> runner /\ pre_fmp_opcode inst.inst_opcode ==>
  ((?i. MEM i out /\ MEM v i.inst_outputs) <=> MEM v inst.inst_outputs)
Proof
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >>
      rpt (drule (cj 1 fresh_ir_var_contract) >> strip_tac >>
           dxrule (cj 2 fresh_ir_var_contract) >> strip_tac) >>
      gvs[mk_inst_def, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
          EXISTS_OR_THM] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs(),
      pre_fmp_opcode_def, is_raw_fmp_opcode_def] >>
  Cases_on `info.fi_publishes_fmp` >> gvs[MEM_APPEND]
QED

Theorem fmp_prefix_chunk_same_after[local]:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  pre_fmp_opcode inst.inst_opcode /\
  (!v. v IN V ==> MEM v s.irs_used_vars /\ v <> runner) /\
  (!v. a = Var v ==> v IN V) /\ (!v. b = Var v ==> v IN V) ==>
  same_after_assigns (REVERSE out ++ tail) a b =
  same_after_assigns (inst::tail) a b
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode = ASSIGN`
  >- gvs[fmp_lower_inst_def, is_raw_fmp_opcode_def] >>
  irule same_after_nonassign_chunk_replace >> simp[] >>
  reverse conj_tac
  >- (gvs[fmp_lower_inst_def, AllCaseEqs(), pre_fmp_opcode_def,
          is_raw_fmp_opcode_def, mk_inst_def]) >>
  qexists `V` >> simp[] >>
  simp[EXTENSION] >> rpt strip_tac >>
  Cases_on `x IN V` >> simp[] >>
  `MEM x s.irs_used_vars /\ x <> runner` by metis_tac[] >>
  drule_all fmp_prefix_chunk_outputs >> simp[] >>
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem fmp_prefix_back_closed[local]:
  step_back_assign inst a = SOME b /\
  (!v. a = Var v ==> v IN V) /\
  (!v. MEM (Var v) inst.inst_operands ==> v IN V) ==>
  !v. b = Var v ==> v IN V
Proof
  Cases_on `a` >>
  gvs[step_back_assign_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `MEM (HD inst.inst_operands) inst.inst_operands` by
    (Cases_on `inst.inst_operands` >> gvs[]) >> metis_tac[]
QED

Theorem fmp_prefix_tail_cong[local]:
  !xs a b. (!i v. MEM i xs /\ MEM (Var v) i.inst_operands ==> v IN V) /\
  (!a b. (!v. a = Var v ==> v IN V) /\ (!v. b = Var v ==> v IN V) ==>
    same_after_assigns left a b = same_after_assigns right a b) /\
  (!v. a = Var v ==> v IN V) /\ (!v. b = Var v ==> v IN V) ==>
  same_after_assigns (xs ++ left) a b = same_after_assigns (xs ++ right) a b
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  simp[same_after_assigns_def] >> Cases_on `a = b` >> simp[] >>
  Cases_on `step_back_assign h a` >> Cases_on `step_back_assign h b` >>
  simp[] >> first_x_assum irule >> simp[] >>
  metis_tac[fmp_prefix_back_closed]
QED

Theorem fmp_prefix_restores_same_after[local]:
  fmp_emit_restores runner s bases = (out,s') /\
  (!v. a = Var v ==> v <> runner) /\
  (!v. b = Var v ==> v <> runner) ==>
  same_after_assigns (REVERSE out ++ tail) a b = same_after_assigns tail a b
Proof
  map_every qid_spec_tac [`tail`, `s'`, `out`, `s`] >> Induct_on `bases`
  >- simp[fmp_emit_restores_def] >>
  simp[fmp_emit_restores_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  first_x_assum drule >> disch_then (qspec_then
    `mk_inst id ASSIGN [Var h] [runner]::tail` mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  Cases_on `a = b`
  >- (Cases_on `tail` >> simp[same_after_assigns_def]) >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[same_after_assigns_def, step_back_assign_def, mk_inst_def]
QED

Theorem fmp_prefix_inst_vars_mono[local]:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  !v. MEM v s.irs_used_vars ==> MEM v s'.irs_used_vars
Proof
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (rpt strip_tac >>
      gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, AllCaseEqs()] >>
      rpt (dxrule (cj 2 fresh_ir_var_contract) >> strip_tac) >>
      gvs[fresh_inst_id_def]) >>
  rpt strip_tac >> gvs[fmp_lower_inst_def, AllCaseEqs()]
QED

Theorem fmp_prefix_restores_vars[local]:
  fmp_emit_restores runner s bases = (out,s') ==>
  s'.irs_used_vars = s.irs_used_vars
Proof
  map_every qid_spec_tac [`s'`, `out`, `s`] >> Induct_on `bases` >>
  simp[fmp_emit_restores_def, AllCaseEqs(), fresh_inst_id_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem fmp_prefix_indexed_vars_mono[local]:
  !xs k s restores out leftover s'.
  fmp_lower_indexed infos ctx runner label k s restores xs = SOME (out,leftover,s') ==>
  !v. MEM v s.irs_used_vars ==> MEM v s'.irs_used_vars
Proof
  Induct >- simp[fmp_lower_indexed_def] >>
  simp[fmpLowerIndexedPropsTheory.fmp_lower_indexed_cons] >>
  rpt strip_tac >> gvs[] >>
  drule fmp_prefix_restores_vars >> strip_tac >>
  drule fmp_prefix_inst_vars_mono >> strip_tac >>
  first_x_assum drule >> metis_tac[]
QED

Theorem fmp_prefix_indexed_same_after[local]:
  !xs k s restores out leftover s' tail a b.
  fmp_lower_indexed infos ctx runner label k s restores xs = SOME (out,leftover,s') /\
  EVERY (\i. pre_fmp_opcode i.inst_opcode) xs /\
  (!i v. MEM i xs /\ MEM (Var v) i.inst_operands ==> v IN V) /\
  (!v. v IN V ==> MEM v s.irs_used_vars /\ v <> runner) /\
  (!v. a = Var v ==> v IN V) /\ (!v. b = Var v ==> v IN V) ==>
  same_after_assigns (REVERSE out ++ tail) a b =
  same_after_assigns (REVERSE xs ++ tail) a b
Proof
  Induct using SNOC_INDUCT
  >- simp[fmp_lower_indexed_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[SNOC_APPEND] >>
  drule fmp_lower_indexed_append >> strip_tac >>
  gvs[fmpLowerIndexedPropsTheory.fmp_lower_indexed_cons,
      fmp_lower_indexed_def] >>
  `!v. v IN V ==> MEM v sp1.irs_used_vars /\ v <> runner` by
    (drule fmp_prefix_indexed_vars_mono >> metis_tac[]) >>
  `!v. v IN V ==> MEM v s0.irs_used_vars /\ v <> runner` by
    (drule fmp_prefix_restores_vars >> metis_tac[]) >>
  simp[REVERSE_APPEND, APPEND_ASSOC] >>
  `same_after_assigns (REVERSE head ++ (REVERSE prefix ++ REVERSE c1 ++ tail)) a b =
   same_after_assigns (x::(REVERSE prefix ++ REVERSE c1 ++ tail)) a b` by
    (irule fmp_prefix_chunk_same_after >> simp[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  fs[APPEND_ASSOC] >>
  irule (fmp_prefix_tail_cong |> Q.SPEC `[x]` |> SRULE [APPEND]) >>
  qexists `V` >> simp[] >>
  map_every qx_gen_tac [`a'`, `b'`] >> strip_tac >>
  `same_after_assigns (REVERSE prefix ++ (REVERSE c1 ++ tail)) a' b' =
   same_after_assigns (REVERSE c1 ++ tail) a' b'` by
    (irule fmp_prefix_restores_same_after >> metis_tac[]) >>
  fs[APPEND_ASSOC] >> first_x_assum irule >> metis_tac[]
QED
