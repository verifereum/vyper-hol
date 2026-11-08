Theory algebraicOptMainCallProofs
Ancestors
  algebraicOptMainScalarProofs algebraicOptRelationProofs
  algebraicOptShapeProofs algebraicOptDefs venomExecSemantics venomState stateFrame
  stateEquiv stateEquivProps execEquivProps list

Theorem ao_main_merge_callee_observations:
  ao_main_observations fn V s r ==>
  ao_main_observations fn V (merge_callee_state s callee) (merge_callee_state r callee)
Proof
  simp[ao_main_observations_def, lookup_var_def, merge_callee_state_def]
QED

Theorem ao_main_adopt_return_observations:
  ao_main_observations fn V s r ==>
  ao_main_observations fn V (adopt_return_fmp ret s) (adopt_return_fmp ret r)
Proof
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, ao_main_observations_def, lookup_var_def]
QED

Theorem ao_main_bind_fold[local]:
  !outs vals s r.
  LENGTH outs = LENGTH vals /\ ao_main_observations fn V s r ==>
  ao_main_observations fn V
    (FOLDL (\s (out,value). update_var out value s) s (ZIP (outs,vals)))
    (FOLDL (\s (out,value). update_var out value s) r (ZIP (outs,vals)))
Proof
  Induct >> Cases_on `vals` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  irule ao_main_observations_update >> simp[ao_main_lookup_def]
QED

Theorem ao_main_bind_outputs_observations:
  ao_main_observations fn V s r ==>
  OPTREL (ao_main_observations fn V)
    (bind_outputs outs vals s) (bind_outputs outs vals r)
Proof
  strip_tac >> simp[bind_outputs_def] >> IF_CASES_TAC >> simp[] >>
  irule ao_main_bind_fold >> simp[]
QED

Theorem ao_main_bind_fold_frame[local]:
  !pairs s.
  (FOLDL (\s (out,value). update_var out value s) s pairs with vs_vars := s.vs_vars) = s
Proof
  rewrite_tac[GSYM state_frame_eq_reconstruct] >>
  irule venomInstProofs1Theory.foldl_update_var_preserves >>
  simp[state_frame_def, update_var_def]
QED

Theorem ao_main_bind_outputs_frame:
  bind_outputs outs vals s = SOME t ==>
  (t with vs_vars := s.vs_vars) = s
Proof
  simp[bind_outputs_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> simp[ao_main_bind_fold_frame]
QED

Theorem ao_main_return_frame:
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state s callee)) = SOME t /\
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state r callee)) = SOME u ==>
  (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
  t.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = r.vs_inst_idx
Proof
  strip_tac >>
  imp_res_tac ao_main_bind_outputs_frame >>
  imp_res_tac bind_outputs_inst_idx >>
  Cases_on `ret.iret_adopt_fmp` >>
  gvs[adopt_return_fmp_def, merge_callee_state_def,
      venom_state_component_equality]
QED

Theorem ao_main_setup_callee:
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  setup_callee fn args s = setup_callee fn args r
Proof
  disch_then (SUBST1_TAC o SYM) >> simp[setup_callee_def]
QED

Theorem ao_main_eval_operands_map[local]:
  !ops vals.
  eval_operands ops s = SOME vals /\
  (!a w. MEM a ops /\ eval_operand a s = SOME w ==>
     eval_operand (f a) r = SOME w) ==>
  eval_operands (MAP f ops) r = SOME vals
Proof
  Induct >> simp[eval_operands_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem ao_main_invoke_transfer:
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  inst.inst_opcode = INVOKE /\ other.inst_opcode = INVOKE /\
  other.inst_outputs = inst.inst_outputs /\
  (!name ops. decode_invoke inst = SOME (name,ops) ==>
    ?ops'. decode_invoke other = SOME (name,ops') /\
      !args. eval_operands ops s = SOME args ==> eval_operands ops' r = SOME args) ==>
  (?e. step_inst fuel ctx inst s = Error e) \/
  lift_result
    (\t u. ao_main_observations fn V t u /\
      (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
      u.vs_inst_idx = r.vs_inst_idx /\ t.vs_inst_idx = s.vs_inst_idx)
    (execution_equiv UNIV) (execution_equiv UNIV)
    (step_inst fuel ctx inst s) (step_inst fuel ctx other r)
Proof
  strip_tac >> Cases_on `decode_invoke inst`
  >- simp[step_inst_def] >>
  rename1 `decode_invoke inst = SOME decoded` >> PairCases_on `decoded` >>
  qpat_x_assum `!name ops. _` (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  Cases_on `lookup_function decoded0 ctx.ctx_functions`
  >- simp[step_inst_def] >>
  rename1 `lookup_function decoded0 ctx.ctx_functions = SOME callee_fn` >>
  Cases_on `eval_operands decoded1 s`
  >- simp[step_inst_def] >>
  rename1 `eval_operands decoded1 s = SOME args` >>
  `eval_operands ops' r = SOME args` by metis_tac[] >>
  `setup_callee callee_fn args s = setup_callee callee_fn args r` by
    (irule ao_main_setup_callee >> simp[]) >>
  Cases_on `setup_callee callee_fn args s`
  >- (gvs[] >> simp[step_inst_def]) >>
  rename1 `setup_callee callee_fn args s = SOME cs` >>
  `setup_callee callee_fn args r = SOME cs` by metis_tac[] >>
  qpat_x_assum `SOME cs = _` kall_tac >>
  Cases_on `run_blocks fuel ctx callee_fn cs` >>
  asm_rewrite_tac[step_inst_def] >>
  simp[lift_result_def, execution_equiv_refl] >>
  drule ao_main_merge_callee_observations >>
  disch_then (qspec_then `v` assume_tac) >>
  drule ao_main_adopt_return_observations >>
  disch_then (qspec_then `i` assume_tac) >>
  drule ao_main_bind_outputs_observations >>
  disch_then (qspecl_then [`i.iret_values`, `inst.inst_outputs`] mp_tac) >>
  Cases_on `bind_outputs inst.inst_outputs i.iret_values
    (adopt_return_fmp i (merge_callee_state s v))` >>
  Cases_on `bind_outputs inst.inst_outputs i.iret_values
    (adopt_return_fmp i (merge_callee_state r v))` >>
  simp[lift_result_def] >> strip_tac >>
  drule_all ao_main_return_frame >> simp[]
QED

Theorem ao_main_invoke_transform_step:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
  ao_source_trace ctx fn trace /\ LAST trace = (h,F,s) /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  MEM inst (fn_insts fn) /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE /\
  ao_main_observations fn V s r /\
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
  (!i x. MEM i (fn_insts fn) /\
     (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) ==>
  (?e. step_inst fuel ctx inst s = Error e) \/
  lift_result
    (\t u. ao_main_observations fn V t u /\
      (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
      u.vs_inst_idx = r.vs_inst_idx /\ t.vs_inst_idx = s.vs_inst_idx)
    (execution_equiv UNIV) (execution_equiv UNIV)
    (step_inst fuel ctx inst s)
    (step_inst fuel ctx (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst) r)
Proof
  strip_tac >> irule ao_main_invoke_transfer >>
  simp[ao_resolve_iszero_inst_def] >> rpt strip_tac >>
  qexists_tac `MAP (ao_resolve_iszero_op (ao_compute_fn_iszero_targets fn) INVOKE) ops` >>
  conj_tac
  >- (qpat_x_assum `decode_invoke inst = _` mp_tac >>
      Cases_on `inst.inst_operands` >> simp[decode_invoke_def] >>
      Cases_on `h'` >> simp[decode_invoke_def, ao_resolve_iszero_op_def]) >>
  rpt strip_tac >> irule ao_main_eval_operands_map >>
  qexists_tac `s` >> simp[] >>
  rpt strip_tac >>
  qpat_assum `inst.inst_opcode = INVOKE` (fn th => once_rewrite_tac[GSYM th]) >>
  `s.vs_labels = r.vs_labels` by
    (qpat_x_assum `s with <|vs_vars := _; vs_inst_idx := _|> = r` mp_tac >>
     simp[venom_state_component_equality]) >>
  `MEM a inst.inst_operands` by
    (qpat_x_assum `decode_invoke inst = _` mp_tac >>
     Cases_on `inst.inst_operands` >> simp[decode_invoke_def] >>
     Cases_on `h'` >> simp[decode_invoke_def] >> metis_tac[]) >>
  irule ao_source_resolved_operand_exact >>
  simp[is_truthy_inst_def] >> metis_tac[]
QED
