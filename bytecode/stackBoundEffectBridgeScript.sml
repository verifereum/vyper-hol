(* Raw ordinary stack effects and their abstract successor contract. *)
Theory stackBoundEffectBridge
Ancestors
  stackBoundEffectCore stackBoundInterface stackBoundDefs vfmExecution vfmState vfmContext
  vfmConstants list rich_list pair arithmetic
Libs
  BasicProvers

Theorem sb_eff_raw_neutral_push:
  sb_eff_neutral mid ==>
  sb_eff_raw 0 1 (bind mid (\v. push_stack (f v)))
Proof
  rw[sb_eff_raw_def, bind_def] >>
  gvs[AllCaseEqs()] >>
  drule_all (iffLR sb_eff_neutral_def) >>
  strip_tac >>
  gvs[push_stack_def, bind_def, ignore_bind_def,
      get_current_context_def, set_current_context_def,
      return_def, fail_def, assert_def, sb_eff_frame_def, AllCaseEqs()] >>
  Cases_on `s.contexts` >> gvs[]
QED

Theorem sb_eff_raw_pop_neutral:
  (!args. sb_eff_neutral (mid args)) ==>
  sb_eff_raw p 0 (bind (pop_stack p) mid)
Proof
  rw[sb_eff_raw_def, pop_stack_def, bind_def, ignore_bind_def,
     get_current_context_def, set_current_context_def,
     return_def, fail_def, assert_def] >>
  gvs[AllCaseEqs(), sb_eff_frame_def] >>
  first_x_assum (qspec_then `TAKE p (FST (HD s.contexts)).stack` mp_tac) >>
  simp[sb_eff_neutral_def] >>
  disch_then (drule_at Any) >> simp[] >> strip_tac >>
  gvs[sb_eff_frame_def] >>
  Cases_on `s.contexts` >> gvs[]
QED

Theorem sb_eff_raw_pop_neutral_push:
  (!args. sb_eff_neutral (mid args)) ==>
  sb_eff_raw p 1
    (bind (pop_stack p)
      (\args. bind (mid args) (\v. push_stack (f args v))))
Proof
  rw[sb_eff_raw_def, pop_stack_def, bind_def, ignore_bind_def,
     get_current_context_def, set_current_context_def,
     return_def, fail_def, assert_def] >>
  gvs[AllCaseEqs(), sb_eff_frame_def] >>
  first_x_assum (qspec_then `TAKE p (FST (HD s.contexts)).stack` mp_tac) >>
  simp[sb_eff_neutral_def] >>
  disch_then (drule_at Any) >> simp[] >> strip_tac >>
  gvs[push_stack_def, bind_def, ignore_bind_def,
      get_current_context_def, set_current_context_def,
      return_def, fail_def, assert_def, sb_eff_frame_def, AllCaseEqs()] >>
  Cases_on `s.contexts` >> gvs[]
QED

Theorem sb_eff_raw_opcode_contract:
  sb_eff_raw p k (step_inst op) /\ ~is_call op /\
  (!s a. wf_state s /\ s.contexts <> [] /\
     sb_decoded (FST (HD s.contexts)) op ==>
     sb_successors (FST (HD s.contexts)).msgParams.code
       ((FST (HD s.contexts)).pc,a) =
       if p <= LENGTH a then
         [((FST (HD s.contexts)).pc + LENGTH (opcode op),
           REPLICATE k NONE ++ DROP p a)] else []) ==>
  sb_opcode_contract op
Proof
  strip_tac >> simp[sb_opcode_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `LENGTH a = LENGTH (FST (HD s.contexts)).stack` by
    metis_tac[bytecode_stack_describes_length] >>
  `bytecode_stack_describes (DROP p a)
    (DROP p (FST (HD s.contexts)).stack)` by
    metis_tac[bytecode_stack_describes_drop] >>
  `sb_successors (FST (HD s.contexts)).msgParams.code
     ((FST (HD s.contexts)).pc,a) =
     if p <= LENGTH a then
       [((FST (HD s.contexts)).pc + LENGTH (opcode op),
         REPLICATE k NONE ++ DROP p a)] else []` by metis_tac[] >>
  conj_tac
  >- (strip_tac >> gen_tac >> strip_tac >>
      gvs[sb_eff_raw_def] >>
      qpat_x_assum `!s r t. _` (drule_at Any) >> simp[] >> strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `sb_inner _ _ = _` mp_tac >>
  simp[sb_inner_def, bind_def] >>
  Cases_on `step_inst op s` >> rename1 `step_inst op s = (res,u)` >>
  `sb_eff_frame s u` by metis_tac[sb_eff_raw_def] >>
  Cases_on `res` >> gvs[sb_eff_frame_def] >>
  simp[inc_pc_or_jump_def, bind_def, get_current_context_def,
       set_current_context_def, return_def] >>
  strip_tac >> gvs[sb_eff_raw_def] >>
  qpat_x_assum `!s r t. _` (qspec_then `s` mp_tac) >> simp[] >>
  strip_tac >>
  Cases_on `s.contexts` >> Cases_on `u.contexts` >>
  gvs[sb_at_def, bytecode_stack_describes_def] >>
  irule LIST_REL_APPEND_suff >> simp[LIST_REL_EL_EQN, EL_REPLICATE]
QED
