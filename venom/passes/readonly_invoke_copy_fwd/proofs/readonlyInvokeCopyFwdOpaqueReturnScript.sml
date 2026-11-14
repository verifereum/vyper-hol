Theory readonlyInvokeCopyFwdOpaqueReturn
Ancestors
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdCalls readonlyInvokeCopyFwdValues
  readonlyInvokeCopyFwdRel
  o1LowerDloadOpaque o1LowerDloadGhost o1LowerDloadJointScalar
  o1LowerDloadPtrDiscipline o1LowerDloadOccurrence
  o1LowerDloadRelocationKernel o1LowerDloadJointRestore frameViewFacts frameRel
  internalReturnCopyFwdSim unitShapeDefs ptrDiscipline taintAgree allocaFrontierBound
  venomExecSemantics venomState venomInst finite_map list rich_list pred_set words

Theorem ricf_opaque_frame_operand_defined:
  ricf_opaque_frame_agree fn D X sites PG G tn s t ==>
  (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))
Proof
  strip_tac >>
  `FDOM t.vs_vars = FDOM s.vs_vars` by
    fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >>
  `t.vs_labels = s.vs_labels` by
    (fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >>
     drule taint_agree_labels >>
     simp[ricf_opaque_view_def]) >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def, FLOOKUP_DEF] >>
  rename1 `IS_SOME (if v IN FDOM s.vs_vars then SOME _ else NONE)` >>
  Cases_on `v IN FDOM s.vs_vars` >> simp[]
QED

Theorem ricf_opaque_ret_front:
  frame_reachable vs C stk PG G tn fn inst s /\ ptr_discipline lo C vs /\
  ricf_opaque_frame_agree fn D X sites params G tn s t /\
  opaque_use_ok fn /\ active_inst fn inst s /\ inst.inst_opcode = RET /\
  inst.inst_operands <> [] ==>
  !op. MEM op (FRONT inst.inst_operands) ==>
    eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    metis_tac[frame_reachable_prov_support] >>
  `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  rpt strip_tac >>
  `MEM op inst.inst_operands` by metis_tac[MEM_FRONT_NOT_NIL] >>
  `op_prov G op = NONE /\ op_taint tn op = {}` by
    metis_tac[ret_operand_no_provenance, ret_operand_untainted] >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    metis_tac[ret_front_non_retpc] >>
  Cases_on `eval_operand op s`
  >- (`IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t)` by
        metis_tac[ricf_opaque_frame_operand_defined] >>
      Cases_on `eval_operand op t` >> gvs[]) >>
  rename1 `eval_operand op s = SOME value` >>
  drule_all ricf_opaque_frame_operand >> strip_tac >>
  `value = y` by
    (irule ld_value_agree_clean >> qexists_tac `sites` >>
     gvs[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
       ricf_value_agree_def]) >> gvs[]
QED

Theorem ricf_opaque_ret_step:
  frame_reachable vs C stk PG G tn fn inst s /\ ptr_discipline lo C vs /\
  ricf_opaque_frame_agree fn D X sites params G tn s t /\
  opaque_use_ok fn /\ active_inst fn inst s /\ inst.inst_opcode = RET /\
  step_inst fuel C inst s = IntRet ret se ==>
  se = s /\ ret.iret_adopt_fmp = NONE /\
  step_inst fuel Ct inst t = IntRet ret t
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))` by
    metis_tac[ricf_opaque_frame_operand_defined] >>
  `step_inst_base inst s = IntRet ret se` by
    (qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
     qpat_assum `inst.inst_opcode = RET`
       (fn opc => simp[opc, Once step_inst_def])) >>
  `inst.inst_operands <> []` by
    (strip_tac >> gvs[step_inst_base_opcode_eqs, eval_operands_def]) >>
  `!op. MEM op (FRONT inst.inst_operands) ==>
    eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ricf_opaque_ret_front >> metis_tac[]) >>
  drule_all ret_front_transfer >> strip_tac >>
  `jr = ret` by simp[internal_return_component_equality] >>
  gvs[] >>
  qpat_assum `inst.inst_opcode = RET`
    (fn opc => qpat_assum `step_inst_base inst t = _`
      (fn target_step => simp[opc, step_inst_non_invoke, target_step]))
QED

Theorem ricf_opaque_frame_update_scalar[local]:
  ricf_opaque_frame_agree fn D X sites PG G tn s t ==>
  ricf_opaque_frame_agree fn D X sites PG (set_prov G [out] NONE)
    (tn with t_var := DRESTRICT tn.t_var (COMPL {out}))
    (update_var out w s) (update_var out w t)
Proof
  simp[ricf_opaque_frame_agree_def, ricf_opaque_view_update_var,
    ricf_visible_prov_set, ricf_is_zero_prov_def] >>
  simp[set_prov_def] >> metis_tac[ricf_frame_update_scalar]
QED

Theorem ricf_opaque_frame_fold_outputs[local]:
  !bindings G tn s t.
  ricf_opaque_frame_agree fn D X sites PG G tn s t ==>
  ricf_opaque_frame_agree fn D X sites PG
    (DRESTRICT G (COMPL (set (MAP FST bindings))))
    (tn with t_var := DRESTRICT tn.t_var (COMPL (set (MAP FST bindings))))
    (FOLDL (\st (out,w). update_var out w st) s bindings)
    (FOLDL (\st (out,w). update_var out w st) t bindings)
Proof
  Induct >- simp[DRESTRICT_UNIV] >>
  simp[] >> qx_gen_tac `h` >> PairCases_on `h` >> rpt strip_tac >>
  drule ricf_opaque_frame_update_scalar >>
  disch_then (qspecl_then [`h1`, `h0`] mp_tac) >> simp[set_prov_def] >> strip_tac >>
  first_x_assum drule >>
  `COMPL {h0} INTER COMPL (set (MAP FST bindings)) =
   COMPL (h0 INSERT set (MAP FST bindings))` by simp[EXTENSION] >>
  simp[DRESTRICT_DRESTRICT]
QED

Theorem ricf_opaque_frame_bind_outputs:
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  bind_outputs outs vals s = SOME s' ==>
  ?t'. bind_outputs outs vals t = SOME t' /\
    ricf_opaque_frame_agree fn D X sites PG (DRESTRICT G (COMPL (set outs)))
      (tn with t_var := DRESTRICT tn.t_var (COMPL (set outs))) s' t'
Proof
  simp[bind_outputs_def] >> rpt strip_tac >> gvs[] >>
  drule ricf_opaque_frame_fold_outputs >>
  disch_then (qspec_then `ZIP (outs,vals)` mp_tac) >> simp[MAP_ZIP]
QED

Theorem ricf_opaque_live_stack_cons:
  ricf_opaque_live_stack_agree D ids tn (sites::maps) (f::stk) (caller::targets) s t <=>
  ricf_opaque_frame_agree f.cf_fn D (ircf_dead ids f.cf_state stk) sites
    (ricf_complete_params f.cf_params f.cf_state.vs_params)
    f.cf_prov (tn with t_var := f.cf_tvar)
    (merge_callee_state f.cf_state s) (merge_callee_state caller t) /\
  ricf_opaque_live_stack_agree D ids tn maps stk targets s t
Proof
  simp[ricf_opaque_live_stack_agree_def] >> eq_tac
  >- (strip_tac >> conj_tac
      >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      simp[] >> gen_tac >> strip_tac >>
      first_x_assum (qspec_then `SUC j` mp_tac) >> simp[]) >>
  strip_tac >> simp[] >> Cases >> simp[]
QED

Theorem ricf_opaque_frame_adopt_return[local]:
  ricf_opaque_frame_agree fn D X sites PG G tn s t ==>
  ricf_opaque_frame_agree fn D X sites PG G tn
    (adopt_return_fmp ret s) (adopt_return_fmp ret t)
Proof
  simp[ricf_opaque_frame_agree_def, ricf_opaque_view_adopt] >>
  metis_tac[ricf_frame_adopt_return]
QED

Theorem ricf_opaque_resume_next:
  ricf_opaque_live_stack_agree D ids tn (sites::maps) (f::stk)
    (caller::targets) se te /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' ==>
  ?t'. bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller te)) = SOME t' /\
    ricf_opaque_frame_agree f.cf_fn D (ircf_dead ids f.cf_state stk) sites
      (ricf_complete_params f.cf_params f.cf_state.vs_params)
      (DRESTRICT f.cf_prov (COMPL (set outs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set outs)))
      (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) /\
    ricf_opaque_live_stack_agree D ids
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set outs))) maps stk targets
      (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  strip_tac >> fs[ricf_opaque_live_stack_cons] >>
  drule ricf_opaque_frame_adopt_return >>
  disch_then (qspec_then `ret` assume_tac) >>
  drule_all ricf_opaque_frame_bind_outputs >> strip_tac >>
  qexists_tac `t'` >> fs[] >> conj_tac
  >- (irule ricf_opaque_frame_inst_idx >> simp[]) >>
  `!older. merge_callee_state older (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) =
      merge_callee_state older se /\
    merge_callee_state older (t' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) =
      merge_callee_state older te` by
    (gen_tac >> conj_tac
     >- (qpat_assum `bind_outputs _ _ _ = SOME s'`
           (mp_tac o AP_TERM ``\st. merge_callee_state older
             (st with vs_inst_idx := SUC f.cf_state.vs_inst_idx)`` o
             MATCH_MP ld_bind_outputs_vars_only) >>
         Cases_on `ret.iret_adopt_fmp` >> simp[adopt_return_fmp_def, merge_callee_state_def]) >>
     qpat_assum `bind_outputs _ _ _ = SOME t'`
       (mp_tac o AP_TERM ``\st. merge_callee_state older
         (st with vs_inst_idx := SUC f.cf_state.vs_inst_idx)`` o
         MATCH_MP ld_bind_outputs_vars_only) >>
     Cases_on `ret.iret_adopt_fmp` >> simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  fs[ricf_opaque_live_stack_agree_def]
QED
