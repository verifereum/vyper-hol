Theory concretizePtrValueSelection
Ancestors concretizePtrAffineTransport concretizePtrValueTransport ptrDiscipline venomExecSemantics
  venomState venomInst contextCodegenRel finite_map words list rich_list pred_set

Theorem ptr_param_step:
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] ==>
  step_inst fuel C inst s =
    if w2n idx < LENGTH s.vs_params then
      OK (update_var out (EL (w2n idx) s.vs_params) s)
    else Error "param: index out of range"
Proof
  strip_tac >> simp[Once step_inst_def] >> simp[step_inst_base_def]
QED

(* PARAM's actual out_taint is empty, so scalar argument bytes must agree
   everywhere. Tagged arguments may still contain arbitrary modular pointers. *)
Theorem ptr_param_transport:
  ptr_vars_transport births positions TG tn s t /\
  ptr_args_transport births positions PT (REPLICATE (LENGTH s.vs_params) {})
    s.vs_params t.vs_params /\
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] /\
  ((?s'. step_inst fuel C inst s = OK s') \/
   (?t'. step_inst fuel C' inst t = OK t')) ==>
  ?s' t'. step_inst fuel C inst s = OK s' /\
    step_inst fuel C' inst t = OK t' /\
    ptr_vars_transport births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  drule ptr_args_transport_lengths >> strip_tac >>
  `w2n idx < LENGTH s.vs_params` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[Once step_inst_def] >> simp[step_inst_base_def] >>
     IF_CASES_TAC >> gvs[]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` kall_tac >>
  `ptr_value_transport births positions (EL (w2n idx) PT) {}
    (EL (w2n idx) s.vs_params) (EL (w2n idx) t.vs_params)` by
    (drule_all ptr_args_transport_el >> simp[EL_REPLICATE]) >>
  qexistsl_tac [`update_var out (EL (w2n idx) s.vs_params) s`,
               `update_var out (EL (w2n idx) t.vs_params) t`] >>
  drule_all ptr_param_step >> disch_then (fn th => simp[th]) >>
  simp[step_prov_def, out_prov_def] >>
  irule ptr_vars_transport_update >> rpt (goal_assum (drule_at Any)) >>
  simp[step_taint_def, out_taint_def, eval_operand_def]
QED

Theorem ptr_setup_callee_transport:
  ptr_args_transport births positions PT masks args args' /\
  NULL fn.fn_blocks = NULL fn'.fn_blocks ==>
  (setup_callee fn args s = NONE <=> setup_callee fn' args' t = NONE) /\
  (!cs ct. setup_callee fn args s = SOME cs /\
           setup_callee fn' args' t = SOME ct ==>
    ptr_args_transport births positions PT masks cs.vs_params ct.vs_params /\
    ptr_vars_transport births positions FEMPTY entry_taint cs ct)
Proof
  simp[setup_callee_def] >> strip_tac >>
  Cases_on `NULL fn'.fn_blocks` >> gvs[] >>
  simp[ptr_vars_transport_def, lookup_var_def, ptr_lookup_transport_def]
QED

Theorem ptr_eval_operands_transport:
  !ops. ptr_vars_transport births positions TG tn s t /\
    EVERY (\op. (?v. op = Var v) \/ (?w. op = Lit w)) ops ==>
    OPTREL (ptr_args_transport births positions
      (MAP (op_prov TG) ops) (MAP (op_taint tn) ops))
      (eval_operands ops s) (eval_operands ops t)
Proof
  Induct >> simp[eval_operands_def, optionTheory.OPTREL_def,
    ptr_args_transport_def] >> rpt strip_tac >>
  `ptr_lookup_transport births positions (op_prov TG h) (op_taint tn h)
    (eval_operand h s) (eval_operand h t)` by
    (irule ptr_vars_transport_eval >> simp[]) >>
  first_x_assum drule >> simp[] >> strip_tac >>
  Cases_on `eval_operand h s` >> Cases_on `eval_operand h t` >>
  gvs[ptr_lookup_transport_def] >>
  Cases_on `eval_operands ops s` >> Cases_on `eval_operands ops t` >>
  gvs[optionTheory.OPTREL_def, ptr_args_transport_def]
QED

Theorem ptr_eval_one_phi_transport:
  ptr_vars_transport births positions TG tn s t /\
  s.vs_prev_bb = t.vs_prev_bb /\
  (!lbl op. s.vs_prev_bb = SOME lbl /\
    resolve_phi lbl inst.inst_operands = SOME op ==>
    (?v. op = Var v) \/ (?w. op = Lit w)) ==>
  OPTREL (\(out,x) (out',y). out = out' /\
      ptr_value_transport births positions (phi_prov s.vs_prev_bb TG inst)
        (phi_taint s.vs_prev_bb tn inst) x y)
    (eval_one_phi s inst) (eval_one_phi t inst)
Proof
  strip_tac >>
  qpat_x_assum `s.vs_prev_bb = t.vs_prev_bb` (fn th => rewrite_tac[eval_one_phi_def, GSYM th]) >>
  Cases_on `s.vs_prev_bb` >> simp[optionTheory.OPTREL_def] >>
  Cases_on `inst.inst_outputs` >> simp[optionTheory.OPTREL_def] >>
  rename1 `inst.inst_outputs = out::outs` >>
  Cases_on `outs` >> simp[optionTheory.OPTREL_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[optionTheory.OPTREL_def] >>
  rename1 `resolve_phi x inst.inst_operands = SOME op` >>
  `ptr_lookup_transport births positions (op_prov TG op) (op_taint tn op)
    (eval_operand op s) (eval_operand op t)` by
    (irule ptr_vars_transport_eval >> metis_tac[]) >>
  Cases_on `eval_operand op s` >> Cases_on `eval_operand op t` >>
  gvs[ptr_lookup_transport_def, optionTheory.OPTREL_def,
      phi_prov_def, phi_taint_def]
QED

(* Project only successful batch results; this is not a new PHI evaluator. *)
Definition ptr_phi_result_def:
  ptr_phi_result insts s =
    case eval_phis s insts of OK post => SOME post | _ => NONE
End

Theorem ptr_phi_result_clauses:
  ptr_phi_result [] s = SOME s /\
  ptr_phi_result (inst::rest) s =
    if inst.inst_opcode <> PHI then SOME s else
    case eval_one_phi s inst of
      NONE => NONE
    | SOME (out,x) => OPTION_MAP (update_var out x) (ptr_phi_result rest s)
Proof
  simp[ptr_phi_result_def, eval_phis_def] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  Cases_on `eval_one_phi s inst` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `eval_phis s rest` >> simp[]
QED

Theorem ptr_eval_phis_transport:
  !insts. ptr_vars_transport births positions TG tn s t /\
    s.vs_prev_bb = t.vs_prev_bb /\
    (!inst lbl op. MEM inst insts /\ s.vs_prev_bb = SOME lbl /\
      resolve_phi lbl inst.inst_operands = SOME op ==>
      (?v. op = Var v) \/ (?w. op = Lit w)) ==>
    OPTREL (ptr_vars_transport births positions
      (phis_prov s.vs_prev_bb TG insts)
      (tn with t_var := phis_taint s.vs_prev_bb tn insts))
      (ptr_phi_result insts s) (ptr_phi_result insts t)
Proof
  Induct >- simp[ptr_phi_result_clauses, optionTheory.OPTREL_def,
                phis_prov_def, phis_taint_def] >>
  rpt strip_tac >>
  Cases_on `h.inst_opcode <> PHI`
  >- simp[ptr_phi_result_clauses, optionTheory.OPTREL_def,
          phis_prov_def, phis_taint_def] >>
  `OPTREL (\(out,x) (out',y). out = out' /\
      ptr_value_transport births positions (phi_prov s.vs_prev_bb TG h)
        (phi_taint s.vs_prev_bb tn h) x y)
    (eval_one_phi s h) (eval_one_phi t h)` by
    (irule ptr_eval_one_phi_transport >> metis_tac[MEM]) >>
  first_x_assum drule >> impl_tac >- metis_tac[MEM] >> strip_tac >>
  Cases_on `eval_one_phi s h` >> Cases_on `eval_one_phi t h` >>
  gvs[optionTheory.OPTREL_def, ptr_phi_result_clauses] >>
  PairCases_on `x` >> PairCases_on `x'` >> gvs[] >>
  Cases_on `ptr_phi_result insts s` >> Cases_on `ptr_phi_result insts t` >>
  gvs[optionTheory.OPTREL_def, phis_prov_def, phis_taint_def] >>
  `h.inst_outputs = [x'0]` by gvs[eval_one_phi_def, AllCaseEqs()] >>
  simp[] >> irule ptr_vars_transport_update >> rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem ptr_scalar_bind_fold:
  !kvs TG tn s t. ptr_vars_transport births positions TG tn s t ==>
  ptr_vars_transport births positions
    (DRESTRICT TG (COMPL (set (MAP FST kvs))))
    (tn with t_var := DRESTRICT tn.t_var (COMPL (set (MAP FST kvs))))
    (FOLDL (\s' (out,x). update_var out x s') s kvs)
    (FOLDL (\t' (out,x). update_var out x t') t kvs)
Proof
  Induct >- simp[ptr_vars_transport_def, FLOOKUP_DRESTRICT, op_taint_def] >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >> simp[] >>
  `ptr_vars_transport births positions (DRESTRICT TG (COMPL {h0}))
    (tn with t_var := DRESTRICT tn.t_var (COMPL {h0}))
    (update_var h0 h1 s) (update_var h0 h1 t)` by
    (simp[ptr_vars_transport_def] >> gen_tac >> Cases_on `v = h0` >>
     gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
         op_taint_def, ptr_lookup_transport_def, ptr_value_transport_refl,
         ptr_vars_transport_def]) >>
  first_x_assum drule >>
  simp[DRESTRICT_DRESTRICT, INTER_DEF, COMPL_DEF, DIFF_DEF, EXTENSION]
QED

Theorem ptr_bind_outputs_transport:
  ptr_vars_transport births positions TG tn s t ==>
  (bind_outputs outs vals s = NONE <=> bind_outputs outs vals t = NONE) /\
  (!s' t'. bind_outputs outs vals s = SOME s' /\
           bind_outputs outs vals t = SOME t' ==>
    ptr_vars_transport births positions (DRESTRICT TG (COMPL (set outs)))
      (tn with t_var := DRESTRICT tn.t_var (COMPL (set outs))) s' t')
Proof
  strip_tac >> simp[bind_outputs_def] >>
  Cases_on `LENGTH outs = LENGTH vals` >> simp[] >> rpt strip_tac >> gvs[] >>
  drule ptr_scalar_bind_fold >>
  disch_then (qspec_then `ZIP (outs,vals)` mp_tac) >> simp[MAP_ZIP]
QED

Theorem ptr_vars_transport_fields:
  ptr_vars_transport births positions TG tn s t /\
  s'.vs_vars = s.vs_vars /\ t'.vs_vars = t.vs_vars /\ tn'.t_var = tn.t_var ==>
  ptr_vars_transport births positions TG tn' s' t'
Proof
  simp[ptr_vars_transport_def, lookup_var_def, op_taint_def]
QED

Theorem ptr_entry_transport:
  ptr_vars_transport births positions TG tn s t /\
  s.vs_prev_bb = t.vs_prev_bb /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
  (!inst lbl op. MEM inst bb.bb_instructions /\ s.vs_prev_bb = SOME lbl /\
    resolve_phi lbl inst.inst_operands = SOME op ==>
    (?v. op = Var v) \/ (?w. op = Lit w)) /\
  enters_block fn s s1 ==>
  ?t1. enters_block fn' t t1 /\
    ptr_vars_transport births positions (entry_prov fn s TG)
      (entry_taint_vars fn s tn) s1 t1
Proof
  strip_tac >>
  `OPTREL (ptr_vars_transport births positions
      (phis_prov s.vs_prev_bb TG bb.bb_instructions)
      (tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions))
      (ptr_phi_result bb.bb_instructions s) (ptr_phi_result bb.bb_instructions t)` by
    (irule ptr_eval_phis_transport >> metis_tac[]) >>
  gvs[enters_block_def, ptr_phi_result_def, optionTheory.OPTREL_def,
      AllCaseEqs()] >>
  rename1 `eval_phis t bb.bb_instructions = OK tp` >>
  simp[enters_block_def, entry_prov_def, entry_taint_vars_def] >>
  irule ptr_vars_transport_fields >> rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem ptr_return_bind_transport:
  ptr_vars_transport births positions TG tn s t /\
  ret.iret_values = ret'.iret_values ==>
  (bind_outputs outs ret.iret_values (adopt_return_fmp ret (merge_callee_state s se)) = NONE <=>
   bind_outputs outs ret'.iret_values (adopt_return_fmp ret' (merge_callee_state t te)) = NONE) /\
  (!s' t'.
    bind_outputs outs ret.iret_values (adopt_return_fmp ret (merge_callee_state s se)) = SOME s' /\
    bind_outputs outs ret'.iret_values (adopt_return_fmp ret' (merge_callee_state t te)) = SOME t' ==>
    ptr_vars_transport births positions (DRESTRICT TG (COMPL (set outs)))
      (tn with t_var := DRESTRICT tn.t_var (COMPL (set outs))) s' t')
Proof
  strip_tac >>
  `ptr_vars_transport births positions TG tn
    (adopt_return_fmp ret (merge_callee_state s se))
    (adopt_return_fmp ret' (merge_callee_state t te))` by
    (irule ptr_vars_transport_fields >> rpt (goal_assum (drule_at Any)) >>
     Cases_on `ret.iret_adopt_fmp` >> Cases_on `ret'.iret_adopt_fmp` >>
     simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  drule ptr_bind_outputs_transport >>
  disch_then (qspecl_then [`ret'.iret_values`, `outs`] mp_tac) >> simp[]
QED

Theorem ptr_phi_parallel_probe:
  OPTION_MAP (\post. (lookup_var "p" post, lookup_var "q" post))
    (ptr_phi_result
      [mk_inst 1 PHI [Label "pred"; Var "q"] ["p"];
       mk_inst 2 PHI [Label "pred"; Var "p"] ["q"]]
      ((update_var "p" 32w (update_var "q" 7w (init_venom_state "entry")))
        with vs_prev_bb := SOME "pred")) = SOME (SOME 7w,SOME 32w) /\
  OPTION_MAP (lookup_var "p")
    (ptr_phi_result
      [mk_inst 1 PHI [Label "pred"; Lit 32w] ["p"];
       mk_inst 2 PHI [Label "pred"; Lit 7w] ["p"]]
      ((init_venom_state "entry") with vs_prev_bb := SOME "pred")) = SOME (SOME 32w)
Proof
  EVAL_TAC
QED

(* These boundaries are local: they do not execute a callee. PARAM uses
   empty scalar masks because its real ghost out_taint is empty. At an
   INVOKE, taint_ok forbids tainted arguments, but proving tag support and
   equal untagged return values remains a global prefix obligation.
   PHIs read the original states and ghosts in parallel and accumulate
   writes in reverse list order (including duplicate-output precedence).
   ptr_entry_transport currently needs a common looked-up block; using it
   for transformed blocks requires proving equality of their PHI prefix,
   not equality of their non-PHI tails. Scalar Label evaluation, if needed
   outside fn_ptr_ok's pointer cases, also remains a separate obligation. *)
