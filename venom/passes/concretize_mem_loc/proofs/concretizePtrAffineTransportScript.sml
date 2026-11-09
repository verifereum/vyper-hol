Theory concretizePtrAffineTransport
Ancestors concretizePtrValueTransport ptrDiscipline venomState venomInst
  venomExecSemantics finite_map words list pred_set

Theorem ptr_vars_transport_update:
  ptr_vars_transport births positions TG tn s t /\
  ptr_value_transport births positions tag mask x y /\
  tn'.t_var = set_var_taint tn.t_var [out] mask ==>
  ptr_vars_transport births positions (set_prov TG [out] tag)
    tn'
    (update_var out x s) (update_var out y t)
Proof
  simp[ptr_vars_transport_def] >> rpt strip_tac >>
  Cases_on `v = out` >> Cases_on `tag` >>
  gvs[set_prov_def, set_var_taint_def, op_taint_def, update_var_def,
      lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
      ptr_lookup_transport_def]
QED

Theorem ptr_assign_transport_lookup[local]:
  ptr_vars_transport births positions TG tn s t /\
  ptr_lookup_transport births positions (op_prov TG op) (op_taint tn op)
    (eval_operand op s) (eval_operand op t) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ step_inst fuel C inst s = OK s' ==>
  ?t'. step_inst fuel C' inst t = OK t' /\
    ptr_vars_transport births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  gvs[Once run_defs, step_inst_base_def, AllCaseEqs()] >>
  gvs[ptr_lookup_transport_some] >>
  qexists_tac `update_var out z t` >>
  simp[Once run_defs, step_inst_base_def] >>
  simp[step_prov_def, out_prov_def, first_prov_def] >>
  irule ptr_vars_transport_update >>
  rpt (goal_assum (drule_at Any)) >>
  simp[step_taint_def, out_taint_def] >>
  qmatch_asmsub_abbrev_tac `ptr_value_transport births positions tag mask x y` >>
  qexists_tac `mask` >> Cases_on `tag` >> gvs[]
QED

Theorem ptr_assign_transport_back_lookup[local]:
  ptr_vars_transport births positions TG tn s t /\
  ptr_lookup_transport births positions (op_prov TG op) (op_taint tn op)
    (eval_operand op s) (eval_operand op t) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ step_inst fuel C' inst t = OK t' ==>
  ?s'. step_inst fuel C inst s = OK s' /\
    ptr_vars_transport births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  gvs[Once run_defs, step_inst_base_def, AllCaseEqs()] >>
  gvs[ptr_lookup_transport_some_right] >>
  qexists_tac `update_var out z s` >>
  simp[Once run_defs, step_inst_base_def] >>
  simp[step_prov_def, out_prov_def, first_prov_def] >>
  irule ptr_vars_transport_update >>
  rpt (goal_assum (drule_at Any)) >>
  simp[step_taint_def, out_taint_def] >>
  qmatch_asmsub_abbrev_tac `ptr_value_transport births positions tag mask x y` >>
  qexists_tac `mask` >> Cases_on `tag` >> gvs[]
QED

Theorem ptr_assign_transport:
  ptr_vars_transport births positions TG tn s t /\
  ((?v. op = Var v) \/ (?w. op = Lit w)) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ step_inst fuel C inst s = OK s' ==>
  ?t'. step_inst fuel C' inst t = OK t' /\
    ptr_vars_transport births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >> irule ptr_assign_transport_lookup >>
  simp[] >> (conj_tac >- metis_tac[]) >> irule ptr_vars_transport_eval >> simp[]
QED

Theorem ptr_assign_transport_all:
  ptr_vars_transport births positions TG tn s t /\
  s.vs_labels = t.vs_labels /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ step_inst fuel C inst s = OK s' ==>
  ?t'. step_inst fuel C' inst t = OK t' /\
    ptr_vars_transport births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >> irule ptr_assign_transport_lookup >>
  simp[] >> (conj_tac >- metis_tac[]) >> irule ptr_vars_transport_eval_all >> simp[]
QED

Theorem ptr_assign_transport_back:
  ptr_vars_transport births positions TG tn s t /\
  ((?v. op = Var v) \/ (?w. op = Lit w)) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ step_inst fuel C' inst t = OK t' ==>
  ?s'. step_inst fuel C inst s = OK s' /\
    ptr_vars_transport births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >> irule ptr_assign_transport_back_lookup >>
  simp[] >> qexistsl_tac [`C'`, `t`] >> simp[] >> irule ptr_vars_transport_eval >> simp[]
QED

Theorem ptr_assign_transport_back_all:
  ptr_vars_transport births positions TG tn s t /\
  s.vs_labels = t.vs_labels /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ step_inst fuel C' inst t = OK t' ==>
  ?s'. step_inst fuel C inst s = OK s' /\
    ptr_vars_transport births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >> irule ptr_assign_transport_back_lookup >>
  simp[] >> qexistsl_tac [`C'`, `t`] >> simp[] >> irule ptr_vars_transport_eval_all >> simp[]
QED

(* Only these affine shapes preserve a single owner displacement. *)
Theorem ptr_affine_step:
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) ==>
  step_inst fuel C inst s =
    exec_pure2 (if inst.inst_opcode = ADD then word_add else word_sub) inst s
Proof
  strip_tac >> simp[Once step_inst_def] >> simp[step_inst_base_def]
QED

Theorem ptr_affine_transport_lookup[local]:
  ptr_vars_transport births positions TG tn s t /\
  ptr_lookup_transport births positions (op_prov TG a) {}
    (eval_operand a s) (eval_operand a t) /\
  ptr_lookup_transport births positions (op_prov TG b) {}
    (eval_operand b s) (eval_operand b t) /\
  inst.inst_operands = [a;b] /\ inst.inst_outputs = [out] /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  (inst.inst_opcode = ADD ==> op_prov TG a = NONE \/ op_prov TG b = NONE) /\
  (inst.inst_opcode = SUB ==> op_prov TG b = NONE) /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  ((?s'. step_inst fuel C inst s = OK s') \/
   (?t'. step_inst fuel C' inst t = OK t')) ==>
  ?s' t'. step_inst fuel C inst s = OK s' /\
    step_inst fuel C' inst t = OK t' /\
    ptr_vars_transport births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  gs[] >>
  gs[ptr_affine_step, exec_pure2_def, AllCaseEqs()] >>
  gs[ptr_lookup_transport_some, ptr_lookup_transport_some_right] >>
  rpt (qpat_x_assum `update_var _ _ _ = _` (SUBST_ALL_TAC o SYM)) >>
  rpt (goal_assum (drule_at Any)) >>
  simp[step_prov_def, out_prov_def, first_prov_def] >>
  irule ptr_vars_transport_update >>
  rpt (goal_assum (drule_at Any)) >>
  qexists_tac `{}` >>
  simp[step_taint_def, out_taint_def] >>
  Cases_on `op_prov TG a` >> Cases_on `op_prov TG b` >>
  gvs[ptr_value_transport_scalar_empty] >>
  metis_tac[ptr_value_transport_add_left, ptr_value_transport_add_right,
            ptr_value_transport_sub_right, WORD_ADD_COMM]
QED

Theorem ptr_affine_transport:
  ptr_vars_transport births positions TG tn s t /\
  ((?v. a = Var v) \/ (?w. a = Lit w)) /\
  ((?v. b = Var v) \/ (?w. b = Lit w)) /\
  inst.inst_operands = [a;b] /\ inst.inst_outputs = [out] /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  (inst.inst_opcode = ADD ==> op_prov TG a = NONE \/ op_prov TG b = NONE) /\
  (inst.inst_opcode = SUB ==> op_prov TG b = NONE) /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  ((?s'. step_inst fuel C inst s = OK s') \/
   (?t'. step_inst fuel C' inst t = OK t')) ==>
  ?s' t'. step_inst fuel C inst s = OK s' /\
    step_inst fuel C' inst t = OK t' /\
    ptr_vars_transport births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `ptr_lookup_transport births positions (op_prov TG a) {}
     (eval_operand a s) (eval_operand a t)` by
    (drule ptr_vars_transport_eval >> disch_then (qspec_then `a` mp_tac) >> simp[]) >>
  `ptr_lookup_transport births positions (op_prov TG b) {}
     (eval_operand b s) (eval_operand b t)` by
    (drule ptr_vars_transport_eval >> disch_then (qspec_then `b` mp_tac) >> simp[]) >>
  irule ptr_affine_transport_lookup >> simp[] >> metis_tac[]
QED

Theorem ptr_affine_transport_all:
  ptr_vars_transport births positions TG tn s t /\
  s.vs_labels = t.vs_labels /\
  inst.inst_operands = [a;b] /\ inst.inst_outputs = [out] /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  (inst.inst_opcode = ADD ==> op_prov TG a = NONE \/ op_prov TG b = NONE) /\
  (inst.inst_opcode = SUB ==> op_prov TG b = NONE) /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  ((?s'. step_inst fuel C inst s = OK s') \/
   (?t'. step_inst fuel C' inst t = OK t')) ==>
  ?s' t'. step_inst fuel C inst s = OK s' /\
    step_inst fuel C' inst t = OK t' /\
    ptr_vars_transport births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `ptr_lookup_transport births positions (op_prov TG a) {}
     (eval_operand a s) (eval_operand a t)` by
    (drule_all ptr_vars_transport_eval_all >> disch_then (qspec_then `a` mp_tac) >> simp[]) >>
  `ptr_lookup_transport births positions (op_prov TG b) {}
     (eval_operand b s) (eval_operand b t)` by
    (drule_all ptr_vars_transport_eval_all >> disch_then (qspec_then `b` mp_tac) >> simp[]) >>
  irule ptr_affine_transport_lookup >> simp[] >> metis_tac[]
QED

(* Concrete operational probes use a zero-sized birth and cross the word
   modulus. No in-site or positive-size premise is hidden in transport. *)
Definition ptr_affine_probe_def:
  ptr_affine_probe opc ops x =
    case step_inst 0 (mk_venom_context [] NONE)
      (mk_inst 7 opc ops ["r"])
      (update_var "p" x (init_venom_state "entry")) of
      OK post => lookup_var "r" post
    | _ => NONE
End

Theorem ptr_affine_zero_size_wrap_probe:
  ptr_lookup_transport (FEMPTY |+ ((0,7),(32,0:num)))
    (FEMPTY |+ (Allocation 7,(64,0))) (SOME (0,7)) {}
    (ptr_affine_probe ADD [Var "p"; Lit 1w] (-1w))
    (ptr_affine_probe ADD [Var "p"; Lit 1w] 31w) /\
  ptr_affine_probe ADD [Var "p"; Lit 1w] (-1w) = SOME 0w /\
  ptr_affine_probe ADD [Var "p"; Lit 1w] 31w = SOME 32w
Proof
  EVAL_TAC >> simp[] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem ptr_affine_sub_wrap_probe:
  ptr_lookup_transport (FEMPTY |+ ((0,7),(32,0:num)))
    (FEMPTY |+ (Allocation 7,(64,0))) (SOME (0,7)) {}
    (ptr_affine_probe SUB [Var "p"; Lit 1w] 0w)
    (ptr_affine_probe SUB [Var "p"; Lit 1w] 32w) /\
  ptr_affine_probe SUB [Var "p"; Lit 1w] 0w = SOME (-1w) /\
  ptr_affine_probe SUB [Var "p"; Lit 1w] 32w = SOME 31w
Proof
  EVAL_TAC >> simp[] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem ptr_affine_selection_scalar_probe:
  ptr_lookup_transport (FEMPTY |+ ((0,7),(32,0:num)))
    (FEMPTY |+ (Allocation 7,(64,0))) (SOME (0,7)) {}
    (ptr_affine_probe ADD [Lit 1w; Var "p"] (-1w))
    (ptr_affine_probe ADD [Lit 1w; Var "p"] 31w) /\
  ptr_lookup_transport (FEMPTY |+ ((0,7),(32,0:num)))
    (FEMPTY |+ (Allocation 7,(64,0))) (SOME (0,7)) {}
    (ptr_affine_probe ASSIGN [Var "p"] (-1w))
    (ptr_affine_probe ASSIGN [Var "p"] 31w) /\
  ptr_affine_probe ADD [Lit 1w; Lit (-1w)] 0w = SOME 0w /\
  ptr_affine_probe SUB [Lit 0w; Lit 1w] 0w = SOME (-1w)
Proof
  EVAL_TAC >> simp[] >> wordsLib.WORD_DECIDE_TAC
QED

(* Integration obligations, not additional assumptions of prefix coverage:
   - taint_ok's first conjunct forces both arithmetic operand masks empty.
   - affine_pointer_ops forbids two syntactic pointer operands for ADD and
     any right pointer operand for SUB. Turning this into the op_prov
     hypotheses requires dynamic-tag support in fn_pv, still owned by the
     global invariant; value transport alone does not imply that support.
   - ptr_vars_transport_eval_all and the *_transport_all boundaries cover
     scalar Labels, including missing lookups, conditional on label-map
     equality. The global target-prefix construction must establish and
     preserve that equality across entry, calls and return; it is not a
     consequence of ptr_vars_transport alone.
   ASSIGN keeps the selected mask rather than requiring it to be empty.
   The disjunction of successful steps in ptr_affine_transport allows the
   construction to start on either side; determinism identifies the given
   endpoint with the constructed endpoint. *)
