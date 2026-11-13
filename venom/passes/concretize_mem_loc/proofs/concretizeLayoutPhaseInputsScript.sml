Theory concretizeLayoutPhaseInputs
Ancestors concretizeLayoutCalleeRoots concretizeLayoutPhaseOrigin
  frameActivationLookup concretizeLayoutParameterRoots venomExecSemantics
  concretizeLayoutArgumentRoots

Theorem parameter_roots_lookup_transport:
  parameter_roots (\i x y. clean_resolved_root L (resolved_parameter_entry rp i) x y) xs ys /\
  (!i tok site. i < LENGTH xs /\ resolved_parameter_entry rp i = SOME (tok,site) ==>
    L' tok = L tok) ==>
  parameter_roots (\i x y. clean_resolved_root L' (resolved_parameter_entry rp i) x y) xs ys
Proof
  simp[parameter_roots_def] >> rpt strip_tac >>
  qpat_x_assum `!j. j < LENGTH xs ==> _` (qspec_then `i` mp_tac) >>
  Cases_on `resolved_parameter_entry rp i`
  >- gvs[clean_resolved_root_def] >>
  PairCases_on `x` >> gvs[clean_resolved_root_def] >>
  metis_tac[]
QED

Theorem parameter_roots_fields:
  parameter_roots R s.vs_params t.vs_params /\
  s'.vs_params = s.vs_params /\ t'.vs_params = t.vs_params ==>
  parameter_roots R s'.vs_params t'.vs_params
Proof
  simp[]
QED

Theorem parameter_roots_normalize:
  parameter_roots R (layout_phase_normalize p s).vs_params
    (layout_phase_normalize q t).vs_params <=>
  parameter_roots R s.vs_params t.vs_params
Proof
  Cases_on `p` >> Cases_on `q` >> simp[layout_phase_normalize_def]
QED

Theorem parameter_roots_activation_push:
  parameter_roots (\i x y. clean_resolved_root
    (activation_lookup default positions ids owners) (resolved_parameter_entry rp i) x y) xs ys /\
  (!i token aid site. i < LENGTH xs /\
    resolved_parameter_entry rp i = SOME ((token,aid),site) ==> token <> birth) ==>
  parameter_roots (\i x y. clean_resolved_root
    (activation_lookup default positions (birth::ids) (owner::owners))
    (resolved_parameter_entry rp i) x y) xs ys
Proof
  rpt strip_tac >> irule parameter_roots_lookup_transport >>
  goal_assum (drule_at Any) >> rpt strip_tac >> PairCases_on `tok` >>
  irule activation_lookup_push >> metis_tac[]
QED

Theorem disciplined_invoke_setup_pushed_roots:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (name,ops) /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn) (activation_lookup default positions ids owners) rv)
    (guarded_bytes (retpc_var fn) rv tn) Rmem Obs s t /\
  s.vs_labels = t.vs_labels /\ eval_operands ops s = SOME args /\
  setup_callee callee args s = SOME sc /\ ~NULL target.fn_blocks /\
  (!i token aid site. i < LENGTH args /\
    EL i (MAP (resolved_op rv) ops) = SOME ((token,aid),site) ==>
    token <> birth) ==>
  ?args' tc. eval_operands ops t = SOME args' /\
    setup_callee target args' t = SOME tc /\
    parameter_roots (\i x y. clean_resolved_root
      (activation_lookup default positions (birth::ids) (owner::owners))
      (resolved_parameter_entry (MAP (resolved_op rv) ops) i) x y)
      sc.vs_params tc.vs_params
Proof
  rpt strip_tac >>
  `LENGTH args = LENGTH ops` by
    (drule_all argument_roots_evaluation >> strip_tac >> simp[]) >>
  drule_all disciplined_invoke_setup_roots >> strip_tac >>
  `LENGTH sc.vs_params = LENGTH ops` by gvs[setup_callee_def] >>
  qexistsl_tac [`args'`, `tc`] >> simp[] >>
  irule parameter_roots_activation_push >>
  simp[parameter_roots_bounded_annotations, resolved_parameter_entry_def] >>
  rpt strip_tac >> gvs[setup_callee_def] >> metis_tac[]
QED
