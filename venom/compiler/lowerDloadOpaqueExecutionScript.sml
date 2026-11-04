Theory lowerDloadOpaqueExecution
Ancestors
  unitShapeDefs execEquivParamBase venomExecSemantics venomInst
  contextCodegenRel list lowerDloadReturnBoundary lowerDloadOrdinaryExecution
  finite_map pred_set venomState lowerDloadPairedBoundary
  lowerDloadOwnership ptrDiscipline

(* Opaque return-PC values cannot be observed by ordinary instructions. *)
Theorem ld_retpc_observable_operand:
  opaque_use_ok fn /\ MEM i (fn_insts fn) /\
  i.inst_opcode <> ASSIGN /\ i.inst_opcode <> PHI /\
  ~MEM i.inst_opcode [RET; RETFMP; DRET] /\
  MEM (Var x) i.inst_operands ==> ~retpc_var fn x
Proof
  strip_tac >> strip_tac >>
  drule_all opaque_use_ok_retpc_use >> simp[retpc_use_ok_def]
QED

(* Only the final operand is permitted to carry an opaque return token. *)
Theorem ld_retpc_return_front:
  opaque_use_ok fn /\ MEM i (fn_insts fn) /\
  MEM i.inst_opcode [RET; RETFMP; DRET] /\
  MEM (Var x) (FRONT i.inst_operands) ==> ~retpc_var fn x
Proof
  strip_tac >> strip_tac >>
  `i.inst_operands <> []` by (strip_tac >> gvs[]) >>
  `MEM (Var x) i.inst_operands` by
    metis_tac[APPEND_FRONT_LAST, MEM_APPEND] >>
  drule_all opaque_use_ok_retpc_use >>
  simp[retpc_use_ok_def] >> rpt strip_tac >>
  gvs[GSYM SNOC_APPEND, FRONT_SNOC]
QED

(* Contraposition of the seeded closure: a nonopaque output of a copy
   cannot have obtained its value from an opaque input.  The seed is
   arbitrary, so the same interface also covers opaque gas variables. *)
Theorem ld_copy_nonopaque_input:
  MEM i (fn_insts fn) /\ i.inst_opcode = ASSIGN /\
  i.inst_operands = [Var y] /\ MEM x i.inst_outputs /\
  ~copy_phi_var origin fn x ==> ~copy_phi_var origin fn y
Proof
  metis_tac[copy_phi_var_assign]
QED

Theorem ld_phi_nonopaque_selected_input:
  MEM i (fn_insts fn) /\ i.inst_opcode = PHI /\
  resolve_phi prev i.inst_operands = SOME (Var y) /\
  MEM x i.inst_outputs /\ ~copy_phi_var origin fn x ==>
  ~copy_phi_var origin fn y
Proof
  strip_tac >> strip_tac >>
  `MEM (Var y) i.inst_operands` by metis_tac[resolve_phi_MEM] >>
  metis_tac[copy_phi_var_phi]
QED

Theorem ld_ret_front_equal:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM i (fn_insts fn) /\
  i.inst_opcode = RET /\ FDOM AG SUBSET fn_pv P fn /\ taint_ok fn tn i s /\
  ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) ==>
  eval_operands (FRONT i.inst_operands) s =
  eval_operands (FRONT i.inst_operands) t
Proof
  strip_tac >> irule ld_owned_operands_clean >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >>
  `MEM op i.inst_operands` by
    (Cases_on `i.inst_operands = []` >- gvs[] >>
     metis_tac[APPEND_FRONT_LAST, MEM_APPEND]) >>
  drule_all ld_ret_operand_scalar >> strip_tac >> simp[] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[ld_retpc_return_front, MEM]
QED

(* Whole-support definedness is deliberately independent of owned values. *)
Theorem ld_supported_operand_defined:
  s.vs_labels = t.vs_labels /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  (!v. op = Var v ==> v IN V) ==>
  (eval_operand op s = NONE <=> eval_operand op t = NONE)
Proof
  Cases_on `op` >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem ld_supported_operands_defined:
  !ops. s.vs_labels = t.vs_labels /\
    (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
    (!v. MEM (Var v) ops ==> v IN V) ==>
    (eval_operands ops s = NONE <=> eval_operands ops t = NONE)
Proof
  Induct >- simp[eval_operands_def] >>
  rpt strip_tac >> simp[eval_operands_def] >>
  `eval_operand h s = NONE <=> eval_operand h t = NONE` by
    (irule ld_supported_operand_defined >> simp[] >>
     qexists_tac `V` >> metis_tac[MEM]) >>
  `eval_operands ops s = NONE <=> eval_operands ops t = NONE` by
    (first_x_assum irule >> metis_tac[MEM]) >>
  Cases_on `eval_operand h s` >> Cases_on `eval_operand h t` >> gvs[] >>
  Cases_on `eval_operands ops s` >> Cases_on `eval_operands ops t` >> gvs[]
QED

Theorem ld_owned_vars_tvar_cong:
  tn'.t_var = tn.t_var /\ un'.t_var = un.t_var ==>
  (ld_owned_vars V E AG AH tn' un' s t <=> ld_owned_vars V E AG AH tn un s t)
Proof
  simp[ld_owned_vars_def, op_taint_def]
QED

(* Updating a variable outside the tracked support needs no value relation.
   Other taint fields are deliberately unconstrained at the output. *)
Theorem ld_owned_vars_update_supported:
  ld_owned_vars V E AG AH tn un s t /\
  (out IN V ==> ld_owned_value E ps pt Ms Mt x y) /\
  tn'.t_var = set_var_taint tn.t_var [out] Ms /\
  un'.t_var = set_var_taint un.t_var [out] Mt ==>
  ld_owned_vars V E (ld_set_prov AG [out] ps) (ld_set_prov AH [out] pt)
    tn' un' (update_var out x s) (update_var out y t)
Proof
  simp[ld_owned_vars_def, update_var_def] >> rpt strip_tac >>
  Cases_on `v = out` >>
  gvs[lookup_var_def, op_taint_def, set_var_taint_def, FLOOKUP_UPDATE] >>
  Cases_on `ps` >> Cases_on `pt` >>
  gvs[ld_set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem ld_lookup_defined_update:
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) ==>
  !v. v IN V ==>
    (lookup_var v (update_var out x s) = NONE <=>
     lookup_var v (update_var out y t) = NONE)
Proof
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED


Theorem ld_nonopaque_assign_backward:
  MEM i (fn_insts fn) /\ i.inst_opcode = ASSIGN /\
  i.inst_operands = [op] /\ i.inst_outputs = [out] /\
  ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG AH tn un s t /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  (!v. op = Var v ==> v IN V) /\
  step_inst fuelT CT i t = OK t' ==>
  ?x y s'. eval_operand op s = SOME x /\ eval_operand op t = SOME y /\
    s' = update_var out x s /\ t' = update_var out y t /\
    step_inst fuelS CS i s = OK s' /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE))
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  Cases_on `eval_operand op t` >> simp[] >> strip_tac >>
  `s.vs_labels = t.vs_labels` by fs[ld_owned_vars_def] >>
  `eval_operand op s = NONE <=> eval_operand op t = NONE` by
    (irule ld_supported_operand_defined >> simp[] >>
     qexists_tac `V` >> simp[]) >>
  Cases_on `eval_operand op s` >> gvs[] >>
  `out IN V /\ ~retpc_var fn out ==>
    ld_owned_value E (ld_op_prov AG op) (ld_op_prov AH op)
      (op_taint tn op) (op_taint un op) x' x` by
    (strip_tac >>
     `!v. op = Var v ==> v IN {v | v IN V /\ ~retpc_var fn v}` by
       (simp[] >> rpt strip_tac >> gvs[] >>
        fs[retpc_var_def] >> metis_tac[ld_copy_nonopaque_input, MEM]) >>
     drule_all ld_owned_operand_value >> simp[]) >>
  reverse conj_tac >- metis_tac[ld_lookup_defined_update] >>
  Cases_on `ld_op_prov AG op` >> Cases_on `ld_op_prov AH op` >>
  simp[ld_step_prov_def, ld_out_prov_def, ld_first_prov_def] >>
  irule ld_owned_vars_update_supported >>
  goal_assum (drule_at Any) >> simp[step_taint_def, out_taint_def] >>
  qexistsl_tac [`op_taint tn op`, `op_taint un op`] >> simp[]
QED

Theorem ld_nonopaque_phis_backward:
  !ins s t t' AG AH tn un.
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG AH tn un s t /\
    (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
    s.vs_prev_bb = t.vs_prev_bb /\
    (!i. MEM i ins ==> MEM i (fn_insts fn)) /\
    (!i v. MEM i ins /\ MEM (Var v) i.inst_operands ==> v IN V) /\
    eval_phis t ins = OK t' ==>
    ?s'. eval_phis s ins = OK s' /\
      ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
        (ld_phis_prov s.vs_prev_bb AG ins) (ld_phis_prov t.vs_prev_bb AH ins)
        (tn with t_var := phis_taint s.vs_prev_bb tn ins)
        (un with t_var := phis_taint t.vs_prev_bb un ins) s' t' /\
      (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE))
Proof
  Induct >> rpt gen_tac >> simp[eval_phis_def, ld_phis_prov_def, phis_taint_def]
  >- (strip_tac >> gvs[]) >>
  strip_tac >> Cases_on `h.inst_opcode = PHI` >> gvs[]
  >- (gvs[eval_one_phi_def, AllCaseEqs()] >>
      rename1 `eval_operand op t = SOME y` >>
      `!v. op = Var v ==> v IN V` by metis_tac[resolve_phi_MEM, MEM] >>
      `s.vs_labels = t.vs_labels` by fs[ld_owned_vars_def] >>
      `eval_operand op s = NONE <=> eval_operand op t = NONE` by
        (irule ld_supported_operand_defined >> simp[] >>
         qexists_tac `V` >> simp[]) >>
      Cases_on `eval_operand op s` >> gvs[] >>
      `out IN V /\ ~retpc_var fn out ==>
        ld_owned_value E (ld_op_prov AG op) (ld_op_prov AH op)
          (op_taint tn op) (op_taint un op) x y` by
        (strip_tac >>
         `!v. op = Var v ==> v IN {v | v IN V /\ ~retpc_var fn v}` by
           (simp[] >> rpt strip_tac >> gvs[] >> fs[retpc_var_def] >>
            metis_tac[ld_phi_nonopaque_selected_input, MEM]) >>
         drule_all ld_owned_operand_value >> simp[]) >>
      first_x_assum (qspecl_then [`s`, `t`] mp_tac) >>
      disch_then drule >> disch_then (qspec_then `s''` mp_tac) >>
      simp[] >> impl_tac >- metis_tac[MEM] >> strip_tac >>
      qexists_tac `update_var out x s'` >>
      conj_tac >- metis_tac[] >>
      reverse conj_tac >- metis_tac[ld_lookup_defined_update] >>
      simp[ld_phi_prov_def, phi_taint_def] >>
      irule ld_owned_vars_update_supported >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`op_taint tn op`, `op_taint un op`] >> simp[]) >>
  first_x_assum irule >> simp[] >> metis_tac[MEM]
QED

(* The hidden token is a word field, hence always defined.  Its two values
   need not agree; the seed rule excludes its output from owned support. *)
Theorem ld_retpc_param_backward:
  MEM i (fn_insts fn) /\ i.inst_opcode = RETPC_PARAM /\
  i.inst_operands = [Lit idx] /\ i.inst_outputs = [out] /\
  ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG AH tn un s t /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE))
Proof
  strip_tac >>
  `retpc_var fn out` by
    (simp[retpc_var_def] >> irule copy_phi_var_seed >> metis_tac[MEM]) >>
  gvs[step_inst_non_invoke, step_inst_base_def] >>
  reverse conj_tac >- metis_tac[ld_lookup_defined_update] >>
  simp[ld_step_prov_def, ld_out_prov_def] >>
  irule ld_owned_vars_update_supported >>
  goal_assum (drule_at Any) >> simp[step_taint_def, out_taint_def] >>
  qexistsl_tac [`{}`, `{}`] >> simp[eval_operand_def]
QED

Theorem ld_eval_operands_front[local]:
  !ops vals. eval_operands ops s = SOME vals ==>
    (vals = [] <=> ops = []) /\
    eval_operands (FRONT ops) s = SOME (FRONT vals)
Proof
  Induct >- simp[eval_operands_def] >> rpt gen_tac >>
  simp[eval_operands_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `ops` >> gvs[eval_operands_def, FRONT_DEF] >>
  first_x_assum drule >> simp[eval_operands_def, FRONT_DEF]
QED

Theorem ld_nonopaque_ret_backward:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM i (fn_insts fn) /\
  i.inst_opcode = RET /\ FDOM AG SUBSET fn_pv P fn /\ taint_ok fn tn i s /\
  ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG AH tn un s t /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  step_inst fuelT CT i t = IntRet rr t' ==>
  step_inst fuelS CS i s = IntRet rr s /\ t' = t
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels` by fs[ld_owned_vars_def] >>
  `eval_operands i.inst_operands s = NONE <=>
   eval_operands i.inst_operands t = NONE` by
    (irule ld_supported_operands_defined >> simp[] >>
     qexists_tac `V` >> simp[]) >>
  `eval_operands (FRONT i.inst_operands) s =
   eval_operands (FRONT i.inst_operands) t` by
    (irule ld_ret_front_equal >> goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  Cases_on `eval_operands i.inst_operands s` >> gvs[] >>
  qpat_assum `eval_operands _ s = SOME _`
    (mp_then Any strip_assume_tac ld_eval_operands_front) >>
  qpat_assum `eval_operands _ t = SOME _`
    (mp_then Any strip_assume_tac ld_eval_operands_front) >> gvs[] >>
  Cases_on `x` >> gvs[]
QED
