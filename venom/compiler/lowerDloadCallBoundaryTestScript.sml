Theory lowerDloadCallBoundaryTest
Ancestors
  lowerDloadReturnBoundary lowerDloadTargetGeometry lowerDloadOrdinaryExecution lowerDloadFrameCertificate
  lowerDloadPairedBoundary lowerDloadOwnership lowerDloadAllocation
  lowerDloadControlPosition lowerDloadDefs venomExecSemantics venomState
  ptrDiscipline contextCodegenRel finite_map pred_set list rich_list

(* Simultaneous boundary schema (not a new relation):
   - source ld_annotated_reachable vs0 C astk k L AP AG tn fn inst s;
     target is at the matching configured macro boundary (or strict prefix).
   - ld_frame_embedding E L H s t; LIST_REL (ld_owned_selection E) AP BP;
     pointwise AG/BH owned selections; ld_owned_vars V E AG BH tn un s t.
   - masked memory uses this E and the owner projection of ld_live astk L AP AG,
     together with fixed bytes below lo; memory is never saved in a frame.
   - ld_alloc_account keys d A s t; d=32*SUM(MAP CARD suspended);
     ld_frame_bound t.vs_alloca_next H BP BH; target ld_stack_bound and floor.
   - source ld_stack_origin on the erased annotated stack; scratch sets/caps
     aligned to fn :: MAP (fn of erased frame) astk.
   - saved frames are aligned with tuples (support,keys,A), and each saved
     ld_saved_embedded uses d=32*SUM of the sets STRICTLY BELOW that frame.
     Independently existential saved displacements cannot establish this.

   Tests below produce source semantic equations, not recursive callee runs.
   Source stack-origin advancement on return will require the recursive
   completed-callee summary; local call-entry alone does not supply that run.
*)

Theorem ld_eval_operands_length[local]:
  !ops s xs. eval_operands ops s = SOME xs ==> LENGTH xs = LENGTH ops
Proof
  Induct >> simp[eval_operands_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem ld_return_values_bind_backward:
  (i.inst_opcode = RET \/ i.inst_opcode = RETFMP) /\
  ld_owned_vars V E AG BH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  step_inst fuelT CT i t = IntRet tret tend /\
  f.lf_inst.inst_outputs = g.lf_inst.inst_outputs /\
  bind_outputs g.lf_inst.inst_outputs tret.iret_values
    (adopt_return_fmp tret (merge_callee_state g.lf_state tend)) = SOME t' ==>
  ?xs ys sret s'.
    eval_operands i.inst_operands s = SOME xs /\
    eval_operands i.inst_operands t = SOME ys /\ xs <> [] /\
    LIST_REL (\(op,x) y. ld_owned_value E (ld_op_prov AG op)
      (ld_op_prov BH op) (op_taint tn op) (op_taint un op) x y)
      (ZIP (i.inst_operands,xs)) ys /\
    sret.iret_values = FRONT xs /\ tret.iret_values = FRONT ys /\
    sret.iret_adopt_fmp = (if i.inst_opcode = RET then NONE else SOME s.vs_fmp) /\
    step_inst fuelS CS i s = IntRet sret s /\
    bind_outputs f.lf_inst.inst_outputs sret.iret_values
      (adopt_return_fmp sret (merge_callee_state f.lf_state s)) = SOME s'
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuelT CT i t = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  qpat_assum `i.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
  simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `eval_operands i.inst_operands t = SOME (y::ys)` >>
  drule_all ld_owned_operands_target >> strip_tac >>
  `LENGTH xs = LENGTH (y::ys)` by metis_tac[ld_eval_operands_length] >>
  `xs <> []` by (strip_tac >> gvs[]) >>
  simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  qpat_assum `i.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >> simp[] >>
  qexists `<| iret_values := FRONT xs;
              iret_adopt_fmp := if i.inst_opcode = RET then NONE else SOME s.vs_fmp |>` >>
  Cases_on `xs` >> gvs[bind_outputs_def, LENGTH_FRONT, adopt_return_fmp_def]
QED

Theorem ld_call_setup_backward:
  lower_dload_function_supply a source = (callee,b) /\
  ld_owned_vars V E AG BH tn un s t /\
  (!v. MEM (Var v) ops ==> v IN V) /\
  eval_operands ops t = SOME args /\
  setup_callee callee args t = SOME cs ==>
  ?sargs ss.
    eval_operands ops s = SOME sargs /\
    LIST_REL (\(op,x) y. ld_owned_value E (ld_op_prov AG op)
      (ld_op_prov BH op) (op_taint tn op) (op_taint un op) x y)
      (ZIP (ops,sargs)) args /\
    setup_callee source sargs s = SOME ss /\
    ld_owned_vars childV E FEMPTY FEMPTY stn utn ss cs /\
    ss.vs_allocas = FEMPTY /\ cs.vs_allocas = FEMPTY /\
    ss.vs_prev_bb = cs.vs_prev_bb /\
    ss.vs_current_bb = cs.vs_current_bb /\
    ss.vs_params = sargs /\ cs.vs_params = args /\
    ss.vs_return_pc_token = (if NULL sargs then 0w else LAST sargs) /\
    cs.vs_return_pc_token = (if NULL args then 0w else LAST args)
Proof
  strip_tac >> drule_all ld_owned_operands_target >> strip_tac >>
  qexists_tac `xs` >> simp[] >>
  `MAP (\bb. bb.bb_label) callee.fn_blocks =
   MAP (\bb. bb.bb_label) source.fn_blocks` by
    (gvs[lower_dload_function_supply_def, AllCaseEqs()] >>
     metis_tac[o1ContractLowerDloadTheory.lower_dload_blocks_supply_labels]) >>
  qpat_x_assum `setup_callee _ _ _ = _` mp_tac >>
  simp[setup_callee_def] >> strip_tac >>
  Cases_on `source.fn_blocks` >> Cases_on `callee.fn_blocks` >> gvs[] >>
  simp[setup_callee_def] >>
  gvs[ld_owned_vars_def, lookup_var_def]
QED

Theorem ld_call_block_entry_backward:
  lower_dload_function_supply a source = (callee,b) /\
  ld_owned_vars V E AG BH tn un ss cs /\
  ss.vs_current_bb = cs.vs_current_bb /\ ss.vs_prev_bb = cs.vs_prev_bb /\
  (!bb i v. MEM bb source.fn_blocks /\ MEM i bb.bb_instructions /\
     MEM (Var v) i.inst_operands ==> v IN V) /\
  enters_block callee cs t1 ==>
  ?s1. enters_block source ss s1 /\
    s1.vs_inst_idx = t1.vs_inst_idx
Proof
  strip_tac >>
  qpat_x_assum `enters_block _ _ _` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  `?bbs z. lower_dload_blocks_supply a source.fn_blocks = (bbs,z) /\
     callee.fn_blocks = bbs` by
    gvs[lower_dload_function_supply_def, AllCaseEqs()] >>
  gvs[] >> drule_all lower_dload_blocks_supply_lookup >> strip_tac >>
  `MEM bb' source.fn_blocks` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `!i v. MEM i bb'.bb_instructions /\ MEM (Var v) i.inst_operands ==> v IN V` by
    metis_tac[] >>
  drule_all ld_owned_lowered_block_phis_backward >> strip_tac >>
  drule lower_dload_block_supply_phis >> strip_tac >>
  simp[enters_block_def] >> metis_tac[]
QED

Theorem ld_return_pop_backward:
  (i.inst_opcode = RET \/ i.inst_opcode = RETFMP) /\
  ld_owned_vars V E AG BH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  step_inst fuelT CT i t = IntRet tret tend /\
  f.lf_inst.inst_outputs = g.lf_inst.inst_outputs /\
  bind_outputs g.lf_inst.inst_outputs tret.iret_values
    (adopt_return_fmp tret (merge_callee_state g.lf_state tend)) = SOME t' /\
  ld_stack_bound n (g::gstk) /\ lo <= g.lf_state.vs_alloca_next /\
  ld_saved_embedded savedV E keys d A f g /\
  d = 32 * SUM (MAP CARD suspended) ==>
  ?sret s'. step_inst fuelS CS i s = IntRet sret s /\
    bind_outputs f.lf_inst.inst_outputs sret.iret_values
      (adopt_return_fmp sret (merge_callee_state f.lf_state s)) = SOME s' /\
    ld_frame_bound t'.vs_alloca_next g.lf_local g.lf_params
      (DRESTRICT g.lf_prov (COMPL (set g.lf_inst.inst_outputs))) /\
    ld_stack_bound t'.vs_alloca_next gstk /\ lo <= t'.vs_alloca_next /\
    ld_alloc_account keys d A s' t' /\
    t'.vs_alloca_next = s'.vs_alloca_next + 32 * SUM (MAP CARD (A::suspended))
Proof
  strip_tac >>
  `?sret s'. step_inst fuelS CS i s = IntRet sret s /\
    bind_outputs f.lf_inst.inst_outputs sret.iret_values
      (adopt_return_fmp sret (merge_callee_state f.lf_state s)) = SOME s'` by
    metis_tac[ld_return_values_bind_backward] >>
  qexistsl_tac [`sret`,`s'`] >> simp[] >>
  drule_all ld_return_geometry >> simp[]
QED

Theorem ld_call_entry_geometry_backward:
  lower_dload_function_supply a source = (callee,b) /\
  ld_owned_vars V E AG BH tn un s t /\
  (!v. MEM (Var v) ops ==> v IN V) /\
  (!bb i v. MEM bb source.fn_blocks /\ MEM i bb.bb_instructions /\
     MEM (Var v) i.inst_operands ==> v IN V) /\
  eval_operands ops t = SOME args /\
  setup_callee callee args t = SOME cs /\ enters_block callee cs t1 /\
  ld_alloc_account keys d A s t /\ FINITE child_keys /\
  d = 32 * SUM (MAP CARD suspended) /\
  ld_frame_bound t.vs_alloca_next H BP BH /\
  ld_stack_bound t.vs_alloca_next gstk /\ lo <= t.vs_alloca_next ==>
  ?sargs ss s1.
    eval_operands ops s = SOME sargs /\
    setup_callee source sargs s = SOME ss /\ enters_block source ss s1 /\
    s1.vs_inst_idx = t1.vs_inst_idx /\
    ld_frame_bound t1.vs_alloca_next FEMPTY (MAP (ld_op_prov BH) ops) FEMPTY /\
    ld_stack_bound t1.vs_alloca_next
      (<| lf_fn := caller; lf_inst := ins; lf_state := t;
          lf_params := BP; lf_prov := BH; lf_tvar := un.t_var;
          lf_local := H |> :: gstk) /\ lo <= t1.vs_alloca_next /\
    ld_alloc_account child_keys (32 * SUM (MAP CARD (A::suspended))) {} s1 t1
Proof
  strip_tac >> drule_all ld_call_setup_backward >>
  disch_then (qspecl_then [`un`,`tn`,`V`] strip_assume_tac) >>
  drule_all ld_call_block_entry_backward >> strip_tac >>
  qexistsl_tac [`sargs`,`ss`,`s1`] >> simp[] >>
  drule_all ld_call_geometry >> simp[]
QED

(* Diagnostic boundary, not a global simulation:
   ld_call_entry_geometry_backward produces actual source argument evaluation,
   setup and block entry from target equations. It also produces the child
   account with the pushed charge A::suspended, for arbitrary A and stack.
   ld_return_pop_backward produces an actual source IntRet and caller bind,
   and restores the saved caller account/floor/stack bound. No inequality
   between the callee frontier and the restored caller frontier is needed.

   Remaining simultaneous pairing obligations (not assumed by these tests):
   - The LIST_REL of evaluated return operands alone is insufficient for
     resumed ld_owned_vars: ret drops output provenance AND output taint.
     Thus the values bound to caller outputs must be equal scalars. A
     sufficient exit interface is, for every return operand op,
       ld_op_prov AG op = NONE /\ op_taint tn op = {}.
     With operand support, ld_owned_operand_clean then gives equal vectors.
     taint_ok excludes tainted RET operands; fn_ptr_ok/ptr_use_ok exclude
     pointer-derived RET operands. The bridge from those source conditions
     to NONE annotated provenance must still be consumed/proved, together
     with bind_outputs preservation for the restricted saved maps.
   - RETFMP is included above only to test semantic existence: the source
     return adopts s.vs_fmp and the target adopts t.vs_fmp. fn_ptr_ok excludes
     RETFMP (and DRET), so global closure should use that exclusion, not an
     unjustified equality of the adopted values.
   - setup retains the complete argument vector; LAST is the return-PC
     token. Its equality needs the same scalar/clean argument discipline
     at that position, not merely equality of vector lengths.
   - Saved certificates must be pushed from the SAME predecessor E, AP/BP,
     AG/BH and account, and indexed with the tail charge sums. The current
     tests do not existentially select independent saved displacements.
   - Source annotated reachability/stack origin at a resumed caller needs
     the recursive completed-source-callee summary. Local source setup and
     IntRet existence alone cannot advance that origin.
*)

Theorem ld_ret_resumed_owned_backward:
  ptr_discipline lo ctx vs0 /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn i s /\
  i.inst_opcode = RET /\ ld_owned_vars V E AG BH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  step_inst fuelT CT i t = IntRet tret tend /\
  f.lf_inst.inst_outputs = g.lf_inst.inst_outputs /\
  bind_outputs g.lf_inst.inst_outputs tret.iret_values
    (adopt_return_fmp tret (merge_callee_state g.lf_state tend)) = SOME t' /\
  ld_saved_embedded savedV E keys d A f g ==>
  ?s'. step_inst fuelS CS i s = IntRet tret s /\
    bind_outputs f.lf_inst.inst_outputs tret.iret_values
      (merge_callee_state f.lf_state s) = SOME s' /\
    ld_owned_vars savedV E
      (DRESTRICT f.lf_prov (COMPL (set f.lf_inst.inst_outputs)))
      (DRESTRICT g.lf_prov (COMPL (set g.lf_inst.inst_outputs)))
      (entry_taint with t_var := DRESTRICT f.lf_tvar
        (COMPL (set f.lf_inst.inst_outputs)))
      (entry_taint with t_var := DRESTRICT g.lf_tvar
        (COMPL (set g.lf_inst.inst_outputs))) s' t'
Proof
  strip_tac >>
  `eval_operands i.inst_operands s = eval_operands i.inst_operands t` by
    (irule ld_annotated_ret_operands_equal >> metis_tac[]) >>
  qpat_x_assum `step_inst fuelT CT i t = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >> simp[] >>
  strip_tac >> gvs[AllCaseEqs(), adopt_return_fmp_def] >>
  drule ld_bind_outputs_target_exists >>
  disch_then (qspec_then `merge_callee_state f.lf_state s` strip_assume_tac) >>
  qexists_tac `s'` >> simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >> simp[] >>
  drule ld_saved_embedded_return_vars >>
  disch_then (qspecl_then [`t`,`s`] assume_tac) >>
  drule_all ld_owned_bind_outputs >> simp[]
QED

(* Each charge is indexed by the strict tail, never by all active frames.
   The head is the very same f,g,E certificate used by the return producer. *)
Theorem ld_saved_charge_push_pop:
  ld_saved_embedded V E keys (32 * SUM (MAP CARD suspended)) A f g /\
  (!j. j < LENGTH suspended ==>
    ld_saved_embedded (EL j supports) E (EL j keysets)
      (32 * SUM (MAP CARD (DROP (SUC j) suspended)))
      (EL j suspended) (EL j fs) (EL j gs)) ==>
  (!j. j < LENGTH (A::suspended) ==>
    ld_saved_embedded (EL j (V::supports)) E (EL j (keys::keysets))
      (32 * SUM (MAP CARD (DROP (SUC j) (A::suspended))))
      (EL j (A::suspended)) (EL j (f::fs)) (EL j (g::gs))) /\
  ld_alloc_account keys (32 * SUM (MAP CARD suspended)) A
    f.lf_state g.lf_state /\
  g.lf_state.vs_alloca_next = f.lf_state.vs_alloca_next +
    32 * SUM (MAP CARD (A::suspended))
Proof
  strip_tac >> conj_tac
  >- (gen_tac >> Cases_on `j` >> simp[] >> metis_tac[]) >>
  drule ld_saved_embedded_account >> strip_tac >> simp[] >>
  drule ld_alloc_account_frontier >> simp[]
QED

Theorem ld_setup_return_token_residual:
  setup_callee source xs s = SOME ss /\
  setup_callee target ys t = SOME ts /\ NULL xs = NULL ys ==>
  (ss.vs_return_pc_token = ts.vs_return_pc_token <=>
   NULL xs \/ LAST xs = LAST ys)
Proof
  simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `NULL ys` >> gvs[]
QED

(* Exact residual of the return-PC audit:
   ptr_use_ok at INVOKE allows any pointer argument position k IN P nm;
   it does not exclude LENGTH args - 1 from P nm. setup_callee copies LAST
   into vs_return_pc_token. RETPC_PARAM [Lit idx] then reads that field
   independently of idx, whereas its pointer provenance has no Var input.
   Thus a relocated pointer in the last argument is not ruled out by the
   current local premises. A global paired boundary must either establish
   equal LAST values from an additional reachable/static invariant, or
   represent the token's relocation and its propagation through RETPC_PARAM.
   The residual theorem above is only an equivalence, not such a producer.

   Independently, resumed source stack origin requires an actual derivation
   of the source run from ss (the source callee setup) to its IntRet state s.
   The local source RET equation produced here supplies only the final step;
   it does not supply that recursive execution derivation. A simultaneous
   recursive summary must retain entry setup, aligned stack certificates,
   source annotated reachability at exit, and source completed callee run.
*)
