Theory bodyPtrBopEnvWitness
Ancestors
  fragGasPathPtr ptrSafeRun ptrDiscipline venomExecSemantics
  venomExecProofs venomInstProofs venomInst venomState fragExec finite_map list arithmetic
  emitHelper emitHelperProps compileEnv exprLowering exprLoweringProps
  context codegenRel

(* A non-PHI at k prevents block entry from skipping past k. *)
Theorem non_phi_prefix_bound:
  !xs k. k < LENGTH xs /\ (EL k xs).inst_opcode <> PHI ==>
    phi_prefix_length xs <= k
Proof
  Induct >> simp[get_instruction_def, phi_prefix_length_def] >>
  Cases_on `k` >> simp[get_instruction_def, phi_prefix_length_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  simp[get_instruction_def]
QED

(* No first-arrival restriction: retain the last actual incoming edge. *)
Theorem path_normal_last_edge:
  !D lo ctx fn PG G tn s n G' tn' r.
    gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
    !t. r = OK t ==>
      (t = s /\ G' = G /\ tn' = tn) \/
      ?H un u m. gas_path_ptr_edge D lo ctx fn PG H un u m G' tn' (OK t)
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> gvs[] >> metis_tac[])
  >> rpt strip_tac >> gvs[exit_result_def]
QED

Theorem caller_edge_endpoint:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  get_instruction bb k = SOME i /\ i.inst_opcode = CALLER /\
  i.inst_outputs = [out] /\
  gas_path_ptr_edge D lo ctx fn PG G tn s n H un (OK t) /\
  t.vs_current_bb = lbl /\ t.vs_inst_idx = SUC k ==>
  FLOOKUP H out = NONE
Proof
  rpt strip_tac >>
  gvs[gas_path_ptr_edge_def, exit_result_def]
  >- suspend "ordinary"
  >- suspend "entry"
  >> gvs[jump_to_def] >> metis_tac[exit_result_def]
QED

Resume caller_edge_endpoint[ordinary]:
  drule_all step_preserves_control_flow >> strip_tac >> gvs[] >>
  gvs[ghost_step_def, step_prov_def, out_prov_def, set_prov_def,
      FLOOKUP_DRESTRICT]
QED

Resume caller_edge_endpoint[entry]:
  drule eval_phis_preserves_current_bb >> strip_tac >> gvs[] >>
  gvs[get_instruction_def] >>
  qspecl_then [`bb.bb_instructions`, `k`] mp_tac non_phi_prefix_bound >>
  simp[]
QED

Finalise caller_edge_endpoint

Theorem caller_path_endpoint:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  get_instruction bb k = SOME i /\ i.inst_opcode = CALLER /\
  i.inst_outputs = [out] /\
  gas_path_ptr D lo ctx fn PG G tn s n H un (OK t) /\
  s.vs_inst_idx = k /\ t.vs_current_bb = lbl /\
  t.vs_inst_idx = SUC k ==>
  op_prov H (Var out) = NONE
Proof
  rpt strip_tac >>
  drule path_normal_last_edge >> simp[] >> strip_tac
  >- gvs[]
  >> simp[op_prov_def] >> irule caller_edge_endpoint >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem emitted_caller_path_endpoint:
  emit_op CALLER [] sa = (op, sb) /\ fn_has_code sa sb fn /\
  gas_path_ptr D lo ctx fn PG G tn s n H un (OK t) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  op_prov H op = NONE
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
          comp_ignore_bind_def, comp_return_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
     SOME (mk_inst sa.cs_next_id CALLER []
       [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[] >> irule caller_path_endpoint >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[mk_inst_def] >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem sender_lower_value_emit:
  lower_value compile_expr cenv ty (Builtin rt (Env Sender) []) sa =
  emit_op CALLER [] sa
Proof
  simp[lower_value_def, comp_bind_def, Once compile_expr_def,
       Once compile_builtin_dispatch_component_eq,
       compile_env_var_def, as_stack_val_def] >>
  Cases_on `emit_op CALLER [] sa` >>
  simp[as_stack_val_def, unwrap_value_def, comp_return_def]
QED

(* The supplied witness may have wandered: the last arrival still
   executes CALLER. No hypothesis restricts G, PG, continuation or PHIs. *)
Theorem sender_same_witness_endpoint:
  lower_value compile_expr cenv ty (Builtin rt (Env Sender) []) sa = (op, sb) /\
  fn_has_code sa sb fn /\
  gas_path_ptr D lo ctx fn PG G tn s n H un (OK t) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  op_prov H op = NONE
Proof
  simp[sender_lower_value_emit] >>
  metis_tac[emitted_caller_path_endpoint]
QED
