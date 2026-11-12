(* Selected return execution through fields-only residual adapters. *)
Theory functionInlinerSelectedReturn
Ancestors
  functionInlinerReturnRouting functionInlinerReturnStorage
  functionInlinerRoutedReturnExecution functionInlinerPhiTransport
  functionInlinerParameterExecution venomExecSemantics venomExecProofs
  venomInst list rich_list indexedLists analysisSimDefs pair
  functionInlinerReturnAdapterLayout functionInlinerReturnTransport
  functionInlinerLocation functionInlinerSiteLayout
  functionInlinerRoutedProvenance functionInlinerOrigin functionInlinerOccurrences
  functionInlinerEnvelopes functionInlinerReachableCuts
  functionInlinerOperationalCuts functionInlinerParameterLifecycle pred_set venomState

Theorem inline_assign_fields_run:
  !xs ys s. MAP inline_inst_fields xs = MAP inline_inst_fields ys /\
    EVERY (\i. i.inst_opcode = ASSIGN) ys ==>
    run_insts fuel ctx xs s = run_insts fuel ctx ys s
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  `h.inst_opcode = ASSIGN` by gvs[] >>
  `step_inst fuel ctx h' s = step_inst fuel ctx h s` by
    (irule inline_fields_step >> gvs[]) >>
  simp[Once run_insts_def] >>
  simp[Once run_insts_def] >>
  Cases_on `step_inst fuel ctx h s` >> simp[] >> metis_tac[]
QED

Theorem inline_return_interval_execute:
  inline_adapter_interval fn l k
    (MAPi (\j op. (ASSIGN,[op],[EL j dests])) ops) ret /\
  LENGTH dests = LENGTH ops /\ eval_operands ops t = SOME vals /\
  (!x v. MEM x dests /\ MEM (Var v) ops ==> x <> v) /\ ~t.vs_halted ==>
  ?bb. lookup_block l fn.fn_blocks = SOME bb /\
    exec_block fuel ctx bb (t with vs_inst_idx := k) =
      OK (jump_to ret (FOLDL (\s (x,w). update_var x w s) t (ZIP (dests,vals))))
Proof
  strip_tac >>
  gvs[inline_adapter_interval_def] >>
  qabbrev_tac `xs = TAKE (LENGTH ops) (DROP k bb.bb_instructions)` >>
  qabbrev_tac `ys = MAP (\(x,op). <|inst_id := 0; inst_opcode := ASSIGN;
    inst_operands := [op]; inst_outputs := [x]|>) (ZIP (dests,ops))` >>
  `MAP inline_inst_fields xs = MAP inline_inst_fields ys` by
    (qpat_x_assum `MAP inline_inst_fields _ = _`
       (mp_tac o Q.AP_TERM `TAKE (LENGTH ops)`) >>
     simp[Abbr `xs`, Abbr `ys`, GSYM MAP_TAKE, TAKE_TAKE, TAKE_APPEND,
       TAKE_LENGTH_TOO_LONG] >>
     disch_then SUBST1_TAC >> irule LIST_EQ >>
     simp[EL_MAP, EL_MAPi, EL_ZIP, inline_inst_fields_def]) >>
  `EVERY (\i. i.inst_opcode = ASSIGN) ys` by
    (simp[Abbr `ys`, EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     pairarg_tac >> simp[]) >>
  `run_insts fuel ctx xs t =
     OK (FOLDL (\s (x,w). update_var x w s) t (ZIP (dests,vals)))` by
    (drule_all inline_assign_fields_run >> disch_then (fn th => rewrite_tac[th]) >>
     unabbrev_all_tac >> irule inline_return_routed_zip_execute >> simp[]) >>
  irule inline_return_sequence_exec_block >>
  conj_tac >- simp[functionInlinerOperationalTheory.inline_writes_control] >>
  qexists `xs` >>
  simp[Abbr `xs`, LENGTH_TAKE, LENGTH_DROP, EL_TAKE, EL_DROP] >>
  `inline_inst_fields (EL (k + LENGTH ops) bb.bb_instructions) =
     (JMP,[Label ret],[])` by
    (qpat_x_assum `MAP inline_inst_fields (TAKE (LENGTH ops + 1) _) = _`
       (mp_tac o Q.AP_TERM `EL (LENGTH ops)`) >>
     simp[EL_MAP, EL_TAKE, EL_DROP, EL_APPEND_EQN]) >>
  qexists `(EL (k + LENGTH ops) bb.bb_instructions).inst_id` >>
  conj_tac
  >- (gvs[get_instruction_def, inline_inst_fields_def] >>
      Cases_on `EL (k + LENGTH ops) bb.bb_instructions` >>
      gvs[instruction_component_equality]) >>
  qpat_x_assum `MAP inline_inst_fields (TAKE (LENGTH ops) _) = _` mp_tac >>
  simp[EVERY_EL] >> rpt strip_tac >>
  first_x_assum (mp_tac o Q.AP_TERM `EL n`) >>
  `LENGTH ys = LENGTH ops` by simp[Abbr `ys`] >>
  gvs[EL_MAP, inline_inst_fields_def, EVERY_EL]
QED

Theorem inline_selected_return_adapter_execute:
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j call (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert p prename fn /\
  inline_namespace_leaf_at cert q sigma child /\
  lookup_block rl child.fn_blocks = SOME rb /\ get_instruction rb ri = SOME ret /\
  MEM ret.inst_opcode [RET; RETFMP] /\ ret.inst_operands = ops ++ [pc] /\
  inline_tracked_snapshot child a route snap frame /\ route.ir_rename = sigma /\
  step_inst fuel C ret snap.ils_state = IntRet ir s' /\ ~frame.ipf_state.vs_halted ==>
  ?ml mj bb.
    lookup_block ml root.fn_blocks = SOME bb /\
    inline_parameter_boundary_path zipper e.ise_final e.ise_return 0 root
      (inline_path_rename zipper e.ise_return) 0 /\
    (?target. lookup_block (inline_path_rename zipper e.ise_return)
      root.fn_blocks = SOME target) /\
    exec_block tfuel Tctx bb (frame.ipf_state with vs_inst_idx := mj) =
      OK (jump_to (inline_path_rename zipper e.ise_return)
        (FOLDL (\s (x,w). update_var x w s) frame.ipf_state
          (ZIP (MAP prename call.inst_outputs,ir.iret_values)))) /\
    s' = snap.ils_state /\ LENGTH call.inst_outputs = LENGTH ir.iret_values
Proof
  strip_tac >>
  `raw_return_user_arity ret = SOME (LENGTH call.inst_outputs)` by
    metis_tac[inline_selected_return_arity, MEM] >>
  drule_all inline_return_source >> strip_tac >>
  `eval_operands (MAP (inline_rename_operand sigma I) ops) frame.ipf_state =
     SOME ir.iret_values` by
    metis_tac[inline_selected_return_user_reads] >>
  drule_all inline_selected_return_namespace >> strip_tac >>
  `inliner_input_ok C /\ MEM child C.ctx_functions /\ MEM ret (fn_insts child)` by
    (conj_tac
     >- metis_tac[inline_annotated_origin_erasure, qualified_origin_erasure,
                 inliner_fn_origin_input_ok] >>
     conj_tac
     >- metis_tac[inline_annotated_origin_routed_leaf, inline_routed_leaf_source_member] >>
     gvs[get_instruction_def, AllCaseEqs(), fn_insts_def,
       unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM, MEM_EL]) >>
  drule_all inline_return_user_namespace >> strip_tac >>
  `!x v. MEM x (MAP prename call.inst_outputs) /\
      MEM (Var v) (MAP (inline_rename_operand sigma I) ops) ==> x <> v` by
    (rpt gen_tac >> strip_tac >> gvs[MEM_MAP] >>
     rename1 `Var v = inline_rename_operand sigma I op` >>
     Cases_on `op` >>
     gvs[functionInlinerFrameTheory.inline_rename_operand_def, EVERY_MEM] >>
     metis_tac[]) >>
  drule_all inline_selected_return_layout >> strip_tac >>
  `MAPi (\k op. (ASSIGN,[inline_rename_operand sigma I op],
        [EL k (MAP prename call.inst_outputs)])) ops =
   MAPi (\k op. (ASSIGN,[op],[EL k (MAP prename call.inst_outputs)]))
     (MAP (inline_rename_operand sigma I) ops)` by
    (irule LIST_EQ >> simp[EL_MAPi, EL_MAP]) >>
  qpat_x_assum `MAPi _ ops = MAPi _ _`
    (fn th => qpat_x_assum `inline_adapter_interval _ _ _ _ _`
       (assume_tac o REWRITE_RULE [th])) >>
  drule inline_return_interval_execute >>
  disch_then (qspecl_then [`ir.iret_values`, `frame.ipf_state`, `tfuel`, `Tctx`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qexistsl [`ml`, `mj`, `bb`] >>
  simp[] >> metis_tac[eval_operands_length]
QED

Theorem inline_return_original_source_resume:
  MEM ret.inst_opcode [RET; RETFMP] /\ ret.inst_operands = ops ++ [pc] /\
  raw_return_user_arity ret = SOME (LENGTH call.inst_outputs) /\
  step_inst fuel C ret s = IntRet ir s' ==>
  ?caller'. bind_outputs call.inst_outputs ir.iret_values saved = SOME caller' /\
    caller' = FOLDL (\s (x,w). update_var x w s) saved
      (ZIP (call.inst_outputs,ir.iret_values)) /\
    bind_outputs call.inst_outputs ir.iret_values
      (adopt_return_fmp ir (merge_callee_state saved s')) =
      SOME (adopt_return_fmp ir (merge_callee_state caller' s')) /\
    (adopt_return_fmp ir (merge_callee_state caller' s')).vs_fmp =
      (if ret.inst_opcode = RETFMP then s'.vs_fmp else saved.vs_fmp)
Proof
  strip_tac >> drule_all inline_return_source >> strip_tac >>
  `LENGTH ir.iret_values = LENGTH call.inst_outputs` by
    metis_tac[eval_operands_length] >>
  `?caller'. bind_outputs call.inst_outputs ir.iret_values saved = SOME caller'` by
    simp[bind_outputs_def] >>
  qexists `caller'` >>
  simp[inline_return_bind_merge] >>
  `caller'.vs_fmp = saved.vs_fmp` by
    metis_tac[functionInlinerFmpTheory.inline_bind_outputs_fmp] >>
  conj_tac >- gvs[bind_outputs_def] >>
  Cases_on `ir.iret_adopt_fmp` >>
  gvs[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem inline_selected_return_execute:
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j call (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert p proute.ir_rename fn /\
  inline_namespace_leaf_at cert q route.ir_rename child /\
  pa.ia_function = fn /\ ca.ia_function = child /\
  lookup_block rl child.fn_blocks = SOME rb /\ get_instruction rb ri = SOME ret /\
  MEM ret.inst_opcode [RET; RETFMP] /\ ret.inst_operands = ops ++ [pc] /\
  inline_tracked_snapshot child ca route snap frame /\
  step_inst fuel C ret snap.ils_state = IntRet ir s' /\ ~frame.ipf_state.vs_halted /\
  inline_owner_storage cert ((q,ca,route,snap)::(p,pa,proute,psnap)::rest) frame /\
  inline_parameter_saved_reads ((q,ca,route,snap)::(p,pa,proute,psnap)::rest) /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((q,ca,route,snap)::(p,pa,proute,psnap)::rest)) ==>
  ?ml mj bb caller'.
    let dests = MAP proute.ir_rename call.inst_outputs;
        writes = FOLDL (\s (x,w). update_var x w s) frame.ipf_state
          (ZIP (dests,ir.iret_values));
        target = jump_to (inline_path_rename zipper e.ise_return) writes;
        resumed = adopt_return_fmp ir (merge_callee_state caller' s');
        psnap' = psnap with <|ils_state := resumed;
          ils_defined := set call.inst_outputs UNION psnap.ils_defined|> in
    lookup_block ml root.fn_blocks = SOME bb /\
    (frame.ipf_state.vs_current_bb = ml /\ frame.ipf_state.vs_inst_idx = mj ==>
      exec_block tfuel Tctx bb frame.ipf_state = OK target) /\
    bind_outputs call.inst_outputs ir.iret_values psnap.ils_state = SOME caller' /\
    resumed.vs_fmp =
      (if ret.inst_opcode = RETFMP then s'.vs_fmp else psnap.ils_state.vs_fmp) /\
    inline_owner_storage cert ((p,pa,proute,psnap')::rest)
      (frame with ipf_state := target) /\
    inline_parameter_saved_reads ((p,pa,proute,psnap')::rest) /\
    inline_parameter_ancestry C cert root
      (inline_parameter_owners ((p,pa,proute,psnap')::rest)) /\
    target.vs_current_bb = inline_path_rename zipper e.ise_return /\
    target.vs_prev_bb = SOME frame.ipf_state.vs_current_bb /\ target.vs_inst_idx = 0 /\
    inline_parameter_boundary_path zipper e.ise_final e.ise_return 0 root
      (inline_path_rename zipper e.ise_return) 0 /\
    (?continuation. lookup_block (inline_path_rename zipper e.ise_return)
      root.fn_blocks = SOME continuation)
Proof
  strip_tac >>
  `route.ir_rename = route.ir_rename` by simp[] >>
  drule_all inline_selected_return_adapter_execute >>
  disch_then (qspecl_then [`tfuel`, `Tctx`] strip_assume_tac) >>
  `raw_return_user_arity ret = SOME (LENGTH call.inst_outputs)` by
    metis_tac[inline_selected_return_arity, MEM] >>
  drule_all inline_return_original_source_resume >>
  disch_then (qspec_then `psnap.ils_state` strip_assume_tac) >>
  drule_all inline_selected_return_namespace >> strip_tac >>
  `INJ proute.ir_rename (set call.inst_outputs UNION psnap.ils_defined) UNIV` by
    metis_tac[pred_setTheory.INJ_SUBSET, pred_setTheory.SUBSET_UNIV] >>
  `inline_owner_storage cert
    ((p,pa,proute,psnap with <|ils_state := caller';
      ils_defined := set call.inst_outputs UNION psnap.ils_defined|>)::rest)
    (frame with ipf_state := FOLDL (\s (x,w). update_var x w s) frame.ipf_state
      (ZIP (MAP proute.ir_rename call.inst_outputs,ir.iret_values)))` by
    metis_tac[inline_owner_storage_return_writes] >>
  drule_all inline_parameter_return_writes_auxiliary >> strip_tac >>
  qexistsl [`ml`, `mj`, `bb`, `caller'`] >> simp[LET_THM] >>
  conj_tac
  >- (strip_tac >>
      `frame.ipf_state with vs_inst_idx := mj = frame.ipf_state` by
        simp[venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `inline_owner_storage _ (_::_::_) _` kall_tac >>
      drule inline_owner_storage_projections >>
      disch_then (qspecl_then
        [`jump_to (inline_path_rename zipper e.ise_return)
           (FOLDL (\s (x,w). update_var x w s) frame.ipf_state
             (ZIP (MAP proute.ir_rename call.inst_outputs,ir.iret_values)))`,
         `adopt_return_fmp ir (merge_callee_state caller' s')`] mp_tac) >>
      Cases_on `ir.iret_adopt_fmp` >>
      simp[adopt_return_fmp_def, merge_callee_state_def, jump_to_def]) >>
  conj_tac
  >- (drule_all inline_parameter_lifecycle_pop >> strip_tac >>
      metis_tac[inline_parameter_lifecycle_head_replace]) >>
  conj_tac
  >- (drule_all inline_parameter_lifecycle_pop >> strip_tac >>
      gvs[inline_parameter_lifecycle_head_replace]) >>
  simp[jump_to_def, functionInlinerOperationalTheory.inline_writes_control]
QED
