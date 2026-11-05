(*
 * The entry block's first steps, for fnEntryStep$fn_entry_block_step.
 *
 * TOP-LEVEL:
 *   entry_run_block        - the entry block has no PHIs, so run_block is
 *                            exec_block from index 0
 *   entry_prefix_frame_sim - entry_params_frame_sim, with the facts about
 *                            the state after the parameters that
 *                            fnBlockBody$block_body_frame_sim also needs
 *)

Theory fnEntryParams
Ancestors
  fnFrameBoundary fnFrameBoundaryEntryParams frameRel contextCodegenRel
  stackPlanGen stackPlanTypes venomExecSemantics venomState venomInst
  venomWf livenessDefs dfgDefs list

(* block_entries_ready: the entry block has no PHIs, so eval_phis leaves
   the state alone and the PHI prefix is empty. *)
Theorem entry_run_block:
  !fuel ctx fn vs.
    codegen_ready_fn fn ==>
    run_block fuel ctx (HD fn.fn_blocks) vs =
    exec_block fuel ctx (HD fn.fn_blocks) (vs with vs_inst_idx := 0)
Proof
  rw[codegen_ready_fn_def] >>
  `fn.fn_blocks <> []` by gvs[wf_function_def, fn_has_entry_def] >>
  gvs[block_entries_ready_def, entry_block_def, listTheory.NULL_EQ] >>
  simp[run_block_def] >>
  Cases_on `(HD fn.fn_blocks).bb_instructions` >>
  gvs[eval_phis_def, phi_prefix_length_def, collect_phis_def] >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >> rw[] >>
  simp[eval_phis_def, phi_prefix_length_def]
QED

Theorem entry_prefix_fields[local]:
  (entry_bind_pairs (entry_param_pairs s (TAKE k insts)) s
     with vs_inst_idx := k).vs_current_bb = s.vs_current_bb /\
  (entry_bind_pairs (entry_param_pairs s (TAKE k insts)) s
     with vs_inst_idx := k).vs_labels = s.vs_labels /\
  (entry_bind_pairs (entry_param_pairs s (TAKE k insts)) s
     with vs_inst_idx := k).vs_call_ctx = s.vs_call_ctx
Proof
  simp[entry_bind_pairs_normal]
QED

Theorem entry_prefix_zero[local]:
  (entry_bind_pairs (entry_param_pairs s (TAKE 0 insts)) s
     with vs_inst_idx := 0) = (s with vs_inst_idx := 0)
Proof
  simp[entry_param_pairs_def]
QED

Theorem entry_prefix_step[local]:
  EVERY (entry_param_shape s) insts /\ k < LENGTH insts ==>
  step_inst fuel ctx (EL k insts)
    (entry_bind_pairs (entry_param_pairs s (TAKE k insts)) s
       with vs_inst_idx := k) =
  OK (entry_bind_pairs (entry_param_pairs s (TAKE (SUC k) insts)) s
       with vs_inst_idx := k)
Proof
  strip_tac >>
  `entry_param_shape
     (entry_bind_pairs (entry_param_pairs s (TAKE k insts)) s
       with vs_inst_idx := k) (EL k insts)` by
    (simp[entry_param_shape_def, entry_bind_pairs_normal] >>
     metis_tac[EVERY_EL, entry_param_shape_def]) >>
  drule entry_param_step >>
  disch_then (qspecl_then [`fuel`, `ctx`] SUBST1_TAC) >>
  simp[rich_listTheory.TAKE_SUC_BY_TAKE, SNOC_APPEND,
       entry_param_pairs_def, entry_bind_pairs_normal,
       rich_listTheory.FOLDL_APPEND]
QED

Theorem entry_prefix_enters[local]:
  !fn cp s st ra rest. codegen_ready_fn fn /\ fn_entry_state_rel cp fn s st ra rest ==>
  enters_block fn s (s with vs_inst_idx := 0)
Proof
  rpt gen_tac >> strip_tac >>
  `fn.fn_blocks <> []` by
    gvs[codegen_ready_fn_def, wf_function_def, fn_has_entry_def] >>
  `NULL (collect_phis (HD fn.fn_blocks).bb_instructions)` by
    gvs[codegen_ready_fn_def, block_entries_ready_def, entry_block_def,
        listTheory.NULL_EQ] >>
  simp[enters_block_def] >>
  qexistsl [`HD fn.fn_blocks`, `s`] >>
  conj_tac
  >- (gvs[fn_entry_state_rel_def] >> Cases_on `fn.fn_blocks` >>
      gvs[lookup_block_def, FIND_def, INDEX_FIND_def]) >>
  Cases_on `(HD fn.fn_blocks).bb_instructions` >>
  gvs[eval_phis_def, phi_prefix_length_def, collect_phis_def] >>
  rename1 `NULL (if inst.inst_opcode = PHI then _ else _)` >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[]
QED

Theorem entry_prefix_active[local]:
  fn.fn_blocks <> [] /\
  s.vs_current_bb = (HD fn.fn_blocks).bb_label /\
  k < LENGTH (get_params (HD fn.fn_blocks).bb_instructions) ==>
  active_inst fn (EL k (get_params (HD fn.fn_blocks).bb_instructions))
    (entry_bind_pairs
       (entry_param_pairs s (TAKE k (get_params (HD fn.fn_blocks).bb_instructions))) s
       with vs_inst_idx := k)
Proof
  strip_tac >>
  qspec_then `(HD fn.fn_blocks).bb_instructions` strip_assume_tac get_params_suffix >>
  simp[active_inst_def, entry_bind_pairs_normal] >>
  qexists `HD fn.fn_blocks` >>
  conj_tac >- (Cases_on `fn.fn_blocks` >> gvs[]) >>
  conj_tac >- (gvs[] >> decide_tac) >>
  conj_tac
  >- (qpat_x_assum `_ = _ ++ suffix`
        (fn th => once_rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `_ = _ ++ suffix`
    (fn th => simp[SimpLHS, Once th, EL_APPEND_EQN])
QED

(* entry_params_frame_sim (same premises, plus the Inv premises and the
   dfg), with four more facts about the state vs_p after the parameter
   prefix, which block_body_frame_sim asks for at the entry block:
   - the parameter instructions leave the current block, the labels and
     the call context alone;
   - Inv holds at vs_p's instruction: fn_entry_inv gives it at the first
     instruction, and reachability_closed carries it over each parameter
     instruction, none a terminator;
   - the alias premise holds at ps1: ps1's stack and spill map hold only
     the parameters' outputs (from the empty initial stack), defined by
     PARAM / FMP_PARAM / RETPC_PARAM, not ASSIGN, so normalize_operand
     returns them unchanged. *)
Theorem entry_prefix_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg fn ch growth spill_base lbl_ctr ps0
   param_ops ps1 r vs as ra rest Inv.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr /\
    prepare_params_plan liveness fn ps0 = (param_ops, ps1) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= spill_base /\
    ps1.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)) /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cp fn vs as ra rest /\
    fn_entry_inv Inv ctx fn vs /\ reachability_closed Inv ctx /\
    asm_block_at prog as.as_pc
      (execute_plan cp.cp_initial_fmp
         (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))
    ==>
    ?n as' vs_p.
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc +
        LENGTH (execute_plan cp.cp_initial_fmp
                  (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
      exec_block fuel ctx (HD fn.fn_blocks) (vs with vs_inst_idx := 0) =
        exec_block fuel ctx (HD fn.fn_blocks) vs_p /\
      vs_p.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions) /\
      fn_frame_inv ctx cp lo fn ra rest as.as_memory ps1 vs_p as' /\
      vs_p.vs_current_bb = vs.vs_current_bb /\
      vs_p.vs_labels = vs.vs_labels /\
      vs_p.vs_call_ctx = vs.vs_call_ctx /\
      (!inst. active_inst fn inst vs_p ==> Inv ctx fn inst vs_p) /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra vs_p) lo at =
         operand_val (frame_view fn ra vs_p) lo (normalize_operand dfg [] at))
Proof
  cheat
QED
