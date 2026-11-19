Theory gasFocusCostLedger
Ancestors
  asmFinalizerPrefix asmFinalizerPrefixFrame codegenAsmProgOk codegenEntryRel
  codegenSymRel asmSplice blockSimHelpers frameJointTrace frameHistoryCfg
  frameOriginHistory frameJointTransition fnSimSpec rich_list
  asmOptimizer asmSem venomExecProps list

(* Compose the given durations and endpoints, without selecting any new edge. *)
Theorem ledger_steps_compose[local]:
  (!x. segment 0 x = ok x) /\
  (!m n x y z. segment m x = ok y /\ segment n y = ok z ==>
                segment (m + n) x = ok z) /\
  (!i. i < LENGTH costs ==>
       segment (EL i costs) (EL i (start::ends)) = ok (EL (SUC i) (start::ends))) ==>
  segment (SUM costs) start = ok (EL (LENGTH costs) (start::ends))
Proof
  strip_tac >>
  `!k. k <= LENGTH costs ==>
       segment (SUM (TAKE k costs)) start = ok (EL k (start::ends))` by
    (Induct >- simp[] >>
     strip_tac >>
     `k < LENGTH costs /\ k <= LENGTH costs` by decide_tac >>
     simp[TAKE_SUC_BY_TAKE, listTheory.SUM_SNOC] >>
     qpat_assum `!m n x y z. _` irule >> qexists `EL k (start::ends)` >>
     conj_tac >- (first_assum irule >> simp[]) >>
     qpat_assum `!i. i < LENGTH costs ==> _` (qspec_then `k` mp_tac) >> simp[]) >>
  first_x_assum (qspec_then `LENGTH costs` mp_tac) >> simp[]
QED

(* The bound is selected on the fixed run, not on any particular ledger. *)
Theorem ledger_run_budget[local]:
  generate_context_plan u.cu_context = SOME cpl /\
  codegen_assembly rpolicy u = SOME prog /\ unit_shape_ok u /\
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
  (fin = asm_opt_finalizer ==>
    codegen_ready u.cu_context /\ label_flow_ok u.cu_context /\ sym_unit_static_ok u) /\
  vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es0
    (entry_asm_state vs0 es0 with as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
  run_call es0 = SOME (result,final) /\ ~frame_resource_starved es0 result final ==>
  ?max_cost. !n ast.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n (entry_asm_state vs0 es0) = AsmOK ast /\
    (fin = asm_opt_finalizer ==>
      ?ss. sym_steps prog (asm_data_env prog vs0.vs_code) n
        (sym_init (entry_asm_state vs0 es0)) = SymOK ss) ==>
    n <= max_cost
Proof
  strip_tac >>
  `fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
  pop_assum (strip_assume_tac)
  >- (gvs[] >>
      `(entry_asm_state vs0 es0 with as_code := assemble prog ++ vs0.vs_data_section) =
       entry_asm_state vs0 es0` by simp[entry_asm_state_def] >>
      `asm_frame_prog_ok prog` by metis_tac[codegen_assembly_frame_prog_ok] >>
      `asm_frame_rel_tail [] prog vs0.vs_data_section es0 (entry_asm_state vs0 es0) es0`
        by metis_tac[] >>
      drule_all finalizer_frame_prefix_ready >> metis_tac[]) >>
  `codegen_ready u.cu_context /\ label_flow_ok u.cu_context /\ sym_unit_static_ok u`
    by metis_tac[] >>
  drule_all focus_finalizer_prefix_bridge >> metis_tac[]
QED

Theorem focus_exact_cost_ledger_bound:
  generate_context_plan u.cu_context = SOME cpl /\
  codegen_assembly rpolicy u = SOME prog /\ unit_shape_ok u /\
  EVERY wf_function u.cu_context.ctx_functions /\
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
  (fin = asm_opt_finalizer ==>
    codegen_ready u.cu_context /\ label_flow_ok u.cu_context /\ sym_unit_static_ok u) /\
  vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es0
    (entry_asm_state vs0 es0 with as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
  run_call es0 = SOME (result,final) /\ ~frame_resource_starved es0 result final ==>
  ?max_cost. !q0 evs qs q costs ats sts.
    !C. C = u.cu_context ==>
    !m. m = LENGTH evs ==>
    !Q. Q = q0::qs ==>
    !A. A = entry_asm_state vs0 es0 :: ats ==>
    !S. S = sym_init (entry_asm_state vs0 es0) :: sts ==>
    !asteps. asteps = asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog ==>
    !ssteps. ssteps = sym_steps prog (asm_data_env prog vs0.vs_code) ==>
    !rank. rank = (\v. case v of JointConfig stk PG G tn fn inst s oms om hs h =>
      case lookup_block s.vs_current_bb fn.fn_blocks of
        NONE => 0
      | SOME bb => LENGTH bb.bb_instructions - s.vs_inst_idx) ==>
    !R. R = SUM (MAP (\func. SUM (MAP (\bb. LENGTH bb.bb_instructions) func.fn_blocks))
                   C.ctx_functions) ==>
    joint_trace vs0 C q0 evs qs q /\
    LENGTH costs = m /\ LENGTH ats = m /\
    LIST_REL (\c pair. 0 < c \/ rank (SND pair) < rank (FST pair)) costs (ZIP (Q,qs)) /\
    (!i. i < m ==> asteps (EL i costs) (EL i A) = AsmOK (EL (SUC i) A)) /\
    (fin = asm_opt_finalizer ==>
      LENGTH sts = m /\
      !i. i < m ==> ssteps (EL i costs) (EL i S) = SymOK (EL (SUC i) S)) ==>
    asteps (SUM costs) (entry_asm_state vs0 es0) = AsmOK (EL m A) /\
    (fin = asm_opt_finalizer ==>
      ssteps (SUM costs) (sym_init (entry_asm_state vs0 es0)) = SymOK (EL m S)) /\
    EVERY (\v. rank v <= R) Q /\ LENGTH qs = m /\
    LENGTH costs = m /\ LENGTH ats = m /\
    LIST_REL (\c pair. 0 < c \/ rank (SND pair) < rank (FST pair)) costs (ZIP (Q,qs)) /\
    SUM costs <= max_cost
Proof
  CONV_TAC (TOP_DEPTH_CONV (Unwind.UNWIND_FORALL_CONV)) >>
  strip_tac >> drule_all ledger_run_budget >>
  disch_then (qx_choose_then `B` assume_tac) >> qexists `B` >>
  rewrite_tac[LET_THM] >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  `LENGTH qs = LENGTH evs` by metis_tac[joint_trace_def, joint_chain_length] >>
  conj_asm1_tac
  >- (qpat_assum `LENGTH costs = LENGTH evs` (SUBST1_TAC o SYM) >>
      irule ledger_steps_compose >> simp[asm_steps_def, asm_steps_compose_ok] >> metis_tac[]) >>
  conj_asm1_tac
  >- (strip_tac >> qpat_assum `LENGTH costs = LENGTH evs` (SUBST1_TAC o SYM) >>
      irule ledger_steps_compose >> simp[sym_steps_def, sym_steps_compose] >> metis_tac[]) >>
  conj_tac
  >- (once_rewrite_tac[EVERY_EL] >> BETA_TAC >> qx_gen_tac `i` >> strip_tac >>
      `joint_config_reachable vs0 u.cu_context (EL i (q0::qs))` by
        (irule joint_trace_reachable_at >> qexistsl [`evs`,`q`] >> fs[]) >>
      Cases_on `EL i (q0::qs)` >> gvs[] >>
      rename1 `JointConfig stk PG G tn fn inst s oms om hs h` >>
      `MEM fn u.cu_context.ctx_functions` by
        (fs[joint_config_reachable_def] >>
         drule joint_origin_history_projection >> strip_tac >>
         metis_tac[frame_history_cfg_invariant]) >>
      Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
      rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
      `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
      `LENGTH bb.bb_instructions <= context_inst_count u.cu_context` by
        metis_tac[context_inst_count_block] >>
      fs[context_inst_count_def] >> decide_tac) >>
  simp[] >>
  qpat_assum `!n ast. _ ==> n <= B` irule >>
  qexists `EL (LENGTH evs) (entry_asm_state vs0 es0::ats)` >> simp[] >> metis_tac[]
QED
