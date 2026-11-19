Theory requestCutFrontierCases
Ancestors
  requestCutCfgTerminal requestCutStoppedGas requestCutForwardTerminal
  requestCutFrameReady requestCutInvokeReady o1ContractCfgNormJointCursors
  fnFramePrefixDriver fnFrameSymbolicPrefix frameJointTransition codegenEntryRel
  asmFrameRel asmOptimizer asmDataEnv asmSem asmSymSem contextCodegenRel
  o1PassContract unitShapeDefs venomExecSemantics venomState venomInst
  concretizeLayoutLocalReturn venomWf vfmExecution finite_map list

(* The remaining stops need either the request-bounded C7 observation or
   static-abort terminal replay. GAS, INVOKE and primitive errors have
   direct readiness proofs at the selected C9 frame. *)
Theorem request_cut_frontier_cases:
  fin IN accepted_finalizers /\ fin rp prog = SOME prog' /\
  asm_frame_prog_ok prog' /\ vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es
    (entry_asm_state vs0 es with as_code := assemble prog' ++ vs0.vs_data_section) es /\
  run_call es = SOME (result,final) /\ ~frame_resource_starved es result final /\
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rp unit = SOME prog /\ unit_shape_ok unit /\
  codegen_ready unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es) /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog n (entry_asm_state vs0 es) = AsmOK ast /\
  q8 = JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8 /\
  q9 = JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9 /\
  cfg_norm_joint_cursors C8 unit.cu_context (schedules,(rounds,cells),saved) q8 q9 /\
  (fin = K SOME ==> normal_frame_plan rp unit cpl prog
    (vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
               vs_return_pc_token := 0w; vs_inst_idx := 0|>) es q9 ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps prog (asm_data_env prog vs0.vs_code) n
      (sym_init (entry_asm_state vs0 es)) = SymOK ss /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rp unit cpl prog
      vs0 es q9 ast ss /\ focus_s7_symbolic_context unit prog) /\
  (inst9.inst_opcode <> PHI ==>
    !l. MEM (Label l) (compute_operands inst9) ==> IS_SOME (FLOOKUP s9.vs_labels l)) /\
  raw_variant fmp vs vs0 /\ raw_reachable vs C fn inst s /\
  inst.inst_opcode <> INVOKE /\ LENGTH s.vs_requests = k /\
  step_inst fuel C inst s = OK post /\ k < LENGTH post.vs_requests /\
  ((inst8.inst_opcode <> INVOKE /\ ?r. step_inst m C8 inst8 s8 = r /\
    ((?u. r = OK u /\ u.vs_halted) \/ (?u. r = Halt u) \/ (?a u. r = Abort a u))) \/
   in_revert_forward fn9 s9 \/
   (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode /\
    (~source_memory_reads_disjoint cpl inst9 s9 \/
     ~context_source_memory_writes_disjoint cpl inst9 s9)) \/
   (fin = asm_opt_finalizer /\
    ?dst x sz src off. inst9.inst_opcode = CODECOPY /\
      inst9.inst_operands = [dst; Var x; sz] /\ code_end_var fn9 x /\
      eval_operand (Var x) s9 = SOME src /\
      FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off /\
      ~(w2n (src - n2w off) < dimword (:256) DIV 2)) \/
   (inst8.inst_opcode = GAS /\ inst9.inst_opcode = GAS /\ s8.vs_gas_readings = []) \/
   (inst9.inst_opcode = INVOKE /\
    ~(?name ops callee args ent. decode_invoke inst9 = SOME (name,ops) /\
      lookup_function name unit.cu_context.ctx_functions = SOME callee /\
      eval_operands ops s9 = SOME args /\ setup_callee callee args s9 = SOME ent)) \/
   (inst9.inst_opcode <> INVOKE /\ ?err. step_inst 0 unit.cu_context inst9 s9 = Error err)) ==>
  k < LENGTH s9.vs_requests \/
  (~in_revert_forward fn9 s9 /\
   ((inst9 = inst8 /\ inst8.inst_opcode <> INVOKE /\
     ?post9. step_inst 0 unit.cu_context inst9 s9 = Halt post9 \/
             ?a. step_inst 0 unit.cu_context inst9 s9 = Abort a post9) \/
    (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode /\
     (~source_memory_reads_disjoint cpl inst9 s9 \/
      ~context_source_memory_writes_disjoint cpl inst9 s9)) \/
    (fin = asm_opt_finalizer /\
     ?dst x sz src off. inst9.inst_opcode = CODECOPY /\
       inst9.inst_operands = [dst; Var x; sz] /\ code_end_var fn9 x /\
       eval_operand (Var x) s9 = SOME src /\
       FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off /\
       ~(w2n (src - n2w off) < dimword (:256) DIV 2))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `q8 = _` SUBST_ALL_TAC >>
  qpat_x_assum `q9 = _` SUBST_ALL_TAC >>
  drule cfg_norm_joint_cursor_supply >> strip_tac >>
  Cases_on `in_revert_forward fn9 s9`
  >- (`~is_param_opcode inst9.inst_opcode` by
        (`ALL_DISTINCT (fn_labels fn9)` by fs[wf_function_def] >>
         `MEM inst9.inst_opcode [RETURNDATACOPY; REVERT]` by
           metis_tac[active_inst_not_revert_forward] >>
         fs[is_param_opcode_def]) >>
      mp_tac (Q.INST [`q9` |-> `JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9`,
        `stk` |-> `stk9`, `PG` |-> `PG9`, `G` |-> `G9`, `tn` |-> `tn9`, `oms` |-> `oms9`,
        `om` |-> `om9`, `hs` |-> `hs9`, `hist` |-> `hist9`,
        `q8` |-> `JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8`,
        `planner_base` |-> `vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
                                     vs_return_pc_token := 0w; vs_inst_idx := 0|>`]
        request_cut_stopped_forward_crossed) >>
      (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >> simp[]) >>
  simp[] >>
  qpat_x_assum `(inst8.inst_opcode <> INVOKE /\ _) \/ _`
    (DISJ_CASES_THEN2 (CONJUNCTS_THEN2 assume_tac
      (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac assume_tac))) assume_tac)
  >- (drule_all request_cut_cfg_terminal_step >> strip_tac >> simp[] >> metis_tac[]) >>
  qpat_x_assum `in_revert_forward fn9 s9 \/ _`
    (DISJ_CASES_THEN assume_tac) >- fs[] >>
  qpat_x_assum `(inst9.inst_opcode <> INVOKE /\ ~is_terminator _ /\ _) \/ _`
    (DISJ_CASES_THEN assume_tac)
  >- (disj2_tac >> disj2_tac >> disj1_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `(fin = asm_opt_finalizer /\ _) \/ _`
    (DISJ_CASES_THEN assume_tac)
  >- (disj2_tac >> disj2_tac >> disj2_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `(inst8.inst_opcode = GAS /\ _) \/ _`
    (DISJ_CASES_THEN2 strip_assume_tac assume_tac)
  >- (mp_tac (Q.INST
        [`q9` |-> `JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9`,
         `current` |-> `(rounds,cells)`] request_cut_stopped_gas_available) >>
      (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >> fs[]) >>
  qpat_x_assum `(inst9.inst_opcode = INVOKE /\ _) \/ _`
    (DISJ_CASES_THEN2 (CONJUNCTS_THEN assume_tac) strip_assume_tac)
  >- (drule_all request_cut_stopped_invoke_ready >> simp[]) >>
  mp_tac (Q.INST
    [`q8` |-> `JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8`,
     `stk` |-> `stk9`, `PG` |-> `PG9`, `G` |-> `G9`, `tn` |-> `tn9`,
     `fn` |-> `fn9`, `inst` |-> `inst9`, `s` |-> `s9`,
     `oms` |-> `oms9`, `om` |-> `om9`, `hs` |-> `hs9`, `h` |-> `hist9`,
     `fuel` |-> `0`, `err` |-> `err`] request_cut_stopped_noninvoke_ready) >>
  (impl_tac
   >- (simp[] >> fs[accepted_finalizers_def] >> metis_tac[])) >>
  simp[]
QED
