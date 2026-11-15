(* Symbolic annotations of the finite source-frame packets. *)
Theory fnFrameSymbolicPrefix
Ancestors
  fnFramePrefixDriver fnFramePrefix fnFramePrefixEntry fnFramePrefixStack
  codegenLabelDisciplined codegenEntrySim codegenEntryRel codegenSymRel
  symFrameBoundary symFrameInst symFrameInvoke symFrameControl
  symBlockBody symFnStep fnBlockStepHelpers stepWriteFootprintBase
  fnEntryPlan fnEntryStep fnBlockBodyHelpers stackOpSim fnFrameBoundaryEntryParams fnEntryParams
  asmDataEnv asmSymBridge asmSymSem asmSem
  fnBlockBodyClasses fnBlockBodySteps fnBlockBody venomWf fnFrameDeepJnz
  fnFrameBoundaryInvoke fnFrameBoundaryGenRet frameRel contextCodegenRel
  stackPlanTypes stackPlanGen planExec unitShapeDefs
  frameJointTrace frameJointTransition frameOriginHistory
  venomInstProps venomExecSemantics venomState venomInst fcgDefs
  list rich_list arithmetic finite_map

Definition active_frame_symbolic_plan_def:
  active_frame_symbolic_plan env rpolicy unit cpl prog fn s a ra rest mem0 ret srest labs0 ss <=>
    ?i r liveness dfg cfg ch growth spill_base lbl_ctr fn_ops ps_end
     bb ps_l h promised ps_dfs block_ops ps_dfs_after ps_after prefix_ops
     rest_ops k ps pc0 pc_ret.
      body_plan_inv rpolicy unit cpl prog unit.cu_context
        (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        i fn r liveness dfg cfg ch growth spill_base lbl_ctr fn_ops ps_end
        bb ps_l h promised ps_dfs block_ops ps_dfs_after ps_after prefix_ops
        rest_ops k ps pc0 s a ra pc_ret rest mem0 /\
      sym_frame_inv prog env unit.cu_context cpl fn ret srest labs0 ps a ss
End

Inductive frame_stack_symbolic_plan:
[~entry:]
  (!env rpolicy unit cpl prog vs0 es0 root others lbl.
    codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
    unit.cu_context.ctx_functions = root :: others /\
    unit.cu_context.ctx_entry = SOME root.fn_name /\
    fn_entry_label root = SOME lbl /\
    fn_entry_state_rel cpl root
      (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
      (entry_asm_state vs0 es0) 0w [] ==>
    frame_stack_symbolic_plan env rpolicy unit cpl prog vs0 es0 [] root
      (entry_asm_state vs0 es0) 0w [] (entry_asm_state vs0 es0).as_memory
      (sym_init (entry_asm_state vs0 es0)) "" [] FEMPTY)
[~call:]
  (!env rpolicy unit cpl prog vs0 es0 stk fn caller_entry
    i r liveness dfg cfg ch growth spill_base lbl_ctr fn_ops ps_end
    bb ps_l h promised ps_dfs block_ops ps_dfs_after ps_after prefix_ops
    rest_ops k ps pc0 vs ast ra pc_ret rest mem0
    f inst nm arg_ops callee args cvs ops ps' rest'
    iops prepared rops arranged ret_lbl ret_off call_post mid saved cas pc
    sentry ret srest labs0 ss sms scas saved_sym.
    frame_stack_symbolic_plan env rpolicy unit cpl prog vs0 es0 stk fn caller_entry
      ra rest mem0 sentry ret srest labs0 /\
    body_plan_inv rpolicy unit cpl prog unit.cu_context
      (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      i fn r liveness dfg cfg ch growth spill_base lbl_ctr fn_ops ps_end
      bb ps_l h promised ps_dfs block_ops ps_dfs_after ps_after prefix_ops
      rest_ops k ps pc0 vs ast ra pc_ret rest mem0 /\
    f.cf_fn = fn /\ f.cf_inst = inst /\ f.cf_state = vs /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
    lookup_function nm unit.cu_context.ctx_functions = SOME callee /\
    eval_operands arg_ops vs = SOME args /\ setup_callee callee args vs = SOME cvs /\
    (vs.vs_call_ctx, vs.vs_tx_ctx, vs.vs_block_ctx, vs.vs_code, vs.vs_prev_hashes) =
      (vs0.vs_call_ctx, vs0.vs_tx_ctx, vs0.vs_block_ctx,
       vs0.vs_code, vs0.vs_prev_hashes) /\
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\ rest_ops = ops ++ rest' /\
    emit_input_plan INVOKE (compute_operands inst)
      (live_vars_at liveness bb.bb_label (k + 1)) ps = (iops, prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops, arranged) /\
    ops = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ call_post /\
    fn_frame_inv unit.cu_context cpl (SND (compute_label_offsets prog))
      fn ra rest mem0 arranged vs mid /\
    plan_state_residual_wf_marked spill_base (compute_operands inst)
      (LENGTH (compute_operands inst)) arranged /\
    arranged.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack ++
      compute_operands inst /\
    mid.as_stack = REVERSE args ++ saved ++ rest /\
    LENGTH args = LENGTH (compute_operands inst) /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog (LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops))) ast = AsmOK mid /\
    asm_block_at prog mid.as_pc (execute_plan cpl.cp_initial_fmp
      ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ call_post)) /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog 3 mid = AsmOK cas /\
    cas = mid with <| as_stack := n2w ret_off :: mid.as_stack; as_pc := pc |> /\
    fn_entry_state_rel cpl callee cvs cas (n2w ret_off) (saved ++ rest) /\
    FLOOKUP (build_offset_to_pc prog) (w2n ((n2w ret_off):bytes32)) =
      SOME (ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3) /\
    sym_frame_inv prog env unit.cu_context cpl fn ret srest labs0 ps ast ss /\
    sym_frame_inv prog env unit.cu_context cpl fn ret srest labs0 arranged mid sms /\
    sym_steps prog env (LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops))) ss = SymOK sms /\
    sym_steps prog env 3 sms = SymOK scas /\
    asm_sym_rel prog env cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack)) saved_sym /\
    scas.sym_mem_labels = sms.sym_mem_labels /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cpl b) /\
    MEM (AsmLabel ret_lbl) prog ==>
    frame_stack_symbolic_plan env rpolicy unit cpl prog vs0 es0 (f::stk) callee cas
      (n2w ret_off) (saved ++ rest) cas.as_memory
      scas ret_lbl (saved_sym ++ srest) scas.sym_mem_labels)
End

Definition entry_frame_symbolic_plan_def:
  entry_frame_symbolic_plan env rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0
    ret srest labs0 ss <=>
  entry_frame_plan rpolicy unit cpl prog fn entry s ast ra pc_ret rest mem0 /\
  asm_sym_rel prog env ast ss /\
  ss.sym_stack = (if fn_has_retpc fn then [Lab ret 0] else []) ++
    MAP Val (REVERSE entry.vs_params) ++ srest /\
  labs0 = ss.sym_mem_labels /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cpl b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) prog)
End

Definition normal_frame_symbolic_plan_def:
  normal_frame_symbolic_plan env rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast ss <=>
  ?saved ra rest mem0 sentry ret srest labs0.
    frame_stack_symbolic_plan env rpolicy unit cpl prog vs0 es0 stk fn saved
      ra rest mem0 sentry ret srest labs0 /\
    (active_frame_symbolic_plan env rpolicy unit cpl prog fn s ast ra rest mem0
       ret srest labs0 ss \/
     ?entry pc_ret.
       entry_frame_symbolic_plan env rpolicy unit cpl prog fn entry s ast
         ra pc_ret rest mem0 ret srest labs0 ss)
End

Definition focus_s7_symbolic_guard_def:
  focus_s7_symbolic_guard prog cpl fn inst s <=>
  (inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode ==>
    source_memory_reads_disjoint cpl inst s /\
    context_source_memory_writes_disjoint cpl inst s) /\
  (!dst x sz src off.
    inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; Var x; sz] /\
    code_end_var fn x /\ eval_operand (Var x) s = SOME src /\
    FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off ==>
      w2n (src - n2w off) < dimword (:256) DIV 2)
End

Definition focus_s7_symbolic_context_def:
  focus_s7_symbolic_context unit prog <=>
    label_flow_ok unit.cu_context /\ sym_unit_static_ok unit /\
    asm_static_wf prog
End

Theorem joint_trace_paired_prefix:
  !j.
  joint_trace vs0 ctx q0 evs qs qlast /\ j <= LENGTH evs /\
  R q0 a0 ss0 /\
  (!i a ss. i < j /\ R (EL i (q0::qs)) a ss ==>
    ?n a1 ss1.
      asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        prog n a = AsmOK a1 /\
      sym_steps prog env n ss = SymOK ss1 /\
      R (EL (SUC i) (q0::qs)) a1 ss1) ==>
  ?n a ss.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n a0 = AsmOK a /\
    sym_steps prog env n ss0 = SymOK ss /\
    R (EL j (q0::qs)) a ss
Proof
  Induct_on `j`
  >- (rpt strip_tac >> qexistsl [`0`, `a0`, `ss0`] >>
      simp[asm_steps_def, asmSpliceTheory.sym_steps_def])
  >> rpt strip_tac
  >> `?n a ss.
        asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
          prog n a0 = AsmOK a /\
        sym_steps prog env n ss0 = SymOK ss /\
        R (EL j (q0::qs)) a ss` by
       (first_x_assum irule >> simp[])
  >> qpat_x_assum `!i a ss. _` (qspecl_then [`j`, `a`, `ss`] mp_tac)
  >> simp[] >> strip_tac
  >> qexistsl [`n + n'`, `a1`, `ss1`]
  >> metis_tac[blockSimHelpersTheory.asm_steps_compose_ok, sym_steps_compose]
QED

Theorem normal_frame_symbolic_initial:
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  codegen_context_obligations (\_ _ _ _. F) unit.cu_context cpl /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  joint_initial vs0 unit.cu_context q /\ focus_s7_symbolic_context unit prog /\
  env = asm_data_env prog vs0.vs_code ==>
  normal_frame_symbolic_plan env rpolicy unit cpl prog vs0 es0 q
    (entry_asm_state vs0 es0) (sym_init (entry_asm_state vs0 es0))
Proof
  strip_tac >>
  `?root others. unit.cu_context.ctx_functions = root::others /\
     unit.cu_context.ctx_entry = SOME root.fn_name /\
     get_params (HD root.fn_blocks).bb_instructions = []` by
    gvs[unit_shape_ok_def, entry_fn_first_def] >>
  `codegen_ready_fn root` by
    fs[codegen_context_obligations_def, codegen_ready_def] >>
  `?lbl. fn_entry_label root = SOME lbl` by
    (Cases_on `root.fn_blocks` >>
     fs[codegen_ready_fn_def, venomWfTheory.wf_function_def,
        venomWfTheory.fn_has_entry_def, fn_entry_label_def, entry_block_def]) >>
  `fn_entry_state_rel cpl root
    (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
    (entry_asm_state vs0 es0) 0w []` by
    metis_tac[codegen_asm_entry_fn_state_rel] >>
  `0 < LENGTH cpl.cp_regions` by
    metis_tac[fnPlanPlaceFnRegionTheory.context_region_leading_label,
      LENGTH, prim_recTheory.LESS_0, EL] >>
  `?r rs. cpl.cp_regions = r::rs` by
    (Cases_on `cpl.cp_regions` >> fs[]) >>
  `MEM root.fn_name (fcg_analyze unit.cu_context).fcg_reachable` by
    (qspecl_then [`unit.cu_context`, `root.fn_name`, `root.fn_name`] mp_tac
      fcgAnalysisPropsTheory.fcg_analyze_reachable_complete >>
     simp[fcg_is_reachable_def, fcg_path_def, ctx_fn_names_def] >>
     fs[codegen_context_obligations_def]) >>
  `asm_block_at prog 0 (execute_plan cpl.cp_initial_fmp r.sr_plan)` by
    metis_tac[codegen_assembly_first_region] >>
  `!l. FLOOKUP vs0.vs_labels l =
    OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l)` by
    fs[codegen_asm_entry_rel_def] >>
  qabbrev_tac `start = vs0 with
    <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>` >>
  `entry_frame_plan rpolicy unit cpl prog root start start
    (entry_asm_state vs0 es0) 0w 0 [] (entry_asm_state vs0 es0).as_memory` by
    (qsuff_tac `entry_frame_plan rpolicy unit cpl prog root start
       (start with vs_inst_idx := 0) (entry_asm_state vs0 es0) 0w 0 []
       (entry_asm_state vs0 es0).as_memory`
     >- simp[Abbr `start`] >>
     irule entry_frame_plan_start >>
     simp[Abbr `start`, entry_asm_state_def, fn_has_retpc_def] >>
     qexists_tac `0` >> simp[]) >>
  `asm_sym_rel prog env (entry_asm_state vs0 es0)
      (sym_init (entry_asm_state vs0 es0)) /\
   (sym_init (entry_asm_state vs0 es0)).sym_stack = [] /\
   (sym_init (entry_asm_state vs0 es0)).sym_mem_labels = FEMPTY` by
    (irule codegen_asm_entry_sym_init >>
     qexistsl_tac [`cpl`, `vs0`] >> simp[asm_data_env_ok_asm_data_env]) >>
  qpat_x_assum `joint_initial _ _ _` mp_tac >>
  simp[Once joint_initial_cases] >> rpt strip_tac >>
  gvs[lookup_function_def, FIND_thm] >>
  `enters_block fn start (start with vs_inst_idx := 0)` by
    metis_tac[fnEntryParamsTheory.entry_prefix_enters] >>
  `s1 = start` by gvs[enters_block_def, Abbr `start`] >>
  simp[normal_frame_symbolic_plan_def] >>
  qexistsl_tac [`entry_asm_state vs0 es0`, `0w`, `[]`,
    `(entry_asm_state vs0 es0).as_memory`,
    `sym_init (entry_asm_state vs0 es0)`, `""`, `[]`, `FEMPTY`] >>
  conj_tac
  >- (irule frame_stack_symbolic_plan_entry >>
      simp[] >> qexists_tac `lbl` >> fs[Abbr `start`]) >>
  disj2_tac >> qexistsl_tac [`start`, `0`] >>
  simp[entry_frame_symbolic_plan_def, fn_has_retpc_def, Abbr `start`,
       codegen_asm_entry_rel_def] >>
  fs[codegen_asm_entry_rel_def]
QED

Theorem body_plan_symbolic_jnz_step:
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = JNZ /\ step_inst fuel ctx inst vs = OK vs1 /\
    focus_s7_symbolic_context unit prog /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
    ?target n as1 off ss1.
      0 < n /\
      vs1 = jump_to target vs /\ MEM target (get_successors inst) /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
      (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
         operand_val (frame_view fn ra vs1) lo at =
         operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
      FLOOKUP lo target = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc /\
      sym_steps prog env n ss = SymOK ss1 /\
      sym_frame_inv prog env ctx cpl fn ret srest labs0 ps_after as1 ss1
Proof
  strip_tac >>
  `!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
     operand_val (frame_view fn ra vs1) lo at =
     operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)` by
    (drule_all body_plan_jnz_step >> strip_tac >> first_assum ACCEPT_TAC) >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule body_plan_inv_equiv >> disch_then drule >> disch_then drule >> strip_tac >>
  `?c l1 l2. inst.inst_operands = [c; Label l1; Label l2] /\
             inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf inst` mp_tac >>
     qpat_x_assum `inst.inst_opcode = JNZ` mp_tac >>
     rpt (pop_assum kall_tac) >> rw[venomWfTheory.inst_wf_def] >> gvs[]) >>
  `~is_label_operand c` by
    (qpat_x_assum `inst_shape_ok inst` mp_tac >>
     qpat_x_assum `inst.inst_operands = _` mp_tac >>
     qpat_x_assum `inst.inst_opcode = JNZ` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[inst_shape_ok_def, label_positions_ok_def]) >>
  `is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `MEM l1 (get_successors inst) /\ MEM l2 (get_successors inst)` by
    (Cases_on `c` >> gvs[get_successors_def, get_label_def, is_label_operand_def]) >>
  `MEM c (compute_operands inst)` by
    (Cases_on `c` >> gvs[compute_operands_def, asmIRTheory.get_non_label_operands_def,
      is_label_operand_def]) >>
  suspend "selected"
QED

Resume body_plan_symbolic_jnz_step[selected]:
  `eval_operand c vs = operand_val (frame_view fn ra vs) lo c` by
    (`eval_operand c vs = eval_operand c (frame_view fn ra vs)` by
       (irule eval_operand_frame_view_vs >> rpt strip_tac >>
        `MEM (Var x) inst.inst_operands` by
          (qpat_x_assum `inst.inst_operands = _` (fn th => rewrite_tac[th]) >>
           qpat_x_assum `c = Var x` (fn th => rewrite_tac[GSYM th, MEM])) >>
        drule_all opaque_use_ok_retpc_use >> strip_tac >>
        gvs[retpc_use_ok_def]) >>
     metis_tac[]) >>
  drule_all body_plan_terminator_last >> strip_tac >>
  mp_tac (Q.INST [`t` |-> `l1`] (SPEC_ALL body_plan_succ_placed)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`tb1`, `pd1`, `op1`, `pa1`, `off1`, `pc1`]
    strip_assume_tac) >>
  mp_tac (Q.INST [`t` |-> `l2`] (SPEC_ALL body_plan_succ_placed)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`tb2`, `pd2`, `op2`, `pa2`, `off2`, `pc2`]
    strip_assume_tac) >>
  suspend "placement"
QED

Resume body_plan_symbolic_jnz_step[placement]:
  qhdtm_assum `body_plan_inv`
    (strip_assume_tac o REWRITE_RULE [body_plan_inv_def]) >>
  qpat_x_assum `inst.inst_opcode = JNZ ==> _` drule >>
  disch_then (qspecl_then [`c`, `l1`, `l2`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
       operand_equiv dfg c at ==>
       operand_val (frame_view fn ra vs) lo c =
       operand_val (frame_view fn ra vs) lo at` by
    (rpt strip_tac >>
     qpat_x_assum `!op at. MEM op (compute_operands inst) /\ _ ==> _` irule >>
     simp[] >> metis_tac[]) >>
  drule_all gen_jnz_frame_sim_deep_exact >> strip_tac >>
  suspend "symbolic"
QED

Resume body_plan_symbolic_jnz_step[symbolic]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `MEM (AsmLabel l1) prog /\ MEM (AsmLabel l2) prog` by
    metis_tac[symBlockBodyTheory.placed_nonentry_sym_code_label] >>
  `ssa_form fn` by fs[codegen_ready_fn_def] >>
  `fn_shape_ok fn` by
    (qpat_x_assum `unit_shape_ok unit` mp_tac >>
     simp[unit_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `label_flow_ok ctx /\ asm_static_wf prog` by
    fs[focus_s7_symbolic_context_def] >>
  `operand_val (frame_view fn ra vs) lo c = SOME w` by metis_tac[] >>
  `1 <= LENGTH ps1.ps_stack` by gvs[] >>
  drule_all sym_jnz_plan_frame_sim >> strip_tac >>
  qpat_x_assum `ps' = ps_after` SUBST_ALL_TAC >>
  suspend "package"
QED

Resume body_plan_symbolic_jnz_step[package]:
  markerLib.RESUME_TAC >>
  `as' = ac` by gvs[] >>
  qpat_x_assum `as' = ac` SUBST_ALL_TAC
  >- (qexistsl_tac [`l1`,
        `LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) +
           (if w = 0w then 4 else 2)`, `ac`, `off1`, `sy`] >>
      qpat_x_assum `ac.as_pc = pc1` SUBST1_TAC >>
      conj_tac >- (Cases_on `w = 0w` >> simp[]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`l2`,
    `LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) +
       (if w = 0w then 4 else 2)`, `ac`, `off2`, `sy`] >>
  qpat_x_assum `ac.as_pc = pc2` SUBST1_TAC >>
  conj_tac >- (Cases_on `w = 0w` >> simp[]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise body_plan_symbolic_jnz_step

Theorem entry_frame_symbolic_plan_next:
  entry_frame_symbolic_plan env rpolicy unit cpl prog fn entry s ast
    ra pc_ret rest mem0 ret srest labs0 ss /\
  s.vs_inst_idx < LENGTH (get_params (HD fn.fn_blocks).bb_instructions) ==>
  ?post.
    step_inst fuel unit.cu_context
      (EL s.vs_inst_idx (get_params (HD fn.fn_blocks).bb_instructions)) s = OK post /\
    entry_frame_symbolic_plan env rpolicy unit cpl prog fn entry
      (post with vs_inst_idx := SUC s.vs_inst_idx) ast
      ra pc_ret rest mem0 ret srest labs0 ss
Proof
  rw[entry_frame_symbolic_plan_def] >>
  drule_all entry_frame_plan_next >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  qexists `post` >> simp[]
QED

Theorem entry_frame_symbolic_plan_ready:
  entry_frame_symbolic_plan env rpolicy unit cpl prog fn entry s ast
    ra pc_ret rest mem0 ret srest labs0 ss /\
  focus_s7_symbolic_context unit prog /\
  s.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions) ==>
  ?n ast1 ss1.
    0 < n /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    sym_steps prog env n ss = SymOK ss1 /\
    active_frame_symbolic_plan env rpolicy unit cpl prog fn s ast1
      ra rest mem0 ret srest labs0 ss1
Proof
  pure_rewrite_tac [entry_frame_symbolic_plan_def, focus_s7_symbolic_context_def] >>
  strip_tac >>
  qpat_x_assum `entry_frame_plan _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [entry_frame_plan_def]) >>
  `s.vs_inst_idx = k` by fs[] >>
  `s = entry_bind_pairs
    (entry_param_pairs entry (get_params (HD fn.fn_blocks).bb_instructions)) entry
      with vs_inst_idx := LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by fs[] >>
  `codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn` by
    metis_tac[body_fn_shape] >>
  drule_all region_fn_plan >> strip_tac >>
  drule_all entry_block_plan >> strip_tac >>
  `!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)` by
    metis_tac[entry_step_spill_bound] >>
  `asm_block_at prog ast.as_pc
     (execute_plan cpl.cp_initial_fmp
       (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops)) /\
   asm_block_at prog ast.as_pc
     (execute_plan cpl.cp_initial_fmp
       (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))` by
    (qpat_x_assum `asm_block_at _ _ (execute_plan _ r.sr_plan)` mp_tac >>
     qpat_assum `r.sr_plan = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
     rpt strip_tac >> fs[]) >>
  `ps1.ps_alloc.sa_next_offset <= r.sr_spill_end` by decide_tac >>
  `?ast1 ss1.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog
      (LENGTH (execute_plan cpl.cp_initial_fmp
        (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))) ast = AsmOK ast1 /\
    ast1.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp
        (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
    fn_frame_inv unit.cu_context cpl (SND (compute_label_offsets prog))
      fn ra rest ast.as_memory ps1 s ast1 /\
    sym_steps prog env (LENGTH (execute_plan cpl.cp_initial_fmp
        (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))) ss = SymOK ss1 /\
    sym_frame_inv prog env unit.cu_context cpl fn ret srest
      ss.sym_mem_labels ps1 ast1 ss1` by
    (irule sym_entry_prefix_asm >> simp[] >>
     conj_tac >-
       (goal_assum (drule_at Any) >> simp[] >>
        qexistsl [`cleanup_caller_height (LENGTH unit.cu_context.ctx_functions)
          unit.cu_context (fcg_analyze unit.cu_context) fn.fn_name`,
          `cleanup_growth_table unit.cu_context (fcg_analyze unit.cu_context)`,
          `lbl_ctr`, `r.sr_spill_base`] >> simp[]) >>
     qexists `entry` >> simp[]) >>
  `!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
    normalize_operand (dfg_build_function fn) [] at = at` by
    (rpt strip_tac >> irule entry_plan_normalize >> simp[] >> metis_tac[]) >>
  drule_at (Pat `codegen_context_obligations _ _ _`) codegen_invoke_targets_retpc >>
  simp[] >> strip_tac >>
  `!l. FLOOKUP s.vs_labels l =
    OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l)` by
    gvs[entry_bind_pairs_normal] >>
  qexistsl [`LENGTH (execute_plan cpl.cp_initial_fmp
    (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))`, `ast1`, `ss1`] >>
  simp[execute_plan_def, exec_stack_op_def] >>
  simp[active_frame_symbolic_plan_def] >>
  irule_at Any entry_body_plan >> simp[] >>
  qexistsl [`ps_end`, `ps_after`, `ps1`, `pc_ret`, `ast.as_pc`,
    `param_ops`, `lbl_ctr`, `i`, `body_ops`] >>
  gvs[entry_bind_pairs_normal] >>
  fs[fn_entry_state_rel_def] >> metis_tac[]
QED

Theorem body_plan_symbolic_jmp_step:
  body_plan_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast
      ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JMP /\ step_inst fuel ctx inst vs = OK vs1 /\
  focus_s7_symbolic_context unit prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps ast ss ==>
  ?target n ast1 off ss1.
    0 < n /\ vs1 = jump_to target vs /\ MEM target (get_successors inst) /\
    asm_steps lo o2pc prog n ast = AsmOK ast1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 ast1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    FLOOKUP lo target = SOME off /\ FLOOKUP o2pc off = SOME ast1.as_pc /\
    sym_steps prog env n ss = SymOK ss1 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps_after ast1 ss1
Proof
  strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule body_plan_inv_equiv >> disch_then drule >> disch_then drule >>
  strip_tac >>
  qhdtm_assum `body_plan_inv`
    (strip_assume_tac o REWRITE_RULE [body_plan_inv_def]) >>
  `?target. inst.inst_operands = [Label target] /\ inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf inst` mp_tac >> simp[inst_wf_def] >> gvs[]) >>
  `is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `MEM target (get_successors inst)` by simp[get_successors_def, get_label_def] >>
  drule_all body_plan_terminator_last >> strip_tac >>
  drule_all body_plan_succ_placed >> strip_tac >>
  `pending_inventory_wf
    (MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
      (live_vars_at liveness target 0))) ps` by metis_tac[] >>
  `LENGTH (MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
      (live_vars_at liveness target 0))) <=
      LENGTH (SND (restore_spilled_plan
        (MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
          (live_vars_at liveness target 0))) ps)).ps_stack /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
        (live_vars_at liveness target 0)))` by metis_tac[] >>
  drule_at (Pos last) sym_jmp_plan_decompose >>
  disch_then (qspec_then
    `MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
      (live_vars_at liveness target 0))` mp_tac) >>
  simp[] >> strip_tac >>
  `asm_static_wf prog` by fs[focus_s7_symbolic_context_def] >>
  `ssa_form fn` by fs[codegen_ready_fn_def] >>
  `fn_shape_ok fn` by
    (qpat_x_assum `unit_shape_ok unit` mp_tac >>
     simp[unit_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `MEM (AsmLabel target) prog` by
    (drule_all symBlockBodyTheory.placed_nonentry_sym_code_label >> simp[]) >>
  `!off. MEM (SORestore off) rops ==> off < dimword (:256)` by
    (qpat_x_assum `ops = _` (fn th => fs[th])) >>
  qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  qpat_x_assum `o2pc = _` SUBST_ALL_TAC >>
  `?ac sy.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog
      (LENGTH (execute_plan cpl.cp_initial_fmp ops)) ast = AsmOK ac /\
    sym_steps prog env (LENGTH (execute_plan cpl.cp_initial_fmp ops)) ss = SymOK sy /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps_after ac sy /\ ac.as_pc = tpc` by
    (irule sym_jmp_plan_frame_sim >>
     simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl [`arranged`, `spill_base`,
       `live_vars_at liveness bb.bb_label (k + 1)`,
       `MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
          (live_vars_at liveness target 0))`, `prepared`, `ps`, `rops`, `sops`] >>
     simp[] >> conj_tac
     >- (qpat_x_assum `EVERY (\op. op <> dead_stack_marker /\ !at. _) (MAP Var _)` mp_tac >>
         qpat_x_assum `dfg = _` mp_tac >>
         qpat_x_assum `liveness = _` mp_tac >>
         qpat_x_assum `bb.bb_label = _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp[EVERY_MEM] >> metis_tac[]) >>
     qpat_x_assum `sym_frame_inv prog env ctx _ _ _ _ _ _ _ _` mp_tac >> simp[] ) >>
  drule_at_then (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)
    (drule_at_then (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
      (drule_at_then (Pat `step_inst _ _ _ _ = _`)
        (drule_at_then (Pat `asm_block_at _ _ _`)
          (drule_at_then (Pat `inst.inst_operands = _`)
            (drule_at_then (Pat `generated_plan_state_wf_marked _ _`)
              (drule_at (Pat `MEM _ cpl.cp_regions`)))))))
    fnFrameDeepJmpTheory.gen_jmp_frame_sim_deep_exact >>
  disch_then (qspecl_then [`build_offset_to_pc prog`, `tbb`,
    `MAP Var (input_vars_from bb.bb_label tbb.bb_instructions
       (live_vars_at liveness target 0))`, `toff`, `tpc`] mp_tac) >>
  simp[] >>
  (impl_tac
   >- (rpt gen_tac >> strip_tac >> irule mem_operand_equiv >>
       goal_assum (drule_at (Pos (el 3))) >>
       simp[] >> rpt strip_tac >>
       metis_tac[pending_inventory_wf_owned])) >>
  strip_tac >>
  `!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
    operand_val (frame_view fn ra vs1) (SND (compute_label_offsets prog)) at =
    operand_val (frame_view fn ra vs1) (SND (compute_label_offsets prog))
      (normalize_operand dfg [] at)` by
    (drule_all body_plan_jmp_step >> strip_tac >> metis_tac[]) >>
  `0 < LENGTH (execute_plan cpl.cp_initial_fmp ops)` by
    (qpat_x_assum `ops = _` SUBST1_TAC >>
     simp[stackOpSimTheory.execute_plan_append,
       planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def]) >>
  qexistsl [`target`, `LENGTH (execute_plan cpl.cp_initial_fmp ops)`,
    `ac`, `toff`, `sy`] >> simp[] >>
  conj_tac
  >- (qpat_x_assum `!at. MEM at ps_after.ps_stack \/ _ ==> _` mp_tac >> simp[]) >>
  qpat_x_assum `sym_frame_inv prog env ctx _ _ _ _ _ _ ac sy` mp_tac >> simp[]
QED

Theorem block_step_symbolic_prefix:
  !unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth spill_base
   lbl_ctr fn_ops ps_end bb pred ps ps_dfs block_ops ps_dfs_after vs as Inv
   ra rest mem0 s_phi env ret srest labs0 ss.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cpl /\
    unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cpl.cp_regions = r /\
    codegen_context_obligations Inv ctx cpl /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    spill_base = r.sr_spill_base /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    fn_ops = r.sr_plan /\
    ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps /\
    vs.vs_prev_bb = SOME pred /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      vs.vs_current_bb ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after) /\
    asm_block_at prog as.as_pc (execute_plan cpl.cp_initial_fmp block_ops) /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps vs as /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    focus_s7_symbolic_context unit prog /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
    ?h promised ps_after prefix_ops rest_ops ps1 n as1 ss1.
      n = LENGTH (execute_plan cpl.cp_initial_fmp (SOLabel bb.bb_label :: prefix_ops)) /\
      generate_block_plan liveness dfg cfg fn bb
        (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
        SOME (block_ops, ps_after) /\
      ps_after.ps_alloc = ps_dfs_after.ps_alloc /\
      ps_after.ps_spilled = ps_dfs_after.ps_spilled /\
      (?prefixL prefixD core.
         ps_after.ps_stack = prefixL ++ core /\
         ps_dfs_after.ps_stack = prefixD ++ core /\
         (!v. MEM v (live_vars_at liveness bb.bb_label (LENGTH bb.bb_instructions)) ==>
            ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD)) /\
      block_plan_state liveness dfg cfg fn bb
        (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
        (phi_prefix_length bb.bb_instructions) ps1 /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (phi_prefix_length bb.bb_instructions -
         LENGTH (get_params bb.bb_instructions))
        (DROP (phi_prefix_length bb.bb_instructions -
               LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
        ps1 = SOME (rest_ops, ps_after) /\
      block_ops = SOLabel bb.bb_label :: prefix_ops ++ rest_ops /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp
                                       (SOLabel bb.bb_label :: prefix_ops)) /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) as1 /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra
           (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)) lo at =
         operand_val (frame_view fn ra
           (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)) lo
           (normalize_operand dfg [] at)) /\
      create_safe_prefix lo o2pc prog n as /\
      sym_steps prog env n ss = SymOK ss1 /\
      sym_frame_inv prog env ctx cpl fn ret srest labs0 ps1 as1 ss1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all sym_block_prefix_prepare >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  `MEM fn ctx.ctx_functions /\ fn_shape_ok fn` by
    (fs[unit_shape_ok_def, listTheory.EVERY_EL] >>
     metis_tac[listTheory.MEM_EL]) >>
  `label_flow_ok ctx /\ asm_static_wf prog` by
    fs[focus_s7_symbolic_context_def] >>
  qpat_assum `block_ops = _` (fn eq =>
    qpat_assum `asm_block_at _ _ _` (mp_tac o REWRITE_RULE [eq])) >>
  rewrite_tac[listTheory.APPEND] >>
  disch_then (mp_then (Pat `asm_block_at _ _ _`) mp_tac sym_label_block_steps) >>
  disch_then (drule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`lo`, `o2pc`] strip_assume_tac) >>
  drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
    sym_block_prefix_step_exact >>
  disch_then (drule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (mp_tac o REWRITE_RULE [fn_frame_inv_pc]) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_all o SIMP_RULE pure_ss [asmSemTheory.asm_state_accfupds, combinTheory.K_THM]) >>
  strip_tac >> suspend "paired_prefix"
QED

Resume block_step_symbolic_prefix[paired_prefix]:
  `create_safe_prefix lo o2pc prog n (as with as_pc := as.as_pc + 1)` by
    (`fn_frame_inv ctx cpl lo fn ra rest mem0 ps vs
       (as with as_pc := as.as_pc + 1)` by simp[fn_frame_inv_pc] >>
     drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
       block_prefix_step >>
     disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
     disch_then (drule_all o SIMP_RULE pure_ss
       [asmSemTheory.asm_state_accfupds, combinTheory.K_THM]) >>
     strip_tac >> gvs[]) >>
  `EL as.as_pc prog = AsmLabel bb.bb_label` by
    (qpat_assum `block_ops = _` (fn eq =>
       qpat_assum `asm_block_at _ as.as_pc (execute_plan _ block_ops)`
         (mp_tac o REWRITE_RULE [eq])) >>
     simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons]) >>
  `create_safe_prefix lo o2pc prog 1 as` by
    (rewrite_tac[arithmeticTheory.ONE, asmRunBoundedTheory.create_safe_prefix_suc] >>
     qpat_assum `EL as.as_pc prog = AsmLabel bb.bb_label`
       (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [asmRunBoundedTheory.create_safe_def,
                          asmRunBoundedTheory.create_safe_prefix_zero]) >>
  `create_safe_prefix lo o2pc prog (1 + n) as` by
    (irule asmRunBoundedTheory.create_safe_prefix_compose >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `as with as_pc := as.as_pc + 1` >> simp[]) >>
  `asm_steps lo o2pc prog (1 + n) as = AsmOK as'` by
    (qpat_assum `asm_steps _ _ _ 1 as = _`
       (fn th => rewrite_tac[MATCH_MP asm_steps_add_ok th]) >> simp[]) >>
  qexistsl_tac [`h`, `promised`, `ps_after`, `clean_ops ++ phi_ops`,
               `body_ops`, `ps1`, `1 + n`, `as'`, `ss'`] >>
  simp[execute_plan_label_length, Once sym_steps_add,
       operand_val_frame_view_inst_idx, listTheory.APPEND_ASSOC] >>
  conj_tac
  >- (qexistsl_tac [`prefixL`, `prefixD`, `core`] >> gvs[]) >>
  conj_tac
  >- (rewrite_tac[fnBlockPlanStaticTheory.block_plan_state_def] >>
      qexistsl_tac [`[]`,
        `ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>`,
        `clean_ops`, `ps2`, `phi_ops`] >> gvs[]) >>
  gvs[] >> metis_tac[]
QED

Finalise block_step_symbolic_prefix

Theorem active_frame_symbolic_ret_boundary:
  frame_stack_symbolic_plan env rpolicy unit cpl prog vs0 es0 stk fn entry ra rest mem0 sentry ret srest labs0 /\
  frame_history vs0 unit.cu_context stk PG G tn fn inst s hs history /\
  active_frame_symbolic_plan env rpolicy unit cpl prog fn s ast ra rest mem0 ret srest labs0 ss /\
  active_inst fn inst s /\ inst.inst_opcode = RET /\
  focus_s7_symbolic_context unit prog /\
  step_inst fuel unit.cu_context inst s = IntRet rv send ==>
  ?n asr ssr.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n ast = AsmOK asr /\
    sym_steps prog env n ss = SymOK ssr /\
    FLOOKUP (build_offset_to_pc prog) (w2n ra) = SOME asr.as_pc /\
    asr.as_stack = REVERSE rv.iret_values ++ rest /\
    fn_return_state_rel unit.cu_context cpl fn send entry asr /\
    asm_sym_rel prog env asr ssr /\
    ssr.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
    (!b. context_spill_byte cpl b /\ ~closure_spill_byte unit.cu_context cpl fn.fn_name b ==> FLOOKUP ssr.sym_mem_labels b = FLOOKUP labs0 b) /\
    (!b. b IN FDOM ssr.sym_mem_labels ==> context_spill_byte cpl b)
Proof
  rpt strip_tac >>
  `mem0 = entry.as_memory /\
   (entry.as_call_ctx, entry.as_tx_ctx, entry.as_block_ctx,
    entry.as_code, entry.as_prev_hashes) =
   (vs0.vs_call_ctx, vs0.vs_tx_ctx, vs0.vs_block_ctx,
    vs0.vs_code, vs0.vs_prev_hashes)` by
    (qpat_x_assum `frame_stack_symbolic_plan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       mp_tac >> rpt (pop_assum kall_tac) >>
     simp[Once frame_stack_symbolic_plan_cases] >> rpt strip_tac >>
     fs[fn_entry_state_rel_def, shared_state_rel_def, fn_frame_inv_def,
        contextCodegenRelTheory.context_venom_asm_rel_def, frame_view_def] >>
     qpat_x_assum `setup_callee _ _ _ = SOME _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [setup_callee_def, AllCaseEqs()]) >>
     qpat_x_assum `_ = cvs` (assume_tac o SYM) >> simp[]) >>
  fs[active_frame_symbolic_plan_def, focus_s7_symbolic_context_def] >>
  drule_all body_plan_active_inst >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  drule_all fnBlockBodyTheory.body_operands_le_16 >> strip_tac >>
  `MEM inst (fn_insts (reachable_fn fn))` by
    (irule reachable_fn_mem_inst >> metis_tac[body_plan_inv_def]) >>
  `ps'.ps_stack = []` by metis_tac[] >>
  drule body_plan_inv_equiv >> disch_then drule >> disch_then drule >> strip_tac >>
  qpat_assum `body_plan_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [body_plan_inv_def]) >>
  `fn_shape_ok fn` by fs[unit_shape_ok_def, EVERY_MEM] >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`) sym_ret_frame_sim_deep >>
  disch_then (drule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  simp[] >>
  disch_then (qspecl_then [`fuel`, `pc_ret`, `rv`, `send`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  drule_all ret_source_frame_boundary >>
  disch_then (qspec_then `ra` strip_assume_tac) >>
  drule frame_history_readonly >> strip_tac >>
  qexistsl [`n`, `as'`, `ss'`] >>
  simp[] >>
  fs[fn_return_state_rel_def, shared_state_rel_def] >> metis_tac[]
QED

Theorem body_plan_symbolic_call_prepare:
  body_plan_inv rpolicy unit cpl prog unit.cu_context
    (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    i fn r liveness dfg cfg ch growth spill_base lbl_ctr fn_ops ps_end
    bb ps_l h promised ps_dfs block_ops ps_dfs_after ps_after prefix_ops
    rest_ops k ps pc0 s ast ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  generate_inst_plan liveness dfg cfg fn inst
    (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
    (k + 1 < LENGTH bb.bb_instructions /\
     is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
    bb.bb_label ps = SOME (ops, ps') /\
  emit_input_plan INVOKE (compute_operands inst)
    (live_vars_at liveness bb.bb_label (k + 1)) ps = (iops, prepared) /\
  reorder_plan dfg (compute_operands inst) prepared = (rops, arranged) /\
  ops = iops ++ rops ++ post /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  asm_static_wf prog /\
  sym_frame_inv prog env unit.cu_context cpl fn ret srest labs0 ps ast ss /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog (LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops))) ast = AsmOK mid ==>
  ?sms. sym_steps prog env (LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops))) ss = SymOK sms /\
    sym_frame_inv prog env unit.cu_context cpl fn ret srest labs0 arranged mid sms
Proof
  rpt strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule_all fnBlockBodyTheory.body_operands_le_16 >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >> fs[] >>
  `unit_shape_ok unit /\ dfg = dfg_build_function fn` by
    gvs[body_plan_inv_def] >>
  drule_all fnFrameBoundaryInvokeTheory.invoke_compute_operands >> strip_tac >>
  gvs[] >>
  fs[EVERY_APPEND, codegen_ready_fn_def,
     fnPlanLineageInventoryTheory.stack_get_depth_is_some,
     finite_mapTheory.FLOOKUP_DEF] >>
  `r.sr_spill_base <= ps.ps_alloc.sa_spill_base` by
    metis_tac[allocMonoTheory.emit_input_plan_spill_base,
              allocMonoTheory.reorder_plan_spill_base] >>
  `fn_shape_ok fn` by metis_tac[unit_shape_ok_def, EVERY_MEM] >>
  `asm_block_at prog ast.as_pc (execute_plan cpl.cp_initial_fmp (iops ++ rops))` by
    (qpat_x_assum `asm_block_at prog ast.as_pc _` mp_tac >>
     simp[execute_plan_def, stackOpSimTheory.asm_block_at_append]) >>
  irule sym_invoke_selected_frame_prefix >> simp[EVERY_APPEND] >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem active_frame_symbolic_call_progress:
  joint_config_reachable vs0 unit.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  frame_stack_symbolic_plan env rpolicy unit cpl prog vs0 es0 stk fn saved
    ra rest mem0 sentry ret srest labs0 /\
  active_frame_symbolic_plan env rpolicy unit cpl prog fn s ast ra rest mem0
    ret srest labs0 ss /\
  ~in_revert_forward fn s /\ env = asm_data_env prog vs0.vs_code /\
  focus_s7_symbolic_context unit prog /\ focus_s7_symbolic_guard prog cpl fn inst s /\
  joint_transition unit.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h) NONE
    (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') ==>
  ?n ast1 ss1.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    sym_steps prog env n ss = SymOK ss1 /\
    normal_frame_symbolic_plan env rpolicy unit cpl prog vs0 es0
      (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') ast1 ss1 /\
    (0 < n \/
     (n = 0 /\ inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
      stk' = stk /\ fn' = fn /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = SUC s.vs_inst_idx /\
      ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        LENGTH bb.bb_instructions - t.vs_inst_idx <
          LENGTH bb.bb_instructions - s.vs_inst_idx))
Proof
  rpt strip_tac >>
  gvs[joint_transition_call_iff, decode_invoke_def, AllCaseEqs(),
      active_frame_symbolic_plan_def, focus_s7_symbolic_context_def] >>
  drule_all body_plan_active_inst >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all fnBlockBodyTheory.body_operands_le_16 >> strip_tac >>
  drule_all fnBlockBodyClassesTheory.body_plan_call_entry >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  fs[] >>
  `unit_shape_ok unit /\ dfg = dfg_build_function fn` by
    gvs[body_plan_inv_def] >>
  drule_at (Pat `MEM inst (fn_insts fn)`) sym_invoke_selected_entry_facts >>
  FAIL_TAC "entry facts matching"
QED

Theorem sym_body_plan_ordinary_ok:
  body_plan_inv rpolicy unit cpl prog unit.cu_context
    (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    i fn r liveness dfg cfg ch growth spill_base lbl_ctr fn_ops ps_end
    bb ps_l h promised ps_dfs block_ops ps_dfs_after ps_after prefix_ops
    rest_ops k ps pc0 s ast ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  ~in_revert_forward fn s /\ step_inst fuel unit.cu_context inst s = OK post /\
  env = asm_data_env prog code /\ focus_s7_symbolic_context unit prog /\
  focus_s7_symbolic_guard prog cpl fn inst s /\
  sym_frame_inv prog env unit.cu_context cpl fn ret srest labs0 ps ast ss ==>
  ?ops ps' rest' n ast1 ss1.
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\ rest_ops = ops ++ rest' /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    fn_frame_inv unit.cu_context cpl (SND (compute_label_offsets prog))
      fn ra rest mem0 ps' post ast1 /\
    ast1.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
    sym_steps prog env n ss = SymOK ss1 /\
    sym_frame_inv prog env unit.cu_context cpl fn ret srest labs0 ps' ast1 ss1
Proof
  strip_tac >>
  fs[focus_s7_symbolic_context_def, focus_s7_symbolic_guard_def] >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  `s.vs_inst_idx = k` by fs[body_plan_inv_def] >>
  `!j. ~revert_forward_pair bb k j` by
    (fs[in_revert_forward_def, revert_forward_at_def] >> metis_tac[]) >>
  drule_all body_operands_le_16 >> strip_tac >>
  `(inst.inst_opcode = LOG ==>
     ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4)` by
    (strip_tac >> drule_all body_log_topics >> Cases_on `inst.inst_operands` >> simp[] >>
     rename1 `head :: tail` >> Cases_on `head` >> simp[] >> metis_tac[]) >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule body_plan_inv_equiv >> disch_then drule >> disch_then drule >> strip_tac >>
  `!e. step_inst fuel unit.cu_context inst s <> Error e` by simp[] >>
  drule body_plan_inv_label_resolve >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> strip_tac >>
  `fn_shape_ok fn` by
    (fs[body_plan_inv_def, unit_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `!l. MEM (AsmDataHeader l) prog ==> l IN FDOM (asm_data_env prog code)` by
    (rpt strip_tac >> simp[asm_data_env_def, FDOM_DRESTRICT] >>
     simp[symbolResolveTheory.compute_label_offsets_def, asmToBytecodeProofsTheory.clo_step_eq] >>
     irule clo_FDOM >> simp[]) >>
  `codegen_assembly rpolicy unit = SOME prog` by fs[body_plan_inv_def] >>
  `sym_data_label prog (asm_data_env prog code) "code_end"` by
    metis_tac[codegen_sym_code_end_label] >>
  `(MEM (Label "runtime_begin") inst.inst_operands ==>
    sym_data_label prog (asm_data_env prog code) "runtime_begin")` by
    metis_tac[codegen_sym_runtime_begin_label] >>
  `dfg = dfg_build_function fn /\
   fn_frame_inv unit.cu_context cpl (SND (compute_label_offsets prog))
     fn ra rest mem0 ps s ast` by fs[body_plan_inv_def] >>
  `?n ast1 ss1.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    fn_frame_inv unit.cu_context cpl (SND (compute_label_offsets prog))
      fn ra rest mem0 ps' post ast1 /\
    ast1.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
    sym_steps prog (asm_data_env prog code) n ss = SymOK ss1 /\
    sym_frame_inv prog (asm_data_env prog code) unit.cu_context cpl
      fn ret srest labs0 ps' ast1 ss1` by
    (Cases_on `inst.inst_opcode = GAS`
     >- (`context_spill_step_safe cpl s post` by
           metis_tac[noninvoke_spill_step_safe] >>
         drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
           sym_gas_frame_sim_deep >>
         disch_then (fn th => first_assum
           (mp_then (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`) mp_tac th)) >>
         disch_then (fn th => first_assum
           (mp_then (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`) mp_tac th)) >>
         simp[] >> disch_then (qspecl_then [`fuel`, `spill_base`, `r`, `post`] mp_tac) >>
         simp[]) >>
     drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
       sym_inst_frame_sim_deep >>
     disch_then (fn th => first_assum
       (mp_then (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`) mp_tac th)) >>
     disch_then (fn th => first_assum
       (mp_then (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`) mp_tac th)) >>
     simp[] >> disch_then (qspecl_then [`fuel`, `spill_base`, `r`, `post`] mp_tac) >>
     simp[] >> disch_then irule >> metis_tac[]) >>
  qexistsl_tac [`ops`, `ps'`, `rest'`, `n`, `ast1`, `ss1`] >> simp[]
QED

Theorem active_frame_symbolic_next_progress:
  joint_config_reachable vs0 unit.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  frame_stack_symbolic_plan env rpolicy unit cpl prog vs0 es0 stk fn saved
    ra rest mem0 sentry ret srest labs0 /\
  active_frame_symbolic_plan env rpolicy unit cpl prog fn s ast ra rest mem0
    ret srest labs0 ss /\
  ~in_revert_forward fn s /\
  env = asm_data_env prog vs0.vs_code /\
  focus_s7_symbolic_context unit prog /\
  focus_s7_symbolic_guard prog cpl fn inst s /\
  joint_transition unit.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h) (SOME (OriginOrdinary fuel post))
    (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') ==>
  ?n ast1 ss1.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    sym_steps prog env n ss = SymOK ss1 /\
    normal_frame_symbolic_plan env rpolicy unit cpl prog vs0 es0
      (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') ast1 ss1 /\
    (0 < n \/
     (n = 0 /\ inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
      stk' = stk /\ fn' = fn /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = SUC s.vs_inst_idx /\
      ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        LENGTH bb.bb_instructions - t.vs_inst_idx <
          LENGTH bb.bb_instructions - s.vs_inst_idx))
Proof
  strip_tac >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[Once joint_transition_cases] >> rpt strip_tac >> gvs[] >>
  fs[active_frame_symbolic_plan_def, focus_s7_symbolic_context_def,
     focus_s7_symbolic_guard_def] >>
  drule_all body_plan_active_inst >> strip_tac >>
  drule sym_body_plan_ordinary_ok >>
  simp[focus_s7_symbolic_context_def, focus_s7_symbolic_guard_def] >>
  disch_then (fn th => first_assum
    (mp_then (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`) mp_tac th)) >>
  disch_then (fn th => first_assum
    (mp_then (Pat `step_inst _ _ _ _ = _`) mp_tac th)) >>
  strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  `s.vs_inst_idx = k` by fs[body_plan_inv_def] >>
  `!j. ~revert_forward_pair bb k j` by
    (fs[in_revert_forward_def, revert_forward_at_def] >> metis_tac[]) >>
  drule body_plan_advance >> simp[] >>
  disch_then (fn th => first_assum
    (mp_then (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`) mp_tac th)) >>
  simp[] >> disch_then (qspecl_then [`rest'`, `ops`, `fuel`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  `post.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
  qexistsl_tac [`n`, `ast1`, `ss1`] >> simp[] >>
  reverse conj_tac
  >- (Cases_on `n = 0` >> simp[] >>
      drule body_plan_inv_facts >> strip_tac >>
      qexists_tac `bb` >> gvs[]) >>
  simp[normal_frame_symbolic_plan_def] >>
  qexistsl_tac [`saved`, `ra`, `rest`, `mem0`, `sentry`, `ret`, `srest`, `labs0`] >>
  simp[] >> disj1_tac >>
  simp[active_frame_symbolic_plan_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem normal_frame_symbolic_joint_progress:
  joint_config_reachable vs0 unit.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  normal_frame_symbolic_plan env rpolicy unit cpl prog vs0 es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast ss /\
  ~in_revert_forward fn s /\
  env = asm_data_env prog vs0.vs_code /\
  focus_s7_symbolic_context unit prog /\
  focus_s7_symbolic_guard prog cpl fn inst s /\
  joint_transition unit.cu_context
    (JointConfig stk PG G tn fn inst s oms om hs h) ev
    (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') ==>
  ?n ast1 ss1.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    sym_steps prog env n ss = SymOK ss1 /\
    normal_frame_symbolic_plan env rpolicy unit cpl prog vs0 es0
      (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') ast1 ss1 /\
    (0 < n \/
     (n = 0 /\ inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
      stk' = stk /\ fn' = fn /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = SUC s.vs_inst_idx /\
      ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        LENGTH bb.bb_instructions - t.vs_inst_idx <
          LENGTH bb.bb_instructions - s.vs_inst_idx))
Proof
  cheat
QED

Theorem normal_frame_symbolic_trace_prefix:
  !j.
  joint_trace vs0 unit.cu_context q0 evs qs qlast /\ j <= LENGTH evs /\
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  codegen_context_obligations (\_ _ _ _. F) unit.cu_context cpl /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  env = asm_data_env prog vs0.vs_code /\ focus_s7_symbolic_context unit prog /\
  (!i stk PG G tn fn inst s oms om hs h.
    i < j /\ EL i (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h ==>
      ~in_revert_forward fn s /\ focus_s7_symbolic_guard prog cpl fn inst s) ==>
  ?n ast ss.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog n (entry_asm_state vs0 es0) = AsmOK ast /\
    sym_steps prog env n (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
    normal_frame_symbolic_plan env rpolicy unit cpl prog vs0 es0
      (EL j (q0::qs)) ast ss
Proof
  cheat
QED

Theorem frame_stack_symbolic_plan_projection:
  !env rpolicy unit cpl prog vs0 es0 stk fn saved ra rest mem0 sentry ret srest labs0.
    frame_stack_symbolic_plan env rpolicy unit cpl prog vs0 es0 stk fn saved
      ra rest mem0 sentry ret srest labs0 ==>
    !tail. initial_ctx_rel_tail tail cpl prog unit.cu_context vs0 es0 ==>
      frame_stack_plan rpolicy unit cpl prog vs0 es0 stk fn saved ra rest mem0
Proof
  ho_match_mp_tac frame_stack_symbolic_plan_ind >> conj_tac
  >- (rpt strip_tac >> irule frame_stack_plan_entry >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  irule frame_stack_plan_call >> metis_tac[]
QED

Theorem normal_frame_symbolic_identity_projection:
  initial_ctx_rel_tail tail cpl prog unit.cu_context vs0 es0 /\
  normal_frame_symbolic_plan env rpolicy unit cpl prog vs0 es0 q ast ss ==>
  normal_frame_plan rpolicy unit cpl prog vs0 es0 q ast /\
  asm_sym_rel prog env ast ss
Proof
  Cases_on `q` >>
  simp[normal_frame_symbolic_plan_def] >> rpt strip_tac >>
  drule_all frame_stack_symbolic_plan_projection >> strip_tac >>
  gvs[active_frame_symbolic_plan_def, entry_frame_symbolic_plan_def,
      sym_frame_inv_def, normal_frame_plan_def, active_frame_plan_def] >>
  metis_tac[]
QED


