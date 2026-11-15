(* Symbolic annotations of the finite source-frame packets. *)
Theory fnFrameSymbolicPrefix
Ancestors
  fnFramePrefixDriver fnFramePrefix fnFramePrefixEntry fnFramePrefixStack
  codegenLabelDisciplined codegenEntrySim codegenEntryRel codegenSymRel
  symFrameBoundary symFrameInst symFrameInvoke symFrameControl
  asmDataEnv asmSymBridge asmSymSem asmSem
  fnBlockBody fnBlockBodySteps fnFrameBoundaryInvoke fnFrameDeepInvoke frameViewFacts frameRel contextCodegenRel
  stackPlanTypes stackPlanGen planExec stackOpSim fnBlockBodyClasses unitShapeDefs
  frameJointTrace frameJointTransition frameOriginHistory
  venomExecSemantics venomState venomInst fcgDefs
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

Theorem frame_stack_symbolic_plan_pop:
  frame_stack_symbolic_plan env rpolicy unit cpl prog vs0 es0 (f::stk) callee entry cra crest cmem csentry cret csrest clabs /\
  focus_s7_symbolic_context unit prog /\
  fn_return_state_rel unit.cu_context cpl callee send entry asr /\
  FLOOKUP (build_offset_to_pc prog) (w2n cra) = SOME asr.as_pc /\
  asr.as_stack = REVERSE rv.iret_values ++ crest /\
  asm_sym_rel prog env asr ssr /\
  ssr.sym_stack = MAP Val (REVERSE rv.iret_values) ++ csrest /\
  (!b. context_spill_byte cpl b /\ ~closure_spill_byte unit.cu_context cpl callee.fn_name b ==> FLOOKUP ssr.sym_mem_labels b = FLOOKUP clabs b) /\
  (!b. b IN FDOM ssr.sym_mem_labels ==> context_spill_byte cpl b) /\
  bind_outputs f.cf_inst.inst_outputs rv.iret_values (adopt_return_fmp rv (merge_callee_state f.cf_state send)) = SOME resumed ==>
  ?n fin sfin caller_entry ra rest mem0 sentry ret srest labs0.
    0 < n /\
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n asr = AsmOK fin /\
    sym_steps prog env n ssr = SymOK sfin /\
    frame_stack_symbolic_plan env rpolicy unit cpl prog vs0 es0 stk f.cf_fn caller_entry ra rest mem0 sentry ret srest labs0 /\
    active_frame_symbolic_plan env rpolicy unit cpl prog f.cf_fn (resumed with vs_inst_idx := SUC f.cf_state.vs_inst_idx) fin ra rest mem0 ret srest labs0 sfin
Proof
  strip_tac >>
  qpat_x_assum `frame_stack_symbolic_plan _ _ _ _ _ _ _ (_::_) _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [frame_stack_symbolic_plan_cases]) >>
  gvs[] >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule_all body_plan_inv_step >>
  disch_then (qx_choosel_then [`next_ops`, `next_ps`, `next_rest`] strip_assume_tac) >>
  `!at. MEM at next_ps.ps_stack \/ at IN FDOM next_ps.ps_spilled ==>
     operand_val (frame_view f.cf_fn ra resumed) (SND (compute_label_offsets prog)) at =
     operand_val (frame_view f.cf_fn ra resumed) (SND (compute_label_offsets prog)) (normalize_operand dfg [] at)` by
    (`dfg = dfg_build_function f.cf_fn /\
      (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
        operand_val (frame_view f.cf_fn ra f.cf_state) (SND (compute_label_offsets prog)) at =
        operand_val (frame_view f.cf_fn ra f.cf_state) (SND (compute_label_offsets prog)) (normalize_operand dfg [] at))` by
       (gvs[body_plan_inv_def] >> metis_tac[]) >>
     drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = SOME _`) alias_invoke_return_preserve >>
     disch_then (drule_at (Pat `bind_outputs _ _ _ = SOME _`)) >>
     disch_then (qspecl_then [`SND (compute_label_offsets prog)`, `ra`] mp_tac) >>
     gvs[] >> disch_tac >> gen_tac >> disch_tac >>
     first_x_assum irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all body_operands_le_16 >> strip_tac >>
  drule_all invoke_plan_decompose >>
  disch_then (qx_choosel_then [`decomp_iops`, `decomp_prepared`, `decomp_rops`,
    `decomp_arranged`, `consumed`, `pushed`, `decomp_ret_lbl`, `called`,
    `pops`, `popped`, `opts`, `swapped`] strip_assume_tac) >>
  gvs[] >>
  qpat_assum `body_plan_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [body_plan_inv_def]) >>
  `ordered_spill_regions cpl.cp_regions /\ ctx_wf unit.cu_context` by
    fs[codegen_context_obligations_def, context_plan_layout_wf_def] >>
  `callee.fn_name = nm` by
    (drule fmpAnalysisPropsTheory.lookup_function_name >> simp[]) >>
  `fn_directly_calls unit.cu_context f.cf_fn.fn_name callee.fn_name` by
    (qpat_x_assum `callee.fn_name = nm` SUBST1_TAC >>
     drule_all invoke_direct_call >> simp[]) >>
  `~TC (fn_directly_calls unit.cu_context) f.cf_fn.fn_name f.cf_fn.fn_name` by
    (drule_all invoke_context_no_cycle >> simp[]) >>
  drule_at (Pat `emit_input_plan _ _ _ _ = _`) invoke_entry_structural_marked >>
  disch_then drule_all >> strip_tac >>
  `LENGTH rv.iret_values = LENGTH f.cf_inst.inst_outputs` by
    (qpat_x_assum `bind_outputs _ _ _ = SOME _` mp_tac >> simp[bind_outputs_def] >> IF_CASES_TAC >> simp[]) >>
  `ssa_form f.cf_fn` by fs[codegen_ready_fn_def] >>
  `sms.sym_mem_labels = sms.sym_mem_labels` by simp[] >>
  `ssr.sym_stack = MAP Val (REVERSE rv.iret_values) ++ (saved_sym ++ srest)` by simp[APPEND_ASSOC] >>
  drule_all (Q.INST [`scas` |-> `sms`] sym_invoke_return_frame_from_callee) >> strip_tac >>
  `ALL_DISTINCT f.cf_inst.inst_outputs` by
    metis_tac[genBlockSimTheory.codegen_ready_inst_outputs_distinct] >>
  `EVERY (\x. ~retpc_var f.cf_fn x) f.cf_inst.inst_outputs` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >>
     irule noncopy_output_not_retpc >>
     conj_tac >- fs[codegen_ready_fn_def] >>
     qexists `f.cf_inst` >> simp[]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword (:256)
     | SORestore off => off < dimword (:256) | _ => T) (pops ++ opts)` by
    fs[EVERY_APPEND] >>
  `fn_return_state_rel unit.cu_context cpl callee send mid asr` by
    fs[fn_return_state_rel_def] >>
  `asm_block_at prog asr.as_pc
     (execute_plan cpl.cp_initial_fmp (SOLabel cret :: pops ++ opts))` by
    (`asr.as_pc = ast.as_pc +
        LENGTH (execute_plan cpl.cp_initial_fmp (decomp_iops ++ decomp_rops)) + 3` by decide_tac >>
     pop_assum SUBST1_TAC >>
     pure_rewrite_tac[APPEND] >>
     irule invoke_return_block >> qexists `nm` >>
     qpat_assum `asm_block_at prog ast.as_pc _` mp_tac >>
     simp[APPEND_ASSOC]) >>
  `asm_static_wf prog` by fs[focus_s7_symbolic_context_def] >>
  `?fin sfin.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog
      (1 + LENGTH (execute_plan cpl.cp_initial_fmp (pops ++ opts))) asr = AsmOK fin /\
    fn_frame_inv unit.cu_context cpl (SND (compute_label_offsets prog)) f.cf_fn ra rest mem0
      (release_dead_spills (live_vars_at liveness f.cf_state.vs_current_bb (k + 1)) swapped) resumed fin /\
    fin.as_pc = asr.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp (SOLabel cret :: (pops ++ opts))) /\
    sym_steps prog env (1 + LENGTH (execute_plan cpl.cp_initial_fmp (pops ++ opts))) ssr = SymOK sfin /\
    sym_frame_inv prog env unit.cu_context cpl f.cf_fn ret srest labs0
      (release_dead_spills (live_vars_at liveness f.cf_state.vs_current_bb (k + 1)) swapped) fin sfin` by
    (irule sym_invoke_return_frame_numeric >>
     simp[] >>
     qpat_assum `fn_frame_inv _ _ _ _ _ _ _ arranged f.cf_state mid` (irule_at Any) >>
     qpat_assum `bind_outputs _ _ _ = SOME resumed` (irule_at Any) >>
     qpat_assum `sym_frame_inv _ _ _ _ _ _ _ _ called asr ssr` (irule_at Any) >>
     qpat_assum `fresh_label _ _ = (cret,called)` (irule_at Any) >>
     qpat_assum `(if _ then _ else _) = (opts,swapped)` (irule_at Any) >>
     qpat_assum `(if _ then _ else _) = (pops,popped)` (irule_at Any) >>
     qpat_assum `MEM r cpl.cp_regions` (irule_at Any) >>
     qpat_assum `mid.as_stack = REVERSE args ++ saved ++ rest` (irule_at Any) >>
     qpat_assum `fn_return_state_rel _ _ _ _ mid asr` (irule_at Any) >>
     gvs[APPEND]) >>
  `resumed.vs_labels = f.cf_state.vs_labels /\
   resumed.vs_call_ctx = f.cf_state.vs_call_ctx /\
   resumed.vs_current_bb = f.cf_state.vs_current_bb` by
    (drule invoke_bind_frame_fields >>
     Cases_on `rv.iret_adopt_fmp` >>
     simp[adopt_return_fmp_def, merge_callee_state_def] >>
     disch_then (fn th => once_rewrite_tac [th]) >> simp[]) >>
  `~is_terminator f.cf_inst.inst_opcode /\
   (!j. ~revert_forward_pair bb k j)` by
    (conj_tac >- simp[is_terminator_def] >>
     gen_tac >> disch_tac >>
     qpat_x_assum `revert_forward_pair bb k j` mp_tac >>
     simp[revert_forward_pair_def, get_instruction_def]) >>
  `fin.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp
     (decomp_iops ++ decomp_rops ++
      [SOPushLabel cret; SOPushLabel nm; SOEmit "JUMP"; SOLabel cret] ++ pops ++ opts))` by
    (fs[execute_plan_append, execute_plan_def, exec_stack_op_def] >> decide_tac) >>
  drule body_plan_advance_core >>
  qpat_assum `bb.bb_label = _` (fn th => rewrite_tac [th]) >>
  disch_then (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = SOME _`)) >>
  disch_then (qspecl_then [`resumed`, `next_rest`, `fin`] mp_tac) >>
  impl_tac
  >- (simp[non_param_insts_def, APPEND_ASSOC] >>
      metis_tac[non_param_insts_def, APPEND_ASSOC]) >>
  strip_tac >>
  qexistsl_tac [`1 + LENGTH (execute_plan cpl.cp_initial_fmp (pops ++ opts))`,
    `fin`, `sfin`] >>
  simp[] >>
  qpat_assum `frame_stack_symbolic_plan _ _ _ _ _ _ _ stk _ _ _ _ _ _ _ _ _`
    (irule_at Any) >>
  pure_rewrite_tac[active_frame_symbolic_plan_def] >>
  qpat_assum `f.cf_state.vs_inst_idx = k` (fn th => rewrite_tac [th]) >>
  first_assum (irule_at Any) >>
  first_assum ACCEPT_TAC
QED

Theorem active_frame_symbolic_return_progress:
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
    (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginResume fuel fn inst s retv send post))
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
  simp[joint_transition_return] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `frame_stack_symbolic_plan _ _ _ _ _ _ _ (_::_) _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [frame_stack_symbolic_plan_cases]) >>
  gvs[] >> FAIL_TAC "return snapshot inversion"
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


