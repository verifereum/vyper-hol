(*
 * The rest of a function's run from inside one of its blocks, on the
 * symbolic machine: fnBlockBody's block_body_frame_sim with the symbolic
 * premises and conclusions added, over the same n steps.  Shared by the
 * two steps of the symbolic fuel induction (symFnStep).
 *
 * TOP-LEVEL:
 *   sym_body_result           - fnBlockBody's conclusion about a run
 *                               result, with the symbolic run
 *   sym_block_body_frame_sim  - the rest of the run, simulated
 *)
Theory symBlockBody
Ancestors
  symFrameBoundary symFrameControl symFrameInvoke symFrameInst symFnSimSpec
  symBodyCanonicalSelected
  codegenSymRel fnBlockBody fnBlockBodySteps fnSimSpec asmSymBridge
  asmSymSem frameRel contextCodegenRel codegenRel unitShapeDefs
  venomExecSemantics venomState venomInst fnPlanLineageEntryProduction symBodyAlgebra symBlockBodyOwnCore symBodyCanonicalClient symBodyStaticFacts symBodyOrdinaryOwn symBodyTerminalOwn symBodyInvokeCanonical symBodyJumpOwn symFrameBoundaryPairing asmSymOwnStep symBodyJumpPointwise

(* block_body_frame_sim's conclusion (fnBlockBodySteps' body_result_simple) with
   the symbolic run from ss over the same n steps: it ends where the
   concrete run halts, reverts or faults, and at an internal return it is
   OK, related, and holds the returned values as words above srest, with
   the memory labels outside the function's closure those of labs0. *)
Definition sym_body_result_def:
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
      as ss res <=>
    (!vs'. res = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps prog env n ss)) /\
    (!a vs'. res = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps prog env n ss)) /\
    (!rv vs'. res = IntRet rv vs' ==>
       ?n as' ss'. asm_steps lo o2pc prog n as = AsmOK as' /\
               as'.as_pc = pc_ret /\
               as'.as_stack = REVERSE rv.iret_values ++ rest /\
               context_memory_rel cpl vs'.vs_memory as'.as_memory /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    read_byte b as'.as_memory = read_byte b mem0) /\
               shared_state_rel vs' as' /\
               sym_steps prog env n ss = SymOK ss' /\
               asm_sym_rel prog env as' ss' /\
               ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
               (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))
End

(* Symbolic execution at supplied label offsets and own-code bytes. *)
Definition sym_body_result_own_def:
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
      as ss res <=>
    (!vs'. res = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps_mode allow_own prog env own n ss)) /\
    (!a vs'. res = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps_mode allow_own prog env own n ss)) /\
    (!rv vs'. res = IntRet rv vs' ==>
       ?n as' ss'. asm_steps lo o2pc prog n as = AsmOK as' /\
               as'.as_pc = pc_ret /\
               as'.as_stack = REVERSE rv.iret_values ++ rest /\
               context_memory_rel cpl vs'.vs_memory as'.as_memory /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    read_byte b as'.as_memory = read_byte b mem0) /\
               shared_state_rel vs' as' /\
               sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
               asm_sym_rel_own lo prog env own as' ss' /\
               ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
               (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))
End

Theorem sym_body_result_error:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss e.
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (Error e)
Proof
  simp[sym_body_result_def]
QED

Theorem sym_body_result_ok:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss vs.
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (OK vs)
Proof
  simp[sym_body_result_def]
QED

Theorem sym_body_result_halt:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss vs.
  (?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
     venom_asm_terminal_rel vs as' /\
     sym_terminal (sym_steps prog env n ss)) ==>
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (Halt vs)
Proof
  simp[sym_body_result_def]
QED

Theorem sym_body_result_abort:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss a vs.
  (?n as'.
     ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
      (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
     venom_asm_terminal_rel vs as' /\
     sym_terminal (sym_steps prog env n ss)) ==>
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (Abort a vs)
Proof
  simp[sym_body_result_def]
QED

Theorem sym_body_result_intret:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss rv vs.
  (?n as' ss'.
     asm_steps lo o2pc prog n as = AsmOK as' /\
     as'.as_pc = pc_ret /\
     as'.as_stack = REVERSE rv.iret_values ++ rest /\
     context_memory_rel cp vs.vs_memory as'.as_memory /\
     (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
          read_byte b as'.as_memory = read_byte b mem0) /\
     shared_state_rel vs as' /\
     sym_steps prog env n ss = SymOK ss' /\ asm_sym_rel prog env as' ss' /\
     ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
     (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
          FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
     (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)) ==>
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (IntRet rv vs)
Proof
  simp[sym_body_result_def]
QED

Theorem sym_body_result_prefix:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as as1 ss ss1 n res.
  asm_steps lo o2pc prog n as = AsmOK as1 /\
  sym_steps prog env n ss = SymOK ss1 /\
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as1 ss1 res ==>
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss res
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (SRULE [sym_steps_mode_def]
    (Q.SPEC `F` sym_body_runs_prefix_mode)) >>
  disch_then assume_tac >>
  gvs[sym_body_result_def] >> rpt conj_tac >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`n' + n`, `as'`] >> simp[] >> metis_tac[]
QED

Theorem sym_body_result_exec:
  !fuel ctx bb vs lo o2pc prog env cp fn mem0 pc_ret rest srest labs0 as ss.
  (!t. exec_block fuel ctx bb vs <> OK t) /\
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (exec_block fuel ctx bb vs) ==>
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  rpt gen_tac >> strip_tac >> simp[block_rest_def] >>
  Cases_on `exec_block fuel ctx bb vs` >> gvs[]
QED

Theorem sym_frame_inv_plan_transport:
  !ps' ps prog env ctx cp fn ret srest labs0 cs ss.
  ps'.ps_stack = ps.ps_stack /\ ps'.ps_spilled = ps.ps_spilled /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps cs ss ==>
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps' cs ss
Proof
  simp[sym_frame_inv_def] >> metis_tac[sym_kinds_ok_plan_transport]
QED

Theorem codegen_sym_code_end_label:
  codegen_assembly rpolicy unit = SOME prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) ==>
  sym_data_label prog env "code_end"
Proof
  MATCH_ACCEPT_TAC codegen_sym_code_end_label_kernel
QED

Theorem data_segment_asm_header:
  !segs ds. MEM ds segs ==>
    MEM (AsmDataHeader ds.ds_label) (data_segment_asm segs)
Proof
  MATCH_ACCEPT_TAC data_segment_asm_header_kernel
QED

Theorem codegen_sym_runtime_begin_label:
  codegen_assembly rpolicy unit = SOME prog /\
  sym_unit_static_ok unit /\ MEM fn unit.cu_context.ctx_functions /\
  MEM inst (fn_insts fn) /\ MEM (Label "runtime_begin") inst.inst_operands /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) ==>
  sym_data_label prog env "runtime_begin"
Proof
  MATCH_ACCEPT_TAC codegen_sym_runtime_begin_label_kernel
QED

Theorem placed_nonentry_sym_code_label:
  !bb fn liveness dfg cfg ps ops ps' prog pc initial_fmp.
  bb <> HD fn.fn_blocks /\
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') /\
  asm_block_at prog pc (execute_plan initial_fmp ops) ==>
  MEM (AsmLabel bb.bb_label) prog
Proof
  MATCH_ACCEPT_TAC placed_nonentry_sym_code_label_kernel
QED

Theorem placed_revert_sym_code_label:
  asm_block_at prog pc (execute_plan initial_fmp revert_postamble) ==>
  MEM (AsmLabel "revert") prog
Proof
  MATCH_ACCEPT_TAC placed_revert_sym_code_label_kernel
QED

Theorem sym_body_ordinary_ok:
  !fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
   ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv ra pc_ret
   rest mem0 inst vs1 env ret srest labs0 ss.
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
  ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  (inst.inst_opcode = LOG ==>
     ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
  step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ?ops ps' rest' n as1 ss1.
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\
    rest_ops = ops ++ rest' /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
    sym_steps prog env n ss = SymOK ss1 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1
Proof
  rpt gen_tac >> strip_tac >>
  `as.as_code = vs.vs_code` by
    gvs[body_inv_def, fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
  `sym_data_label prog env "code_end"` by
    (irule codegen_sym_code_end_label_kernel >> gvs[body_inv_def] >> metis_tac[]) >>
  `(MEM (Label "runtime_begin") inst.inst_operands ==>
    sym_data_label prog env "runtime_begin")` by
    (strip_tac >> irule codegen_sym_runtime_begin_label_kernel >>
     drule body_inv_facts >> strip_tac >> drule_all body_inv_inst >> strip_tac >>
     gvs[body_inv_def] >> metis_tac[]) >>
  gvs[body_inv_reloc_specialize] >>
  `asm_data_env_lo_ok (SND (compute_label_offsets prog)) prog env vs.vs_code` by
    gvs[sym_frame_inv_def, asm_data_env_lo_ok_canonical, asm_sym_rel_def] >>
  `sym_frame_inv_own (SND (compute_label_offsets prog)) prog env vs.vs_code
    ctx cpl fn ret srest labs0 ps as ss` by simp[sym_frame_inv_canonical_own] >>
  drule_at (Pat `body_inv_reloc`) (SRULE [sym_steps_mode_def] (Q.INST [`allow_own` |-> `F`, `own` |-> `vs.vs_code`]
    (SPEC_ALL sym_body_ordinary_ok_own_kernel))) >>
  strip_tac >> gvs[sym_frame_inv_canonical_own] >> metis_tac[]
QED

Theorem sym_body_gas_ok:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = GAS /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ?ops ps' rest' n as1 ss1.
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\
    rest_ops = ops ++ rest' /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
    sym_steps prog env n ss = SymOK ss1 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1
Proof
  strip_tac >>
  `as.as_code = vs.vs_code` by
    gvs[body_inv_def, fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
  gvs[body_inv_reloc_specialize] >>
  `asm_data_env_lo_ok (SND (compute_label_offsets prog)) prog env vs.vs_code` by
    gvs[sym_frame_inv_def, asm_data_env_lo_ok_canonical, asm_sym_rel_def] >>
  `sym_frame_inv_own (SND (compute_label_offsets prog)) prog env vs.vs_code
    ctx cpl fn ret srest labs0 ps as ss` by simp[sym_frame_inv_canonical_own] >>
  drule_at (Pat `body_inv_reloc`) (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `own` |-> `vs.vs_code`] sym_body_gas_ok_own_kernel)) >>
  strip_tac >> gvs[sym_frame_inv_canonical_own] >> metis_tac[]
QED

Theorem invoke_operands_wf_shape:
  !inst. invoke_operands_wf inst ==>
    ?nm args. inst.inst_operands = Label nm :: args
Proof
  MATCH_ACCEPT_TAC invoke_operands_wf_shape_kernel
QED

Theorem sym_body_invoke_step:
  gen_fn_sim_at_simple fuel /\ sym_fn_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = INVOKE /\ LENGTH (compute_operands inst) <= 16 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ?ops ps' rest'.
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\
    rest_ops = ops ++ rest' /\
    (!vs1. step_inst fuel ctx inst vs = OK vs1 ==>
      ?n as1 ss1.
        asm_steps lo o2pc prog n as = AsmOK as1 /\
        fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
        as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
        sym_steps prog env n ss = SymOK ss1 /\
        sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1) /\
    (!vs1. step_inst fuel ctx inst vs = Halt vs1 ==>
      sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
        as ss (Halt vs1)) /\
    (!a vs1. step_inst fuel ctx inst vs = Abort a vs1 ==>
      sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
        as ss (Abort a vs1))
Proof
  simp_tac (srw_ss()) [sym_body_result_def] >>
  MATCH_ACCEPT_TAC sym_body_invoke_step_canonical_kernel
QED

Theorem sym_body_halt_step:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = Halt vs1 /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (Halt vs1)
Proof
  strip_tac >>
  `as.as_code = vs.vs_code` by
    gvs[body_inv_def, fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
  gvs[body_inv_reloc_specialize] >>
  `asm_data_env_lo_ok (SND (compute_label_offsets prog)) prog env vs.vs_code` by
    gvs[sym_frame_inv_def, asm_data_env_lo_ok_canonical, asm_sym_rel_def] >>
  `sym_frame_inv_own (SND (compute_label_offsets prog)) prog env vs.vs_code
    ctx cpl fn ret srest labs0 ps as ss` by simp[sym_frame_inv_canonical_own] >>
  drule_at (Pat `body_inv_reloc`) (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `own` |-> `vs.vs_code`] sym_body_halt_step_own_kernel)) >>
  simp[sym_body_result_def] >> metis_tac[]
QED

Theorem sym_body_abort_step:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = Abort a vs1 /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (Abort a vs1)
Proof
  strip_tac >>
  `as.as_code = vs.vs_code` by
    gvs[body_inv_def, fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
  `(inst.inst_opcode = ASSERT ==> MEM (AsmLabel "revert") prog)` by
    (drule body_inv_facts >> strip_tac >> drule_all body_inv_inst >> strip_tac >>
     drule_all body_inv_static >> strip_tac >>
     gvs[body_inv_def] >> metis_tac[placed_revert_sym_code_label_kernel]) >>
  gvs[body_inv_reloc_specialize] >>
  `asm_data_env_lo_ok (SND (compute_label_offsets prog)) prog env vs.vs_code` by
    gvs[sym_frame_inv_def, asm_data_env_lo_ok_canonical, asm_sym_rel_def] >>
  `sym_frame_inv_own (SND (compute_label_offsets prog)) prog env vs.vs_code
    ctx cpl fn ret srest labs0 ps as ss` by simp[sym_frame_inv_canonical_own] >>
  drule_at (Pat `body_inv_reloc`) (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `own` |-> `vs.vs_code`] sym_body_abort_step_own_kernel)) >>
  simp[sym_body_result_def] >> metis_tac[]
QED

Theorem sym_body_ret_step:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = IntRet rv vs1 /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (IntRet rv vs1)
Proof
  strip_tac >>
  `as.as_code = vs.vs_code` by
    gvs[body_inv_def, fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
  gvs[body_inv_reloc_specialize] >>
  `asm_data_env_lo_ok (SND (compute_label_offsets prog)) prog env vs.vs_code` by
    gvs[sym_frame_inv_def, asm_data_env_lo_ok_canonical, asm_sym_rel_def] >>
  `sym_frame_inv_own (SND (compute_label_offsets prog)) prog env vs.vs_code
    ctx cpl fn ret srest labs0 ps as ss` by simp[sym_frame_inv_canonical_own] >>
  drule_at (Pat `body_inv_reloc`) (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `own` |-> `vs.vs_code`] sym_body_ret_step_own_kernel)) >>
  simp[sym_body_result_def, asm_sym_rel_own_canonical] >> metis_tac[]
QED

Theorem body_inv_rest_placed:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 ==>
  asm_block_at prog as.as_pc (execute_plan cpl.cp_initial_fmp rest_ops)
Proof
  simp[body_inv_reloc_specialize] >> metis_tac[body_inv_rest_placed_reloc_kernel]
QED

Theorem sym_body_revert_abort:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  revert_forward_pair bb k j /\ exec_block fuel ctx bb vs = Abort a vs1 /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (Abort a vs1)
Proof
  strip_tac >>
  `as.as_code = vs.vs_code` by
    gvs[body_inv_def, fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
  `MEM (AsmLabel "revert") prog` by
    (drule body_inv_facts >> strip_tac >>
     gvs[body_inv_def] >> metis_tac[placed_revert_sym_code_label_kernel]) >>
  gvs[body_inv_reloc_specialize] >>
  `asm_data_env_lo_ok (SND (compute_label_offsets prog)) prog env vs.vs_code` by
    gvs[sym_frame_inv_def, asm_data_env_lo_ok_canonical, asm_sym_rel_def] >>
  `sym_frame_inv_own (SND (compute_label_offsets prog)) prog env vs.vs_code
    ctx cpl fn ret srest labs0 ps as ss` by simp[sym_frame_inv_canonical_own] >>
  drule_at (Pat `body_inv_reloc`) (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `own` |-> `vs.vs_code`] sym_body_revert_abort_own_kernel)) >>
  simp[sym_body_result_def] >> metis_tac[]
QED

Theorem sym_body_revert_step:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\ revert_forward_pair bb k j /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  (!t. exec_block fuel ctx bb vs <> OK t) /\
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (exec_block fuel ctx bb vs)
Proof
  strip_tac >>
  `vs.vs_inst_idx = k` by gvs[body_inv_def] >>
  `revert_forward_pair bb vs.vs_inst_idx j` by metis_tac[] >>
  drule fnBlockBodyClassesTheory.rf_exec_block_cases >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >> strip_tac
  >- (simp[] >> drule_all sym_body_revert_abort >> simp[]) >>
  simp[sym_body_result_error]
QED

Theorem body_step_entry_inv:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst vs = OK vs1 /\
  ~vs1.vs_halted ==>
  fn_entry_inv Inv ctx fn vs1
Proof
  simp[body_inv_reloc_specialize] >> metis_tac[body_step_entry_inv_reloc_kernel]
QED

Theorem body_jump_entry_lineage:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  MEM t (cfg_succs_of cfg bb.bb_label) /\
  dfs_block_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) t ps_tdfs ==>
  lineage_entry liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label t
    (ps_tdfs with <| ps_stack := ps_after.ps_stack;
                     ps_spilled := ps_after.ps_spilled |>)
Proof
  simp[body_inv_reloc_specialize] >> metis_tac[body_jump_entry_lineage_reloc_kernel]
QED

Theorem body_jump_entry_frame:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  ps_tdfs.ps_alloc.sa_spill_base = spill_base /\
  ps_tdfs.ps_alloc.sa_next_offset <= ps_end.ps_alloc.sa_next_offset /\
  fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 ==>
  fn_frame_inv ctx cpl lo fn ra rest mem0
    (ps_tdfs with <| ps_stack := ps_after.ps_stack;
                     ps_spilled := ps_after.ps_spilled |>) vs1 as1
Proof
  simp[body_inv_reloc_specialize] >> metis_tac[body_jump_entry_frame_reloc_kernel]
QED

Theorem body_jump_entry:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst vs = OK vs1 /\ vs1 = jump_to t vs /\
  MEM t (get_successors inst) /\
  fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
  (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
    operand_val (frame_view fn ra vs1) lo at =
    operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
  FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc ==>
  ?tbb ps_tdfs tops tafter pe.
    pe = ps_tdfs with <| ps_stack := ps_after.ps_stack;
                         ps_spilled := ps_after.ps_spilled |> /\
    ~vs1.vs_halted /\ vs1.vs_labels = vs.vs_labels /\
    vs1.vs_call_ctx = vs.vs_call_ctx /\ vs1.vs_current_bb = t /\
    vs1.vs_prev_bb = SOME bb.bb_label /\ tbb.bb_label = t /\
    lookup_block vs1.vs_current_bb fn.fn_blocks = SOME tbb /\
    tbb <> HD fn.fn_blocks /\ fn_reachable fn tbb.bb_label /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      bb.bb_label tbb.bb_label pe /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      vs1.vs_current_bb ps_tdfs /\
    generate_block_plan liveness dfg cfg fn tbb ps_tdfs = SOME (tops,tafter) /\
    asm_block_at prog as1.as_pc (execute_plan cpl.cp_initial_fmp tops) /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 pe vs1 as1 /\
    fn_entry_inv Inv ctx fn vs1 /\
    (!at. MEM at pe.ps_stack \/ at IN FDOM pe.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at))
Proof
  rewrite_tac[body_inv_reloc_specialize] >> strip_tac >>
  drule_all body_jump_entry_reloc_kernel >> simp[]
QED

Theorem sym_body_jump_continue:
  gen_fn_frame_sim_at_simple fuel /\ sym_fn_frame_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst vs = OK vs1 /\ vs1 = jump_to t vs /\
  MEM t (get_successors inst) /\
  asm_steps lo o2pc prog n as = AsmOK as1 /\
  fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
  (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
    operand_val (frame_view fn ra vs1) lo at =
    operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
  FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_steps prog env n ss = SymOK ss1 /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps_after as1 ss1 ==>
  ~vs1.vs_halted /\
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (run_blocks fuel ctx fn vs1)
Proof
  strip_tac >> drule_all body_jump_entry >> strip_tac >>
  conj_tac >- simp[] >>
  irule sym_body_result_prefix >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  `sym_frame_inv prog env ctx cpl fn ret srest labs0 pe as1 ss1` by
    (irule sym_frame_inv_plan_transport >> goal_assum (drule_at Any) >> simp[]) >>
  qhdtm_assum `sym_fn_frame_sim_at`
    (mp_tac o REWRITE_RULE [sym_fn_frame_sim_at_def]) >>
  pure_rewrite_tac [sym_body_result_def] >>
  disch_then (drule_at (Pat `sym_frame_inv`)) >>
  disch_then (drule_at (Pat `fn_frame_inv`)) >>
  disch_then (drule_at (Pat `generate_block_plan`)) >>
  disch_then (drule_at (Pat `lineage_entry`)) >>
  disch_then irule >>
  qhdtm_assum `body_inv` (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  gvs[] >> rpt conj_tac >> metis_tac[]
QED

Theorem body_succ_sym_label:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\ MEM t (get_successors inst) ==>
  ?off pc. FLOOKUP lo t = SOME off /\ off < dimword (:256) /\
    FLOOKUP o2pc off = SOME pc /\ MEM (AsmLabel t) prog
Proof
  rewrite_tac[body_inv_reloc_specialize] >> strip_tac >>
  drule_at (Pat `body_inv_reloc`) body_succ_sym_label_reloc_kernel >>
  metis_tac[placed_nonentry_sym_code_label_kernel]
QED

Theorem jmp_wf_operands:
  inst_wf inst /\ inst.inst_opcode = JMP ==>
  ?target. inst.inst_operands = [Label target] /\ inst.inst_outputs = [] /\
    is_terminator inst.inst_opcode /\ MEM target (get_successors inst)
Proof
  MATCH_ACCEPT_TAC jmp_wf_operands_kernel
QED

Theorem sym_body_jmp_prefix:
  gen_fn_frame_sim_at_simple fuel /\ sym_fn_frame_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JMP /\ step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ?n as1 ss1 t off.
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    sym_steps prog env n ss = SymOK ss1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps_after as1 ss1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    is_terminator inst.inst_opcode /\ MEM t (get_successors inst) /\
    vs1 = jump_to t vs /\
    FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc
Proof
  strip_tac >> drule_all body_inv_inst >> strip_tac >>
  drule_all jmp_wf_operands >> strip_tac >>
  `!t. MEM t (get_successors inst) ==> MEM (AsmLabel t) prog` by
    (rpt strip_tac >> drule_all body_succ_sym_label >> metis_tac[]) >>
  `as.as_code = vs.vs_code` by
    gvs[body_inv_def, fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
  gvs[body_inv_reloc_specialize] >>
  `asm_data_env_lo_ok (SND (compute_label_offsets prog)) prog env vs.vs_code` by
    gvs[sym_frame_inv_def, asm_data_env_lo_ok_canonical, asm_sym_rel_def] >>
  `sym_frame_inv_own (SND (compute_label_offsets prog)) prog env vs.vs_code
    ctx cpl fn ret srest labs0 ps as ss` by simp[sym_frame_inv_canonical_own] >>
  drule_at (Pat `body_inv_reloc`) (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `own` |-> `vs.vs_code`] sym_body_jmp_prefix_pointwise)) >>
  simp[sym_frame_inv_canonical_own] >>
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `sym_frame_inv`)) >> simp[] >>
  strip_tac >> qexistsl [`n`, `as1`, `ss1`, `t`, `off`] >> gvs[] >> metis_tac[]
QED

Theorem jnz_wf_operands:
  inst_wf inst /\ inst_shape_ok inst /\ inst.inst_opcode = JNZ ==>
  ?c l1 l2. inst.inst_operands = [c; Label l1; Label l2] /\
    inst.inst_outputs = [] /\ ~is_label_operand c /\
    is_terminator inst.inst_opcode /\ MEM c (compute_operands inst) /\
    MEM l1 (get_successors inst) /\ MEM l2 (get_successors inst)
Proof
  MATCH_ACCEPT_TAC jnz_wf_operands_kernel
QED

Theorem jnz_condition_frame_view:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = JNZ /\ inst.inst_operands = [c; Label l1; Label l2] ==>
  eval_operand c vs = eval_operand c (frame_view fn ra vs)
Proof
  MATCH_ACCEPT_TAC jnz_condition_frame_view_kernel
QED

Theorem sym_body_jnz_prefix:
  gen_fn_frame_sim_at_simple fuel /\ sym_fn_frame_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JNZ /\ step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ?n as1 ss1 t off.
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    sym_steps prog env n ss = SymOK ss1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps_after as1 ss1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    is_terminator inst.inst_opcode /\ MEM t (get_successors inst) /\
    vs1 = jump_to t vs /\
    FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc
Proof
  strip_tac >> drule_all body_inv_inst >> strip_tac >>
  drule_all body_inv_static >> strip_tac >>
  drule_all jnz_wf_operands >> strip_tac >>
  `!c l1 l2. inst.inst_operands = [c; Label l1; Label l2] ==>
    eval_operand c vs = eval_operand c (frame_view fn ra vs)` by
    (rpt strip_tac >> irule jnz_condition_frame_view >>
     drule body_inv_facts >> strip_tac >> simp[] >> metis_tac[]) >>
  `!t. MEM t (get_successors inst) ==> MEM (AsmLabel t) prog` by
    (rpt strip_tac >> drule_all body_succ_sym_label >> metis_tac[]) >>
  `as.as_code = vs.vs_code` by
    gvs[body_inv_def, fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
  gvs[body_inv_reloc_specialize] >>
  `asm_data_env_lo_ok (SND (compute_label_offsets prog)) prog env vs.vs_code` by
    gvs[sym_frame_inv_def, asm_data_env_lo_ok_canonical, asm_sym_rel_def] >>
  `sym_frame_inv_own (SND (compute_label_offsets prog)) prog env vs.vs_code
    ctx cpl fn ret srest labs0 ps as ss` by simp[sym_frame_inv_canonical_own] >>
  drule_at (Pat `body_inv_reloc`) (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `own` |-> `vs.vs_code`] sym_body_jnz_prefix_pointwise)) >>
  simp[sym_frame_inv_canonical_own] >>
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `sym_frame_inv`)) >> simp[] >>
  strip_tac >> qexistsl [`n`, `as1`, `ss1`, `t`, `off`] >> gvs[] >> metis_tac[]
QED

Theorem sym_body_jmp_step:
  gen_fn_frame_sim_at_simple fuel /\ sym_fn_frame_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JMP /\ step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ~vs1.vs_halted /\
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (run_blocks fuel ctx fn vs1)
Proof
  strip_tac >> drule_all sym_body_jmp_prefix >> strip_tac >>
  drule_all sym_body_jump_continue >> simp[]
QED

Theorem sym_body_jnz_step:
  gen_fn_frame_sim_at_simple fuel /\ sym_fn_frame_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JNZ /\ step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ~vs1.vs_halted /\
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (run_blocks fuel ctx fn vs1)
Proof
  strip_tac >> drule_all sym_body_jnz_prefix >> strip_tac >>
  drule_all sym_body_jump_continue >> simp[]
QED

Theorem sym_body_nonterm_prefix:
  gen_fn_sim_at_simple fuel /\ sym_fn_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  (inst.inst_opcode = LOG ==>
    ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
  step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ?prefix' rest' ps' vs' as1 ss1 n.
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix' rest' (SUC k) ps' pc0 vs' as1 Inv
      ra pc_ret rest mem0 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1 /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    sym_steps prog env n ss = SymOK ss1 /\
    block_rest fuel ctx fn bb vs = block_rest fuel ctx fn bb vs' /\
    vs'.vs_call_ctx = vs.vs_call_ctx
Proof
  strip_tac >> drule sym_body_nonterm_prefix_selected_canonical >>
  disch_then (drule_at (Pat `sym_frame_inv`)) >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  simp[] >> (impl_tac >- (strip_tac >> drule_all sym_body_invoke_step_canonical_kernel >> simp[])) >>
  simp[]
QED

Theorem sym_body_out_of_range:
  LENGTH bb.bb_instructions <= vs.vs_inst_idx ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  strip_tac >> drule fnBlockBodyHelpersTheory.exec_block_out_of_range >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  drule block_rest_error >> simp[sym_body_result_error]
QED

Theorem sym_body_terminator:
  gen_fn_frame_sim_at_simple fuel /\ sym_fn_frame_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  strip_tac >> drule_all body_inv_inst >> strip_tac >>
  `vs.vs_inst_idx = k` by gvs[body_inv_def] >>
  `get_instruction bb vs.vs_inst_idx = SOME inst` by metis_tac[] >>
  drule_all fnBlockBodyHelpersTheory.step_ok_terminator_jump >> strip_tac
  >- (drule_all sym_body_jmp_step >> strip_tac >> metis_tac[block_rest_jump])
  >- (drule_all sym_body_jnz_step >> strip_tac >> metis_tac[block_rest_jump]) >>
  gvs[inst_shape_ok_def]
QED

Theorem sym_body_nonok:
  gen_fn_sim_at_simple fuel /\ sym_fn_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = res /\ (!s. res <> OK s) /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  strip_tac >> rewrite_tac [sym_body_result_def] >>
  drule sym_body_nonok_selected_canonical >>
  disch_then (drule_at (Pat `sym_frame_inv`)) >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
  simp[] >> (impl_tac >- (strip_tac >> drule_all sym_body_invoke_step_canonical_kernel >> simp[])) >>
  simp[]
QED

Theorem sym_body_inst_bounds:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst ==>
  LENGTH (compute_operands inst) <= 16 /\
  (inst.inst_opcode = LOG ==>
    ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4)
Proof
  strip_tac >> drule (iffLR body_inv_reloc_specialize) >> strip_tac >>
  drule_all sym_body_inst_bounds_reloc_kernel >> simp[]
QED

Theorem sym_body_revert_result:
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\ revert_forward_pair bb k j /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  strip_tac >> drule_all sym_body_revert_step >> strip_tac >>
  irule sym_body_result_exec >> simp[]
QED

Theorem sym_body_nonterm_result:
  (!m. m < d ==>
    !k prefix_ops rest_ops ps vs as ss.
      m = LENGTH bb.bb_instructions - k /\
      gen_fn_sim_at_simple fuel /\ gen_fn_frame_sim_at_simple fuel /\
      sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel /\
      body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
        growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
        block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
        ra pc_ret rest mem0 /\
      label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
      sym_unit_static_ok unit /\ asm_static_wf prog /\
      (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
      sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
      sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
        as ss (block_rest fuel ctx fn bb vs)) /\
  d = LENGTH bb.bb_instructions - k /\
  gen_fn_sim_at_simple fuel /\ sym_fn_sim_at fuel /\
  gen_fn_frame_sim_at_simple fuel /\ sym_fn_frame_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  (inst.inst_opcode = LOG ==>
    ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
  step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  rewrite_tac [sym_body_result_def] >> strip_tac >>
  drule_at (Pos (el 1)) sym_body_canonical_nonterm_application >>
  disch_then (drule_at (Pat `body_inv`)) >>
  disch_then (drule_at (Pat `sym_frame_inv`)) >> simp[]
QED

Theorem sym_body_run:
  !d k prefix_ops rest_ops ps vs as ss.
    d = LENGTH bb.bb_instructions - k /\
    gen_fn_sim_at_simple fuel /\ gen_fn_frame_sim_at_simple fuel /\
    sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel /\
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
    sym_unit_static_ok unit /\ asm_static_wf prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
    sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
      as ss (block_rest fuel ctx fn bb vs)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`LENGTH bb.bb_instructions`,
    `\(k,prefix_ops,rest_ops,ps,vs,as,ss).
      gen_fn_sim_at_simple fuel /\ gen_fn_frame_sim_at_simple fuel /\
      sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel /\
      body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
        growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
        block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
        ra pc_ret rest mem0 /\ label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
      sym_unit_static_ok unit /\ asm_static_wf prog /\
      (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
      sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss`,
    `\(k:num,prefix_ops:stack_op list,rest_ops:stack_op list,ps:plan_state,vs,as,ss).
      sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
        as ss (block_rest fuel ctx fn bb vs)`] mp_tac sym_body_run_client >>
  (impl_tac >-
    (POP_ASSUM_LIST (K all_tac) >>
     simp_tac (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] >>
     rewrite_tac [sym_body_result_def] >>
     rpt gen_tac >> strip_tac >>
     drule_all sym_body_canonical_branches >> simp[CONJ_ASSOC])) >>
  disch_then (qspec_then `(k,prefix_ops,rest_ops,ps,vs,as,ss)` mp_tac) >> simp[]
QED

(* body_inv bundles block_body_frame_sim's premises. *)
Theorem sym_block_body_frame_sim:
  !fuel rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
   ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv ra pc_ret
   rest mem0 env ret srest labs0 ss.
    gen_fn_sim_at_simple fuel /\ gen_fn_frame_sim_at_simple fuel /\
    sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel /\
    body_inv rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    (* ----- The symbolic side ----- *)
    label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
    sym_unit_static_ok unit /\ asm_static_wf prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
      as ss (block_rest fuel ctx fn bb vs)
Proof
  rpt strip_tac >> metis_tac[sym_body_run]
QED
