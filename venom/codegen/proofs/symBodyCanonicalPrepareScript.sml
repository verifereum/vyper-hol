(* Canonical client preparation; INVOKE is an explicit selected-outcome cut. *)
Theory symBodyCanonicalPrepare
Ancestors
  symBodyOrdinaryOwn symBodyTerminalOwn symBodyStaticFacts symBodyJumpPointwise
  symBodyJumpOwn symBodySuccessorPointwise symBlockBodyOwnCore symBodyAlgebra
  symFrameBoundaryPairing symFnSimSpec fnBlockBodySteps fnBlockBodyClasses
  fnBlockBody fnBlockBodyHelpers asmSymOwnStep codegenSymRel asmSymBridge frameRel
  contextCodegenRel codegenRel venomExecSemantics venomInst venomState

(* Parse-time abbreviations, not logical definitions. *)
val _ = Parse.temp_overload_on ("can_A",
  ``\k prefix_ops rest_ops ps vs as ss.
    gen_fn_sim_at_simple fuel /\ gen_fn_frame_sim_at_simple fuel /\
    sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel /\
    body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
    sym_unit_static_ok unit /\ asm_static_wf prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss``);

val _ = Parse.temp_overload_on ("can_R",
  ``\as ss res.
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
               (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))``);

val _ = Parse.temp_overload_on ("can_invoke_outcome",
  ``\k rest_ops ps vs as ss inst.
    ?ops ps' rest'.
      generate_inst_plan liveness dfg (cfg:cfg_analysis) fn inst
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
        ?n as1 ss1. asm_steps lo o2pc prog n as = AsmOK as1 /\
          fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
          as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
          sym_steps prog env n ss = SymOK ss1 /\
          sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1) /\
      (!vs1. step_inst fuel ctx inst vs = Halt vs1 ==> can_R as ss (Halt vs1)) /\
      (!a vs1. step_inst fuel ctx inst vs = Abort a vs1 ==> can_R as ss (Abort a vs1))``);

val _ = Parse.temp_overload_on ("can_invoke_cut",
  ``!k prefix_ops rest_ops ps vs as ss inst.
    can_A k prefix_ops rest_ops ps vs as ss /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = INVOKE /\ LENGTH (compute_operands inst) <= 16 /\
    (?nm args. inst.inst_operands = Label nm :: args) ==>
    can_invoke_outcome k rest_ops ps vs as ss inst``);

Theorem can_facts[local]:
  can_A k prefix_ops rest_ops ps vs as ss ==>
  lo = SND (compute_label_offsets prog) /\
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  asm_data_env_lo_ok lo prog env vs.vs_code /\
  sym_frame_inv_own lo prog env vs.vs_code ctx cpl fn ret srest labs0 ps as ss
Proof
  strip_tac >>
  `as.as_code = vs.vs_code` by
    (gvs[body_inv_def, fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def]) >>
  gvs[body_inv_reloc_specialize] >>
  simp[sym_frame_inv_canonical_own] >>
  gvs[sym_frame_inv_def, asm_data_env_lo_ok_canonical, asm_sym_rel_def]
QED

Theorem can_runs_prefix[local]:
  asm_steps lo o2pc prog n as = AsmOK as1 /\
  sym_steps prog env n ss = SymOK ss1 /\ can_R as1 ss1 res ==>
  can_R as ss res
Proof
  strip_tac >>
  drule_all (SRULE [sym_steps_mode_def] (Q.SPEC `F` sym_body_runs_prefix_mode)) >>
  disch_then assume_tac >>
  rpt conj_tac >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexistsl [`n + n'`, `as'`] >> simp[] >> metis_tac[]
QED

Theorem can_nonterm_prefix[local]:
  can_invoke_cut /\ can_A k prefix_ops rest_ops ps vs as ss /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  (inst.inst_opcode = LOG ==> ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
  step_inst fuel ctx inst vs = OK vs1 ==>
  ?prefix' rest' ps' vs' as1 ss1 n.
    can_A (SUC k) prefix' rest' ps' vs' as1 ss1 /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    sym_steps prog env n ss = SymOK ss1 /\
    block_rest fuel ctx fn bb vs = block_rest fuel ctx fn bb vs'
Proof
  strip_tac >> drule_all can_facts >> strip_tac >>
  `?ops ps' rest' n as1 ss1.
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
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1` by
    (Cases_on `inst.inst_opcode = INVOKE`
     >- (`?nm args. inst.inst_operands = Label nm :: args` by
           (drule_all body_inv_inst >> strip_tac >>
            irule invoke_operands_wf_shape_kernel >>
            gvs[stackPlanGenTheory.codegen_ready_inst_def]) >>
         `can_invoke_outcome k rest_ops ps vs as ss inst` by
           (qpat_x_assum `can_invoke_cut` irule >> simp[] >> metis_tac[]) >>
         first_x_assum drule >> strip_tac >> metis_tac[]) >>
     Cases_on `inst.inst_opcode = GAS`
     >- (mp_tac (SRULE [sym_steps_mode_def] (Q.INST [`allow_own` |-> `F`] sym_body_gas_ok_own_kernel)) >> FAIL_TAC "gas theorem") >>
     `sym_data_label prog env "code_end"` by
       (irule codegen_sym_code_end_label_kernel >> gvs[body_inv_def]) >>
     `(MEM (Label "runtime_begin") inst.inst_operands ==>
       sym_data_label prog env "runtime_begin")` by
       (strip_tac >> irule codegen_sym_runtime_begin_label_kernel >>
        drule body_inv_facts >> strip_tac >> drule_all body_inv_inst >> strip_tac >>
        gvs[body_inv_def] >> metis_tac[]) >>
     drule_all (SRULE [sym_steps_mode_def] (Q.SPEC `F` sym_body_ordinary_ok_own_kernel)) >>
     strip_tac >> fs[sym_frame_inv_canonical_own] >> metis_tac[]) >>
  drule_all body_inv_advance >> strip_tac >>
  `vs.vs_inst_idx = k` by gvs[body_inv_def] >>
  drule_all body_inv_inst >> strip_tac >>
  `get_instruction bb vs.vs_inst_idx = SOME inst` by metis_tac[] >>
  drule_all block_rest_advance >> strip_tac >>
  qexistsl [`prefix_ops ++ ops`, `rest'`, `ps'`,
    `vs1 with vs_inst_idx := SUC k`, `as1`, `ss1`, `n`] >> simp[]
QED

Theorem sym_body_canonical_branches_given_invoke:
  can_invoke_cut ==>
  !k prefix_ops rest_ops ps vs as ss.
    can_A k prefix_ops rest_ops ps vs as ss ==>
    can_R as ss (block_rest fuel ctx fn bb vs) \/
    (k < LENGTH bb.bb_instructions /\
      ?prefix' rest' ps' vs' as1 ss1.
        can_A (SUC k) prefix' rest' ps' vs' as1 ss1 /\
        (can_R as1 ss1 (block_rest fuel ctx fn bb vs') ==>
         can_R as ss (block_rest fuel ctx fn bb vs)))
Proof
  FAIL_TAC "inspect abbreviation"
QED
