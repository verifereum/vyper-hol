(* Relocated body client preparation. INVOKE is an explicit selected-outcome cut. *)
Theory symBodyOwnPrepare
Ancestors
  symBlockBodyOwnCore symBodyOrdinaryOwn symBodyTerminalOwn symBodyStaticFacts
  symBodyJumpOwn symBodySuccessorPointwise symBodyAlgebra
  symFnSimSpec fnBlockBody fnBlockBodyClasses fnBlockBodySteps venomInstProps

(* Parse-time abbreviations only; no new logical constants. *)
val _ = Parse.temp_overload_on ("own_body_result",
  ``\allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0 as ss res.
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
               (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))``);

val _ = Parse.temp_overload_on ("own_admissible",
  ``\allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
      ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0
      (k,prefix_ops,rest_ops,ps,vs,as,ss).
    gen_fn_sim_at_simple_reloc fuel /\ gen_fn_frame_sim_at_simple_reloc fuel /\
    sym_fn_sim_at_own allow_own fuel /\ sym_fn_frame_sim_at_own allow_own fuel /\
    body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
    code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\ asm_static_wf prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
    sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss``);

val _ = Parse.temp_overload_on ("own_invoke_outcomes",
  ``\allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
      ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0
      prefix_ops rest_ops k ps vs as ss inst.
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
        sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
        sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps' as1 ss1) /\
    (!vs1. step_inst fuel ctx inst vs = Halt vs1 ==>
      ?n as1. asm_steps lo o2pc prog n as = AsmHalt as1 /\
        venom_asm_terminal_rel vs1 as1 /\
        sym_terminal (sym_steps_mode allow_own prog env own n ss)) /\
    (!a vs1. step_inst fuel ctx inst vs = Abort a vs1 ==>
      ?n as1. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as1) \/
               (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as1)) /\
        venom_asm_terminal_rel vs1 as1 /\
        sym_terminal (sym_steps_mode allow_own prog env own n ss))``);
val _ = Parse.temp_overload_on ("own_invoke_cut",
  ``\allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
      ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0.
    !k prefix_ops rest_ops ps vs as ss inst.
    own_admissible allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
      ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 (k,prefix_ops,rest_ops,ps,vs,as,ss) /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    inst.inst_opcode = INVOKE /\ LENGTH (compute_operands inst) <= 16 /\
    (?nm arg_ops. inst.inst_operands = Label nm :: arg_ops) ==>
    own_invoke_outcomes allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
      ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 prefix_ops rest_ops k ps vs as ss inst``);

Theorem own_invoke_selected[local]:
  own_invoke_cut allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
      ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 /\ own_admissible allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
      ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 (k,prefix_ops,rest_ops,ps,vs,as,ss) /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = INVOKE /\ LENGTH (compute_operands inst) <= 16 ==>
  own_invoke_outcomes allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
      ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 prefix_ops rest_ops k ps vs as ss inst
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  `?nm arg_ops. inst.inst_operands = Label nm :: arg_ops` by
    (drule_all body_inv_inst_reloc >> strip_tac >>
     irule invoke_operands_wf_shape_kernel >>
     gvs[stackPlanGenTheory.codegen_ready_inst_def]) >>
  gvs[] >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem own_nonterm_advance[local]:
  own_invoke_cut allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
      ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 /\ own_admissible allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
      ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 (k,prefix_ops,rest_ops,ps,vs,as,ss) /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  (inst.inst_opcode = LOG ==>
    ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
  step_inst fuel ctx inst vs = OK vs1 ==>
  ?prefix' rest' ps' vs' as1 ss1 n.
    own_admissible allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
      ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 (SUC k,prefix',rest',ps',vs',as1,ss1) /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
    block_rest fuel ctx fn bb vs = block_rest fuel ctx fn bb vs'
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  `sym_data_label prog env "code_end"` by
    (irule codegen_sym_code_end_label_kernel >>
     gvs[body_inv_reloc_def] >> metis_tac[]) >>
  `(MEM (Label "runtime_begin") inst.inst_operands ==>
    sym_data_label prog env "runtime_begin")` by
    (strip_tac >> drule_all body_inv_inst_reloc >> strip_tac >>
     qhdtm_x_assum `body_inv_reloc` mp_tac >>
     qpat_x_assum `!k prefix_ops rest_ops ps vs as ss. _` kall_tac >>
     simp_tac (srw_ss()) [body_inv_reloc_def] >> strip_tac >>
     irule codegen_sym_runtime_begin_label_kernel >>
     asm_simp_tac bool_ss [] >>
     qexistsl [`fn`, `inst`, `rpolicy`, `unit`] >> simp[] >>
     metis_tac[listTheory.MEM_EL]) >>
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
      ps' = SOME (rest', ps_after) /\ rest_ops = ops ++ rest' /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
    sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps' as1 ss1` by
    (Cases_on `inst.inst_opcode = INVOKE`
     >- (drule_all own_invoke_selected >> strip_tac >>
         first_x_assum drule >> strip_tac >> metis_tac[]) >>
     Cases_on `inst.inst_opcode = GAS`
     >- (drule_all sym_body_gas_ok_own_kernel >> metis_tac[]) >>
     drule_all sym_body_ordinary_ok_own_kernel >> metis_tac[]) >>
  drule_all body_inv_advance_reloc >> strip_tac >>
  `vs.vs_inst_idx = k` by gvs[body_inv_reloc_def] >>
  drule_all body_inv_inst_reloc >> strip_tac >>
  `get_instruction bb vs.vs_inst_idx = SOME inst` by metis_tac[] >>
  drule_all block_rest_advance >> strip_tac >>
  `vs1.vs_code = vs.vs_code` by metis_tac[step_preserves_code] >>
  qexistsl [`prefix_ops ++ ops`, `rest'`, `ps'`,
    `vs1 with vs_inst_idx := SUC k`, `as1`, `ss1`, `n`] >> simp[]
QED
