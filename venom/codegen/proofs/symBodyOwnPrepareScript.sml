(* Relocated body client preparation. INVOKE is an explicit selected-outcome cut. *)
Theory symBodyOwnPrepare
Ancestors
  symBlockBodyOwnCore symBodyAdvanceOwn symBodyJumpContinueOwn
  symBodyResultBranchesOwn symBodyStaticFacts symBodyAlgebra
  symFnSimSpec fnBlockBody fnBlockBodySteps

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

val _ = Parse.temp_overload_on ("own_result",
  ``\allow_own fuel lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0 bb
       (k:num,prefix_ops:stack_op list,rest_ops:stack_op list,ps:plan_state,vs,as,ss).
    own_body_result allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
      as ss (block_rest fuel ctx fn bb vs)``);

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
     irule symBodyStaticFactsTheory.invoke_operands_wf_shape >>
     gvs[stackPlanGenTheory.codegen_ready_inst_def]) >>
  gvs[] >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem own_nonterm_advance:
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
  `inst.inst_opcode = INVOKE ==>
    own_invoke_outcomes allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
      ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0
      prefix_ops rest_ops k ps vs as ss inst` by
    (BETA_TAC >> strip_tac >> drule_all (SRULE [] own_invoke_selected) >> simp[]) >>
  drule_all sym_body_nonterm_prefix_selected_own >> strip_tac >>
  qexistsl [`prefix'`, `rest'`, `ps'`, `vs'`, `as1`, `ss1`, `n`] >> simp[]
QED

Theorem own_result_prefix[local]:
  asm_steps lo o2pc prog n as = AsmOK as1 /\
  sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
  own_body_result allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as1 ss1 res ==>
  own_body_result allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss res
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  drule_all sym_body_runs_prefix_mode >> disch_then assume_tac >>
  rpt conj_tac >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexistsl [`n + n'`, `as'`] >> simp[] >> metis_tac[]
QED

Theorem own_nonterm_successor[local]:
  own_invoke_cut allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
    ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 /\
  own_admissible allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
    ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 (k,prefix_ops,rest_ops,ps,vs,as,ss) /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  (inst.inst_opcode = LOG ==> ?tc args. inst.inst_operands = Lit tc::args /\ w2n tc <= 4) /\
  step_inst fuel ctx inst vs = OK vs1 ==>
  ?y. FST y = SUC k /\
    own_admissible allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
      ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 y /\
    (own_result allow_own fuel lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0 bb y ==>
     own_result allow_own fuel lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0 bb
       (k,prefix_ops,rest_ops,ps,vs,as,ss))
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  drule_all (SRULE [] own_nonterm_advance) >> strip_tac >>
  qexists `(SUC k,prefix',rest',ps',vs',as1,ss1)` >> simp_tac (srw_ss()) [] >>
  simp[] >> strip_tac >> irule (SRULE [] own_result_prefix) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem own_jump_continue:
  own_admissible allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
    ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 (k,prefix_ops,rest_ops,ps,vs,as,ss) /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst vs = OK vs1 /\
  vs1 = jump_to t vs /\ MEM t (get_successors inst) /\
  asm_steps lo o2pc prog n as = AsmOK as1 /\
  fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
  (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
    operand_val (frame_view fn ra vs1) lo at =
    operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
  FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc /\
  sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps_after as1 ss1 ==>
  ~vs1.vs_halted /\
  own_body_result allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (run_blocks fuel ctx fn vs1)
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  drule_all (BETA_RULE sym_body_jump_continue_minimal_own) >> simp[]
QED

Theorem own_terminator_result:
  own_admissible allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
    ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 (k,prefix_ops,rest_ops,ps,vs,as,ss) /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst vs = OK vs1 ==>
  own_result allow_own fuel lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0 bb
    (k,prefix_ops,rest_ops,ps,vs,as,ss)
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  drule_all (BETA_RULE sym_body_terminator_minimal_own) >> simp[]
QED

Theorem own_revert_result:
  own_admissible allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
    ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 (k,prefix_ops,rest_ops,ps,vs,as,ss) /\
  revert_forward_pair bb k j ==>
  own_result allow_own fuel lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0 bb
    (k,prefix_ops,rest_ops,ps,vs,as,ss)
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  drule_all (BETA_RULE sym_body_revert_result_minimal_own) >>
  disch_then (qspec_then `fuel` mp_tac) >> simp[]
QED

Theorem own_nonok_result:
  own_invoke_cut allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
    ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 /\
  own_admissible allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
    ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 (k,prefix_ops,rest_ops,ps,vs,as,ss) /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  (!j. ~revert_forward_pair bb k j) /\ LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = res /\ (!s. res <> OK s) ==>
  own_result allow_own fuel lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0 bb
    (k,prefix_ops,rest_ops,ps,vs,as,ss)
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  `inst.inst_opcode = INVOKE ==>
    own_invoke_outcomes allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
      ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0
      prefix_ops rest_ops k ps vs as ss inst` by
    (BETA_TAC >> strip_tac >> drule_all (SRULE [] own_invoke_selected) >> simp[]) >>
  drule_all (BETA_RULE sym_body_nonok_selected_own) >> simp[]
QED

Theorem sym_body_own_branches_given_invoke:
  own_invoke_cut allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
    ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 /\
  own_admissible allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
    ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0
      (k,prefix_ops,rest_ops,ps,vs,as,ss) ==>
  own_result allow_own fuel lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0 bb
    (k,prefix_ops,rest_ops,ps,vs,as,ss) \/
  (k < LENGTH bb.bb_instructions /\
   ?y. FST y = SUC k /\
    own_admissible allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
      ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 y /\
    (own_result allow_own fuel lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0 bb y ==>
     own_result allow_own fuel lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0 bb
       (k,prefix_ops,rest_ops,ps,vs,as,ss)))
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  reverse (Cases_on `k < LENGTH bb.bb_instructions`)
  >- (disj1_tac >>
      `vs.vs_inst_idx = k` by gvs[body_inv_reloc_def] >>
      `?e. exec_block fuel ctx bb vs = Error e` by
        metis_tac[fnBlockBodyHelpersTheory.exec_block_out_of_range, arithmeticTheory.NOT_LESS] >>
      drule block_rest_error >> simp_tac (srw_ss()) []) >>
  `EL k bb.bb_instructions = EL k bb.bb_instructions` by simp[] >>
  drule_all sym_body_inst_bounds_reloc_kernel >> strip_tac >>
  Cases_on `?j. revert_forward_pair bb k j`
  >- (disj1_tac >> pop_assum strip_assume_tac >>
      drule_all (SRULE [] own_revert_result) >> simp[]) >>
  pop_assum (assume_tac o REWRITE_RULE [NOT_EXISTS_THM]) >>
  Cases_on `?vs1. step_inst fuel ctx (EL k bb.bb_instructions) vs = OK vs1`
  >- (pop_assum strip_assume_tac >>
      Cases_on `is_terminator (EL k bb.bb_instructions).inst_opcode`
      >- (disj1_tac >> drule_all (SRULE [] own_terminator_result) >> simp[]) >>
      disj2_tac >> simp[] >> drule_all (SRULE [] own_nonterm_successor) >> simp[]) >>
  disj1_tac >>
  `!s. step_inst fuel ctx (EL k bb.bb_instructions) vs <> OK s` by metis_tac[] >>
  `step_inst fuel ctx (EL k bb.bb_instructions) vs =
   step_inst fuel ctx (EL k bb.bb_instructions) vs` by simp[] >>
  drule_all (SRULE [] own_nonok_result) >> simp[]
QED

Theorem sym_body_own_nonterm_application_given_invoke:
  own_invoke_cut allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
    ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 /\
  (!m. m < d ==>
    !y. m = LENGTH bb.bb_instructions - FST y /\
      own_admissible allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
        growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
        ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0 y ==>
      own_result allow_own fuel lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0 bb y) /\
  d = LENGTH bb.bb_instructions - k /\
  own_admissible allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
    ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0
      (k,prefix_ops,rest_ops,ps,vs,as,ss) ==>
  own_result allow_own fuel lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0 bb
    (k,prefix_ops,rest_ops,ps,vs,as,ss)
Proof
  strip_tac >>
  drule_all sym_body_own_branches_given_invoke >> strip_tac >- simp[] >>
  qspecl_then [`LENGTH bb.bb_instructions`,
    `own_admissible allow_own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
      ps_dfs_after ps_after pc0 Inv ra pc_ret rest mem0 env own ret srest labs0`,
    `own_result allow_own fuel lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0 bb`]
    mp_tac sym_body_nonterm_result_client >>
  disch_then (qspec_then `d` mp_tac) >>
  disch_then (qspec_then `(k,prefix_ops,rest_ops,ps,vs,as,ss)` mp_tac) >>
  simp_tac (srw_ss()) [] >> disch_then irule >> simp[]
QED
