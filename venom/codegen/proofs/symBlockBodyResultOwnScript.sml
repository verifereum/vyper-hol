(* Upper body-result API: the shared induction instantiated at the own client. *)
Theory symBlockBodyResultOwn
Ancestors
  symBlockBody symBodyOwnClient symBlockBodyOwnCore symBodyOrdinaryOwn
  symBodyTerminalOwn symBodyJumpOwn symBodyAlgebra fnBlockBody fnBlockBodySteps
  codegenSymRel fnSimSpec symFnSimSpec

Theorem sym_body_result_error_own:
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (Error e)
Proof
  simp[sym_body_result_own_def]
QED

Theorem sym_body_result_ok_own:
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (OK vs)
Proof
  simp[sym_body_result_own_def]
QED

Theorem sym_body_result_halt_own:
  (?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
    venom_asm_terminal_rel vs as' /\
    sym_terminal (sym_steps_mode allow_own prog env own n ss)) ==>
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (Halt vs)
Proof
  simp[sym_body_result_own_def]
QED

Theorem sym_body_result_abort_own:
  (?n as'.
    ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
     (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
    venom_asm_terminal_rel vs as' /\
    sym_terminal (sym_steps_mode allow_own prog env own n ss)) ==>
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (Abort a vs)
Proof
  simp[sym_body_result_own_def]
QED

Theorem sym_body_result_intret_own:
  (?n as' ss'. asm_steps lo o2pc prog n as = AsmOK as' /\
    as'.as_pc = pc_ret /\ as'.as_stack = REVERSE rv.iret_values ++ rest /\
    context_memory_rel cpl vs.vs_memory as'.as_memory /\
    (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
      read_byte b as'.as_memory = read_byte b mem0) /\ shared_state_rel vs as' /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
    asm_sym_rel_own lo prog env own as' ss' /\
    ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
    (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b)) ==>
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (IntRet rv vs)
Proof
  simp[sym_body_result_own_def]
QED

Theorem sym_body_result_prefix_own:
  asm_steps lo o2pc prog n as = AsmOK as1 /\
  sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as1 ss1 res ==>
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss res
Proof
  strip_tac >> drule_all sym_body_runs_prefix_mode >> disch_then assume_tac >>
  gvs[sym_body_result_own_def] >> rpt conj_tac >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexistsl [`n' + n`, `as'`] >> simp[] >> metis_tac[]
QED

Theorem sym_body_result_exec_own:
  (!t. exec_block fuel ctx bb vs <> OK t) /\
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (exec_block fuel ctx bb vs) ==>
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  strip_tac >> simp[block_rest_def] >>
  Cases_on `exec_block fuel ctx bb vs` >> gvs[]
QED

Theorem sym_body_run_own:
  !d k prefix_ops rest_ops ps vs as ss.
    d = LENGTH bb.bb_instructions - k /\
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
    sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
    sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
      as ss (block_rest fuel ctx fn bb vs)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`LENGTH bb.bb_instructions`,
    `\(k,prefix_ops,rest_ops,ps,vs,as,ss).
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
      sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss`,
    `\(k:num,prefix_ops:stack_op list,rest_ops:stack_op list,ps:plan_state,vs,as,ss).
      sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
        as ss (block_rest fuel ctx fn bb vs)`] mp_tac sym_body_run_client >>
  (impl_tac >-
    (POP_ASSUM_LIST (K all_tac) >>
     simp_tac (srw_ss()) [pairTheory.FORALL_PROD] >>
     rewrite_tac [sym_body_result_own_def] >> rpt gen_tac >> strip_tac >>
     drule_all (SRULE [] sym_body_own_branches) >>
     simp[pairTheory.EXISTS_PROD, CONJ_ASSOC])) >>
  disch_then (qspec_then `(k,prefix_ops,rest_ops,ps,vs,as,ss)` mp_tac) >> simp[]
QED

Theorem sym_block_body_frame_sim_own:
  !allow_own own fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
   ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv ra pc_ret
   rest mem0 env ret srest labs0 ss.
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
    sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
    sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
      as ss (block_rest fuel ctx fn bb vs)
Proof
  rpt strip_tac >> metis_tac[sym_body_run_own]
QED
