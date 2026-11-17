(* Unconditional canonical body client join. *)
Theory symBodyCanonicalClient
Ancestors
  symBodyCanonicalPrepare symBodyInvokeCanonical

(* Parse-time abbreviations for the existing expanded client contracts only. *)
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

Theorem sym_body_canonical_branches:
  !k prefix_ops rest_ops ps vs as ss.
    can_A k prefix_ops rest_ops ps vs as ss ==>
    can_R as ss (block_rest fuel ctx fn bb vs) \/
    (k < LENGTH bb.bb_instructions /\
      ?prefix' rest' ps' vs' as1 ss1.
        can_A (SUC k) prefix' rest' ps' vs' as1 ss1 /\
        (can_R as1 ss1 (block_rest fuel ctx fn bb vs') ==>
         can_R as ss (block_rest fuel ctx fn bb vs)))
Proof
  mp_tac sym_body_canonical_branches_given_invoke >>
  (impl_tac >-
    (rpt gen_tac >> strip_tac >> simp_tac (srw_ss()) [] >>
     irule sym_body_invoke_step_canonical_kernel >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[])) >>
  simp[]
QED

Theorem sym_body_canonical_nonterm_application:
  (!m. m < d ==> !k prefix_ops rest_ops ps vs as ss.
    m = LENGTH bb.bb_instructions - k /\ can_A k prefix_ops rest_ops ps vs as ss ==>
    can_R as ss (block_rest fuel ctx fn bb vs)) /\
  d = LENGTH bb.bb_instructions - k /\ can_A k prefix_ops rest_ops ps vs as ss ==>
  can_R as ss (block_rest fuel ctx fn bb vs)
Proof
  strip_tac >>
  drule_at (Pos (el 2)) sym_body_canonical_nonterm_application_given_invoke >>
  disch_then (drule_at (Pat `body_inv`)) >>
  disch_then (drule_at (Pat `sym_frame_inv`)) >>
  (impl_tac >-
    (conj_tac >-
       (rpt gen_tac >> strip_tac >> simp_tac (srw_ss()) [] >>
        irule sym_body_invoke_step_canonical_kernel >>
        rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
     simp[])) >>
  simp[]
QED
