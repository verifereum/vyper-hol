Theory staticAbortStoppedBodyCut
Ancestors
  fnStaticAbortBoundary fnBlockBody symBlockBody contextStaticAbortRel
  staticAbortExec staticAbortDefs contextCodegenRel asmSem asmSymSem asmSplice
  codegenSymRel venomExecSemantics venomExecProps venomInst unitShapeDefs
  o1LowerDloadRequestForward o1LowerDloadForwardInversion stepWriteFootprintForward
  list rich_list

val _ = Parse.hide "cp";
val _ = Parse.hide "base";

Theorem stopped_body_cut_observation:
  !rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
   ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv ra pc_ret
   rest mem0 env ret srest labs0 ss.
    body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
    label_flow_ok ctx /\
    code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
      ctx /\ sym_unit_static_ok unit /\
    asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps ast ss /\
    (in_static_abort_prefix fn vs \/ in_revert_forward fn vs) ==>
    ((!vs'. block_rest fuel ctx fn bb vs = Halt vs' ==>
       ?n out. asm_steps lo o2pc prog n ast = AsmHalt out /\
         venom_asm_terminal_rel vs' out /\ sym_terminal (sym_steps prog env n ss)) /\
     (!a vs'. block_rest fuel ctx fn bb vs = Abort a vs' ==>
       (?n out. (asm_steps lo o2pc prog n ast = AsmRevert out \/
                 asm_steps lo o2pc prog n ast = AsmFault out) /\
          sym_terminal (sym_steps prog env n ss) /\ out.as_requests <<= vs'.vs_requests) \/
       (?nc cut sc iC fnC rC livC dfgC cfgC chC growthC spillC ctrC fnopsC endC
         bbC pslC hC promisedC dfsC blockC dfsafterC afterC prefixC restopsC kC
         psC pcC cvsC raC pcretC restC memC retC srestC labsC.
          asm_steps lo o2pc prog nc ast = AsmOK cut /\
          sym_steps prog env nc ss = SymOK sc /\
          body_inv_abort rpolicy unit cpl prog ctx lo o2pc iC fnC rC livC dfgC cfgC
            chC growthC spillC ctrC fnopsC endC bbC pslC hC promisedC dfsC blockC
            dfsafterC afterC prefixC restopsC kC psC pcC cvsC cut Inv
            raC pcretC restC memC /\
          sym_frame_inv prog env ctx cpl fnC retC srestC labsC psC cut sc /\
          (in_static_abort_prefix fnC cvsC \/ in_revert_forward fnC cvsC) /\
          cut.as_requests = vs'.vs_requests)) /\
     (!rv vs'. block_rest fuel ctx fn bb vs = IntRet rv vs' ==>
       ?n out ss'. asm_steps lo o2pc prog n ast = AsmOK out /\
         out.as_pc = pc_ret /\ out.as_stack = REVERSE rv.iret_values ++ rest /\
         context_memory_rel cpl vs'.vs_memory out.as_memory /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           read_byte b out.as_memory = read_byte b mem0) /\
         shared_state_rel vs' out /\ sym_steps prog env n ss = SymOK ss' /\
         asm_sym_rel prog env out ss' /\
         ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
         (!b. context_spill_byte cpl b /\ ~closure_spill_byte ctx cpl fn.fn_name b ==>
           FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
         (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b)))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
   fn_frame_inv ctx cpl lo fn ra rest mem0 ps vs ast` by
    fs[body_inv_abort_def] >>
  `(!v. exec_block fuel ctx bb vs <> OK v) /\
   (!rv v. exec_block fuel ctx bb vs <> IntRet rv v) /\
   (!v. exec_block fuel ctx bb vs <> Halt v)` by
    (Cases_on `in_static_abort_prefix fn vs`
     >- (`vs.vs_call_ctx.cc_static /\ static_abort_at bb vs.vs_inst_idx` by
           (fs[in_static_abort_prefix_def] >> gvs[]) >>
         rpt conj_tac >> rpt gen_tac >>
         FIRST [irule (cj 1 static_abort_at_no_normal),
                irule (cj 2 static_abort_at_no_normal),
                irule static_abort_at_no_halt] >> simp[]) >>
     `in_revert_forward fn vs` by metis_tac[] >>
     `revert_forward_at bb vs.vs_inst_idx` by
       (qpat_assum `in_revert_forward fn vs` mp_tac >>
        pure_rewrite_tac[in_revert_forward_def] >> strip_tac >> gvs[]) >>
     rpt conj_tac >> rpt gen_tac >>
     FIRST [irule (cj 1 revert_forward_at_no_normal),
            irule (cj 2 revert_forward_at_no_normal),
            irule o1LowerDloadForwardInversionTheory.revert_forward_at_no_halt] >>
     simp[]) >>
  `!a vs'. exec_block fuel ctx bb vs = Abort a vs' ==>
     vs'.vs_requests = vs.vs_requests` by
    (rpt gen_tac >> strip_tac >>
     Cases_on `in_static_abort_prefix fn vs`
     >- (qpat_assum `in_static_abort_prefix fn vs` mp_tac >>
         pure_rewrite_tac[in_static_abort_prefix_def] >> strip_tac >>
         gvs[] >> metis_tac[static_abort_at_abort_requests, exec_block_def]) >>
     `in_revert_forward fn vs` by metis_tac[] >>
     `revert_forward_at bb vs.vs_inst_idx` by
       (qpat_assum `in_revert_forward fn vs` mp_tac >>
        pure_rewrite_tac[in_revert_forward_def] >> strip_tac >> gvs[]) >>
     qpat_x_assum `revert_forward_at _ _` mp_tac >>
     pure_rewrite_tac[revert_forward_at_def] >> strip_tac
     >- (drule ld_forward_fetch_abort_requests >>
         disch_then (drule_at (Pat `run_block_non_phis _ _ _ _ = _`)) >>
         simp[]) >>
     drule_at (Pat `run_block_non_phis _ _ _ _ = _`) assign_suffix_abort_requests >>
     disch_then irule >>
     qexistsl_tac [`vs.vs_inst_idx`, `0`] >>
     simp[] >>
     qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
     pure_rewrite_tac[revert_forward_pair_def] >> strip_tac >>
     conj_tac >- (rpt strip_tac >> gvs[]) >>
     goal_assum (drule_at (Pat `get_instruction _ _ = SOME _`)) >> simp[]) >>
  Cases_on `exec_block fuel ctx bb vs` >>
  gvs[block_rest_def] >>
  drule static_abort_frame_cut >> strip_tac >>
  disj2_tac >>
  qexistsl_tac [`0`, `ast`, `ss`] >>
  simp[asm_steps_def, sym_steps_def] >>
  goal_assum (drule_at (Pat `body_inv_abort`)) >>
  goal_assum (drule_at (Pat `sym_frame_inv`)) >> simp[]
QED

(* Failed proof fragments retained for the task's diagnostic history.
   The first request attempt used the unsimplified alias as a match pattern:
     irule static_abort_at_abort_requests >>
     goal_assum (drule_at (Pat `exec_block _ _ _ _ = _`))
   But the live equality already used run_block_non_phis.

   A positional fetch specialization failed because drule generalized its
   remaining parameters in a different order:
     drule ld_forward_fetch_abort_requests >>
     disch_then (qspecl_then [`bb`, `vs`, `vs'`, `fuel`, `ctx`, `a`] mp_tac)
   The final proof instead matches the live execution equality.

   The suffix witness trial had its existential witnesses reversed:
     disch_then irule >> qexistsl_tac [`0`, `vs.vs_inst_idx`] >> simp[] >>
     qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
     simp[revert_forward_pair_def] >> metis_tac[]
   This produced an impossible suffix condition and timed out. Inspection
   showed the existential order is j,n, not n,j.

   Before splitting the suffix condition, this selector failed on a
   conjunctive goal:
     goal_assum (drule_at (Pat `get_instruction _ _ = SOME _`)) >> simp[]
   The initial arithmetic branch closer also ignored the assumptions:
     conj_tac >- (rpt strip_tac >> decide_tac)
   The final branch uses gvs to discharge the inconsistent bounds.
*)
