(* Own-code label flow through the last four O1 function passes. *)
Theory o1LabelFlowOwnLate
Ancestors
  codegenSymOwnRel
  o1LabelFlowOwnSimplifyRepair o1LabelFlowOwnSimplifyChain
  o1LabelFlowOwnSimplifyJump o1LabelFlowOwnSimplifyIteration
  o1LabelFlowOwnSue o1LabelFlowOwnDft o1LabelFlowOwnCfgNorm
  o1LabelFlowLateContracts o1LabelFlowStaticContracts
  o1LabelFlowMiddle o1PassContract venomPassSchedule list

(* Function shape supplies the relaxed CODECOPY source clause.  The late
   passes need only transport restricted uses of code-end pointers.
   Existing support: o1LabelFlowSimplifyPreservation/SimplifyChain/Retention,
   o1LabelFlowSueNegative, o1LabelFlowLateDft, and
   o1LabelFlowCfgSplitTaint/CfgSplitPreservation. *)
Theorem compose_late_own:
  !k pass rp observed s f out ctx.
  ((k = 5 /\ pass = CFP_Simple VP_SimplifyCFG) \/
   (k = 6 /\ pass = CFP_Simple VP_SingleUseExpansion) \/
   (k = 7 /\ pass = CFP_Simple VP_DFT) \/
   (k = 8 /\ pass = CFP_Simple VP_CFGNormalization)) /\
  fn_pass_step rp pass observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  o1_fn_row k f /\
  (label_flow_own_ok (ctx with ctx_functions := [f]) /\
   (k <= 1 ==> !i. MEM i (fn_insts f) ==>
     ~MEM (Label "code_end") i.inst_operands) /\
   (2 <= k /\ k <= 4 ==> middle_code_end_lifetime f) /\
   (k <= 3 ==> no_raw_fmp_ops f) /\ fmp_sig_no_param f) ==>
  (label_flow_own_ok (ctx with ctx_functions := [out.fpo_function]) /\
   (SUC k <= 1 ==> !i. MEM i (fn_insts out.fpo_function) ==>
     ~MEM (Label "code_end") i.inst_operands) /\
   (2 <= SUC k /\ SUC k <= 4 ==>
     middle_code_end_lifetime out.fpo_function) /\
   (SUC k <= 3 ==> no_raw_fmp_ops out.fpo_function) /\
   fmp_sig_no_param out.fpo_function)
Proof
  mp_tac simplify_row5_code_end_uses_conditional >>
  (impl_tac >-
    (conj_tac >- (gen_tac >> MATCH_ACCEPT_TAC simplify_unreachable_code_end_uses) >>
     conj_tac >- (gen_tac >> MATCH_ACCEPT_TAC simplify_fix_phis_code_end_uses) >>
     conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC simplify_chain_merge_code_end_uses) >>
     rpt gen_tac >> MATCH_ACCEPT_TAC simplify_jump_code_end_uses)) >>
  disch_then (mk_asm "simplify") >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  (`o1_fn_shape observed.cu_context out.fpo_function` by
    (mp_tac o1_fn_passes_steps >>
     simp[o1_fn_passes_def, o1_step_contracts_from_def,
          o1_step_contract_at_def] >> metis_tac[]) >>
  `MEM f observed.cu_context.ctx_functions` by
    metis_tac[fn_pass_step_def, venomFnScheduleRunnerPropsTheory.lookup_unique_function_member] >>
  `wf_function f` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\
     code_end_var f x ==>
     (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
     (i.inst_opcode = CODECOPY /\ ?dst sz.
       i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)` by
    (fs[label_flow_own_ok_def] >> metis_tac[]) >>
  reverse conj_tac
  >- (drule fn_pass_step_fmp_sig_no_param >> simp[fn_pass_tag_def]) >>
  irule label_flow_own_ok_from_code_end_use >>
  simp[] >> reverse conj_tac
  >- fs[o1_fn_shape_def])
  >- (asm "simplify" drule >> simp[])
  >- (drule sue_row_code_end_uses >> simp[])
  >- (drule dft_row7_code_end_uses >> simp[]) >>
  drule cfg_norm_row_code_end_uses >> simp[]
QED
