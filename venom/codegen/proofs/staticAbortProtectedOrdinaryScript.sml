(* Ordinary symbolic progress before either relaxed-memory abort cut. *)
Theory staticAbortProtectedOrdinary
Ancestors
  fnStaticAbortBodyFacts symBlockBody symFrameInst codegenSymRel
  fnBlockBodySteps fnStaticAbortBoundary unitShapeDefs

val _ = Parse.hide "cp";
val _ = Parse.hide "base";

Theorem sym_body_abort_protected_ordinary_ok:
  !fuel rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
   ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv ra pc_ret
   rest mem0 inst vs1 env ret srest labs0 ss.
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
  ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  (inst.inst_opcode = LOG ==>
     ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
  step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\
  code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
    ctx /\ sym_unit_static_ok unit /\
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
  drule body_inv_abort_plan >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule body_plan_inv_equiv >> disch_then drule >> disch_then drule >> strip_tac >>
  drule_all body_inv_abort_memory >> strip_tac >>
  `!e. step_inst fuel ctx inst vs <> Error e` by simp[] >>
  drule body_plan_inv_label_resolve >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> strip_tac >>
  qhdtm_assum `body_inv_abort`
    (strip_assume_tac o REWRITE_RULE [body_inv_abort_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `sym_data_label prog env "code_end"` by
    metis_tac[codegen_sym_code_end_label] >>
  `(MEM (Label "runtime_begin") inst.inst_operands ==>
    sym_data_label prog env "runtime_begin")` by
    metis_tac[codegen_sym_runtime_begin_label] >>
  `!dst x sz w off. inst.inst_opcode = CODECOPY /\
    inst.inst_operands = [dst; Var x; sz] /\ code_end_var fn x /\
    eval_operand (Var x) vs = SOME w /\
    FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off ==>
    w2n (w - n2w off) < dimword (:256) DIV 2` by
    (rpt strip_tac >>
     `FLOOKUP vs.vs_labels "code_end" = SOME (n2w off)` by simp[] >>
     `Inv ctx fn inst vs` by
       (qpat_x_assum `!j. active_inst fn j vs ==> Inv ctx fn j vs`
          (qspec_then `inst` mp_tac) >> simp[]) >>
     qpat_x_assum `code_end_offset_ok _ _`
       (qspecl_then [`fn`, `inst`, `vs`, `dst`, `x`, `sz`, `w`, `n2w off`]
          mp_tac o BETA_RULE o REWRITE_RULE [code_end_offset_ok_def]) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `!dist prev val_op. inst.inst_opcode = PHI /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME dist /\
    vs.vs_prev_bb = SOME prev /\ resolve_phi prev inst.inst_operands = SOME val_op ==>
    operand_val (frame_view fn ra vs) lo (stack_peek dist ps.ps_stack) =
    eval_operand val_op (frame_view fn ra vs)` by simp[] >>
  `inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")` by simp[] >>
  (* Failed routes: backward existential matching and frame-first chained
     drule_at did not specialize the planner tuple. Specialize the original
     closed theorem directly, leaving its remaining outer names unchanged. *)
  mp_tac (Q.INST
    [`cp:context_plan` |-> `cpl:context_plan`,
     `base:num` |-> `spill_base:num`,
     `next_liveness` |-> `live_vars_at liveness bb.bb_label (k + 1)`,
     `is_halting` |-> `bb_is_halting bb`,
     `next_is_term` |-> `k + 1 < LENGTH bb.bb_instructions /\
                         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode`,
     `bb_label` |-> `bb.bb_label`]
    (SPEC_ALL (INST_TYPE [``:'a`` |-> ``:cfg_analysis``]
      sym_inst_frame_sim_deep))) >>
  (impl_tac >- (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
                first_assum ACCEPT_TAC)) >>
  disch_then (qspec_then `vs1` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `n` (qx_choose_then `as1`
    (qx_choose_then `ss1` strip_assume_tac))) >>
  qexistsl_tac [`ops`, `ps'`, `rest'`, `n`, `as1`, `ss1`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
