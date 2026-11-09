(*
 * The symbolic fuel induction: the two steps of fnEntryStep and fnBlockStep
 * with the symbolic run added, and their closure over all fuel.  The
 * concrete function-level statements at each fuel come from codegen's own
 * steps (fn_entry_block_step, fn_block_frame_step).
 *
 * TOP-LEVEL:
 *   sym_fn_entry_block_step  - sym_fn_sim_at (SUC fuel) from the four
 *                              function statements at fuel
 *   sym_fn_block_frame_step  - sym_fn_frame_sim_at (SUC fuel), likewise
 *   sym_fn_sims_all          - all four at every fuel
 *)
Theory symFnStep
Ancestors
  symBlockBody symFrameBoundary symFnSimSpec codegenSymRel fnEntryStep
  fnBlockStep fnBlockStepHelpers fnBlockBody fnSimSpec asmSymBridge
  asmSymSem frameRel contextCodegenRel codegenRel venomExecSemantics
  venomState planExec stackOpSim blockSimHelpers

(* These names are representation variables in the boundary contracts. *)
val _ = Parse.hide "base";
val _ = Parse.hide "body";
Theorem sym_frame_inv_cleanup_fields:
  !prog env ctx cp fn ret srest labs0 ps h promised as ss.
    sym_frame_inv prog env ctx cp fn ret srest labs0
      (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
      as ss <=>
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss
Proof
  simp[sym_frame_inv_def, sym_kinds_ok_def]
QED

Theorem sym_label_block_steps:
  !lo o2pc prog as fmp lbl ops env ctx cp fn ret srest labs0 ps ss.
    asm_block_at prog as.as_pc (execute_plan fmp (SOLabel lbl :: ops)) /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    asm_steps lo o2pc prog 1 as = AsmOK (as with as_pc := as.as_pc + 1) /\
    sym_steps prog env 1 ss =
      SymOK (ss with sym_base := ss.sym_base with as_pc := as.as_pc + 1) /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps
      (as with as_pc := as.as_pc + 1)
      (ss with sym_base := ss.sym_base with as_pc := as.as_pc + 1) /\
    asm_block_at prog (as.as_pc + 1) (execute_plan fmp ops)
Proof
  rpt gen_tac >> strip_tac >> drule label_block_steps >> strip_tac >> simp[] >>
  gvs[sym_frame_inv_def, asm_sym_rel_def] >>
  gvs[execute_plan_def, exec_stack_op_def, asm_block_at_cons] >>
  conj_tac
  >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [numLib.num_CONV ``1:num``])) >>
      simp[sym_steps_def, sym_step_def, sym_lift_def,
           asmSemTheory.asm_step_def, asmSemTheory.asm_next_def,
           sym_state_component_equality]) >>
  simp[sym_kinds_ok_def] >> gvs[sym_kinds_ok_def] >> metis_tac[]
QED

Theorem sym_body_result_prefix:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss res n as1 ss1.
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    sym_steps prog env n ss = SymOK ss1 /\
    sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
      as1 ss1 res ==>
    sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
      as ss res
Proof
  rpt gen_tac >> simp[sym_body_result_def] >> strip_tac >> rpt conj_tac
  >> rpt gen_tac >> strip_tac
  >> first_x_assum drule >> strip_tac
  >> qexists_tac `n + n'`
  >> simp[stackOpSimTheory.asm_steps_add, sym_steps_add]
  >> metis_tac[]
QED

Theorem sym_block_prefix_step:
  !ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb
   pred ps_l h promised vs as s_phi clean_ops ps2 ops ps3 r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\ vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    generated_plan_state_wf_marked spill_base ps_l /\
    (!op v. (MEM op ps_l.ps_stack \/ op IN FDOM ps_l.ps_spilled) /\
       ~MEM op (FLAT (MAP (\inst. inst.inst_operands)
                       (collect_phis bb.bb_instructions))) /\
       (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
       ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    (LENGTH (cfg_preds_of cfg bb.bb_label) <= 1 ==>
     !op v. (MEM op ps_l.ps_stack \/ op IN FDOM ps_l.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) (clean_ops ++ ops) \/
           MEM (SORestore off) (clean_ops ++ ops) ==> off < dimword (:256)) /\
    (!at. MEM at ps_l.ps_stack \/ at IN FDOM ps_l.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps_l vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = bb.bb_instructions /\
    (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
     then clean_stack_plan liveness cfg fn bb
            (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
     else ([], ps_l with <| ps_cleanup_height := h;
                            ps_cleanup_promised := promised |>)) =
      (clean_ops, ps2) /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (non_param_insts bb) ps2 = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp (clean_ops ++ ops)) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps_l as ss ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (phi_prefix_length bb.bb_instructions)
        (non_param_insts bb) ps2 = SOME (phi_ops, ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (phi_prefix_length bb.bb_instructions)
        (DROP (phi_prefix_length bb.bb_instructions) (non_param_insts bb))
        ps1 = SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc +
        LENGTH (execute_plan cp.cp_initial_fmp (clean_ops ++ phi_ops)) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps prog env n ss = SymOK ss' /\
      sym_frame_inv prog env ctx cp fn ret srest labs0 ps1 as' ss'
Proof
  rpt gen_tac >> strip_tac >>
  drule take_drop_phi_prefix >> strip_tac >>
  Cases_on `LENGTH (cfg_preds_of cfg bb.bb_label) = 1`
  >- suspend "single"
  >> suspend "join"
QED

Resume sym_block_prefix_step[single]:
  qpat_assum `LENGTH (TAKE _ _) = _` (fn len =>
  irule (GEN_ALL (REWRITE_RULE [len, listTheory.TAKE_DROP, stackPlanTypesTheory.plan_state_accfupds, combinTheory.K_THM,
      fnPlanPrefixTheory.wf_marked_cleanup_fields, fn_frame_inv_cleanup_fields,
      sym_frame_inv_cleanup_fields]
    (Q.INST [`ps` |-> `ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>`,
             `base:num` |-> `spill_base:num`,
             `phis:instruction list` |-> `TAKE (phi_prefix_length bb.bb_instructions) (non_param_insts bb)`,
             `body:instruction list` |-> `DROP (phi_prefix_length bb.bb_instructions) (non_param_insts bb)`]
      (SPEC_ALL sym_single_pred_prefix_frame_sim))))) >> simp[] >>
  conj_tac >- gvs[listTheory.MEM_APPEND] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`ch`, `growth`, `h`, `lbl_ctr`, `pred`, `promised`, `ps_l`, `spill_base`, `vs`] >> gvs[] >> metis_tac[]
QED

Resume sym_block_prefix_step[join]:
  cheat
QED

Finalise sym_block_prefix_step

Theorem sym_fn_entry_block_step:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
         sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel ==>
         sym_fn_sim_at (SUC fuel)
Proof
  cheat
QED

Theorem sym_fn_block_frame_step:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
         sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel ==>
         sym_fn_frame_sim_at (SUC fuel)
Proof
  cheat
QED

Theorem sym_fn_sims_all:
  !fuel. gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
         sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel
Proof
  Induct
  >- (simp[gen_fn_sim_at_def, gen_fn_frame_sim_at_def, sym_fn_sim_at_def,
           sym_fn_frame_sim_at_def] >>
      rpt strip_tac >> gvs[Once run_blocks_def]) >>
  metis_tac[fn_entry_block_step, fn_block_frame_step,
            sym_fn_entry_block_step, sym_fn_block_frame_step]
QED
