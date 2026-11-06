Theory fnPlanLineageDelayedReset
Ancestors
  fnPlanLineageEntryProduction fnPlanLineageQuarantine fnPlanLineageInventory list rich_list finite_map

(* Stack quarantine does not require spill absence. The native prefix keeps
   its original next-live and next-terminator arguments at every position. *)
Theorem native_inst_prefix_stack_quarantine:
  !lv dfg cfg fn lbl halt n len xs ps k qs.
    native_inst_prefix lv dfg cfg fn lbl halt n len xs ps k qs ==>
    !v. ~MEM (Var v) ps.ps_stack /\
      (!i. i < k ==> inst_wf (EL i xs) /\ codegen_ready_inst (EL i xs) /\
        ~MEM (Var v) (EL i xs).inst_operands /\
        ~MEM v (EL i xs).inst_outputs /\
        (!targets. (EL i xs).inst_opcode = JMP /\
          join_target_ops lv fn lbl (EL i xs) = SOME targets ==>
          ~MEM (Var v) targets)) ==>
      ~MEM (Var v) qs.ps_stack
Proof
  ho_match_mp_tac native_inst_prefix_ind >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `k < LENGTH xs` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  `inst = EL k xs` by metis_tac[listTheory.HD_DROP, listTheory.HD] >>
  rename1 `generate_inst_plan _ _ _ _ _ _ _ _ _ mid = SOME (ops,final)` >>
  `~MEM (Var v) mid.ps_stack` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     `i < SUC k` by decide_tac >> metis_tac[]) >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
  gvs[] >> drule_all native_inst_stack_quarantine >> simp[]
QED

(* This conditional boundary allows arbitrary incoming spills. Native event
   production must still supply the request-free interval and the final
   regular reset before reactivation; PHI need not provide that reset. *)
Theorem branch_native_delayed_reset:
  !lv dfg cfg fn bb pred pred_bb v ps cleanup_ops cs halt n len xs k mid
    inst nl term step_ops qs.
    cfg_preds_of cfg bb.bb_label = [pred] /\
    1 < LENGTH (cfg_succs_of cfg pred) /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    MEM v (live_vars_at lv pred (LENGTH pred_bb.bb_instructions)) /\
    ~MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at lv bb.bb_label 0)) /\
    LIST_ELEM_COUNT (Var v) ps.ps_stack <= 1 /\
    clean_stack_plan lv cfg fn bb ps = (cleanup_ops,cs) /\
    native_inst_prefix lv dfg cfg fn bb.bb_label halt n len xs cs k mid /\
    (!i. i < k ==> inst_wf (EL i xs) /\ codegen_ready_inst (EL i xs) /\
      ~MEM (Var v) (EL i xs).inst_operands /\
      ~MEM v (EL i xs).inst_outputs /\
      (!targets. (EL i xs).inst_opcode = JMP /\
        join_target_ops lv fn bb.bb_label (EL i xs) = SOME targets ==>
        ~MEM (Var v) targets)) /\
    generate_inst_plan lv dfg cfg fn inst nl halt term bb.bb_label mid =
      SOME (step_ops,qs) /\
    inst_wf inst /\ codegen_ready_inst inst /\
    ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
    (!targets. inst.inst_opcode = JMP /\
      join_target_ops lv fn bb.bb_label inst = SOME targets ==>
      ~MEM (Var v) targets) /\
    ~MEM v nl /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> OFFSET /\
    ~is_param_opcode inst.inst_opcode /\ inst.inst_opcode <> NOP ==>
    ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `~MEM (Var v) cs.ps_stack` by
    (drule_all clean_stack_plan_branch_unique_absent >> simp[]) >>
  `~MEM (Var v) mid.ps_stack` by
    (drule_all native_inst_prefix_stack_quarantine >> simp[]) >>
  drule_all native_regular_inst_physical_reset >> simp[]
QED
