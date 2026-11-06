Theory fnPlanLineageDelayedReset
Ancestors
  fnPlanLineageEntryProduction fnPlanLineageQuarantine list rich_list

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
