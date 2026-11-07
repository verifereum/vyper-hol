Theory fnLineageInvJoinContract
Ancestors fnLineageInvActualSchedule fnLineageInvSetupSuffix
  fnPlanLineagePhiSchedule fnPlanLineageInventory stackPlanGen list rich_list

(* A consumer-side contract: the raw replay producer must supply the literal
   marker prefixes, not merely an arbitrary common suffix.  Spill maps are
   preserved separately; this statement does not invent map equality. *)
Theorem actual_phi_prefix_common_core:
 !k insts lv dfg cfg fn lbl halt np bl i ps qs pops qops pe qe
   m n suffix ops al u v pc qc.
 k <= LENGTH insts /\ EVERY (\inst. inst.inst_opcode = PHI) (TAKE k insts) /\
 (k < LENGTH insts \/ bl = i + np + k) /\
 phi_schedule_run
   (MAPi (\j inst. (inst, live_vars_at lv lbl (i + np + SUC j), halt))
     (TAKE k insts)) ps =
   (ops, ps with <|ps_stack := REPLICATE m dead_stack_marker ++ suffix; ps_alloc := al|>) /\
 phi_schedule_run
   (MAPi (\j inst. (inst, live_vars_at lv lbl (i + np + SUC j), halt))
     (TAKE k insts)) qs =
   (ops, qs with <|ps_stack := REPLICATE n dead_stack_marker ++ suffix; ps_alloc := al|>) /\
 generate_block_insts_prefix lv dfg cfg fn lbl halt np bl i k insts ps = SOME (pops,pe) /\
 generate_block_insts_prefix lv dfg cfg fn lbl halt np bl i k insts qs = SOME (qops,qe) /\
 lineage_core u pc pe /\ EVERY is_var_operand pc /\
 lineage_core v qc qe /\ EVERY is_var_operand qc ==>
 pops = qops /\ pc = qc /\ pe.ps_alloc = qe.ps_alloc /\
 pe.ps_spilled = ps.ps_spilled /\ qe.ps_spilled = qs.ps_spilled /\
 pe.ps_cleanup_height = ps.ps_cleanup_height /\
 qe.ps_cleanup_height = qs.ps_cleanup_height /\
 pe.ps_cleanup_promised = ps.ps_cleanup_promised /\
 qe.ps_cleanup_promised = qs.ps_cleanup_promised /\
 pe.ps_label_counter = ps.ps_label_counter /\ qe.ps_label_counter = qs.ps_label_counter /\
 pe.ps_cleanup_growth = ps.ps_cleanup_growth /\ qe.ps_cleanup_growth = qs.ps_cleanup_growth
Proof
 rpt gen_tac >> strip_tac >>
 gvs[actual_phi_prefix_run] >>
 qpat_x_assum `lineage_core u pc _` mp_tac >>
 qpat_x_assum `lineage_core v qc _` mp_tac >>
 simp[lineage_core_def] >> rpt strip_tac >>
 `FILTER (\op. op <> dead_stack_marker) pc = pc /\
  FILTER (\op. op <> dead_stack_marker) qc = qc` by
   (simp[FILTER_EQ_ID, EVERY_MEM] >>
    gvs[EVERY_MEM, stackPlanTypesTheory.is_var_operand_def,
        stackPlanGenTheory.dead_stack_marker_def] >>
    metis_tac[stackPlanTypesTheory.is_var_operand_def]) >>
 qpat_x_assum `_ = REPLICATE u dead_stack_marker ++ pc`
   (mp_tac o Q.AP_TERM `FILTER (\op. op <> dead_stack_marker)`) >>
 qpat_x_assum `_ = REPLICATE v dead_stack_marker ++ qc`
   (mp_tac o Q.AP_TERM `FILTER (\op. op <> dead_stack_marker)`) >>
 `!r. FILTER (\op. op <> dead_stack_marker) (REPLICATE r dead_stack_marker) = []` by
   simp[FILTER_EQ_NIL, EVERY_MEM, MEM_REPLICATE] >>
 simp[FILTER_APPEND]
QED

