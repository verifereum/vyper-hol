Theory fnLineageInvActualSchedule
Ancestors
  fnPlanPrefix fnPlanLineagePhiTemporal indexedLists stackPlanGen venomInst list arithmetic

Theorem actual_phi_prefix_run:
 !k insts lv dfg cfg fn lbl halt np bl i ps.
 k <= LENGTH insts /\ EVERY (\inst. inst.inst_opcode = PHI) (TAKE k insts) /\
 (k < LENGTH insts \/ bl = i + np + k) ==>
 generate_block_insts_prefix lv dfg cfg fn lbl halt np bl i k insts ps =
 SOME (phi_schedule_run
   (MAPi (\j inst. (inst, live_vars_at lv lbl (i + np + SUC j), halt))
     (TAKE k insts)) ps)
Proof
 Induct_on `k`
 >- simp[generate_block_insts_prefix_def, phi_schedule_run_def] >>
 Cases_on `insts` >- simp[] >> rpt gen_tac >> strip_tac >>
 gvs[generate_block_insts_prefix_def, generate_inst_plan_def,
     is_pre_codegen_opcode_def, is_unlowered_fmp_opcode_def,
     is_unlowered_internal_call_opcode_def, is_raw_fmp_opcode_def,
     indexedListsTheory.MAPi_def, combinTheory.o_DEF,
     phi_schedule_run_def] >>
 Cases_on `t` >> gvs[arithmeticTheory.ADD_CLAUSES,
   GSYM arithmeticTheory.ADD1] >>
 rpt (pairarg_tac >> gvs[]) >>
 qpat_x_assum `!insts. _` kall_tac >>
 qmatch_goalsub_abbrev_tac `MAPi f _` >>
 qmatch_asmsub_abbrev_tac `MAPi g _` >>
 `f = g` by simp[Abbr `f`, Abbr `g`, FUN_EQ_THM,
   arithmeticTheory.ADD_COMM] >> gvs[]
QED
