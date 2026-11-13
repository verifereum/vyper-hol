(* TOP-LEVEL: alloca_history_no_alloca_slice - passing over a slice of
   non-ALLOCA instructions with the allocations unchanged keeps the
   allocation history. *)
Theory allocaHistorySlice
Ancestors
  allocaHistory venomInst venomState list arithmetic

(* A slice of non-ALLOCA instructions, passed over with the allocations
   unchanged, keeps the allocation history. *)
Theorem alloca_history_no_alloca_slice:
  !func s t bb insts rest.
    alloca_history func s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = insts ++ rest /\
    EVERY (\i. i.inst_opcode <> ALLOCA) insts ==>
    alloca_history func (t with vs_inst_idx := s.vs_inst_idx + LENGTH insts)
Proof
  rpt strip_tac >>
  `alloca_history func (s with vs_inst_idx := s.vs_inst_idx + LENGTH insts)` by
    (qpat_x_assum `alloca_history _ s`
       (strip_assume_tac o REWRITE_RULE [alloca_history_def]) >>
     rewrite_tac[alloca_history_def] >> conj_tac >- simp[] >>
     rpt strip_tac >>
     rename1 `get_instruction bb2 k = SOME inst` >>
     `k < s.vs_inst_idx + LENGTH insts` by
       (qpat_x_assum `k < _` mp_tac >> simp[]) >>
     `lookup_block s.vs_current_bb func.fn_blocks = SOME bb2` by
       (qpat_x_assum `lookup_block _ _ = SOME bb2` mp_tac >> simp[]) >>
     `bb2 = bb` by metis_tac[optionTheory.SOME_11] >>
     qpat_x_assum `bb2 = bb` SUBST_ALL_TAC >>
     Cases_on `k < s.vs_inst_idx` >- (simp[] >> metis_tac[]) >>
     `k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst` by
       (qpat_x_assum `get_instruction bb k = _` mp_tac >>
        rw[get_instruction_def]) >>
     `k - s.vs_inst_idx + s.vs_inst_idx = k` by decide_tac >>
     `k - s.vs_inst_idx < LENGTH insts` by decide_tac >>
     `EL (k - s.vs_inst_idx) (DROP s.vs_inst_idx bb.bb_instructions) = inst` by
       (qspecl_then [`k - s.vs_inst_idx`, `s.vs_inst_idx`, `bb.bb_instructions`]
          mp_tac listTheory.EL_DROP >> simp[]) >>
     `EL (k - s.vs_inst_idx) insts = inst` by
       (qpat_x_assum `EL _ (DROP _ _) = _` mp_tac >>
        qpat_x_assum `DROP _ _ = _ ++ _` (fn th => rewrite_tac [th]) >>
        simp[listTheory.EL_APPEND_EQN]) >>
     `MEM inst insts` by metis_tac[listTheory.EL_MEM] >>
     `inst.inst_opcode <> ALLOCA` by
       (qpat_x_assum `EVERY _ insts` mp_tac >>
        rewrite_tac[listTheory.EVERY_MEM] >>
        disch_then (qspec_then `inst` mp_tac) >> simp[]) >>
     metis_tac[]) >>
  irule alloca_history_frame >>
  qexists_tac `s with vs_inst_idx := s.vs_inst_idx + LENGTH insts` >> simp[]
QED
