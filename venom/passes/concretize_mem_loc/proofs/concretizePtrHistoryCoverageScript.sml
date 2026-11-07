Theory concretizePtrHistoryCoverage
Ancestors
  concretizePtrContextRoot concretizePtrChronologicalHistory
  concretizePtrPairedRoot list finite_map

(* Conditional integration only: the universal step premise is not discharged. *)
Theorem ptr_paired_history_coverage:
  C.ctx_entry = Ct.ctx_entry /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions Ct.ctx_functions /\
  ptr_stage_placements Ct positions /\ vs.vs_vars = FEMPTY /\
  EVERY (\f. first_block_no_phi f /\ fn_inst_wf f /\
    EVERY bb_well_formed f.fn_blocks /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) Ct.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  (!h a ht at done tokens registry births PT TG saved entries H calls ws zt.
    ptr_paired_prefix R lp positions lo vs C Ct
      h a ht at done tokens registry births PT TG saved entries H calls ws /\
    a.po_inst.inst_opcode <> NOP /\
    at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
    ptr_chrono_step Ct at zt ==>
    ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
      delta <> [] /\ LENGTH snapshots = LENGTH delta /\
      ptr_paired_prefix R lp positions lo vs C Ct
        (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
        tokens' registry' births' PT' TG' saved' entries'
        (H ++ snapshots) calls' ws' /\
      z.po_inst.inst_opcode <> NOP /\
      zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst) ==>
  !ht at. ptr_chrono_history vs Ct ht at ==>
    ?h a done tokens registry births PT TG saved entries H calls ws.
      ptr_paired_prefix R lp positions lo vs C Ct
        h a ht at done tokens registry births PT TG saved entries H calls ws /\
      a.po_inst.inst_opcode <> NOP /\
      at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst
Proof
  disch_tac >> rpt gen_tac >> pop_assum mp_tac >>
  once_rewrite_tac[AND_IMP_INTRO] >>
  once_rewrite_tac[CONJ_COMM] >> pure_once_rewrite_tac[GSYM AND_IMP_INTRO] >>
  Induct_on `ptr_chrono_history vs Ct ht at` >>
  rpt strip_tac
  >- (`ptr_chrono_history vs Ct
         [ptr_observe [] [] FEMPTY entry_taint fn inst s1]
         (ptr_observe [] [] FEMPTY entry_taint fn inst s1)` by
        metis_tac[ptr_chrono_history_rules] >>
      `(ptr_observe [] [] FEMPTY entry_taint fn inst s1).po_stack = []` by
        simp[ptr_observe_def] >>
      drule_all ptr_paired_context_root >>
      disch_then (qspec_then `lo` strip_assume_tac) >>
      fs[ptr_observe_def] >>
      qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (irule_at Any) >> simp[]) >>
  qpat_x_assum `_ ==> ?h a done tokens registry births PT TG saved entries H calls ws. _`
    mp_tac >> impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `!h a ht at done tokens registry births PT TG saved entries H calls ws zt. _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ (_ ++ _) _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >> simp[]
QED
