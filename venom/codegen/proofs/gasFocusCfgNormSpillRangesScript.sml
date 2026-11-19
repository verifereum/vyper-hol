Theory gasFocusCfgNormSpillRanges
Ancestors
  o1ContractCfgNormJointCursors o1ContractCfgNormCursorProjection
  o1PassLift o1PassContract frameJointTransition
  contextPlanLayoutProps unitMemInv memSafeRun venomState
  list pair arithmetic words

(* The current cursor suffices for both spill checks, before any edge is taken. *)
Theorem focus_cfg_norm_pre_edge_ranges:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  generate_context_plan C9 = SOME cpl /\
  ~in_revert_forward fn9 s9 /\
  ((inst_mem_ranges inst9 s9 <> [] /\
    inst_mem_ranges inst9 s9 = inst_mem_ranges inst8 s8 /\
    ~in_revert_forward fn8 s8) ==>
     lowered_mem_fact cpl.cp_max_static_eom C8 fn8 inst8 s8 /\
     cpl.cp_initial_fmp <= w2n s8.vs_initial_fmp) ==>
  source_memory_reads_disjoint cpl inst9 s9 /\
  context_source_memory_writes_disjoint cpl inst9 s9
Proof
  strip_tac >>
  `lowered_mem_ok cpl.cp_max_static_eom cpl.cp_initial_fmp C9 fn9 inst9 s9` by
    (Cases_on `inst_mem_ranges inst9 s9 = []`
     >- simp[lowered_mem_ok_def] >>
     `inst_mem_ranges inst9 s9 = inst_mem_ranges inst8 s8 /\
      ~in_revert_forward fn8 s8` by
       (Cases_on `current` >> gvs[cfg_norm_joint_cursors_def] >>
        qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        disch_then drule >> simp[] >> strip_tac >>
        metis_tac[cfg_norm_cursors_projection, mem_corr_def]) >>
     `lowered_mem_fact cpl.cp_max_static_eom C8 fn8 inst8 s8 /\
      cpl.cp_initial_fmp <= w2n s8.vs_initial_fmp` by simp[] >>
     fs[lowered_mem_fact_def, lowered_mem_ok_def, EVERY_MEM, FORALL_PROD] >>
     rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  drule generate_context_plan_spill_gap >> strip_tac >>
  conj_tac
  >- (irule lowered_reads_disjoint >> metis_tac[]) >>
  irule lowered_writes_disjoint >> metis_tac[]
QED
