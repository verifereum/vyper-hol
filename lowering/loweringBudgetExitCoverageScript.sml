(* Terminal coverage compares actual recorder counts, not fuel annotations. *)
Theory loweringBudgetExitCoverage
Ancestors
  loweringCallBudgetHistory loweringJointPrefixHistory
  contextCodegenRel venomInst list rich_list fragExec
  loweringBudgetPathDeterminism loweringBudgetTerminalFrontier
  loweringBudgetStoreRecorder

Theorem lower_budget_exit_certificate_bounds_path:
  !D0 lo0 explicit0 D lo explicit ctx p h_cert marks_cert r G' tn' h marks q.
    p.bp_stack = [] /\ MEM p.bp_fn ctx.ctx_functions /\
    (!fn. MEM fn ctx.ctx_functions ==>
      ALL_DISTINCT (fn_labels fn) /\
      !bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    lower_budget_certificate (D0,lo0,explicit0,ctx) p h_cert marks_cert
      (INR (r,G',tn')) /\
    exit_result r /\
    lower_budget_path F (D,lo,explicit,ctx) p h marks q ==>
    LENGTH h <= LENGTH h_cert /\
    lower_history_count h <= lower_history_count h_cert
Proof
  rpt gen_tac >> strip_tac >>
  `?qc mc i fuel.
    lower_budget_path T (D0,lo0,explicit0,ctx) p h_cert mc qc /\
    active_inst qc.bp_fn i qc.bp_state /\ i.inst_opcode <> INVOKE /\
    ((step_inst fuel ctx i qc.bp_state = r /\ exit_result r /\
      (!ret t. r = IntRet ret t ==> qc.bp_stack = [])) \/
     (?t. step_inst fuel ctx i qc.bp_state = OK t /\
       is_terminator i.inst_opcode /\ t.vs_halted))` by
    (gvs[lower_budget_certificate_def] >>
     metis_tac[exit_result_def]) >>
  `ALL_DISTINCT (fn_labels qc.bp_fn)` by
    metis_tac[lower_budget_path_current_fn_mem] >>
  `LENGTH h <= LENGTH h_cert` by
    (spose_not_then assume_tac >>
     `LENGTH h_cert <= LENGTH h /\ SUC (LENGTH h_cert) <= LENGTH h` by
       decide_tac >>
     qpat_assum `lower_budget_path F _ _ h _ _`
       (mp_then Any (qspec_then `LENGTH h_cert` mp_tac)
         lower_budget_path_take) >>
     disch_then drule >>
     disch_then (qx_choose_then `cutpoint`
       (qx_choose_then `cutmarks` strip_assume_tac)) >>
     `cutpoint = qc` by
       metis_tac[lower_budget_path_equal_length_sync, LENGTH_TAKE] >>
     qpat_assum `lower_budget_path F _ _ h _ _`
       (mp_then Any (qspec_then `SUC (LENGTH h_cert)` mp_tac)
         lower_budget_path_take) >>
     disch_then drule >> strip_tac >>
     gvs[TAKE_SUC_BY_TAKE, SNOC_APPEND] >>
     metis_tac[lower_budget_terminal_no_extension]) >>
  conj_tac >- simp[] >>
  qpat_assum `lower_budget_path T _ _ h_cert _ _`
    (mp_then Any (qspec_then `LENGTH h` mp_tac) lower_budget_path_take) >>
  disch_then drule >> strip_tac >>
  `MAP lower_event_consumes h =
   MAP lower_event_consumes (TAKE (LENGTH h) h_cert)` by
    metis_tac[lower_budget_path_equal_length_sync, LENGTH_TAKE] >>
  `LENGTH (FILTER I (MAP lower_event_consumes h)) =
   LENGTH (FILTER I (MAP lower_event_consumes (TAKE (LENGTH h) h_cert)))` by
    simp[] >>
  fs[FILTER_MAP, combinTheory.o_DEF, lower_history_count_def] >>
  `h_cert = TAKE (LENGTH h) h_cert ++ DROP (LENGTH h) h_cert` by
    simp[TAKE_DROP] >>
  metis_tac[FILTER_APPEND, LENGTH_APPEND, arithmeticTheory.LE_ADD]
QED
