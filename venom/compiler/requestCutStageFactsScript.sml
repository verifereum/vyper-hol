Theory requestCutStageFacts
Ancestors
  o1PipelineCompose o1DftStageSsa dftContractGas
  o1PassContract venomPassSchedule dftRunRel dftDefs unitMemInv
  venomState venomInst venomWf list arithmetic

Theorem request_cut_stage_facts:
  (!i. i < 9 ==> ctx_pass_stage rp (EL i o1_fn_passes) (o1_walk_view rp i)
    (stage i) (stage (SUC i))) /\
  (!i. i <= 9 ==> o1_ctx_shape (stage i) /\
    EVERY (o1_fn_row i) (stage i).ctx_functions) /\
  code_layout_valid v ==>
  ctx_pass_stage rp (CFP_Simple VP_DFT) (o1_walk_view rp 7) (stage 7) (stage 8) /\
  ctx_pass_stage rp (CFP_Simple VP_CFGNormalization) (o1_walk_view rp 8) (stage 8) (stage 9) /\
  o1_pre 7 (stage 7) (stage 8) /\
  EVERY wf_ssa (stage 7).ctx_functions /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn)) (stage 7).ctx_functions /\
  LIST_REL (\f g. g = dft_fn f) (stage 7).ctx_functions (stage 8).ctx_functions /\
  LIST_REL dft_fn_rel (stage 7).ctx_functions (stage 8).ctx_functions /\
  (stage 8).ctx_entry = (stage 7).ctx_entry /\
  ctx_labels_bound (stage 7) v.vs_labels /\
  max_live_eom (stage 9) = max_live_eom (stage 7) /\
  (!i. i <= 9 ==> EVERY wf_function (stage i).ctx_functions)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!i. i < 9 ==> _` (fn th =>
    map_every (fn n => assume_tac (SIMP_RULE (srw_ss()) [o1_fn_passes_def] (Q.SPEC n th)))
      [`7`, `8`]) >>
  qpat_assum `!i. i <= 9 ==> _` (fn th =>
    map_every (fn n => strip_assume_tac (SIMP_RULE (srw_ss()) [] (Q.SPEC n th)))
      [`7`, `8`]) >>
  `o1_pre 7 (stage 7) (stage 8)` by simp[o1_pre_def] >>
  `EVERY wf_ssa (stage 7).ctx_functions /\
   EVERY (\fn. EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn))
     (stage 7).ctx_functions` by
    (fs[o1_fn_row_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all dft_stage_fn_rel >> strip_tac >>
  `ctx_labels_bound (stage 7) v.vs_labels` by metis_tac[dft_ctx_labels_bound] >>
  `max_live_eom (stage 9) = max_live_eom (stage 7)` by
    (mp_tac (Q.INST [`rpolicy` |-> `rp`] o1_walk_stages_max_live_eom) >>
     simp[o1_fn_passes_def] >> disch_tac >>
     qpat_assum `!j. j + 3 <= 9 ==> _` (fn th =>
       map_every (fn n => assume_tac (SIMP_RULE (srw_ss()) [] (Q.SPEC n th)))
         [`4`, `6`]) >> simp[]) >>
  simp[] >> rpt strip_tac >>
  `o1_ctx_shape (stage i)` by metis_tac[] >>
  fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]
QED
