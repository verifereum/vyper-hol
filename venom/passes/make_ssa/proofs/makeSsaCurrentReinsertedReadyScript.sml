Theory makeSsaCurrentReinsertedReady
Ancestors makeSsaCurrentReinsertedOrigin makeSsaCurrentPhiBatch
  makeSsaCurrentRetainedNonclobber
  makeSsaCurrentCleanupRuntime venomExecSemantics venomState stateFrame
  finite_map list rich_list

Theorem current_eval_one_phi_output:
  eval_one_phi st inst = SOME (dst,value) ==> inst.inst_outputs = [dst]
Proof
  simp[eval_one_phi_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem current_phi_batch_selected_value:
  !pre r incoming post src value.
  EVERY (\i. i.inst_opcode = PHI) pre /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) pre)) /\
  r < LENGTH pre /\ eval_one_phi incoming (EL r pre) = SOME (src,value) /\
  eval_phis incoming pre = OK post ==> lookup_var src post = SOME value
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `r`
  >- (gvs[eval_phis_def, AllCaseEqs()] >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  gvs[eval_phis_def, AllCaseEqs(), ALL_DISTINCT_APPEND] >>
  `h.inst_outputs = [out]` by metis_tac[current_eval_one_phi_output] >>
  `(EL n pre).inst_outputs = [src]` by metis_tac[current_eval_one_phi_output] >>
  `src <> out` by
    (fs[MEM_FLAT, MEM_MAP] >> metis_tac[EL_MEM, MEM]) >>
  first_x_assum drule_all >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem current_cleanup_segment_next_ready:
  insts = pre ++ copies ++ rest /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) /\
  r < LENGTH pre /\ k < LENGTH copies /\
  (EL r pre).inst_outputs = [src] /\
  (EL k copies).inst_opcode = ASSIGN /\
  (EL k copies).inst_operands = [Var src] /\
  (EL k copies).inst_outputs = [dst] /\
  EVERY current_cleanup_shape copies /\ lookup_var src post = SOME value /\
  current_copies_run (TAKE k copies) post = OK before ==>
  ?after. step_inst_base (EL k copies) before = OK after /\
    lookup_var dst after = SOME value /\
    execution_frame after = execution_frame before /\
    after.vs_current_bb = before.vs_current_bb /\
    after.vs_prev_bb = before.vs_prev_bb
Proof
  strip_tac >>
  `MEM src (FLAT (MAP (\i. i.inst_outputs) pre))` by
    (simp[MEM_FLAT, MEM_MAP] >> qexists `[src]` >> simp[] >>
     metis_tac[EL_MEM]) >>
  `~MEM src (FLAT (MAP (\i. i.inst_outputs) copies))` by
    metis_tac[current_outputs_split_nonclobber] >>
  `lookup_var src before = lookup_var src post` by
    (irule current_copies_run_untouched >>
     qexists `TAKE k copies` >>
     simp[EVERY_TAKE] >> rpt strip_tac >>
     metis_tac[current_outputs_take_subset, MEM_FLAT, MEM_MAP]) >>
  qexists `update_var dst value before` >>
  drule_all current_cleanup_assign_step >>
  disch_then (qspec_then `before` mp_tac) >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem current_certificate_reinserted_next_ready:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  fn_phi_outputs_single_def fn /\ blocks_have_leading_phi fn.fn_blocks /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [v] /\ current_actual_inserted fn v h /\
  fn_phis_non_degenerate fn /\ old.bb_instructions = phis ++ tail /\
  EVERY (\p. p.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH phis ==>
  ?out src r c batch.
    lookup_block h fn'.fn_blocks = SOME out /\
    current_token_name H (CurrentOriginal h i 0) = SOME src /\ src <> v /\
    r < batch /\ batch <= c /\ c < LENGTH out.bb_instructions /\
    (EL r out.bb_instructions).inst_opcode = PHI /\
    (EL r out.bb_instructions).inst_outputs = [src] /\
    (EL c out.bb_instructions).inst_opcode = ASSIGN /\
    (EL c out.bb_instructions).inst_operands = [Var src] /\
    (EL c out.bb_instructions).inst_outputs = [v] /\
    EVERY (\p. p.inst_opcode = PHI) (TAKE batch out.bb_instructions) /\
    (DROP batch out.bb_instructions = [] \/
     (HD (DROP batch out.bb_instructions)).inst_opcode <> PHI) /\
    (!copies rest incoming post before value.
      out.bb_instructions = TAKE batch out.bb_instructions ++ copies ++ rest /\
      c < batch + LENGTH copies /\ EVERY current_cleanup_shape copies /\
      eval_one_phi incoming (EL r out.bb_instructions) = SOME (src,value) /\
      eval_phis incoming (TAKE batch out.bb_instructions) = OK post /\
      current_copies_run (TAKE (c-batch) copies) post = OK before ==>
      ?after. step_inst_base (EL c out.bb_instructions) before = OK after /\
        lookup_var v after = SOME value /\
        execution_frame after = execution_frame before /\
        after.vs_current_bb = before.vs_current_bb /\
        after.vs_prev_bb = before.vs_prev_bb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_certificate_reinserted_origin >>
  disch_then (qx_choose_then `out` (qx_choose_then `src`
    (qx_choose_then `r` (qx_choose_then `c` (qx_choose_then `batch`
      (map_every assume_tac o CONJUNCTS)))))) >>
  `ALL_DISTINCT (FLAT (MAP (\j. j.inst_outputs) out.bb_instructions))` by
    (irule current_certificate_block_outputs_distinct >> metis_tac[]) >>
  qexistsl_tac [`out`, `src`, `r`, `c`, `batch`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `LENGTH (TAKE batch out.bb_instructions) = batch` by simp[] >>
  `ALL_DISTINCT (FLAT (MAP (\j. j.inst_outputs)
    (TAKE batch out.bb_instructions)))` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >>
     qpat_assum `out.bb_instructions = _ ++ _`
       (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     simp[ALL_DISTINCT_APPEND]) >>
  `lookup_var src post = SOME value` by
    (irule current_phi_batch_selected_value >>
     qexistsl_tac [`incoming`, `TAKE batch out.bb_instructions`, `r`] >>
     simp[EL_TAKE]) >>
  `EL (c-batch) copies = EL c out.bb_instructions` by
    (qpat_x_assum `out.bb_instructions = _ ++ _` (fn th => once_rewrite_tac[th]) >>
     simp[EL_APPEND_EQN]) >>
  `r < LENGTH (TAKE batch out.bb_instructions) /\
   c-batch < LENGTH copies /\
   (EL r (TAKE batch out.bb_instructions)).inst_outputs = [src] /\
   (EL (c-batch) copies).inst_opcode = ASSIGN /\
   (EL (c-batch) copies).inst_operands = [Var src] /\
   (EL (c-batch) copies).inst_outputs = [v]` by simp[EL_TAKE] >>
  drule_all current_cleanup_segment_next_ready >> simp[]
QED
