Theory livenessSoundProofs
Ancestors
  livenessTerminationProofs
Libs
  listTheory rich_listTheory pairTheory arithmeticTheory pred_setTheory
  finite_mapTheory livenessDefsTheory livenessBlockProofsTheory
  livenessTransferProofsTheory livenessInvariantProofsTheory
  dfAnalyzeDefsTheory dfHelperDefsTheory venomInstTheory venomWfTheory

Theorem liveness_recompute_bounded:
  !fn lbl idx v.
    let st = liveness_recompute fn in
    MEM v (live_vars_at st lbl idx) ==> MEM v (fn_all_vars fn.fn_blocks)
Proof
  simp[live_vars_at_def] >> rpt strip_tac >>
  irule lv_bounded_read >> qexistsl_tac [`idx`,`lbl`,`liveness_recompute fn`] >>
  simp[] >> metis_tac[liveness_recompute_invariant, lv_inv_def]
QED

Definition lv_witness_def:
  lv_witness bbs cfg l i v <=>
    ?path. cfg_exec_path cfg ((l,i)::path) /\
           used_before_defined bbs v ((l,i)::path)
End

Theorem lv_witness_use:
  var_used_at bbs l i v ==> lv_witness bbs cfg l i v
Proof
  strip_tac >> simp[lv_witness_def] >> qexists_tac `[]` >>
  simp[cfg_exec_path_def, used_before_defined_def] >> qexists_tac `0` >> simp[]
QED

Theorem lv_witness_prepend:
  lv_witness bbs cfg l' i' v /\ ~var_defined_at bbs l i v /\
  ((l = l' /\ i' = i + 1) \/ (MEM l' (cfg_succs_of cfg l) /\ i' = 0)) ==>
  lv_witness bbs cfg l i v
Proof
  simp[lv_witness_def] >> rpt strip_tac >>
  qexists_tac `(l',i')::path` >> simp[cfg_exec_path_def] >>
  gvs[used_before_defined_def] >> qexists_tac `SUC k` >> simp[] >>
  rpt strip_tac >> Cases_on `j` >> gvs[]
QED

Theorem lv_witness_transfer:
  lookup_block l bbs = SOME bb /\ i < LENGTH bb.bb_instructions /\
  (!v. MEM v live ==> lv_witness bbs cfg l (SUC i) v) /\
  MEM v (liveness_transfer bbs (EL i bb.bb_instructions) live) ==>
  lv_witness bbs cfg l i v
Proof
  simp[liveness_transfer_def, live_update_mem] >> rpt strip_tac
  >- (irule lv_witness_prepend >>
      conj_tac >- (simp[var_defined_at_def] >> metis_tac[]) >>
      qexistsl_tac [`SUC i`,`l`] >> simp[])
  >> irule lv_witness_use >> simp[var_used_at_def] >> metis_tac[]
QED

Theorem lv_witness_backwards:
  !n i. lv_witness bbs cfg l (i+n) v /\
    (!j. i <= j /\ j < i+n ==> ~var_defined_at bbs l j v) ==>
    lv_witness bbs cfg l i v
Proof
  Induct >- simp[] >> rpt strip_tac >>
  irule lv_witness_prepend >> conj_tac
  >- (first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
  qexistsl_tac [`SUC i`,`l`] >> simp[] >>
  first_x_assum irule >> conj_tac
  >- (rpt gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
  metis_tac[ADD_CLAUSES]
QED

Theorem lv_phi_witness:
  lookup_block l bbs = SOME bb /\ bb_well_formed bb /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
  MEM (src,v) (phi_pairs inst.inst_operands) ==>
  lv_witness bbs cfg l 0 v
Proof
  rpt strip_tac >>
  `?k. k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst`
    by metis_tac[MEM_EL] >>
  irule lv_witness_backwards >> qexists_tac `k` >> simp[] >> reverse conj_tac
  >- (irule lv_witness_use >> simp[var_used_at_def] >>
      `MEM v (operand_vars inst.inst_operands)` suffices_by simp[inst_uses_def] >>
      qpat_x_assum `MEM (src,v) _` mp_tac >>
      qspec_tac (`inst.inst_operands`,`ops`) >>
      ho_match_mp_tac phi_pairs_ind >>
      rw[phi_pairs_def, operand_vars_def, operand_var_def] >>
      rpt strip_tac >> TRY (Cases_on `operand_var v1`) >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[var_defined_at_def] >>
  fs[bb_well_formed_def] >> metis_tac[]
QED

Definition lv_sound_def:
  lv_sound bbs cfg st <=>
    !l i v. MEM v (df_at [] st l i) ==> lv_witness bbs cfg l i v
End

Theorem lv_out_witness:
  wf_function fn /\ lv_sound fn.fn_blocks (cfg_analyze fn) st /\
  MEM v (liveness_out fn.fn_blocks (cfg_analyze fn) l st) ==>
  lv_witness fn.fn_blocks (cfg_analyze fn) l
    (LENGTH (liveness_instrs fn.fn_blocks l)) v
Proof
  simp[liveness_out_def, mem_foldl_list_union, MEM_MAP] >> rpt strip_tac >>
  rename1 `MEM s (cfg_succs_of (cfg_analyze fn) l)` >>
  `lv_witness fn.fn_blocks (cfg_analyze fn) s 0 v` by
    (Cases_on `lookup_block s fn.fn_blocks` >>
     gvs[liveness_edge_transfer_def]
     >- metis_tac[lv_sound_def] >>
     drule input_vars_from_phi_correct_proof >> strip_tac
     >- metis_tac[lv_sound_def] >>
     irule lv_phi_witness >>
     metis_tac[wf_function_def, lookup_block_mem]) >>
  irule lv_witness_prepend >> conj_tac
  >- (simp[var_defined_at_def, liveness_instrs_def] >>
      Cases_on `lookup_block l fn.fn_blocks` >> simp[]) >>
  qexistsl_tac [`0`,`s`] >> simp[]
QED

Theorem lv_block_witness:
  wf_function fn /\ lv_sound fn.fn_blocks (cfg_analyze fn) st ==>
  !n l i v. n = LENGTH (liveness_instrs fn.fn_blocks l) - i /\
    i <= LENGTH (liveness_instrs fn.fn_blocks l) /\
    MEM v (df_at [] (liveness_block fn.fn_blocks (cfg_analyze fn) l st) l i) ==>
    lv_witness fn.fn_blocks (cfg_analyze fn) l i v
Proof
  strip_tac >> Induct
  >- (rpt strip_tac >>
      `i = LENGTH (liveness_instrs fn.fn_blocks l)` by decide_tac >>
      gvs[liveness_block_exit] >> metis_tac[lv_out_witness]) >>
  rpt strip_tac >>
  `i < LENGTH (liveness_instrs fn.fn_blocks l)` by decide_tac >>
  drule liveness_block_transfer >> disch_then (qspecl_then [`st`,`cfg_analyze fn`] assume_tac) >>
  Cases_on `lookup_block l fn.fn_blocks` >> gvs[liveness_instrs_def] >>
  irule lv_witness_transfer >>
  qexistsl_tac [`x`,`df_at [] (liveness_block fn.fn_blocks (cfg_analyze fn) l st) l (SUC i)`] >>
  simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[liveness_instrs_def] >> decide_tac
QED

Theorem lv_sound_block:
  wf_function fn /\ lv_sound fn.fn_blocks (cfg_analyze fn) st ==>
  lv_sound fn.fn_blocks (cfg_analyze fn)
    (liveness_block fn.fn_blocks (cfg_analyze fn) l st)
Proof
  strip_tac >> simp[lv_sound_def] >> rpt strip_tac >>
  Cases_on `l' = l`
  >- (gvs[] >> Cases_on `i <= LENGTH (liveness_instrs fn.fn_blocks l)`
      >- (irule lv_block_witness >> metis_tac[]) >>
      `LENGTH (liveness_instrs fn.fn_blocks l) < i` by decide_tac >>
      gvs[liveness_block_beyond] >> metis_tac[lv_sound_def]) >>
  gvs[liveness_block_other_inst] >> metis_tac[lv_sound_def]
QED

Theorem lv_sound_init:
  lv_sound bbs cfg (init_df_state [] labels)
Proof
  simp[lv_sound_def, init_df_state_def, df_at_def]
QED

Theorem lv_sound_fuel:
  wf_function fn ==>
  !fuel wl st. lv_sound fn.fn_blocks (cfg_analyze fn) st ==>
    lv_sound fn.fn_blocks (cfg_analyze fn)
      (SND (wl_iterate_fuel fuel (liveness_changed fn.fn_blocks)
        (liveness_block fn.fn_blocks (cfg_analyze fn))
        (cfg_preds_of (cfg_analyze fn)) wl st))
Proof
  strip_tac >> Induct >> simp[worklistDefsTheory.wl_iterate_fuel_def] >>
  rpt strip_tac >> Cases_on `wl` >>
  simp[worklistDefsTheory.wl_iterate_fuel_def] >>
  Cases_on `liveness_changed fn.fn_blocks h st
    (liveness_block fn.fn_blocks (cfg_analyze fn) h st)` >>
  simp[worklistDefsTheory.wl_step_def, lv_sound_block]
QED

Theorem liveness_recompute_sound:
  !fn lbl idx v.
    let cfg = cfg_analyze fn in
    let st = liveness_recompute fn in
    let bbs = fn.fn_blocks in
    wf_function fn /\ MEM v (live_vars_at st lbl idx) ==>
    ?path. cfg_exec_path cfg ((lbl,idx)::path) /\
           used_before_defined bbs v ((lbl,idx)::path)
Proof
  simp[live_vars_at_def] >> rpt strip_tac >>
  `?fuel. liveness_recompute_fuel fuel fn = liveness_recompute fn` by
    metis_tac[liveness_recompute_fuel_agreement] >>
  `lv_sound fn.fn_blocks (cfg_analyze fn) (liveness_recompute_fuel fuel fn)` by
    (simp_tac pure_ss [liveness_recompute_fuel_def, LET_THM] >>
     irule lv_sound_fuel >> simp[lv_sound_init]) >>
  metis_tac[lv_sound_def, lv_witness_def]
QED

val _ = List.app (fn (_,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail "oracle in liveness soundness API")
  (DB.thms "livenessSoundProofs");
