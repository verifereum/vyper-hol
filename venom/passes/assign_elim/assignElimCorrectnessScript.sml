(*
 * Assign Elimination — Correctness Statement
 *
 * Copy propagation preserves semantics: replacing Var x with Var y
 * where x := assign y gives the same value because copy_sound ensures
 * lookup_var x s = lookup_var y s at every use site.
 *
 * Variables that are outputs of NOP'd ASSIGNs are excluded from
 * equivalence (assign_elim_eliminated_vars). These variables are dead
 * after copy propagation substitutes all their uses with the source.
 *
 * The error disjunct covers the edge case where a forwardable ASSIGN's
 * Var source is undefined at runtime. In SSA programs with proper
 * dominance, this is unreachable, but we don't have a formal dominance
 * predicate so it appears as a disjunct.
 *
 * Preconditions:
 *   wf_function fn — well-formed function (unique labels, entry, bb_well_formed)
 *   fn_inst_wf fn — all instructions structurally well-formed
 *   s.vs_inst_idx = 0 — standard execution entry point
 *   fn_entry_label fn = SOME s.vs_current_bb — execution starts at entry
 *   non-terminator interior — no non-last instruction is a terminator
 *   operand_cond — no instruction in the substituted function reads
 *     an eliminated variable (holds in SSA form)
 *)

Theory assignElimCorrectness
Ancestors
  assignElimProofs passSharedProps passSimulationProps
  assignElimDefs passSharedDefs venomWf venomInst venomState
  passSimulationDefs analysisSimDefs
  assignElimConvergence dfAnalyzeProofs
Libs
  indexedListsTheory

Theorem assign_elim_function_correct:
  !fuel ctx fn s.
    let elim = assign_elim_eliminated_vars fn in
    let result = copy_prop_analyze fn in
    let fn_subst = analysis_function_transform NONE result
                     (\v inst. [assign_subst_inst v inst]) fn in
    wf_function fn /\
    fn_inst_wf fn /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    (!bb inst x.
       MEM bb fn_subst.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN elim) ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv elim) (execution_equiv elim) (execution_equiv elim)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (assign_elim_function fn) s)
Proof
  ACCEPT_TAC assign_elim_function_correct_proof
QED

(* ===== Per-instruction structural properties ===== *)

Triviality aei_preserves_id[local]:
  !pv v inst. (assign_elim_inst pv v inst).inst_id = inst.inst_id
Proof
  rw[assign_elim_inst_def, LET_THM, mk_nop_inst_def]
QED

Triviality aei_term_opcode[local]:
  !pv v inst. is_terminator inst.inst_opcode ==>
    (assign_elim_inst pv v inst).inst_opcode = inst.inst_opcode
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> PHI` by
    (Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  `~is_forwardable_assign pv inst` by
    (simp[is_forwardable_assign_def] >>
     Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  simp[assign_elim_inst_def, LET_THM]
QED

Triviality aei_opcode[local]:
  !pv v inst. (assign_elim_inst pv v inst).inst_opcode = inst.inst_opcode \/
              (assign_elim_inst pv v inst).inst_opcode = NOP
Proof
  rpt strip_tac >>
  simp[assign_elim_inst_def, LET_THM] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  Cases_on `is_forwardable_assign pv inst` >> simp[mk_nop_inst_def]
QED

Triviality aei_outputs[local]:
  !pv v inst. (assign_elim_inst pv v inst).inst_outputs = inst.inst_outputs \/
              (assign_elim_inst pv v inst).inst_outputs = []
Proof
  rpt strip_tac >>
  simp[assign_elim_inst_def, LET_THM] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  Cases_on `is_forwardable_assign pv inst` >> simp[mk_nop_inst_def]
QED

(* ===== Copy lattice no-Label invariant ===== *)

(* copy_prop_transfer never introduces Label values into the copy map.
   is_forwardable_assign requires src ≠ Label, and transitive resolution
   through existing Label-free copies also gives non-Label values.
   Proved for the full assign_elim_function pipeline: after unwrap_copies,
   get_label of any substituted operand is preserved. *)
Triviality copy_map_no_label[local]:
  !pv inst copies_opt.
    (!k v. FLOOKUP (unwrap_copies copies_opt) k = SOME v ==>
           !l. v <> Label l) ==>
    (!k v. FLOOKUP (unwrap_copies (copy_prop_transfer pv inst copies_opt)) k =
             SOME v ==>
           !l. v <> Label l)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[copy_prop_transfer_def, LET_THM, unwrap_copies_def] >>
  Cases_on `copies_opt` >> simp[] >>
  rename1 `SOME copies` >>
  simp[finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  BasicProvers.every_case_tac >> gvs[] >>
  gvs[finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE,
      is_forwardable_assign_def] >>
  gvs[unwrap_copies_def] >> res_tac >> gvs[] >>
  BasicProvers.every_case_tac >> gvs[] >> res_tac >> gvs[]
QED

(* The get_label of subst_op_map results matches original when copies are Label-free *)
Triviality subst_op_map_preserves_get_label[local]:
  !copies op.
    (!k v. FLOOKUP copies k = SOME v ==> !l. v <> Label l) ==>
    get_label (subst_op_map copies op) = get_label op
Proof
  rpt strip_tac >>
  Cases_on `op` >> simp[subst_op_map_def, get_label_def] >>
  Cases_on `FLOOKUP copies s` >> simp[get_label_def] >>
  rename1 `SOME val` >>
  `!l. val <> Label l` by metis_tac[] >>
  Cases_on `val` >> gvs[get_label_def]
QED

(* Join preserves no-Label bilaterally *)
Triviality copy_prop_join_no_label[local]:
  !a b.
    (!k v. FLOOKUP (unwrap_copies a) k = SOME v ==> !l. v <> Label l) /\
    (!k v. FLOOKUP (unwrap_copies b) k = SOME v ==> !l. v <> Label l) ==>
    (!k v. FLOOKUP (unwrap_copies (copy_prop_join a b)) k = SOME v ==>
           !l. v <> Label l)
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[copy_prop_join_def, unwrap_copies_def, copy_prop_join_raw_def,
       finite_mapTheory.FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> res_tac
QED

(* df_process_block doesn't modify ds_inst *)
Triviality process_block_inst_unchanged[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st.
    (df_process_block dir bottom join transfer edge_transfer
       ctx entry_val cfg bbs lbl st).ds_inst = st.ds_inst
Proof
  rpt gen_tac >> simp[dfAnalyzeDefsTheory.df_process_block_def, LET_THM] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >> simp[]
QED

(* FOLDL of join on no-Label values preserves no-Label *)
Triviality foldl_join_no_label[local]:
  !preds g init.
    (!k v. FLOOKUP (unwrap_copies init) k = SOME v ==> !l. v <> Label l) /\
    (!pred. MEM pred preds ==>
      !k v. FLOOKUP (unwrap_copies (g pred)) k = SOME v ==>
            !l. v <> Label l) ==>
    !k v. FLOOKUP (unwrap_copies
      (FOLDL (\acc pred. copy_prop_join acc (g pred)) init preds)) k =
      SOME v ==> !l. v <> Label l
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >> simp[] >>
  first_x_assum (qspecl_then [`g`, `copy_prop_join init (g h)`] mp_tac) >>
  impl_tac >- (fs[] >> metis_tac[copy_prop_join_no_label]) >>
  simp[]
QED

(* FOLDL of copy_prop_join directly on a list of values *)
Triviality foldl_join_vals_no_label[local]:
  !vals init.
    (!k v. FLOOKUP (unwrap_copies init) k = SOME v ==> !l. v <> Label l) /\
    EVERY (\val. !k v. FLOOKUP (unwrap_copies val) k = SOME v ==>
                       !l. v <> Label l) vals ==>
    !k v. FLOOKUP (unwrap_copies (FOLDL copy_prop_join init vals)) k =
      SOME v ==> !l. v <> Label l
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  PURE_ONCE_REWRITE_TAC[listTheory.FOLDL] >> BETA_TAC >>
  first_x_assum match_mp_tac >>
  conj_tac
  >- (match_mp_tac copy_prop_join_no_label >>
      conj_tac >> first_x_assum ACCEPT_TAC)
  >> first_x_assum ACCEPT_TAC
QED

(* Process changed equivalence (replicated from dfAnalyzeProofs) *)
Triviality process_changed_equiv[local]:
  !dir (bottom:'a) join transfer edge_transfer ctx entry_val cfg bbs lbl st.
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let changed = (\lbl (old:'a df_state) new.
                     df_boundary bottom new lbl <> df_boundary bottom old lbl) in
    changed lbl st (process lbl st) <=> process lbl st <> st
Proof
  rw[dfAnalyzeDefsTheory.df_process_block_def,
     dfAnalyzeDefsTheory.df_boundary_def] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >> simp[] >>
  simp[dfAnalyzeDefsTheory.df_state_component_equality,
       finite_mapTheory.fmap_eq_flookup,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  CCONTR_TAC >> fs[] >>
  first_x_assum (qspec_then `lbl` mp_tac) >> simp[] >>
  Cases_on `FLOOKUP st.ds_boundary lbl` >> fs[]
QED

(* ===== Boundary no-Label at worklist fixpoint ===== *)

(* The no-label predicate on a df_state's boundary *)
Definition boundary_no_label_def:
  boundary_no_label (st : copy_lattice option df_state) <=>
    !lbl v. FLOOKUP st.ds_boundary lbl = SOME v ==>
      !k w. FLOOKUP (unwrap_copies v) k = SOME w ==> !l. w <> Label l
End

(* df_boundary satisfies no-Label when state does *)
Triviality df_boundary_no_label[local]:
  !st lbl.
    boundary_no_label st ==>
    !k w. FLOOKUP (unwrap_copies (df_boundary NONE st lbl)) k = SOME w ==>
    !l. w <> Label l
Proof
  rpt strip_tac >>
  `?v. FLOOKUP st.ds_boundary lbl = SOME v /\
       FLOOKUP (unwrap_copies v) k = SOME w` by (
    fs[dfAnalyzeDefsTheory.df_boundary_def] >>
    Cases_on `FLOOKUP st.ds_boundary lbl` >> fs[unwrap_copies_def]) >>
  qpat_x_assum `boundary_no_label _`
    (mp_tac o REWRITE_RULE [boundary_no_label_def]) >>
  disch_then (qspecl_then [`lbl`, `v`] mp_tac) >>
  impl_tac >- first_x_assum ACCEPT_TAC >>
  disch_then (qspecl_then [`k`, `w`] mp_tac) >>
  impl_tac >- first_x_assum ACCEPT_TAC >>
  simp[]
QED

(* P-instantiated versions for the no-label predicate *)
local
  val ty = ``:copy_lattice option``
  val nlP = ``\(v : copy_lattice option).
    !k w. FLOOKUP (unwrap_copies v) k = SOME w ==> !l. w <> Label l``
  fun inst_P thm =
    let val P_var = hd (free_vars (concl thm))
        val tyvar = hd (type_vars (snd (dest_var P_var)))
        val thm1 = INST_TYPE [tyvar |-> ty] thm
        val P_var1 = hd (free_vars (concl thm1))
    in BETA_RULE (INST [P_var1 |-> nlP] thm1) end
in
  val df_fold_no_label = REWRITE_RULE [GSYM AND_IMP_INTRO]
    (cj 1 (inst_P dfAnalyzeProofsTheory.df_fold_block_P))
  val df_joined_no_label =
    inst_P dfAnalyzeProofsTheory.df_joined_val_P
  val populate_no_label =
    inst_P dfAnalyzeProofsTheory.populate_inst_P
end;

(* fold final_val inherits no-label from boundary_no_label *)
Triviality fold_final_val_no_label[local]:
  !fn lbl st final_val inst_map.
    boundary_no_label st /\
    df_fold_block Forward (copy_prop_transfer (phi_used_vars fn)) lbl
      (case lookup_block lbl fn.fn_blocks of
         NONE => [] | SOME bb => bb.bb_instructions)
      (df_joined_val Forward NONE copy_prop_join copy_prop_edge_transfer
         (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) st lbl) = (final_val, inst_map)
    ==>
    !k w. FLOOKUP (unwrap_copies final_val) k = SOME w ==> !l. w <> Label l
Proof
  rpt gen_tac >> strip_tac >>
  (* Prove init_val (joined_val) is label-free *)
  `!k w. FLOOKUP (unwrap_copies (df_joined_val Forward NONE copy_prop_join
      copy_prop_edge_transfer (phi_used_vars fn)
      (OPTION_MAP (\lbl. (lbl,SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) st lbl)) k = SOME w ==> !l. w <> Label l` by
    (ho_match_mp_tac df_joined_no_label >>
     rpt conj_tac
     >- simp[unwrap_copies_def]
     >- (Cases_on `fn_entry_label fn` >> simp[unwrap_copies_def])
     >- metis_tac[copy_prop_join_no_label]
     >- simp[copy_prop_edge_transfer_def]
     >> qpat_x_assum `boundary_no_label _`
          (ACCEPT_TAC o REWRITE_RULE [boundary_no_label_def])) >>
  (* Prove transfer preserves label-freeness *)
  `!inst a. (!k w. FLOOKUP (unwrap_copies a) k = SOME w ==> !l. w <> Label l)
    ==> !k w. FLOOKUP (unwrap_copies (copy_prop_transfer (phi_used_vars fn)
          inst a)) k = SOME w ==> !l. w <> Label l` by
    metis_tac[copy_map_no_label] >>
  (* Apply df_fold_block_P, discharging both premises *)
  qpat_x_assum `df_fold_block _ _ _ _ _ = _`
    (mp_tac o MATCH_MP df_fold_no_label) >>
  impl_tac >- first_x_assum ACCEPT_TAC >>
  impl_tac >- first_x_assum ACCEPT_TAC >>
  simp[]
QED

(* Processing preserves boundary_no_label *)
Triviality process_boundary_no_label[local]:
  !fn lbl st.
    boundary_no_label st ==>
    boundary_no_label
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt gen_tac >> strip_tac >>
  simp[dfAnalyzeDefsTheory.df_process_block_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >- simp[] >>
  (* Changed case: boundary updated at lbl *)
  simp[boundary_no_label_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `lbl' = lbl` >> gvs[]
  >- (
    (* lbl' = lbl: show copy_prop_join is label-free *)
    `!k w. FLOOKUP (unwrap_copies (df_boundary NONE st lbl)) k = SOME w ==>
       !l. w <> Label l` by
      (match_mp_tac df_boundary_no_label >> simp[]) >>
    `!k w. FLOOKUP (unwrap_copies final_val) k = SOME w ==>
       !l. w <> Label l` by
      (ho_match_mp_tac fold_final_val_no_label >> metis_tac[]) >>
    match_mp_tac copy_prop_join_no_label >> metis_tac[])
  >> (* lbl' ≠ lbl: from boundary_no_label *)
  rpt strip_tac >>
  qpat_x_assum `boundary_no_label _`
    (mp_tac o REWRITE_RULE [boundary_no_label_def]) >>
  disch_then (qspecl_then [`lbl'`, `v`] mp_tac) >>
  impl_tac >- first_x_assum ACCEPT_TAC >>
  disch_then (qspecl_then [`k`, `w`] mp_tac) >>
  impl_tac >- first_x_assum ACCEPT_TAC >>
  simp[]
QED

(* Init state boundary is label-free *)
Triviality init_boundary_no_label[local]:
  !labels.
    boundary_no_label (init_df_state NONE labels)
Proof
  simp[boundary_no_label_def, dfAnalyzeDefsTheory.init_df_state_def] >>
  rpt gen_tac >> strip_tac >>
  imp_res_tac dfAnalyzeProofsTheory.foldl_fempty_val >>
  gvs[unwrap_copies_def]
QED

(* Adding SOME FEMPTY to boundary preserves no-label *)
Triviality boundary_no_label_update_fempty[local]:
  !st lbl.
    boundary_no_label st ==>
    boundary_no_label (st with ds_boundary := st.ds_boundary |+ (lbl, SOME FEMPTY))
Proof
  rpt gen_tac >> strip_tac >>
  CONV_TAC (REWRITE_CONV [boundary_no_label_def]) >>
  rpt gen_tac >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `lbl' = lbl` >> simp[]
  >- (strip_tac >> gvs[unwrap_copies_def])
  >> strip_tac >> rpt gen_tac >> strip_tac >> gen_tac >>
     qpat_x_assum `boundary_no_label _`
       (mp_tac o REWRITE_RULE [boundary_no_label_def]) >>
     disch_then (qspecl_then [`lbl'`, `v`] mp_tac) >>
     impl_tac >- first_x_assum ACCEPT_TAC >>
     disch_then (qspecl_then [`k`, `w`] mp_tac) >>
     impl_tac >- first_x_assum ACCEPT_TAC >>
     simp[]
QED

(* Worklist result has label-free boundaries and empty ds_inst *)
Triviality copy_prop_wl_boundary_no_label[local]:
  !fn.
    wf_function fn /\ fn_inst_wf fn ==>
    let pv = phi_used_vars fn in
    let entry_val = OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn) in
    let cfg = cfg_analyze fn in
    let process = df_process_block Forward NONE copy_prop_join copy_prop_transfer
                    copy_prop_edge_transfer pv entry_val cfg fn.fn_blocks in
    let changed = (\lbl (old:copy_lattice option df_state) new.
                     df_boundary NONE new lbl <> df_boundary NONE old lbl) in
    let st0 = init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks) in
    let st0' = (case entry_val of NONE => st0
                | SOME (lbl, v) =>
                    st0 with ds_boundary := st0.ds_boundary |+ (lbl, v)) in
    let wl0 = cfg.cfg_dfs_pre in
    let wl_result = SND (wl_iterate changed process (cfg_succs_of cfg) wl0 st0') in
      boundary_no_label wl_result /\ wl_result.ds_inst = FEMPTY
Proof
  rpt gen_tac >> strip_tac >> simp[LET_THM] >>
  qmatch_goalsub_abbrev_tac
    `boundary_no_label (SND (wl_iterate changed process deps wl0 st0'))` >>
  `copy_prop_measure_inv fn (SND (wl_iterate changed process deps wl0 st0')) /\
   boundary_no_label (SND (wl_iterate changed process deps wl0 st0')) /\
   (SND (wl_iterate changed process deps wl0 st0')).ds_inst = FEMPTY`
    suffices_by simp[] >>
  qspecl_then [
      `copy_prop_measure fn`, `copy_prop_measure_bound fn`, `changed`,
      `process`, `deps`, `wl0`, `st0'`,
      `\st:copy_lattice option df_state.
         copy_prop_measure_inv fn st /\ boundary_no_label st /\
         st.ds_inst = FEMPTY`,
      `\lbl. MEM lbl (cfg_analyze fn).cfg_dfs_pre`]
    mp_tac
    (INST_TYPE [alpha |-> ``:copy_lattice option df_state``,
                beta |-> ``:string``]
      worklistProofsTheory.wl_iterate_invariant_process_restricted) >>
  simp[] >>
  `!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st` by
    simp[Abbr `changed`, Abbr `process`,
         SRULE [LET_THM] process_changed_equiv] >>
  `!lbl st. MEM lbl wl0 /\ copy_prop_measure_inv fn st /\
            boundary_no_label st /\ process lbl st <> st ==>
     copy_prop_measure fn st < copy_prop_measure fn (process lbl st)` by
    (rpt strip_tac >> simp[Abbr `process`, Abbr `wl0`] >>
     irule copy_prop_measure_monotone >> fs[]) >>
  `!lbl st. (process lbl st).ds_inst = st.ds_inst` by
    (rpt strip_tac >> simp[Abbr `process`, process_block_inst_unchanged]) >>
  `!lbl st. MEM lbl wl0 /\ copy_prop_measure_inv fn st /\
            boundary_no_label st ==>
     copy_prop_measure_inv fn (process lbl st) /\
     boundary_no_label (process lbl st)` by
    (rpt strip_tac >> simp[Abbr `process`]
     >- metis_tac[copy_prop_measure_inv_preserved]
     >> irule process_boundary_no_label >> simp[]) >>
  `copy_prop_measure_inv fn st0'` by
    (qunabbrev_tac `st0'` >>
     mp_tac (SPEC_ALL copy_prop_measure_inv_initial) >>
     Cases_on `fn_entry_label fn` >> simp[]) >>
  `boundary_no_label st0'` by
    (qunabbrev_tac `st0'` >>
     Cases_on `fn_entry_label fn` >> simp[]
     >- simp[init_boundary_no_label]
     >> irule boundary_no_label_update_fempty >>
        simp[init_boundary_no_label]) >>
  `st0'.ds_inst = FEMPTY` by
    (qunabbrev_tac `st0'` >>
     Cases_on `fn_entry_label fn` >>
     simp[dfAnalyzeDefsTheory.init_df_state_def]) >>
  `!x. copy_prop_measure_inv fn x ==>
     copy_prop_measure fn x <= copy_prop_measure_bound fn` by
    (rpt strip_tac >> irule copy_prop_measure_bounded >>
     fs[copy_prop_measure_inv_def]) >>
  `EVERY (\lbl. MEM lbl wl0) wl0` by simp[Abbr `wl0`, listTheory.EVERY_MEM] >>
  `!lbl. MEM lbl wl0 ==> EVERY (\lbl'. MEM lbl' wl0) (deps lbl)` by
    (simp[Abbr `deps`, Abbr `wl0`] >>
     metis_tac[analysisSimPropsTheory.cfg_dfs_pre_succs_closed,
               listTheory.EVERY_MEM]) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >> rpt conj_tac >> metis_tac[])
  >> strip_tac >> gvs[]
QED

(* All ds_inst values of copy_prop_analyze are label-free *)
Triviality copy_prop_analyze_inst_no_label[local]:
  !fn k' v'.
    wf_function fn /\ fn_inst_wf fn /\
    FLOOKUP (copy_prop_analyze fn).ds_inst k' = SOME v' ==>
    !k0 w. FLOOKUP (unwrap_copies v') k0 = SOME w ==> !l. w <> Label l
Proof
  rpt gen_tac >>
  PURE_REWRITE_TAC [copy_prop_analyze_def, dfAnalyzeDefsTheory.df_analyze_def,
                     LET_DEF] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac
    `df_populate_inst Forward NONE copy_prop_join
       copy_prop_transfer copy_prop_edge_transfer pv
       entry_val cfg bbs lbls wl_res` >>
  strip_tac >>
  `boundary_no_label wl_res /\ wl_res.ds_inst = FEMPTY` by
    (qunabbrev_tac `wl_res` >>
     mp_tac (SPEC_ALL (SRULE [LET_THM] copy_prop_wl_boundary_no_label)) >>
     simp[]) >>
  `!k v. FLOOKUP (df_populate_inst Forward NONE copy_prop_join
      copy_prop_transfer copy_prop_edge_transfer pv entry_val cfg
      bbs lbls wl_res).ds_inst k = SOME v ==>
    !k' w. FLOOKUP (unwrap_copies v) k' = SOME w ==> !l. w <> Label l`
    suffices_by
      (strip_tac >>
       MAP_EVERY qunabbrev_tac [`pv`,`entry_val`,`cfg`,`bbs`,`lbls`,`wl_res`] >>
       metis_tac[]) >>
  ho_match_mp_tac populate_no_label >>
  rpt conj_tac
  >- simp[unwrap_copies_def]
  >- (qunabbrev_tac `entry_val` >>
      Cases_on `fn_entry_label fn` >>
      simp[unwrap_copies_def])
  >- metis_tac[copy_prop_join_no_label]
  >- metis_tac[copy_map_no_label]
  >- simp[copy_prop_edge_transfer_def]
  >- (qpat_x_assum `boundary_no_label _`
        (ACCEPT_TAC o REWRITE_RULE [boundary_no_label_def]))
  >> gvs[]
QED

(* Main result: copy_prop_analyze never produces Label values *)
Triviality copy_prop_no_label[local]:
  !fn lbl idx k v.
    wf_function fn /\ fn_inst_wf fn ==>
    FLOOKUP (unwrap_copies (df_at NONE (copy_prop_analyze fn) lbl idx)) k =
      SOME v ==>
    !l. v <> Label l
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[dfAnalyzeDefsTheory.df_at_def] >>
  CASE_TAC >- simp[unwrap_copies_def] >>
  strip_tac >> gen_tac >>
  metis_tac[copy_prop_analyze_inst_no_label]
QED

(* ===== Obligations ===== *)

Triviality map_get_label_subst[local]:
  !copies ops.
    (!k v. FLOOKUP copies k = SOME v ==> !l. v <> Label l) ==>
    MAP get_label (MAP (subst_op_map copies) ops) = MAP get_label ops
Proof
  gen_tac >> Induct >> simp[] >> rpt strip_tac >>
  metis_tac[subst_op_map_preserves_get_label]
QED

Triviality aei_get_successors[local]:
  !fn pv v inst.
    (!k op. FLOOKUP (unwrap_copies v) k = SOME op ==> !l. op <> Label l) ==>
    get_successors (assign_elim_inst pv v inst) = get_successors inst
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >-
    simp[assign_elim_inst_def, LET_THM] >>
  Cases_on `is_forwardable_assign pv inst` >- (
    `inst.inst_opcode = ASSIGN` by fs[is_forwardable_assign_def] >>
    simp[assign_elim_inst_def, LET_THM, mk_nop_inst_def,
         get_successors_def, is_terminator_def]) >>
  simp[assign_elim_inst_def, LET_THM, get_successors_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  `MAP get_label (MAP (subst_op_map (unwrap_copies v)) inst.inst_operands) =
   MAP get_label inst.inst_operands` by
    (irule map_get_label_subst >> first_assum ACCEPT_TAC) >>
  gvs[unwrap_copies_def]
QED

Triviality ae_bb_succs[local]:
  !fn bb. wf_function fn /\ fn_inst_wf fn /\ bb_well_formed bb ==>
    bb_succs (bb with bb_instructions :=
      MAPi (\idx inst. assign_elim_inst (phi_used_vars fn)
        (df_at NONE (copy_prop_analyze fn) bb.bb_label idx) inst)
        bb.bb_instructions) = bb_succs bb
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  simp[bb_succs_def] >>
  `LAST (MAPi (\idx inst. assign_elim_inst (phi_used_vars fn)
    (df_at NONE (copy_prop_analyze fn) bb.bb_label idx) inst) (h::t)) =
   assign_elim_inst (phi_used_vars fn)
    (df_at NONE (copy_prop_analyze fn) bb.bb_label (LENGTH t))
    (LAST (h::t))` by simp[last_mapi] >>
  gvs[] >>
  `!k op. FLOOKUP (unwrap_copies (df_at NONE (copy_prop_analyze fn) bb.bb_label
    (LENGTH t))) k = SOME op ==> !l. op <> Label l` by
    metis_tac[copy_prop_no_label] >>
  imp_res_tac aei_get_successors >> gvs[]
QED

Theorem assign_elim_preserves_wf_function:
  ∀fn. wf_function fn ∧ fn_inst_wf fn ⇒ wf_function (assign_elim_function fn)
Proof
  rpt strip_tac >>
  PURE_REWRITE_TAC[assign_elim_function_def, LET_DEF] >> BETA_TAC >>
  irule clear_nops_function_preserves_wf >>
  PURE_ONCE_REWRITE_TAC[aft_singleton_eq_fmt_mapi] >>
  ho_match_mp_tac (SIMP_RULE std_ss [AND_IMP_INTRO] fmt_preserves_wf_function) >>
  rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> ho_match_mp_tac mapi_transform_bb_well_formed >> simp[] >>
      rpt conj_tac >> rpt gen_tac >> strip_tac >>
      simp[assign_elim_inst_def, LET_THM] >>
      BasicProvers.every_case_tac >>
      gvs[mk_nop_inst_def, is_terminator_def, is_forwardable_assign_def])
  >- (rpt strip_tac >> simp[ae_bb_succs])
  >- (fs[wf_function_def] >>
      ho_match_mp_tac mapi_transform_fn_inst_ids_bb >> simp[aei_preserves_id])
  >> simp[]
QED

Theorem assign_elim_preserves_ssa_form:
  ∀fn. wf_function fn ∧ fn_inst_wf fn ∧ ssa_form fn ⇒ ssa_form (assign_elim_function fn)
Proof
  rpt strip_tac >>
  PURE_REWRITE_TAC[assign_elim_function_def, LET_DEF] >> BETA_TAC >>
  irule clear_nops_function_preserves_ssa >>
  PURE_ONCE_REWRITE_TAC[aft_singleton_eq_fmt_mapi] >>
  ho_match_mp_tac (SIMP_RULE std_ss [AND_IMP_INTRO]
    (SIMP_RULE std_ss [GSYM AND_IMP_INTRO] fmt_preserves_ssa_form_general)) >>
  rpt strip_tac
  >- (gvs[indexedListsTheory.MEM_MAPi] >>
      rename1 `idx < LENGTH bb.bb_instructions` >>
      qexists_tac `EL idx bb.bb_instructions` >>
      simp[listTheory.MEM_EL] >>
      conj_tac >- (qexists_tac `idx` >> simp[]) >>
      metis_tac[aei_outputs, aei_preserves_id])
  >- (fs[wf_function_def] >>
      ho_match_mp_tac mapi_transform_fn_inst_ids_bb >> simp[aei_preserves_id])
  >- fs[wf_function_def]
  >> simp[]
QED
