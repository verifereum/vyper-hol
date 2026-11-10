Theory cseSourceProps
Ancestors dfAnalyzeDefs dfAnalyzeProofs worklistWfProofs availExprDefs venomWfProps venomExecProps cseCanonProps availExprProofs

Theorem df_fold_forward_transfer_cong:
 !is idx a im.
 (!i v. MEM i is ==> tr i v = U i v) ==>
 df_fold_forward tr lbl is idx a im = df_fold_forward U lbl is idx a im
Proof
 Induct >> simp[df_fold_forward_def] >> rpt strip_tac >>
 first_x_assum irule >> metis_tac[]
QED

Theorem df_fold_backward_transfer_cong:
 !is idx a im.
 (!i v. MEM i is ==> tr i v = U i v) ==>
 df_fold_backward tr lbl is idx a im = df_fold_backward U lbl is idx a im
Proof
 Induct >> simp[df_fold_backward_def] >> rpt strip_tac >>
 `df_fold_backward tr lbl is (idx + 1) a im =
  df_fold_backward U lbl is (idx + 1) a im` by
   (first_x_assum irule >> metis_tac[]) >>
 simp[] >> pairarg_tac >> simp[]
QED

Theorem df_fold_block_transfer_cong:
 (!i v. MEM i is ==> tr i v = U i v) ==>
 df_fold_block dir tr lbl is a = df_fold_block dir U lbl is a
Proof
 strip_tac >> Cases_on `dir` >> simp[df_fold_block_def] >>
 metis_tac[df_fold_forward_transfer_cong, df_fold_backward_transfer_cong]
QED

Theorem df_function_instrs_transfer_cong:
 (!i a. MEM i (fn_insts fn) ==> tr ctx i a = ur ctx i a) ==>
 df_fold_block dir (tr ctx) lbl
   (case lookup_block lbl fn.fn_blocks of NONE => [] | SOME bb => bb.bb_instructions) v =
 df_fold_block dir (ur ctx) lbl
   (case lookup_block lbl fn.fn_blocks of NONE => [] | SOME bb => bb.bb_instructions) v
Proof
 strip_tac >> irule df_fold_block_transfer_cong >>
 Cases_on `lookup_block lbl fn.fn_blocks` >> simp[] >> rpt strip_tac >>
 first_x_assum irule >> simp[venomInstTheory.fn_insts_def] >>
 irule venomInstTheory.fmp_fn_insts_blocks_intro >>
 metis_tac[venomExecPropsTheory.lookup_block_MEM]
QED

Theorem df_process_block_transfer_cong:
 (!i a. MEM i (fn_insts fn) ==> tr ctx i a = ur ctx i a) ==>
 df_process_block dir bottom join tr edge ctx entry cfg fn.fn_blocks =
 df_process_block dir bottom join ur edge ctx entry cfg fn.fn_blocks
Proof
 strip_tac >> drule df_function_instrs_transfer_cong >> strip_tac >>
 simp[FUN_EQ_THM, df_process_block_def]
QED

Theorem df_populate_inst_transfer_cong:
 (!i a. MEM i (fn_insts fn) ==> tr ctx i a = ur ctx i a) ==>
 df_populate_inst dir bottom join tr edge ctx entry cfg fn.fn_blocks lbls st =
 df_populate_inst dir bottom join ur edge ctx entry cfg fn.fn_blocks lbls st
Proof
 strip_tac >> drule df_function_instrs_transfer_cong >> strip_tac >>
 simp[df_populate_inst_def]
QED

Theorem df_analyze_transfer_cong:
 (!i a. MEM i (fn_insts fn) ==> tr ctx i a = ur ctx i a) ==>
 df_analyze dir bottom join tr edge ctx entry fn =
 df_analyze dir bottom join ur edge ctx entry fn
Proof
 strip_tac >>
 drule df_process_block_transfer_cong >> strip_tac >>
 drule df_populate_inst_transfer_cong >> strip_tac >>
 simp[df_analyze_def]
QED

(* This guard changes no transfer actually invoked by this function's analysis. *)
Definition cse_guarded_avail_transfer_def:
 cse_guarded_avail_transfer fn d inst a =
   if MEM inst (fn_insts fn) then avail_transfer_opt d inst a else a
End

Theorem cse_guarded_avail_analyze:
 df_analyze dir bottom join (cse_guarded_avail_transfer fn) edge d entry fn =
 df_analyze dir bottom join avail_transfer_opt edge d entry fn
Proof
 irule df_analyze_transfer_cong >> simp[cse_guarded_avail_transfer_def]
QED

Theorem df_process_boundary_bilateral:
 !dir bottom join transfer edge ctx entry cfg bbs lbl st P.
 P bottom /\
 (case entry of NONE => T | SOME (l,v) => P v) /\
 (!a b. P a /\ P b ==> P (join a b)) /\
 (!i a. P a ==> P (transfer ctx i a)) /\
 (!src dst a. P a ==> P (edge ctx src dst a)) /\
 (!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v) ==>
 !k v. FLOOKUP (df_process_block dir bottom join transfer edge ctx entry cfg bbs lbl st).ds_boundary k = SOME v ==> P v
Proof
 rpt gen_tac >> strip_tac >>
 `P (df_joined_val dir bottom join edge ctx entry cfg st lbl)` by
   (irule df_joined_val_P >> metis_tac[]) >>
 simp_tac std_ss [df_process_block_def, LET_THM] >>
 pairarg_tac >> gvs[] >>
 drule_all df_fold_block_P >> strip_tac >>
 IF_CASES_TAC >> simp[] >> rpt strip_tac >>
 gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >>
 `!l. P (df_boundary bottom st l)` by
   (gen_tac >> simp[df_boundary_def] >>
    Cases_on `FLOOKUP st.ds_boundary l` >> simp[] >> metis_tac[]) >>
 metis_tac[]
QED

Definition df_values_valid_def:
 df_values_valid P st <=>
   (!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v) /\
   (!k v. FLOOKUP st.ds_inst k = SOME v ==> P v)
End

Theorem df_process_values_valid:
 P bottom /\ (case entry of NONE => T | SOME (l,v) => P v) /\
 (!a b. P a /\ P b ==> P (join a b)) /\
 (!i a. P a ==> P (transfer ctx i a)) /\
 (!src dst a. P a ==> P (edge ctx src dst a)) /\
 df_values_valid P st ==>
 df_values_valid P (df_process_block dir bottom join transfer edge ctx entry cfg bbs lbl st)
Proof
 simp[df_values_valid_def] >> strip_tac >> conj_tac
 >- (match_mp_tac df_process_boundary_bilateral >> metis_tac[]) >>
 simp_tac std_ss [df_process_block_def, LET_THM] >>
 pairarg_tac >> simp[] >> IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem df_populate_values_valid:
 P bottom /\ (case entry of NONE => T | SOME (l,v) => P v) /\
 (!a b. P a /\ P b ==> P (join a b)) /\
 (!i a. P a ==> P (transfer ctx i a)) /\
 (!src dst a. P a ==> P (edge ctx src dst a)) /\
 df_values_valid P st ==>
 df_values_valid P (df_populate_inst dir bottom join transfer edge ctx entry cfg bbs lbls st)
Proof
 simp[df_values_valid_def] >> strip_tac >> reverse conj_tac
 >- (match_mp_tac populate_inst_P >> metis_tac[]) >>
 simp[df_populate_inst_def] >>
 `!acc. (!k v. FLOOKUP acc.ds_boundary k = SOME v ==> P v) ==>
   (!k v. FLOOKUP (FOLDL (\st' lbl.
     let joined = df_joined_val dir bottom join edge ctx entry cfg st lbl in
     let instrs = case lookup_block lbl bbs of NONE => [] | SOME bb => bb.bb_instructions in
     let (fv,im) = df_fold_block dir (transfer ctx) lbl instrs joined in
     st' with ds_inst := FUNION im st'.ds_inst) acc lbls).ds_boundary k = SOME v ==> P v)`
   suffices_by (simp_tac bool_ss [LET_THM] >> metis_tac[]) >>
 Induct_on `lbls` >> simp[] >> rpt gen_tac >> strip_tac >>
 pairarg_tac >> gvs[LET_THM] >>
 qpat_x_assum `!acc. _` match_mp_tac >> simp[] >> metis_tac[]
QED

Theorem df_initial_values_valid:
 P bottom /\ (case entry of NONE => T | SOME (l,v) => P v) ==>
 df_values_valid P
  (case entry of NONE => init_df_state bottom lbls | SOME (l,v) =>
    (init_df_state bottom lbls) with ds_boundary :=
      (init_df_state bottom lbls).ds_boundary |+ (l,v))
Proof
 strip_tac >> Cases_on `entry` >> gvs[]
 >- (simp[df_values_valid_def, init_df_state_def] >>
     metis_tac[foldl_fempty_val]) >>
 PairCases_on `x` >> gvs[] >>
 simp[df_values_valid_def, init_df_state_def, finite_mapTheory.FLOOKUP_UPDATE] >>
 rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[foldl_fempty_val]
QED

Theorem df_analyze_invariant_bilateral_wf:
 !dir bottom join transfer edge ctx entry fn P (R:'r->'r->bool) rho Q valid.
 let cfg = cfg_analyze fn in
 let process = df_process_block dir bottom join transfer edge ctx entry cfg fn.fn_blocks in
 let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) fn.fn_blocks) in
 let initial = case entry of NONE => st0 | SOME (l,v) =>
   st0 with ds_boundary := st0.ds_boundary |+ (l,v) in
 let deps = case dir of Forward => cfg_succs_of cfg | Backward => cfg_preds_of cfg in
 let wl0 = case dir of Forward => cfg.cfg_dfs_pre | Backward => cfg.cfg_dfs_post in
 P bottom /\ (case entry of NONE => T | SOME (l,v) => P v) /\
 (!a b. P a /\ P b ==> P (join a b)) /\
 (!i a. P a ==> P (transfer ctx i a)) /\
 (!src dst a. P a ==> P (edge ctx src dst a)) /\
 WF R /\ Q initial /\ EVERY valid wl0 /\
 (!l. valid l ==> EVERY valid (deps l)) /\
 (!l st. valid l /\ Q st ==> Q (process l st)) /\
 (!l st. valid l /\ Q st /\ process l st <> st ==>
    R (rho (process l st)) (rho st)) ==>
 (!lbl idx. P (df_at bottom (df_analyze dir bottom join transfer edge ctx entry fn) lbl idx)) /\
 (!lbl. P (df_boundary bottom (df_analyze dir bottom join transfer edge ctx entry fn) lbl))
Proof
 rpt gen_tac >> simp_tac bool_ss [LET_THM] >> strip_tac >>
 `df_values_valid P (df_analyze dir bottom join transfer edge ctx entry fn)` suffices_by
  (simp[df_values_valid_def, df_at_def, df_boundary_def] >>
   rpt strip_tac >> CASE_TAC >> simp[] >> metis_tac[]) >>
 simp_tac bool_ss [df_analyze_def, LET_THM] >>
 match_mp_tac df_populate_values_valid >> simp[] >>
 qmatch_goalsub_abbrev_tac `wl_iterate changed process deps wl0 initial` >>
 `(\st. Q st /\ df_values_valid P st)
   (SND (wl_iterate changed process deps wl0 initial))` suffices_by simp[] >>
 irule (cj 2 (Q.ISPEC `R:'r->'r->bool` wl_iterate_terminates_wf)) >> conj_tac
 >- (simp[Abbr `initial`] >> irule df_initial_values_valid >> simp[]) >>
 conj_tac
 >- simp[Abbr `changed`, Abbr `process`,
          SRULE [LET_THM] df_process_changed_equiv] >>
 qexistsl_tac [`R`, `rho'`, `valid`] >> simp[] >>
 rpt strip_tac >> simp[Abbr `process`] >>
 irule df_process_values_valid >> metis_tac[]
QED

Definition cse_sources_valid_def:
 cse_sources_valid fn a <=>
  !e src. (?xs. FLOOKUP (avail_unwrap a) e = SOME xs /\ MEM src xs) ==>
    MEM src (fn_insts fn) /\
    avail_source_birth (dfg_build_function fn) e src src
End

Theorem cse_sources_valid_bottom:
 cse_sources_valid fn NONE /\ cse_sources_valid fn (SOME avail_empty)
Proof
 simp[cse_sources_valid_def, avail_unwrap_def, avail_empty_def]
QED

Theorem cse_sources_valid_meet:
 !a b. cse_sources_valid fn a /\ cse_sources_valid fn b ==>
 cse_sources_valid fn (avail_meet_opt a b)
Proof
 Cases >> Cases >>
 simp[avail_meet_opt_def, cse_sources_valid_def, avail_unwrap_def,
      avail_meet_two_source_member] >> metis_tac[]
QED

Theorem cse_sources_valid_transfer:
 !i a. cse_sources_valid fn a ==>
 cse_sources_valid fn (cse_guarded_avail_transfer fn (dfg_build_function fn) i a)
Proof
 rpt gen_tac >> simp[cse_guarded_avail_transfer_def] >>
 IF_CASES_TAC >> simp[] >>
 Cases_on `a` >>
 simp[cse_sources_valid_def, avail_transfer_opt_def, avail_unwrap_def,
      avail_empty_def, avail_transfer_inst_source_member,
      avail_source_birth_def] >>
 rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem cse_avail_analyze_sources_valid:
 !fn. wf_function fn ==>
 (!lbl idx. cse_sources_valid fn (df_at NONE (avail_analyze fn) lbl idx)) /\
 (!lbl. cse_sources_valid fn (df_boundary NONE (avail_analyze fn) lbl))
Proof
 gen_tac >> disch_tac >>
 simp_tac bool_ss [avail_analyze_def, LET_THM,
                   GSYM cse_guarded_avail_analyze] >>
 ho_match_mp_tac (INST_TYPE [``:'r`` |-> ``:num # num``]
   (SRULE [LET_THM] df_analyze_invariant_bilateral_wf)) >>
 qexistsl_tac [`($< LEX $<) : num # num -> num # num -> bool`,
               `\st. cse_boundary_rank (set (fn_labels fn)) (df_boundary NONE st)`,
               `\st. T`, `\lbl. MEM lbl (fn_labels fn)`] >>
 simp[cse_sources_valid_bottom, cse_sources_valid_meet,
      cse_sources_valid_transfer, avail_edge_transfer_def,
      pairTheory.WF_LEX, prim_recTheory.WF_LESS,
      listTheory.EVERY_MEM] >>
 conj_tac
 >- (Cases_on `fn_entry_label fn` >> simp[cse_sources_valid_bottom]) >>
 conj_tac
 >- metis_tac[dfAnalyzePropsTheory.cfg_dfs_pre_subset_fn_labels] >>
 conj_tac
 >- metis_tac[cfgAnalysisPropsTheory.cfg_analyze_succ_labels] >>
 rpt strip_tac >> irule cse_process_boundary_rank >> simp[]
QED

Theorem cse_avail_source_provenance:
 !fn lbl idx e xs src.
 wf_function fn /\
 FLOOKUP (avail_unwrap (df_at NONE (avail_analyze fn) lbl idx)) e = SOME xs /\
 MEM src xs ==>
 MEM src (fn_insts fn) /\
 avail_source_birth (dfg_build_function fn) e src src
Proof
 rpt strip_tac >> drule cse_avail_analyze_sources_valid >>
 simp[cse_sources_valid_def] >> metis_tac[]
QED

Theorem cse_avail_get_source_provenance:
 !fn lbl idx e src.
 wf_function fn /\
 avail_get_source (avail_unwrap (df_at NONE (avail_analyze fn) lbl idx)) e = SOME src ==>
 MEM src (fn_insts fn) /\
 avail_source_birth (dfg_build_function fn) e src src
Proof
 rpt gen_tac >> simp[avail_get_source_def, AllCaseEqs()] >>
 rpt strip_tac >> gvs[] >>
 metis_tac[cse_avail_source_provenance, listTheory.MEM]
QED
