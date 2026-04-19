(*
 * Memory Copy Elision — Convergence Proofs
 *
 * Proves that copy_fact_analyze terminates (is_fixpoint holds).
 *
 * The convergence argument follows the same pattern as assign_elim:
 * 1. Join (DRESTRICT-based) only removes entries from finite maps.
 * 2. Transfer adds at most one entry per instruction.
 * 3. The total entries across all program points is bounded.
 * 4. A weighted measure strictly increases when the state changes.
 *
 * TOP-LEVEL EXPORTS:
 *   copy_fact_join_absorption — absorption law for join
 *   copy_fact_is_fixpoint — analysis reaches fixpoint
 *   copy_fact_joined_def — joined entry value at block boundary
 *)

Theory memoryCopyElisionConvergence
Ancestors
  memoryCopyElisionDefs dfAnalyzeProofs dfAnalyzeDefs dfgDefs
  cfgHelpers cfgAnalysisProps
  latticeDefs worklistDefs venomInst
  finite_map list pred_set arithmetic pair
Libs
  pairLib

(* ===== Join absorption ===== *)

Theorem copy_fact_join_raw_idem[local]:
  !dfg f1 f2.
    copy_fact_join_raw dfg (copy_fact_join_raw dfg f1 f2) f2 =
    copy_fact_join_raw dfg f1 f2
Proof
  rpt gen_tac >>
  simp[copy_fact_join_raw_def, DRESTRICT_DRESTRICT] >>
  `{k | cf_agree dfg f1 f2 k} INTER
   {k | cf_agree dfg (DRESTRICT f1 {k | cf_agree dfg f1 f2 k}) f2 k} =
   {k | cf_agree dfg f1 f2 k}` suffices_by simp[] >>
  rw[EXTENSION] >> eq_tac >> rpt strip_tac >> fs[] >>
  fs[cf_agree_def, FLOOKUP_DRESTRICT] >>
  rpt CASE_TAC >> fs[]
QED

Theorem copy_fact_join_raw_self[local]:
  !dfg (f:copy_fact_lattice_raw). copy_fact_join_raw dfg f f = f
Proof
  rpt gen_tac >>
  simp[copy_fact_join_raw_def, fmap_EXT, FDOM_DRESTRICT] >>
  conj_tac
  >- (rw[EXTENSION] >> eq_tac >> rpt strip_tac >> fs[] >>
      simp[cf_agree_def, FLOOKUP_DEF, operand_equiv_def])
  >- (rpt strip_tac >> simp[DRESTRICT_DEF])
QED

Theorem copy_fact_join_absorption:
  !dfg a b. copy_fact_join dfg (copy_fact_join dfg a b) b =
            copy_fact_join dfg a b
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[copy_fact_join_def, copy_fact_join_raw_idem, copy_fact_join_raw_self]
QED

(* ===== Joined value at block boundary ===== *)

(* Matches df_joined_val_def specialized to MCE parameters *)
Definition copy_fact_joined_def:
  copy_fact_joined (ctx : copy_elision_ctx) fn st lbl =
    df_joined_val Forward NONE (copy_fact_join ctx.ce_dfg)
      copy_fact_edge_transfer ctx
      (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) st lbl
End

(* ===== Bound set: all possible write locations ===== *)

(* All mem_loc keys that copy_fact_transfer could ever add to the lattice.
   This is the set of ce_memloc_from_ops bp dst sz for all copy instructions
   in the function with well-formed operand lists [dst; src; sz]. *)
Definition fn_copy_locs_def:
  fn_copy_locs (bp : bp_result) fn =
    FLAT (MAP (\inst.
      if is_copy_opcode inst.inst_opcode then
        case inst.inst_operands of
          [dst; src; sz] => [ce_memloc_from_ops bp dst sz]
        | _ => []
      else []) (fn_insts fn))
End

(* ===== Convergence machinery ===== *)

(* Per-value measure. NONE=0 (bottom). SOME fmap = max_keys+1-CARD(FDOM fmap).
   Increases as entries are lost (smaller FDOM = larger measure). *)
Definition cf_val_measure_def:
  cf_val_measure max_keys (NONE : copy_fact_lattice) = 0 /\
  cf_val_measure max_keys (SOME fmap) = max_keys + 1 - CARD (FDOM fmap)
End
val _ = delsimps ["cf_val_measure_def"]

(* State invariant: all FDOM bounded by fn_copy_locs *)
Definition cf_state_inv_def:
  cf_state_inv bp fn (st : copy_fact_lattice df_state) <=>
    (!lbl fmap. FLOOKUP st.ds_boundary lbl = SOME (SOME fmap) ==>
       FDOM fmap SUBSET set (fn_copy_locs bp fn)) /\
    (!k fmap. FLOOKUP st.ds_inst k = SOME (SOME fmap) ==>
       FDOM fmap SUBSET set (fn_copy_locs bp fn))
End

(* Extended invariant for convergence proof *)
Definition cf_measure_inv_def:
  cf_measure_inv ctx fn (st : copy_fact_lattice df_state) <=>
    fn_inst_wf fn /\
    cf_state_inv ctx.ce_bp fn st /\
    (let transfer = copy_fact_transfer ctx in
     let instrs_of lbl = case lookup_block lbl fn.fn_blocks of
                           NONE => [] | SOME bb => bb.bb_instructions in
     (* C3: fold coherence *)
     (!lbl v0. FLOOKUP st.ds_inst (lbl, 0n) = SOME v0 ==>
        !k v. FLOOKUP (SND (df_fold_block Forward (transfer)
                 lbl (instrs_of lbl) v0)) k = SOME v ==>
          FLOOKUP st.ds_inst k = SOME v) /\
     (* C4: key closure *)
     (!lbl j. (lbl, j) IN FDOM st.ds_inst ==>
        (lbl, 0n) IN FDOM st.ds_inst) /\
     (* C5: processed implies boundary exists *)
     (!lbl. (lbl, 0n) IN FDOM st.ds_inst ==>
        lbl IN FDOM st.ds_boundary))
End

(* Boundary measure *)
Definition cf_boundary_measure_def:
  cf_boundary_measure bp fn (st : copy_fact_lattice df_state) =
    let mv = CARD (set (fn_copy_locs bp fn)) in
    let dfs_pre = (cfg_analyze fn).cfg_dfs_pre in
    SUM (MAP (\lbl. cf_val_measure mv (df_boundary NONE st lbl))
             (fn_labels fn ++ dfs_pre))
End

(* Fresh count *)
Definition cf_fresh_count_def:
  cf_fresh_count ctx fn (st : copy_fact_lattice df_state) =
    let dfs_pre = (cfg_analyze fn).cfg_dfs_pre in
    CARD {lbl | MEM lbl (fn_labels fn ++ dfs_pre) /\
                (lbl, 0n) IN FDOM st.ds_inst /\
                FLOOKUP st.ds_inst (lbl, 0n) =
                SOME (copy_fact_joined ctx fn st lbl)}
End

(* Full measure *)
Definition cf_measure_def:
  cf_measure ctx fn (st : copy_fact_lattice df_state) =
    let dfs_pre = (cfg_analyze fn).cfg_dfs_pre in
    let all_count = LENGTH (fn_labels fn) + LENGTH dfs_pre in
    (all_count + 1) * cf_boundary_measure ctx.ce_bp fn st +
    CARD (FDOM st.ds_inst INTER df_valid_inst_keys fn.fn_blocks) +
    cf_fresh_count ctx fn st +
    CARD (FDOM st.ds_boundary INTER set dfs_pre)
End

(* Measure bound *)
Definition cf_measure_bound_def:
  cf_measure_bound ctx fn =
    let max_keys = CARD (set (fn_copy_locs ctx.ce_bp fn)) in
    let nlabels = LENGTH (fn_labels fn) in
    let total_slots = df_total_inst_slots fn.fn_blocks in
    let ndfs = LENGTH (cfg_analyze fn).cfg_dfs_pre in
    let all_count = nlabels + ndfs in
    (all_count + 1) * ((max_keys + 1) * (nlabels + ndfs)) +
    total_slots +
    (nlabels + ndfs) +
    ndfs
End

(* ===== Basic lemmas ===== *)

(* Per-value measure is bounded under the invariant *)
Theorem cf_val_measure_bounded[local]:
  !v mv.
    (case v of NONE => T
     | SOME fmap => CARD (FDOM fmap) <= mv) ==>
    cf_val_measure mv v <= mv + 1
Proof
  Cases >> simp[cf_val_measure_def]
QED

(* copy_fact_join preserves FDOM ⊆ bound *)
Theorem cf_join_fdom_subset[local]:
  !dfg c1 c2 bound.
    (case c1 of NONE => T | SOME fmap => FDOM fmap SUBSET bound) /\
    (case c2 of NONE => T | SOME fmap => FDOM fmap SUBSET bound) ==>
    (case copy_fact_join dfg c1 c2 of NONE => T
     | SOME fmap => FDOM fmap SUBSET bound)
Proof
  Cases_on `c1` >> Cases_on `c2` >>
  simp[copy_fact_join_def, copy_fact_join_raw_def, FDOM_DRESTRICT] >>
  metis_tac[SUBSET_INTER_ABSORPTION, INTER_SUBSET, SUBSET_TRANS]
QED

(* copy_fact_invalidate preserves FDOM ⊆ bound *)
Theorem cf_invalidate_fdom_subset[local]:
  !aliases bp cfl wloc bound.
    FDOM cfl SUBSET bound ==>
    FDOM (copy_fact_invalidate aliases bp cfl wloc) SUBSET bound
Proof
  rpt strip_tac >>
  simp[copy_fact_invalidate_def] >>
  IF_CASES_TAC >> simp[FDOM_DRESTRICT] >>
  metis_tac[INTER_SUBSET, SUBSET_TRANS]
QED

(* copy_fact_transfer preserves FDOM ⊆ S when S contains the write_loc *)
Theorem cf_transfer_fdom_subset[local]:
  !ctx inst v bound.
    (case v of NONE => T | SOME fmap => FDOM fmap SUBSET bound) /\
    (is_copy_opcode inst.inst_opcode ==>
       !dst src sz. inst.inst_operands = [dst; src; sz] ==>
         ce_memloc_from_ops ctx.ce_bp dst sz IN bound) ==>
    (case copy_fact_transfer ctx inst v of NONE => T
     | SOME fmap => FDOM fmap SUBSET bound)
Proof
  rpt strip_tac >>
  `FDOM (unwrap_copy_facts v) SUBSET bound` by
    (Cases_on `v` >> fs[unwrap_copy_facts_def, FDOM_FEMPTY]) >>
  simp[copy_fact_transfer_def, LET_THM] >>
  (* Case split on instruction type *)
  Cases_on `is_copy_opcode inst.inst_opcode` >> simp[]
  >- ((* is_copy_opcode *)
      Cases_on `inst.inst_operands` >> simp[FDOM_FEMPTY] >>
      Cases_on `t` >> simp[FDOM_FEMPTY] >>
      Cases_on `t'` >> simp[FDOM_FEMPTY] >>
      (* 4+ operands => FEMPTY, trivially bounded *)
      Cases_on `t` >> simp[FDOM_FEMPTY] >>
      Cases_on `inst.inst_opcode = MCOPY /\
        (case FLOOKUP (unwrap_copy_facts v) (ce_memloc_from_ops ctx.ce_bp h h'')
         of SOME cf => cf.cf_opcode = MCOPY /\
              operand_equiv ctx.ce_dfg cf.cf_source h' /\
              operand_equiv ctx.ce_dfg cf.cf_size h''
         | NONE => F)` >> simp[] >>
      pairarg_tac >> simp[] >>
      Cases_on `ml_is_fixed (ce_memloc_from_ops ctx.ce_bp h h'') /\
                (!l. final_src <> Label l) /\
                (final_op = MCOPY ==>
                   ml_is_fixed (ce_memloc_from_ops ctx.ce_bp final_src h'') /\
                   ~ma_may_alias ctx.ce_aliases (ce_memloc_from_ops ctx.ce_bp h h'')
                     (ce_memloc_from_ops ctx.ce_bp final_src h''))` >> gvs[]
      >- (simp[FDOM_FUPDATE, SUBSET_DEF] >> rpt strip_tac >> gvs[] >>
          `FDOM (copy_fact_invalidate ctx.ce_aliases ctx.ce_bp
            (unwrap_copy_facts v)
            (ce_memloc_from_ops ctx.ce_bp h h'')) SUBSET bound` by
            (irule cf_invalidate_fdom_subset >> fs[]) >>
          fs[SUBSET_DEF])
      >> (* ¬ml_is_fixed or Label source: just invalidate *)
      irule cf_invalidate_fdom_subset >> fs[])
  >- ((* not is_copy_opcode *)
      Cases_on `inst.inst_opcode = MSTORE` >> simp[]
      >- (irule cf_invalidate_fdom_subset >> fs[])
      >> Cases_on `Eff_MEMORY IN write_effects inst.inst_opcode \/
                   is_alloca_op inst.inst_opcode \/
                   is_ext_call_op inst.inst_opcode` >>
         simp[FDOM_FEMPTY, copy_fact_prune_vars_def, FDOM_DRESTRICT] >>
         fs[SUBSET_DEF])
QED

(* FOLDL copy_fact_join preserves FDOM ⊆ S *)
Theorem foldl_cf_join_fdom_subset[local]:
  !dfg l init bound.
    (case init of NONE => T | SOME fmap => FDOM fmap SUBSET bound) /\
    EVERY (\v. case v of NONE => T | SOME fmap => FDOM fmap SUBSET bound) l ==>
    (case FOLDL (copy_fact_join dfg) init l of NONE => T
     | SOME fmap => FDOM fmap SUBSET bound)
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  metis_tac[cf_join_fdom_subset]
QED

(* df_boundary values satisfy FDOM ⊆ S under invariant *)
Theorem df_boundary_cf_inv[local]:
  !bp fn st lbl.
    cf_state_inv bp fn st ==>
    (case df_boundary NONE st lbl of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_copy_locs bp fn))
Proof
  rpt strip_tac >> simp[df_boundary_def] >>
  CASE_TAC >> simp[] >>
  Cases_on `x` >> simp[] >>
  fs[cf_state_inv_def] >> res_tac
QED

Theorem df_boundary_map_cf_inv[local]:
  !bp fn st lbls.
    cf_state_inv bp fn st ==>
    EVERY (\v. case v of NONE => T
       | SOME fmap => FDOM fmap SUBSET set (fn_copy_locs bp fn))
      (MAP (\nbr. df_boundary NONE st nbr) lbls)
Proof
  Induct_on `lbls` >> simp[] >> rpt strip_tac >> metis_tac[df_boundary_cf_inv]
QED

(* Helper: FOLDL copy_fact_join over boundary values satisfies bound *)
Triviality cf_foldl_boundary_inv[local]:
  !ctx fn st lbls init.
    cf_state_inv ctx.ce_bp fn st /\
    (case init of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_copy_locs ctx.ce_bp fn)) ==>
    (case FOLDL (copy_fact_join ctx.ce_dfg) init
                (MAP (\nbr. df_boundary NONE st nbr) lbls) of
       NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_copy_locs ctx.ce_bp fn))
Proof
  rpt strip_tac >>
  irule foldl_cf_join_fdom_subset >> simp[] >>
  irule df_boundary_map_cf_inv >> simp[]
QED

(* case [] => x | _::_ => FOLDL f x l = FOLDL f x l *)
Triviality case_list_foldl[local]:
  !l (f:'a -> 'b -> 'a) x.
    (case l of [] => x | v::vs => FOLDL f x l) = FOLDL f x l
Proof Cases_on `l` >> simp[]
QED

(* copy_fact_joined satisfies the invariant *)
Theorem cf_joined_inv[local]:
  !ctx fn st lbl.
    cf_state_inv ctx.ce_bp fn st ==>
    (case copy_fact_joined ctx fn st lbl of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_copy_locs ctx.ce_bp fn))
Proof
  rpt strip_tac >>
  simp[copy_fact_joined_def, df_joined_val_def, LET_THM,
       direction_case_def, copy_fact_edge_transfer_def,
       case_list_foldl] >>
  Cases_on `fn_entry_label fn` >> simp[]
  >- (irule cf_foldl_boundary_inv >> simp[])
  >- (IF_CASES_TAC >> simp[]
      >- (irule cf_join_fdom_subset >> simp[FDOM_FEMPTY] >>
          irule cf_foldl_boundary_inv >> simp[])
      >- (irule cf_foldl_boundary_inv >> simp[]))
QED

(* ===== Transfer FDOM preservation for fn_copy_locs ===== *)

(* Key: copy_fact_transfer adds keys only from fn_copy_locs *)
Theorem cf_transfer_inst_fdom[local]:
  !ctx fn inst v.
    MEM inst (fn_insts fn) /\
    (case v of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_copy_locs ctx.ce_bp fn)) ==>
    (case copy_fact_transfer ctx inst v of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_copy_locs ctx.ce_bp fn))
Proof
  rpt strip_tac >>
  irule cf_transfer_fdom_subset >> simp[] >>
  rpt strip_tac >>
  simp[fn_copy_locs_def, MEM_FLAT, MEM_MAP] >>
  qexists_tac `[ce_memloc_from_ops ctx.ce_bp dst sz]` >> simp[] >>
  qexists_tac `inst` >> simp[]
QED

(* ===== Initial invariant ===== *)

Theorem cf_init_state_inv[local]:
  !ctx fn.
    cf_state_inv ctx.ce_bp fn
      (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks))
Proof
  simp[cf_state_inv_def, init_df_state_def, FDOM_FEMPTY] >>
  rpt strip_tac >>
  imp_res_tac dfAnalyzeProofsTheory.foldl_fupdate_const >> gvs[]
QED

Theorem cf_init_state_inv_entry[local]:
  !ctx fn lbl.
    cf_state_inv ctx.ce_bp fn
      (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks) with
         ds_boundary :=
           (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks))
             .ds_boundary |+ (lbl, SOME FEMPTY))
Proof
  simp[cf_state_inv_def, init_df_state_def, FLOOKUP_UPDATE, FDOM_FEMPTY] >>
  rpt strip_tac >> Cases_on `lbl = lbl'` >> gvs[] >>
  imp_res_tac dfAnalyzeProofsTheory.foldl_fupdate_const >> gvs[]
QED

(* ===== Measure boundedness ===== *)

Triviality sum_map_le_bound[local]:
  !f bound l. EVERY (\x. f x <= bound) l ==>
    SUM (MAP f l) <= bound * LENGTH l
Proof
  Induct_on `l` >> simp[MULT_CLAUSES] >> rpt strip_tac >>
  `SUM (MAP f l) <= bound * LENGTH l` by (first_x_assum irule >> fs[]) >>
  DECIDE_TAC
QED

Triviality cf_val_measure_boundary_le[local]:
  !bp fn st lbl.
    cf_state_inv bp fn st ==>
    cf_val_measure (CARD (set (fn_copy_locs bp fn)))
      (df_boundary NONE st lbl) <=
    CARD (set (fn_copy_locs bp fn)) + 1
Proof
  rpt strip_tac >>
  irule cf_val_measure_bounded >>
  mp_tac (SPECL [``bp : bp_result``, ``fn : ir_function``,
                 ``st : copy_fact_lattice df_state``, ``lbl : string``]
    df_boundary_cf_inv) >> simp[] >>
  Cases_on `df_boundary NONE st lbl` >> simp[] >>
  metis_tac[CARD_SUBSET, FINITE_LIST_TO_SET]
QED

Triviality cf_fresh_count_bounded[local]:
  !ctx fn st.
    cf_fresh_count ctx fn st <=
    LENGTH (fn_labels fn) + LENGTH (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt gen_tac >> simp[cf_fresh_count_def, LET_THM] >>
  match_mp_tac LESS_EQ_TRANS >>
  qexists_tac `CARD (set (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre))` >>
  conj_tac
  >- (irule CARD_SUBSET >> simp[FINITE_LIST_TO_SET, SUBSET_DEF])
  >- (match_mp_tac LESS_EQ_TRANS >>
      qexists_tac `CARD (set (fn_labels fn)) + CARD (set (cfg_analyze fn).cfg_dfs_pre)` >>
      conj_tac >- simp[CARD_UNION_LE] >>
      metis_tac[CARD_LIST_TO_SET, LESS_EQ_LESS_EQ_MONO])
QED

Theorem cf_measure_bounded:
  !ctx fn st.
    cf_measure_inv ctx fn st ==>
    cf_measure ctx fn st <= cf_measure_bound ctx fn
Proof
  rpt strip_tac >>
  `cf_state_inv ctx.ce_bp fn st` by fs[cf_measure_inv_def] >>
  (* Bound 1: boundary measure *)
  `cf_boundary_measure ctx.ce_bp fn st <=
   (CARD (set (fn_copy_locs ctx.ce_bp fn)) + 1) *
   (LENGTH (fn_labels fn) + LENGTH (cfg_analyze fn).cfg_dfs_pre)` by (
    simp_tac std_ss [cf_boundary_measure_def, LET_THM] >>
    irule LESS_EQ_TRANS >>
    irule_at Any sum_map_le_bound >>
    qexists_tac `CARD (set (fn_copy_locs ctx.ce_bp fn)) + 1` >>
    once_rewrite_tac[GSYM MAP_APPEND] >>
    simp[EVERY_MAP, EVERY_MEM, MEM_APPEND] >> rpt strip_tac >>
    irule cf_val_measure_boundary_le >> simp[]) >>
  (* Bound 2: inst CARD *)
  `CARD (FDOM st.ds_inst INTER df_valid_inst_keys fn.fn_blocks) <=
   (df_total_inst_slots fn.fn_blocks : num)` by (
    match_mp_tac LESS_EQ_TRANS >>
    qexists_tac `CARD (df_valid_inst_keys fn.fn_blocks)` >>
    simp[dfAnalyzeProofsTheory.df_valid_inst_keys_card] >>
    ONCE_REWRITE_TAC[INTER_COMM] >>
    irule CARD_INTER_LESS_EQ >>
    simp[dfAnalyzeProofsTheory.df_valid_inst_keys_finite]) >>
  (* Bound 3: fresh count *)
  `cf_fresh_count ctx fn st <=
   LENGTH (fn_labels fn) + LENGTH (cfg_analyze fn).cfg_dfs_pre`
    by metis_tac[cf_fresh_count_bounded] >>
  (* Bound 4: dfs_visited *)
  `CARD (FDOM st.ds_boundary INTER set (cfg_analyze fn).cfg_dfs_pre) <=
   LENGTH (cfg_analyze fn).cfg_dfs_pre` by (
    match_mp_tac LESS_EQ_TRANS >>
    qexists_tac `CARD (set (cfg_analyze fn).cfg_dfs_pre)` >>
    simp[CARD_LIST_TO_SET] >>
    ONCE_REWRITE_TAC[INTER_COMM] >>
    irule CARD_INTER_LESS_EQ >>
    simp[FINITE_LIST_TO_SET]) >>
  (* Combine *)
  simp_tac std_ss [cf_measure_def, cf_measure_bound_def, LET_THM] >>
  irule LESS_EQ_LESS_EQ_MONO >>
  REVERSE conj_tac >- first_assum ACCEPT_TAC >>
  irule LESS_EQ_LESS_EQ_MONO >>
  REVERSE conj_tac >- first_assum ACCEPT_TAC >>
  irule LESS_EQ_LESS_EQ_MONO >>
  REVERSE conj_tac >- first_assum ACCEPT_TAC >>
  irule LESS_MONO_MULT2 >> simp[]
QED

(* ===== DRESTRICT helper ===== *)

Triviality drestrict_subset_id[local]:
  !f (s : 'a -> bool).
    DRESTRICT f s = f <=> FDOM f SUBSET s
Proof
  rpt gen_tac >> eq_tac
  >- (strip_tac >>
      `FDOM (DRESTRICT f s) = FDOM f` by simp[] >>
      gvs[FDOM_DRESTRICT, EXTENSION, IN_INTER, SUBSET_DEF] >> metis_tac[])
  >- (strip_tac >> simp[fmap_eq_flookup, FLOOKUP_DRESTRICT] >>
      gen_tac >> Cases_on `FLOOKUP f x` >> simp[] >>
      `x IN FDOM f` by fs[FLOOKUP_DEF] >>
      `x IN s` by fs[SUBSET_DEF] >> simp[])
QED

(* ===== Process equality ===== *)

(* Reformulate df_process_block in terms of copy_fact_joined + df_fold_block *)
Triviality cf_process_eq[local]:
  !ctx fn lbl st.
    df_process_block Forward NONE (copy_fact_join ctx.ce_dfg)
      copy_fact_transfer copy_fact_edge_transfer ctx
      (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks lbl st =
    let instrs = case lookup_block lbl fn.fn_blocks of
                   NONE => [] | SOME bb => bb.bb_instructions in
    let (fv, inst_map) = df_fold_block Forward (copy_fact_transfer ctx)
                           lbl instrs (copy_fact_joined ctx fn st lbl) in
    let new_bnd = copy_fact_join ctx.ce_dfg (df_boundary NONE st lbl) fv in
      if new_bnd = df_boundary NONE st lbl then st
      else st with ds_boundary := st.ds_boundary |+ (lbl, new_bnd)
Proof
  simp[df_process_block_def, copy_fact_joined_def]
QED

(* ===== Join strict increase ===== *)

Triviality cf_val_measure_join_strict[local]:
  !dfg mv a b.
    (case a of NONE => T | SOME fmap => CARD (FDOM fmap) <= mv) /\
    (case b of NONE => T | SOME fmap => CARD (FDOM fmap) <= mv) /\
    copy_fact_join dfg a b <> a ==>
    cf_val_measure mv a < cf_val_measure mv (copy_fact_join dfg a b)
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[copy_fact_join_def, cf_val_measure_def, copy_fact_join_raw_def,
       FDOM_DRESTRICT] >>
  rpt strip_tac >>
  qabbrev_tac `ag = {x'' | cf_agree dfg x x' x''}` >>
  `~(FDOM x SUBSET ag)` by metis_tac[drestrict_subset_id] >>
  `FDOM x INTER ag PSUBSET FDOM x` by (
    fs[PSUBSET_DEF, INTER_SUBSET, SUBSET_DEF, EXTENSION] >> metis_tac[]) >>
  `CARD (FDOM x INTER ag) < CARD (FDOM x)` by
    (irule CARD_PSUBSET >> simp[FDOM_FINITE]) >>
  simp[LE_SUB_LCANCEL]
QED

(* ===== SUM helpers ===== *)

Triviality sum_map_le[local]:
  !f g l. EVERY (\x. f x <= g x) l ==> SUM (MAP f l) <= SUM (MAP g l)
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> DECIDE_TAC
QED

Triviality sum_map_lt[local]:
  !f g l.
    EVERY (\x. f x <= g x) l /\
    (?y. MEM y l /\ f y < g y) ==>
    SUM (MAP f l) < SUM (MAP g l)
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >> gvs[]
  >- (`SUM (MAP f l) <= SUM (MAP g l)` by
        (irule sum_map_le >> fs[]) >> DECIDE_TAC)
  >- (`f h <= g h` by fs[] >>
      `SUM (MAP f l) < SUM (MAP g l)` by metis_tac[] >> DECIDE_TAC)
QED

(* ===== Boundary strict increase ===== *)

Triviality boundary_measure_strict[local]:
  !ctx fn lbl st new_val.
    cf_measure_inv ctx fn st /\
    MEM lbl (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre) /\
    cf_val_measure (CARD (set (fn_copy_locs ctx.ce_bp fn)))
                   (df_boundary NONE st lbl) <
    cf_val_measure (CARD (set (fn_copy_locs ctx.ce_bp fn))) new_val ==>
    cf_boundary_measure ctx.ce_bp fn st <
    cf_boundary_measure ctx.ce_bp fn
      (st with ds_boundary := st.ds_boundary |+ (lbl, new_val))
Proof
  rpt strip_tac >>
  simp[cf_boundary_measure_def, LET_THM] >>
  ntac 2 (once_rewrite_tac[GSYM MAP_APPEND]) >>
  irule sum_map_lt >> simp[] >>
  `!x. cf_val_measure (CARD (set (fn_copy_locs ctx.ce_bp fn)))
         (df_boundary NONE
            (st with ds_boundary := st.ds_boundary |+ (lbl, new_val)) x) =
       if x = lbl then
         cf_val_measure (CARD (set (fn_copy_locs ctx.ce_bp fn))) new_val
       else
         cf_val_measure (CARD (set (fn_copy_locs ctx.ce_bp fn)))
           (df_boundary NONE st x)` by
    (rpt strip_tac >> simp[df_boundary_def, FLOOKUP_UPDATE] >>
     IF_CASES_TAC >> simp[]) >>
  rpt conj_tac >>
  TRY (simp[EVERY_MEM] >> rpt strip_tac >>
       IF_CASES_TAC >> simp[] >> NO_TAC) >>
  qexists_tac `lbl` >> fs[MEM_APPEND]
QED


(* ===== Weighted inequality helper ===== *)

Triviality weighted_lt_cancel[local]:
  !w (a:num) a' c. a < a' /\ c <= w ==> (w + 1) * a + c < (w + 1) * a'
Proof
  rpt strip_tac >>
  `(w + 1) * a + c <= (w + 1) * a + w` by simp[] >>
  `(w + 1) * a + w < (w + 1) * (a + 1)` by simp[LEFT_ADD_DISTRIB] >>
  `a + 1 <= a'` by simp[] >>
  `(w + 1) * (a + 1) <= (w + 1) * a'` by simp[LE_MULT_LCANCEL] >>
  simp[]
QED

(* ===== cf_joined boundary equality ===== *)

Triviality cf_joined_boundary_eq[local]:
  !ctx fn st bnd di.
    (!x. df_boundary NONE (st with <| ds_inst := di; ds_boundary := bnd |>) x =
         df_boundary NONE st x) ==>
    !x. copy_fact_joined ctx fn
          (st with <| ds_inst := di; ds_boundary := bnd |>) x =
        copy_fact_joined ctx fn st x
Proof
  rpt strip_tac >>
  simp[copy_fact_joined_def, df_joined_val_def, LET_THM,
       direction_case_def, copy_fact_edge_transfer_def]
QED

(* ===== Invariant preservation ===== *)

(* df_fold_block preserves FDOM bound for inst slots — via df_fold_block_forward_invariant *)
Triviality cf_fold_fdom[local]:
  !ctx fn lbl instrs v0 fv inst_map.
    df_fold_block Forward (copy_fact_transfer ctx) lbl instrs v0 =
      (fv, inst_map) /\
    EVERY (\inst. MEM inst (fn_insts fn)) instrs /\
    (case v0 of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_copy_locs ctx.ce_bp fn)) ==>
    (case fv of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_copy_locs ctx.ce_bp fn)) /\
    (!k v. FLOOKUP inst_map k = SOME v ==>
      (case v of NONE => T
       | SOME fmap => FDOM fmap SUBSET set (fn_copy_locs ctx.ce_bp fn)))
Proof
  rpt gen_tac >> strip_tac >>
  drule dfAnalyzeProofsTheory.df_fold_block_forward_invariant >>
  disch_then (qspec_then
    `\v. case v of NONE => T
         | SOME fmap => FDOM fmap SUBSET set (fn_copy_locs ctx.ce_bp fn)` mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >> irule cf_transfer_inst_fdom >>
               fs[EVERY_MEM] >> metis_tac[]) >>
  strip_tac >> simp[] >> metis_tac[]
QED

Triviality find_mem[local]:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  Induct_on `l` >> simp[FIND_thm] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Triviality fn_insts_blocks_mem[local]:
  !bbs bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts_blocks bbs)
Proof
  Induct >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

(* Helper: boundary FDOM preserved after join update *)
Triviality cf_boundary_fdom_preserved[local]:
  !ctx fn st lbl fv.
    cf_state_inv ctx.ce_bp fn st /\
    (case fv of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_copy_locs ctx.ce_bp fn)) /\
    (case df_boundary NONE st lbl of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_copy_locs ctx.ce_bp fn)) ==>
    !lbl' fmap.
      FLOOKUP (st.ds_boundary |+ (lbl,
        copy_fact_join ctx.ce_dfg (df_boundary NONE st lbl) fv)) lbl' =
        SOME (SOME fmap) ==>
      FDOM fmap SUBSET set (fn_copy_locs ctx.ce_bp fn)
Proof
  rpt strip_tac >>
  fs[FLOOKUP_UPDATE] >>
  Cases_on `lbl = lbl'` >> gvs[]
  >- (qspecl_then [`ctx.ce_dfg`, `df_boundary NONE st lbl`, `fv`,
                    `set (fn_copy_locs ctx.ce_bp fn)`]
        mp_tac cf_join_fdom_subset >> simp[] >> strip_tac >>
      Cases_on `copy_fact_join ctx.ce_dfg (df_boundary NONE st lbl) fv` >>
      gvs[])
  >- (fs[cf_state_inv_def] >> res_tac)
QED

(* State invariant preservation *)
Triviality cf_state_inv_preserved[local]:
  !ctx fn lbl st.
    fn_inst_wf fn /\ cf_state_inv ctx.ce_bp fn st ==>
    cf_state_inv ctx.ce_bp fn
      (df_process_block Forward NONE (copy_fact_join ctx.ce_dfg)
         copy_fact_transfer copy_fact_edge_transfer ctx
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt strip_tac >>
  `case copy_fact_joined ctx fn st lbl of NONE => T
   | SOME fmap => FDOM fmap SUBSET set (fn_copy_locs ctx.ce_bp fn)`
    by metis_tac[cf_joined_inv] >>
  `case df_boundary NONE st lbl of NONE => T
   | SOME fmap => FDOM fmap SUBSET set (fn_copy_locs ctx.ce_bp fn)`
    by metis_tac[df_boundary_cf_inv] >>
  simp[cf_process_eq] >>
  simp_tac std_ss [LET_THM] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  `EVERY (\inst. MEM inst (fn_insts fn))
     (case lookup_block lbl fn.fn_blocks of NONE => []
      | SOME bb => bb.bb_instructions)` by (
    simp[EVERY_MEM] >> rpt strip_tac >>
    Cases_on `lookup_block lbl fn.fn_blocks` >> fs[] >>
    simp[fn_insts_def] >> irule fn_insts_blocks_mem >>
    fs[lookup_block_def] >> imp_res_tac find_mem >> metis_tac[]) >>
  drule_all cf_fold_fdom >> strip_tac >>
  simp[cf_state_inv_def] >> rpt conj_tac
  >- metis_tac[cf_boundary_fdom_preserved]
  >> fs[cf_state_inv_def]
QED

(* Full invariant preservation *)
Theorem cf_inv_preserved:
  !ctx fn lbl st.
    cf_measure_inv ctx fn st ==>
    cf_measure_inv ctx fn
      (df_process_block Forward NONE (copy_fact_join ctx.ce_dfg)
         copy_fact_transfer copy_fact_edge_transfer ctx
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt strip_tac >>
  simp[cf_measure_inv_def] >>
  conj_tac >- fs[cf_measure_inv_def] >>
  conj_tac >- (
    irule cf_state_inv_preserved >>
    fs[cf_measure_inv_def]) >>
  (* New df_process_block only updates ds_boundary, ds_inst unchanged.
     So C3-C5 (about ds_inst) are trivially preserved. *)
  simp[cf_process_eq] >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  fs[cf_measure_inv_def] >> metis_tac[]
QED

(* Initial invariant *)
Theorem cf_measure_inv_initial:
  !ctx fn.
    fn_inst_wf fn ==>
    (case OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn) of
       NONE =>
         cf_measure_inv ctx fn
           (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks))
     | SOME (lbl, v) =>
         cf_measure_inv ctx fn
           (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks) with
              ds_boundary :=
                (init_df_state NONE
                   (MAP (\bb. bb.bb_label) fn.fn_blocks)).ds_boundary |+
                (lbl, v)))
Proof
  rpt strip_tac >>
  simp[cf_measure_inv_def, LET_THM] >>
  Cases_on `fn_entry_label fn` >> simp[] >>
  simp[init_df_state_def, FLOOKUP_UPDATE, FLOOKUP_DEF, FDOM_FUPDATE,
       FDOM_FEMPTY, cf_init_state_inv, cf_init_state_inv_entry]
QED

(* ===== Monotonicity ===== *)

(* Main monotonicity theorem.
   Since df_process_block only changes ds_boundary (never ds_inst),
   when result <> st the boundary at lbl must have strictly changed.
   The weighted measure (w+1)*boundary + fresh + dfs_visited strictly increases. *)
Theorem cf_measure_monotone:
  !ctx fn lbl st.
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    cf_measure_inv ctx fn st /\
    df_process_block Forward NONE (copy_fact_join ctx.ce_dfg)
      copy_fact_transfer copy_fact_edge_transfer ctx
      (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks lbl st <> st ==>
    cf_measure ctx fn st <
    cf_measure ctx fn
      (df_process_block Forward NONE (copy_fact_join ctx.ce_dfg)
         copy_fact_transfer copy_fact_edge_transfer ctx
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt strip_tac >>
  rewrite_tac[cf_process_eq] >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  qabbrev_tac `joined = copy_fact_joined ctx fn st lbl` >>
  qabbrev_tac `instrs = case lookup_block lbl fn.fn_blocks of
                           NONE => [] | SOME bb => bb.bb_instructions` >>
  qabbrev_tac `new_bnd = copy_fact_join ctx.ce_dfg (df_boundary NONE st lbl) fv` >>
  (* Since result <> st, boundary must have changed *)
  `new_bnd <> df_boundary NONE st lbl` by (
    strip_tac >>
    qpat_x_assum `_ <> st` mp_tac >> simp[] >>
    rewrite_tac[cf_process_eq] >>
    simp_tac std_ss [LET_THM] >>
    qunabbrev_tac `instrs` >> qunabbrev_tac `joined` >>
    qpat_x_assum `df_fold_block _ _ _ _ _ = _` (fn th => simp[th]) >>
    fs[markerTheory.Abbrev_def]) >>
  (* Bound cardinalities of fv and old boundary *)
  `case fv of NONE => T
   | SOME fmap => CARD (FDOM fmap) <=
                  CARD (set (fn_copy_locs ctx.ce_bp fn))` by (
    `EVERY (\inst. MEM inst (fn_insts fn)) instrs` by (
      qunabbrev_tac `instrs` >>
      Cases_on `lookup_block lbl fn.fn_blocks` >> simp[EVERY_MEM] >>
      rpt strip_tac >> simp[fn_insts_def] >>
      irule fn_insts_blocks_mem >>
      fs[lookup_block_def] >> metis_tac[find_mem]) >>
    `cf_state_inv ctx.ce_bp fn st` by fs[cf_measure_inv_def] >>
    `case joined of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_copy_locs ctx.ce_bp fn)` by
      metis_tac[cf_joined_inv] >>
    qspecl_then [`ctx`, `fn`, `lbl`, `instrs`, `joined`, `fv`, `inst_map`]
      mp_tac cf_fold_fdom >>
    impl_tac >- simp[] >>
    strip_tac >> Cases_on `fv` >> fs[] >>
    irule CARD_SUBSET >> fs[FINITE_LIST_TO_SET]) >>
  `case df_boundary NONE st lbl of NONE => T
   | SOME fmap => CARD (FDOM fmap) <=
                  CARD (set (fn_copy_locs ctx.ce_bp fn))` by (
    Cases_on `FLOOKUP st.ds_boundary lbl` >> simp[df_boundary_def] >>
    Cases_on `x` >> simp[] >>
    fs[cf_measure_inv_def, cf_state_inv_def] >>
    first_x_assum drule >> strip_tac >>
    irule CARD_SUBSET >> fs[FINITE_LIST_TO_SET]) >>
  (* Result is st with ds_boundary updated only — ds_inst unchanged *)
  simp_tac std_ss [cf_measure_def, LET_THM] >>
  (* cf_boundary_measure strictly increases *)
  `cf_boundary_measure ctx.ce_bp fn st <
   cf_boundary_measure ctx.ce_bp fn
     (st with ds_boundary := st.ds_boundary |+ (lbl, new_bnd))` by (
    irule boundary_measure_strict >> simp[MEM_APPEND] >>
    qpat_x_assum `Abbrev (new_bnd = _)` (SUBST_ALL_TAC o
      REWRITE_RULE [markerTheory.Abbrev_def]) >>
    irule cf_val_measure_join_strict >> simp[]) >>
  (* CARD(ds_boundary ∩ dfs_pre) grows *)
  `CARD (FDOM st.ds_boundary INTER set (cfg_analyze fn).cfg_dfs_pre) <=
   CARD (FDOM (st.ds_boundary |+ (lbl, new_bnd)) INTER
         set (cfg_analyze fn).cfg_dfs_pre)` by (
    irule CARD_SUBSET >> simp[FINITE_INTER, FDOM_FUPDATE] >>
    simp[SUBSET_DEF, IN_INTER] >> metis_tac[IN_INSERT]) >>
  (* fresh_count bounded *)
  assume_tac (Q.SPECL [`ctx`, `fn`, `st`] cf_fresh_count_bounded) >>
  gvs[] >>
  (* Apply weighted inequality: (w+1)*a + c < (w+1)*a' when a < a' and c <= w *)
  mp_tac (ISPECL [
    ``LENGTH (fn_labels fn) + LENGTH (cfg_analyze fn).cfg_dfs_pre``,
    ``cf_boundary_measure ctx.ce_bp fn st``,
    ``cf_boundary_measure ctx.ce_bp fn
        (st with ds_boundary := st.ds_boundary |+ (lbl, new_bnd))``,
    ``cf_fresh_count ctx fn st``] weighted_lt_cancel) >>
  simp[]
QED

(* ===== Main convergence theorem ===== *)

val fixpoint_restricted_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_analyze_fixpoint_process_restricted));

Theorem copy_fact_is_fixpoint:
  !ctx fn.
    fn_inst_wf fn ==>
    is_fixpoint
      (df_process_block Forward NONE (copy_fact_join ctx.ce_dfg)
         copy_fact_transfer copy_fact_edge_transfer ctx
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (df_analyze Forward NONE (copy_fact_join ctx.ce_dfg)
         copy_fact_transfer copy_fact_edge_transfer ctx
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
Proof
  rpt strip_tac >>
  match_mp_tac fixpoint_restricted_fwd >>
  qexists_tac `cf_measure ctx fn` >>
  qexists_tac `cf_measure_bound ctx fn` >>
  qexists_tac `cf_measure_inv ctx fn` >>
  qexists_tac `\lbl. MEM lbl (cfg_analyze fn).cfg_dfs_pre` >>
  BETA_TAC >> rpt conj_tac
  >- (rpt strip_tac >> fs[] >> metis_tac[cf_measure_monotone])
  >- (rpt strip_tac >> metis_tac[cf_inv_preserved])
  >- (mp_tac (SPEC_ALL cf_measure_inv_initial) >>
      Cases_on `fn_entry_label fn` >> simp[] >> metis_tac[])
  >- (rpt strip_tac >> irule cf_measure_bounded >> metis_tac[])
  >- (match_mp_tac (SIMP_RULE std_ss [LET_THM]
        dfAnalyzeProofsTheory.df_process_deps_complete_proof |>
        SPEC ``Forward : direction`` |>
        SIMP_RULE std_ss [dfAnalyzeDefsTheory.direction_case_def]) >>
      rw[copy_fact_join_absorption] >>
      metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond])
  >- simp[EVERY_MEM]
  >- (rpt strip_tac >> fs[] >>
      imp_res_tac analysisSimPropsTheory.cfg_dfs_pre_succs_closed >>
      fs[EVERY_MEM])
QED
