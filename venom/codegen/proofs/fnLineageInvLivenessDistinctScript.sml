Theory fnLineageInvLivenessDistinct
Ancestors livenessDefs dfAnalyzeDefs finite_map list
  fnPlanLineagePhiMaps fnPlanPrefix livenessBlockProofs dfHelperDefs
  livenessTerminationProofs worklistDefs

Theorem liveness_backward_distinct:
 !insts bbs lbl idx acc im entry im'.
 ALL_DISTINCT acc /\
 (!key vs. FLOOKUP im key = SOME vs ==> ALL_DISTINCT vs) /\
 df_fold_backward (liveness_transfer bbs) lbl insts idx acc im = (entry, im') ==>
 ALL_DISTINCT entry /\
 (!key vs. FLOOKUP im' key = SOME vs ==> ALL_DISTINCT vs)
Proof
 Induct_on `insts`
 >- (simp[df_fold_backward_def] >> rpt strip_tac >>
     gvs[FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]) >>
 rpt gen_tac >> strip_tac >>
 gvs[df_fold_backward_def] >> pairarg_tac >> gvs[] >>
 first_x_assum drule_all >> strip_tac >>
 `ALL_DISTINCT (liveness_transfer bbs h acc')` by
   simp[liveness_transfer_def, live_update_ALL_DISTINCT] >>
 simp[] >> rpt strip_tac >> gvs[FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]
QED

Theorem liveness_backward_block_distinct:
 !bbs lbl insts acc entry im.
 ALL_DISTINCT acc /\
 df_fold_block Backward (liveness_transfer bbs) lbl insts acc = (entry, im) ==>
 ALL_DISTINCT entry /\
 (!key vs. FLOOKUP im key = SOME vs ==> ALL_DISTINCT vs)
Proof
 rewrite_tac[df_fold_block_def, direction_case_def] >> rpt gen_tac >> strip_tac >>
 drule_at (Pat `df_fold_backward _ _ _ _ _ _ = _`) liveness_backward_distinct >>
 simp[] >> strip_tac >> simp[]
QED

Theorem ready_liveness_edge_distinct:
 !fn succ pred live.
 codegen_ready_fn fn /\ ALL_DISTINCT live ==>
 ALL_DISTINCT (liveness_edge_transfer fn.fn_blocks succ pred live)
Proof
 rpt gen_tac >> strip_tac >> simp[liveness_edge_transfer_def] >>
 Cases_on `lookup_block succ fn.fn_blocks` >> simp[] >>
 irule input_vars_from_distinct >> simp[] >>
 `MEM x fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
 drule_all phi_codegen_block_ready >> simp[stackPlanGenTheory.phi_block_ready_def]
QED

Theorem list_union_distinct:
 !xs ys. ALL_DISTINCT xs /\ ALL_DISTINCT ys ==> ALL_DISTINCT (list_union xs ys)
Proof
 simp[list_union_def, ALL_DISTINCT_APPEND, FILTER_ALL_DISTINCT, MEM_FILTER]
QED

Theorem foldl_list_union_distinct:
 !xss acc. EVERY ALL_DISTINCT xss /\ ALL_DISTINCT acc ==>
 ALL_DISTINCT (FOLDL list_union acc xss)
Proof
 Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
 simp[list_union_distinct]
QED

Theorem ready_liveness_out_distinct:
 !fn lbl st.
 codegen_ready_fn fn /\ (!l i. ALL_DISTINCT (df_at [] st l i)) ==>
 ALL_DISTINCT (liveness_out fn.fn_blocks (cfg_analyze fn) lbl st)
Proof
 rpt strip_tac >> simp[liveness_out_def] >>
 irule foldl_list_union_distinct >> simp[EVERY_MAP, EVERY_MEM] >>
 rpt strip_tac >> irule ready_liveness_edge_distinct >> simp[]
QED

Theorem ready_liveness_block_distinct:
 !fn st lbl.
 codegen_ready_fn fn /\ (!l i. ALL_DISTINCT (df_at [] st l i)) ==>
 !l i. ALL_DISTINCT
   (df_at [] (liveness_block fn.fn_blocks (cfg_analyze fn) lbl st) l i)
Proof
 rpt gen_tac >> strip_tac >> rpt gen_tac >>
 Cases_on `l = lbl`
 >- (gvs[] >> rename1 `liveness_block _ _ lbl st` >>
     Cases_on `i <= LENGTH (liveness_instrs fn.fn_blocks lbl)`
     >- (simp[liveness_block_read] >>
         Cases_on `df_fold_block Backward (liveness_transfer fn.fn_blocks) lbl
           (liveness_instrs fn.fn_blocks lbl)
           (liveness_out fn.fn_blocks (cfg_analyze fn) lbl st)` >>
         `ALL_DISTINCT (liveness_out fn.fn_blocks (cfg_analyze fn) lbl st)` by
           (irule ready_liveness_out_distinct >> simp[]) >>
         drule_all liveness_backward_block_distinct >> strip_tac >>
         drule_all backward_fold_lookup >> strip_tac >>
         simp[] >> metis_tac[]) >>
     simp[liveness_block_beyond]) >>
 simp[liveness_block_other_inst]
QED

Theorem analyzed_live_vars_distinct:
 !fn lbl idx. codegen_ready_fn fn ==>
 ALL_DISTINCT (live_vars_at (liveness_analyze fn) lbl idx)
Proof
 rpt gen_tac >> strip_tac >>
 `!l i. ALL_DISTINCT (df_at [] (liveness_recompute fn) l i)` suffices_by
   simp[live_vars_at_def, liveness_analyze_def] >>
 simp[liveness_recompute_def] >>
 irule (liveness_recompute_lift |> Q.INST
   [`Q` |-> `\p. !l i. ALL_DISTINCT (df_at [] (SND p) l i)`] |> BETA_RULE) >>
 conj_tac
 >- simp[init_df_state_def, df_at_def] >>
 rpt strip_tac >> Cases_on `p` >> Cases_on `q` >> gvs[] >>
 Cases_on `liveness_changed fn.fn_blocks h r
   (liveness_block fn.fn_blocks (cfg_analyze fn) h r)` >>
 simp[wl_step_def] >> irule ready_liveness_block_distinct >> simp[]
QED
