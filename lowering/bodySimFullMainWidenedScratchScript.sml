(* Scratch statement-level check for the widened body-simulation header. *)
Theory bodySimFullMainWidenedScratch
Ancestors
  loweringPosts bodyFullPostsMods bodyFullPreds bodyFullPredsMods bodyInvSplit bodySimFull bodySim
  bodyFullShadowBodyInv bodyLoopCalls contractInvContextProps constSubst constSubstMods
  vyperTypeContract[qualified,ignore_grammar] vyperAST vyperInterpreter
  vyperState vyperTypeCallGraph supportedStmts alist list option pair finite_map

val _ = Parse.hide "body";

Theorem stmt_state_rel_frame_wide:
  stmt_state_rel H ctx func cenv cx es s ==>
  immutable_frame_mods func cenv cx es s
Proof
  strip_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _ _` mp_tac >>
  simp[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def,
       immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def]
QED

Theorem stmt_state_rel_frame_conj_wide:
  stmt_state_rel H ctx func cenv cx es s /\
  immutable_frame_mods func cenv cx es s /\ P <=>
  stmt_state_rel H ctx func cenv cx es s /\ P
Proof
  EQ_TAC
  >- metis_tac[]
  >- (strip_tac >>
      `immutable_frame_mods func cenv cx es s` by
        (irule stmt_state_rel_frame_wide >> metis_tac[]) >>
      metis_tac[])
QED

Theorem immutable_holds_mods_wide:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  (immutable_holds_mods cenv cx t tv w es s <=>
   immutable_holds cenv cx t tv w es s)
Proof
  strip_tac >>
  `ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops` by
    fs[cenv_module_pins_mods_def, module_body_inv_def] >>
  rw[immutable_holds_mods_def, immutable_holds_def] >>
  simp[optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED

Theorem vv_place_ptr_mods_wide:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  (vv_place_ptr_mods cenv cx es s tv vv <=>
   vv_place_ptr cenv cx es s tv vv)
Proof
  strip_tac >>
  `ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops` by
    fs[cenv_module_pins_mods_def, module_body_inv_def] >>
  Cases_on `vv` >> Cases_on `tv` >>
  TRY (rename1 `PlaceR place` >> Cases_on `place`) >>
  simp[vv_place_ptr_mods_def, vv_place_ptr_def,
       optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED

Theorem vv_holds_mods_wide:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  (vv_holds_mods cenv cx t tv vv es s <=> vv_holds cenv cx t tv vv es s)
Proof
  strip_tac >> Cases_on `vv` >> simp[vv_holds_mods_def] >>
  rename1 `p.ptr_location = LocCode` >>
  Cases_on `p.ptr_location = LocCode` >>
  simp[vv_holds_def, vv_holds_mods_def] >>
  metis_tac[immutable_holds_mods_wide]
QED

Theorem expr_post_mods_wide:
  expr_post_mods H ctx func cenv cx e es sa sb s0 es' v op s <=>
  expr_post H ctx func cenv cx e es sa sb s0 es' v op s
Proof
  rw[expr_post_mods_def] >> EQ_TAC
  >- (strip_tac >> first_assum ACCEPT_TAC)
  >- (strip_tac >>
      `stmt_state_rel H ctx func cenv cx es' s` by
        (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         simp[expr_post_def]) >>
      `immutable_frame_mods func cenv cx es' s` by
        (qpat_x_assum `stmt_state_rel _ _ _ _ _ _ _` mp_tac >>
         simp[exprLoweringPropsTheory.stmt_state_rel_def,
              loweringStateRelDefsTheory.state_rel_def,
              immutable_frame_mods_def, immutables_rel_mods_def,
              immutable_alloca_sep_mods_def]) >>
      simp[])
QED

Theorem vv_post_mods_wide:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  (vv_post_mods H ctx func cenv cx e es sa sb s0 es' tv vv s <=>
   vv_post H ctx func cenv cx e es sa sb s0 es' tv vv s)
Proof
  strip_tac >> EQ_TAC
  >- (strip_tac >>
      `vv_holds_mods cenv cx (post_value_type cenv e) tv vv es' s <=>
       vv_holds cenv cx (post_value_type cenv e) tv vv es' s` by
        (irule vv_holds_mods_wide >> metis_tac[]) >>
      `vv_place_ptr_mods cenv cx es' s tv vv <=>
       vv_place_ptr cenv cx es' s tv vv` by
        (irule vv_place_ptr_mods_wide >> metis_tac[]) >>
      fs[vv_post_mods_def, vv_post_def] >> metis_tac[])
  >- (strip_tac >>
      `stmt_state_rel H ctx func cenv cx es' s` by fs[vv_post_def] >>
      `immutable_frame_mods func cenv cx es' s` by
        (qpat_x_assum `stmt_state_rel _ _ _ _ _ _ _` mp_tac >>
         simp[exprLoweringPropsTheory.stmt_state_rel_def,
              loweringStateRelDefsTheory.state_rel_def,
              immutable_frame_mods_def, immutables_rel_mods_def,
              immutable_alloca_sep_mods_def]) >>
      `vv_holds_mods cenv cx (post_value_type cenv e) tv vv es' s <=>
       vv_holds cenv cx (post_value_type cenv e) tv vv es' s` by
        (irule vv_holds_mods_wide >> metis_tac[]) >>
      `vv_place_ptr_mods cenv cx es' s tv vv <=>
       vv_place_ptr cenv cx es' s tv vv` by
        (irule vv_place_ptr_mods_wide >> metis_tac[]) >>
      fs[vv_post_mods_def, vv_post_def] >> metis_tac[])
QED

Theorem expr_sim_full_mods_wide:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  (expr_sim_full_mods cfg cenv cx ty e es <=>
   expr_sim_full cfg cenv cx ty e es)
Proof
  strip_tac >> PairCases_on `cfg` >>
  simp[bodyFullPostsModsTheory.expr_sim_full_mods_def,
       bodySimFullTheory.expr_sim_full_def,
       dead_lo_ok_mods_def, bodyPtrDefsTheory.dead_lo_ok_def,
       ghost_inv_at_mods_def, bodyPtrDefsTheory.ghost_inv_at_def,
       expr_post_mods_wide, stmt_state_rel_frame_wide,
       stmt_state_rel_frame_conj_wide, SF CONJ_ss]
QED

Theorem expr_vv_sim_full_mods_wide:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  (expr_vv_sim_full_mods cfg cenv cx ty e es <=>
   expr_vv_sim_full cfg cenv cx ty e es)
Proof
  strip_tac >> PairCases_on `cfg` >>
  drule_all immutable_holds_mods_wide >>
  drule_all vv_holds_mods_wide >>
  drule_all vv_place_ptr_mods_wide >>
  strip_tac >> strip_tac >> strip_tac >>
  ASM_SIMP_TAC bool_ss
    [bodyFullPostsModsTheory.expr_vv_sim_full_mods_def,
     bodySimFullTheory.expr_vv_sim_full_def,
     bodyFullPostsModsTheory.vv_post_mods_def,
     loweringPostsTheory.vv_post_def,
     dead_lo_ok_mods_def, bodyPtrDefsTheory.dead_lo_ok_def,
     ghost_inv_at_mods_def, bodyPtrDefsTheory.ghost_inv_at_def,
     immutable_holds_mods_wide, vv_holds_mods_wide,
     vv_place_ptr_mods_wide,
     stmt_state_rel_frame_wide, stmt_state_rel_frame_conj_wide,
     SF CONJ_ss]
QED

Theorem expr_map_sim_full_mods_wide:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  (expr_map_sim_full_mods cfg cenv cx ty e es <=>
   expr_map_sim_full cfg cenv cx ty e es)
Proof
  strip_tac >> PairCases_on `cfg` >>
  simp[bodyFullPostsModsTheory.expr_map_sim_full_mods_def,
       bodySimFullTheory.expr_map_sim_full_def,
       dead_lo_ok_mods_def, bodyPtrDefsTheory.dead_lo_ok_def,
       ghost_inv_at_mods_def, bodyPtrDefsTheory.ghost_inv_at_def,
       stmt_state_rel_frame_wide, stmt_state_rel_frame_conj_wide, SF CONJ_ss]
QED

Theorem stmt_frag_full_mods_wide:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  (stmt_frag_full_mods cfg cx lctx RetQ cenv m shadow_m source es <=>
   stmt_frag_full cfg cx lctx RetQ cenv m shadow_m source es)
Proof
  strip_tac >> PairCases_on `cfg` >>
  simp[bodyFullPostsModsTheory.stmt_frag_full_mods_def,
       bodySimFullTheory.stmt_frag_full_def,
       dead_lo_ok_mods_def, bodyPtrDefsTheory.dead_lo_ok_def,
       ghost_inv_at_mods_def, bodyPtrDefsTheory.ghost_inv_at_def,
       stmt_state_rel_frame_wide, stmt_state_rel_frame_conj_wide, SF CONJ_ss]
QED

(* The signed header keeps its two guards.  The post callbacks are the
   widened single-file posts, by expr_post_mods_wide and vv_post_mods_wide.
   The induction itself is intentionally admitted in this fast-fail scratch. *)
val linked_body_guard_wide =
  ``ALOOKUP cx.sources cx.txn.target = SOME mods /\
    vyperTypeContract$exports_ok cx.layouts cx.txn.target mods exps /\
    IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target mods) /\
    EVERY (struct_args_unique o SND) mods /\
    (!src tops vis mut nr raw fn args dflts ret ss.
       ALOOKUP mods src = SOME tops /\
       MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
       stmts_loop_calls_ok mods
         (subst_consts_stmts_mods (consts_env_mods mods) ss))``;
val linked_calls_live_wide =
  ``\calls. EVERY (\k. MEM k
      (vyperTypeContract$linked_live_functions mods exps)) calls``;
fun linked_body_ind_wide rank_guard =
  evaluate_ind |> Q.SPECL [
    `\cx s. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_stmt s) /\ stmt_loop_calls_ok mods s ==>
       body_stmt_full_ok_mods mods exps cx s`,
    `\cx ss. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_stmts ss) /\ stmts_loop_calls_ok mods ss ==>
       body_stmts_full_ok_mods mods exps cx ss`,
    `\cx it. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_iterator it) ==>
       body_iterator_full_ok_mods mods exps cx it`,
    `\cx tyv nm body vs. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_stmts body) /\ stmts_loop_calls_ok mods body ==>
       body_for_full_ok_mods mods exps cx tyv nm body vs`,
    `\cx e. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_expr e) ==>
       body_expr_full_ok_mods mods exps cx e`,
    `\cx es. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_exprs es) ==>
       body_exprs_full_ok_mods mods exps cx es`,
    `\cx t. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_target t) ==>
       body_base_target_full_ok_mods mods exps cx t`,
    `\cx t. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_target t) ==>
       body_base_target_full_ok_mods mods exps cx t`,
    `\cx g v. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_atarget g) ==>
       body_tuple_target_full_ok_mods mods exps cx g v`,
    `\cx gs vs. ^rank_guard /\ ^linked_body_guard_wide /\
       ^linked_calls_live_wide (int_calls_atargets gs) ==>
       body_tuple_targets_full_ok_mods mods exps cx gs vs`]
  |> CONV_RULE (DEPTH_CONV BETA_CONV);
val ranked_linked_body_ind_wide = linked_body_ind_wide ``LENGTH (remcode cx) <= rank``;

Theorem body_sim_full_mutual_ranked_mods_widened:
  !mods exps rank:num. ^(snd (dest_imp (concl ranked_linked_body_ind_wide)))
Proof
  cheat
QED

val unranked_linked_body_ind_wide = linked_body_ind_wide ``T``;

Theorem body_sim_full_mutual_mods_widened:
  !mods exps. ^(simpLib.SIMP_CONV bool_ss []
    (snd (dest_imp (concl unranked_linked_body_ind_wide))) |> concl |> rhs)
Proof
  rpt gen_tac >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  qmatch_asmsub_rename_tac `ALOOKUP cx.sources cx.txn.target` >>
  qspecl_then [`mods`, `exps`, `LENGTH (remcode cx)`] strip_assume_tac
    body_sim_full_mutual_ranked_mods_widened >>
  first_x_assum irule >> asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem body_stmt_full_ok_singleton_wide:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
  EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
    (int_calls_stmt s) /\
  struct_args_unique tops /\
  (!vis mut nr raw fn args dflts ret ss.
     MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
     stmts_loop_calls_ok [(NONE,tops)]
       (subst_consts_stmts (module_consts_env tops []) ss)) /\
  stmt_loop_calls_ok [(NONE,tops)] s ==>
  body_stmt_full_ok cx s
Proof
  strip_tac >>
  `body_stmt_full_ok_mods [(NONE,tops)] [] cx s` by
    (irule (cj 1 (Q.SPECL [`[(NONE,tops)]`,`[]`]
      body_sim_full_mutual_mods_widened)) >>
     simp[alistTheory.ALOOKUP_def,
          constSubstModsTheory.consts_env_mods_singleton,
          constSubstModsTheory.subst_consts_mods_singleton] >>
     conj_tac
     >- first_assum ACCEPT_TAC
     >- metis_tac[vyperTypeContractTheory.check_contract_single_module_exports_ok,
                 optionTheory.IS_SOME_EXISTS]) >>
  `body_stmt_full_ok_mods [(NONE,tops)] [] cx s <=> body_stmt_full_ok cx s` by
    (irule body_stmt_full_ok_mods_singleton >> first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

Theorem check_single_exports_from_is_some_wide:
  IS_SOME (vyperTypeContract$check_contract F layouts addr [(NONE,tops)]) ==>
  vyperTypeContract$exports_ok layouts addr [(NONE,tops)] []
Proof
  strip_tac >>
  qpat_x_assum `IS_SOME (vyperTypeContract$check_contract _ _ _ _)`
    (mp_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  strip_tac >>
  metis_tac[vyperTypeContractTheory.check_contract_single_module_exports_ok]
QED

Theorem no_singleton_body_inv_false:
  (!tops. ALOOKUP cx.sources cx.txn.target <> SOME [(NONE,tops)]) /\
  body_inv tops ctx cenv cx ==> F
Proof
  strip_tac >>
  qpat_assum `body_inv _ _ _ _`
    (assume_tac o MATCH_MP body_inv_contract) >>
  qpat_assum `contract_inv _ _ _ _ _`
    (assume_tac o MATCH_MP contract_inv_singleton_source_modules) >>
  metis_tac[]
QED

Theorem body_expr_no_singleton_source_wide:
  (!tops. ALOOKUP cx.sources cx.txn.target <> SOME [(NONE,tops)]) ==>
  body_expr_full_ok cx e
Proof
  `(!cx e. (!tops. ALOOKUP cx.sources cx.txn.target <> SOME [(NONE,tops)]) ==>
       body_expr_full_ok cx e) /\
   (!cx es. (!tops. ALOOKUP cx.sources cx.txn.target <> SOME [(NONE,tops)]) ==>
       body_exprs_full_ok cx es)` by
    (ho_match_mp_tac bodyFullPredsTheory.body_expr_full_ok_ind >>
     rpt conj_tac >> rpt strip_tac >>
     once_rewrite_tac[bodyFullPredsTheory.body_expr_full_ok_def] >>
     simp[] >>
     metis_tac[no_singleton_body_inv_false]) >>
  metis_tac[]
QED

Theorem body_stmt_no_singleton_source_wide:
  (!tops. ALOOKUP cx.sources cx.txn.target <> SOME [(NONE,tops)]) ==>
  body_stmt_full_ok cx s
Proof
  strip_tac >>
  once_rewrite_tac[bodyFullPredsTheory.body_stmt_full_ok_def] >>
  rpt gen_tac >> rpt strip_tac >>
  metis_tac[no_singleton_body_inv_false]
QED

Theorem body_stmts_no_singleton_source_wide:
  (!tops. ALOOKUP cx.sources cx.txn.target <> SOME [(NONE,tops)]) ==>
  body_stmts_full_ok cx ss
Proof
  strip_tac >>
  once_rewrite_tac[bodyFullPredsTheory.body_stmts_full_ok_def] >>
  rpt gen_tac >> rpt strip_tac >>
  metis_tac[no_singleton_body_inv_false]
QED

Theorem body_results_no_singleton_source_wide:
  (!tops. ALOOKUP cx.sources cx.txn.target <> SOME [(NONE,tops)]) ==>
  body_results_full_ok cx es
Proof
  strip_tac >>
  Induct_on `es` >>
  simp[bodyFullPredsTheory.body_results_full_ok_def] >>
  metis_tac[body_expr_no_singleton_source_wide]
QED

Theorem body_exprs_no_singleton_source_wide:
  (!tops. ALOOKUP cx.sources cx.txn.target <> SOME [(NONE,tops)]) ==>
  body_exprs_full_ok cx es
Proof
  strip_tac >>
  Induct_on `es` >>
  simp[bodyFullPredsTheory.body_exprs_full_ok_def] >>
  metis_tac[body_expr_no_singleton_source_wide]
QED

Theorem body_iterator_no_singleton_source_wide:
  (!tops. ALOOKUP cx.sources cx.txn.target <> SOME [(NONE,tops)]) ==>
  body_iterator_full_ok cx it
Proof
  strip_tac >>
  Cases_on `it` >>
  simp[bodyFullPredsTheory.body_iterator_full_ok_def] >>
  metis_tac[body_expr_no_singleton_source_wide]
QED

Theorem body_for_no_singleton_source_wide:
  (!tops. ALOOKUP cx.sources cx.txn.target <> SOME [(NONE,tops)]) ==>
  body_for_full_ok cx tyv nm body vs
Proof
  strip_tac >>
  simp[bodyFullPredsTheory.body_for_full_ok_def] >>
  metis_tac[body_stmts_no_singleton_source_wide]
QED

Theorem body_base_target_no_singleton_source_wide:
  (!tops. ALOOKUP cx.sources cx.txn.target <> SOME [(NONE,tops)]) ==>
  body_base_target_full_ok cx bt
Proof
  strip_tac >>
  completeInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >>
  gvs[bodyFullPredsTheory.body_base_target_full_ok_def, expr_size_def] >>
  metis_tac[body_expr_no_singleton_source_wide]
QED

Theorem body_tuple_target_no_singleton_source_wide:
  ((!tops. ALOOKUP cx.sources cx.txn.target <> SOME [(NONE,tops)]) ==>
     body_tuple_target_full_ok cx g v) /\
  ((!tops. ALOOKUP cx.sources cx.txn.target <> SOME [(NONE,tops)]) ==>
     body_tuple_targets_full_ok cx gs vs)
Proof
  `(!cx g v. (!tops. ALOOKUP cx.sources cx.txn.target <> SOME [(NONE,tops)]) ==>
       body_tuple_target_full_ok cx g v) /\
   (!cx gs vs. (!tops. ALOOKUP cx.sources cx.txn.target <> SOME [(NONE,tops)]) ==>
       body_tuple_targets_full_ok cx gs vs)` by
    (ho_match_mp_tac bodyFullPredsTheory.body_tuple_target_full_ok_ind >>
     rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
     once_rewrite_tac[bodyFullPredsTheory.body_tuple_target_full_ok_def] >>
     gvs[] >>
     metis_tac[body_base_target_no_singleton_source_wide,
               no_singleton_body_inv_false]) >>
  metis_tac[]
QED

Theorem body_sim_full_mutual_guarded_wide:
  (!cx s. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_stmt s) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmt_loop_calls_ok [(NONE,tops)] s) ==>
    body_stmt_full_ok cx s) /\
  (!cx ss. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_stmts ss) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmts_loop_calls_ok [(NONE,tops)] ss) ==>
    body_stmts_full_ok cx ss) /\
  (!cx it. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_iterator it) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_iterator_full_ok cx it) /\
  (!cx tyv nm body vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_stmts body) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmts_loop_calls_ok [(NONE,tops)] body) ==>
    body_for_full_ok cx tyv nm body vs) /\
  (!cx e. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_expr e) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_expr_full_ok cx e) /\
  (!cx es. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_exprs es) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_exprs_full_ok cx es) /\
  (!cx t. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_target t) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_base_target_full_ok cx t) /\
  (!cx t. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_target t) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_base_target_full_ok cx t) /\
  (!cx g v. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_atarget g) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_tuple_target_full_ok cx g v) /\
  (!cx gs vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_atargets gs) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_tuple_targets_full_ok cx gs vs)
Proof
  rpt conj_tac
  >- (rpt gen_tac >> rpt strip_tac >>
      Cases_on `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` >>
      rpt strip_tac
      >- (TRY (qpat_assum `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (strip_assume_tac)) >>
          TRY (qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (qspec_then `tops` (assume_tac o SIMP_RULE bool_ss []))) >>
          `body_stmt_full_ok_mods [(NONE,tops)] [] cx s` by
            (irule (cj 1 (Q.SPECL [`[(NONE,tops)]`,`[]`]
              body_sim_full_mutual_mods_widened)) >>
             simp[alistTheory.ALOOKUP_def,
                  constSubstModsTheory.consts_env_mods_singleton,
                  constSubstModsTheory.subst_consts_mods_singleton] >>
             metis_tac[check_single_exports_from_is_some_wide]) >>
          metis_tac[body_stmt_full_ok_mods_singleton])
      >- metis_tac[body_stmt_no_singleton_source_wide])
  >- (rpt gen_tac >> rpt strip_tac >>
      Cases_on `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` >>
      rpt strip_tac
      >- (TRY (qpat_assum `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (strip_assume_tac)) >>
          TRY (qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (qspec_then `tops` (assume_tac o SIMP_RULE bool_ss []))) >>
          `body_stmts_full_ok_mods [(NONE,tops)] [] cx ss` by
            (irule (cj 2 (Q.SPECL [`[(NONE,tops)]`,`[]`]
              body_sim_full_mutual_mods_widened)) >>
             simp[alistTheory.ALOOKUP_def,
                  constSubstModsTheory.consts_env_mods_singleton,
                  constSubstModsTheory.subst_consts_mods_singleton] >>
             metis_tac[check_single_exports_from_is_some_wide]) >>
          metis_tac[body_stmts_full_ok_mods_singleton])
      >- metis_tac[body_stmts_no_singleton_source_wide])
  >- (rpt gen_tac >> rpt strip_tac >>
      Cases_on `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` >>
      rpt strip_tac
      >- (TRY (qpat_assum `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (strip_assume_tac)) >>
          TRY (qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (qspec_then `tops` (assume_tac o SIMP_RULE bool_ss []))) >>
          `body_iterator_full_ok_mods [(NONE,tops)] [] cx it` by
            (irule (cj 3 (Q.SPECL [`[(NONE,tops)]`,`[]`]
              body_sim_full_mutual_mods_widened)) >>
             simp[alistTheory.ALOOKUP_def,
                  constSubstModsTheory.consts_env_mods_singleton,
                  constSubstModsTheory.subst_consts_mods_singleton] >>
             metis_tac[check_single_exports_from_is_some_wide]) >>
          metis_tac[body_iterator_full_ok_mods_singleton])
      >- metis_tac[body_iterator_no_singleton_source_wide])
  >- (rpt gen_tac >> rpt strip_tac >>
      Cases_on `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` >>
      rpt strip_tac
      >- (TRY (qpat_assum `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (strip_assume_tac)) >>
          TRY (qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (qspec_then `tops` (assume_tac o SIMP_RULE bool_ss []))) >>
          `body_for_full_ok_mods [(NONE,tops)] [] cx tyv nm body vs` by
            (irule (cj 4 (Q.SPECL [`[(NONE,tops)]`,`[]`]
              body_sim_full_mutual_mods_widened)) >>
             simp[alistTheory.ALOOKUP_def,
                  constSubstModsTheory.consts_env_mods_singleton,
                  constSubstModsTheory.subst_consts_mods_singleton] >>
             metis_tac[check_single_exports_from_is_some_wide]) >>
          metis_tac[body_for_full_ok_mods_singleton])
      >- metis_tac[body_for_no_singleton_source_wide])
  >- (rpt gen_tac >> rpt strip_tac >>
      Cases_on `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` >>
      rpt strip_tac
      >- (TRY (qpat_assum `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (strip_assume_tac)) >>
          TRY (qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (qspec_then `tops` (assume_tac o SIMP_RULE bool_ss []))) >>
          `body_expr_full_ok_mods [(NONE,tops)] [] cx e` by
            (irule (cj 5 (Q.SPECL [`[(NONE,tops)]`,`[]`]
              body_sim_full_mutual_mods_widened)) >>
             simp[alistTheory.ALOOKUP_def,
                  constSubstModsTheory.consts_env_mods_singleton,
                  constSubstModsTheory.subst_consts_mods_singleton] >>
             metis_tac[check_single_exports_from_is_some_wide]) >>
          metis_tac[body_expr_full_ok_mods_singleton])
      >- metis_tac[body_expr_no_singleton_source_wide])
  >- (rpt gen_tac >> rpt strip_tac >>
      Cases_on `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` >>
      rpt strip_tac
      >- (TRY (qpat_assum `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (strip_assume_tac)) >>
          TRY (qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (qspec_then `tops` (assume_tac o SIMP_RULE bool_ss []))) >>
          `body_exprs_full_ok_mods [(NONE,tops)] [] cx es` by
            (irule (cj 6 (Q.SPECL [`[(NONE,tops)]`,`[]`]
              body_sim_full_mutual_mods_widened)) >>
             simp[alistTheory.ALOOKUP_def,
                  constSubstModsTheory.consts_env_mods_singleton,
                  constSubstModsTheory.subst_consts_mods_singleton] >>
             metis_tac[check_single_exports_from_is_some_wide]) >>
          metis_tac[body_expr_full_ok_mods_singleton])
      >- metis_tac[body_exprs_no_singleton_source_wide])
  >- (rpt gen_tac >> rpt strip_tac >>
      Cases_on `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` >>
      rpt strip_tac
      >- (TRY (qpat_assum `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (strip_assume_tac)) >>
          TRY (qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (qspec_then `tops` (assume_tac o SIMP_RULE bool_ss []))) >>
          `body_base_target_full_ok_mods [(NONE,tops)] [] cx t` by
            (irule (cj 7 (Q.SPECL [`[(NONE,tops)]`,`[]`]
              body_sim_full_mutual_mods_widened)) >>
             simp[alistTheory.ALOOKUP_def,
                  constSubstModsTheory.consts_env_mods_singleton,
                  constSubstModsTheory.subst_consts_mods_singleton] >>
             metis_tac[check_single_exports_from_is_some_wide]) >>
          metis_tac[body_base_target_full_ok_mods_singleton])
      >- metis_tac[body_base_target_no_singleton_source_wide])
  >- (rpt gen_tac >> rpt strip_tac >>
      Cases_on `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` >>
      rpt strip_tac
      >- (TRY (qpat_assum `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (strip_assume_tac)) >>
          TRY (qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (qspec_then `tops` (assume_tac o SIMP_RULE bool_ss []))) >>
          `body_base_target_full_ok_mods [(NONE,tops)] [] cx t` by
            (irule (cj 8 (Q.SPECL [`[(NONE,tops)]`,`[]`]
              body_sim_full_mutual_mods_widened)) >>
             simp[alistTheory.ALOOKUP_def,
                  constSubstModsTheory.consts_env_mods_singleton,
                  constSubstModsTheory.subst_consts_mods_singleton] >>
             metis_tac[check_single_exports_from_is_some_wide]) >>
          metis_tac[body_base_target_full_ok_mods_singleton])
      >- metis_tac[body_base_target_no_singleton_source_wide])
  >- (rpt gen_tac >> rpt strip_tac >>
      Cases_on `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` >>
      rpt strip_tac
      >- (TRY (qpat_assum `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (strip_assume_tac)) >>
          TRY (qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (qspec_then `tops` (assume_tac o SIMP_RULE bool_ss []))) >>
          `body_tuple_target_full_ok_mods [(NONE,tops)] [] cx g v` by
            (irule (cj 9 (Q.SPECL [`[(NONE,tops)]`,`[]`]
              body_sim_full_mutual_mods_widened)) >>
             simp[alistTheory.ALOOKUP_def,
                  constSubstModsTheory.consts_env_mods_singleton,
                  constSubstModsTheory.subst_consts_mods_singleton] >>
             metis_tac[check_single_exports_from_is_some_wide]) >>
          metis_tac[body_tuple_target_full_ok_mods_singleton])
      >- metis_tac[body_tuple_target_no_singleton_source_wide])
  >- (rpt gen_tac >> rpt strip_tac >>
      Cases_on `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` >>
      rpt strip_tac
      >- (TRY (qpat_assum `?tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (strip_assume_tac)) >>
          TRY (qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
            (qspec_then `tops` (assume_tac o SIMP_RULE bool_ss []))) >>
          `body_tuple_targets_full_ok_mods [(NONE,tops)] [] cx gs vs` by
            (irule (cj 10 (Q.SPECL [`[(NONE,tops)]`,`[]`]
              body_sim_full_mutual_mods_widened)) >>
             simp[alistTheory.ALOOKUP_def,
                  constSubstModsTheory.consts_env_mods_singleton,
                  constSubstModsTheory.subst_consts_mods_singleton] >>
             metis_tac[check_single_exports_from_is_some_wide]) >>
          metis_tac[body_tuple_target_full_ok_mods_singleton])
      >- metis_tac[body_tuple_target_no_singleton_source_wide])
QED


Theorem body_sim_full_mutual:
  (!cx s. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_stmt s) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmt_loop_calls_ok [(NONE,tops)] s) ==>
    body_stmt_full_ok cx s) /\
  (!cx ss. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_stmts ss) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmts_loop_calls_ok [(NONE,tops)] ss) ==>
    body_stmts_full_ok cx ss) /\
  (!cx it. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_iterator it) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_iterator_full_ok cx it) /\
  (!cx tyv nm body vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_stmts body) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss)) /\
                 stmts_loop_calls_ok [(NONE,tops)] body) ==>
    body_for_full_ok cx tyv nm body vs) /\
  (!cx e. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_expr e) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_expr_full_ok cx e) /\
  (!cx es. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_exprs es) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_exprs_full_ok cx es) /\
  (!cx t. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_target t) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_base_target_full_ok cx t) /\
  (!cx g v. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_atarget g) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_tuple_target_full_ok cx g v) /\
  (!cx gs vs. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 IS_SOME (vyperTypeContract$check_contract F cx.layouts cx.txn.target [(NONE,tops)]) /\
                 EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
                   (int_calls_atargets gs) /\
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret ss.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret ss) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) ss))) ==>
    body_tuple_targets_full_ok cx gs vs)
Proof
  rpt conj_tac
  >- (rpt gen_tac >> rpt strip_tac >>
      irule (cj 1 body_sim_full_mutual_guarded_wide) >>
      metis_tac[])
  >- (rpt gen_tac >> rpt strip_tac >>
      irule (cj 2 body_sim_full_mutual_guarded_wide) >>
      metis_tac[])
  >- (rpt gen_tac >> rpt strip_tac >>
      irule (cj 3 body_sim_full_mutual_guarded_wide) >>
      metis_tac[])
  >- (rpt gen_tac >> rpt strip_tac >>
      irule (cj 4 body_sim_full_mutual_guarded_wide) >>
      metis_tac[])
  >- (rpt gen_tac >> rpt strip_tac >>
      irule (cj 5 body_sim_full_mutual_guarded_wide) >>
      metis_tac[])
  >- (rpt gen_tac >> rpt strip_tac >>
      irule (cj 6 body_sim_full_mutual_guarded_wide) >>
      metis_tac[])
  >- (rpt gen_tac >> rpt strip_tac >>
      irule (cj 7 body_sim_full_mutual_guarded_wide) >>
      metis_tac[])
  >- (rpt gen_tac >> rpt strip_tac >>
      irule (cj 9 body_sim_full_mutual_guarded_wide) >>
      metis_tac[])
  >- (rpt gen_tac >> rpt strip_tac >>
      irule (cj 10 body_sim_full_mutual_guarded_wide) >>
      metis_tac[])
QED


Theorem body_sim_header_post_equiv:
  cenv_module_pins_mods mods cenv /\
  module_body_inv mods src tops cenv cx ==>
  ((expr_post_mods H ctx func cenv cx e es sa sb s0 es' v op s <=>
    expr_post H ctx func cenv cx e es sa sb s0 es' v op s) /\
   (vv_post_mods H ctx func cenv cx e es sa sb s0 es' tv vv s <=>
    vv_post H ctx func cenv cx e es sa sb s0 es' tv vv s))
Proof
  strip_tac >>
  conj_tac
  >- irule expr_post_mods_wide
  >- (irule vv_post_mods_wide >> metis_tac[])
QED
