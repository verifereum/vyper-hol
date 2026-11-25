(* The scope pop and the optional exit jump of a linked If. *)
Theory bodyIfArmFinishMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit bodyFullShared
  bodyMemoryDefs bodyPtrDefs bodySimFull fragGasEmitCtrl fragGasOriginPtr
  stmtSimProps stmtSimDefs stmtFragPtr exprSimDefs exprLoweringProps
  loweringPosts loweringStateRelDefs compileEnv freshWrites allocaHistory
  ptrDiscipline emitHelperProps fragExec gasShadow
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  venomExecSemantics venomInst venomState finite_map list pair

Theorem if_pop_lookup[local]:
  cenv_top_ext cenv cb (sc :: rest) /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
  lookup_scopes n rest = SOME entry ==>
  lookup_scopes n (sc :: rest) = SOME entry /\
  FLOOKUP cb.ce_vars n = FLOOKUP cenv.ce_vars n
Proof
  strip_tac >>
  `n NOTIN FDOM sc` by (strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac >- simp[FLOOKUP_DEF, lookup_scopes_def] >>
  CCONTR_TAC >> fs[cenv_top_ext_def] >>
  qpat_x_assum `!n. FLOOKUP cb.ce_vars n <> _ ==> _` drule >> simp[]
QED

Theorem if_pop_ghost[local]:
  ghost_inv_at_mods D lo d cb cx (ee with scopes := sc :: ee.scopes) G tn u /\
  cenv_top_ext cenv cb (sc :: ee.scopes) /\
  (!n. n IN FDOM sc ==> lookup_scopes n ee.scopes = NONE) ==>
  ghost_inv_at_mods D lo d cenv cx ee G tn u
Proof
  strip_tac >>
  `cb.ce_modules = cenv.ce_modules /\ cb.ce_module_vars = cenv.ce_module_vars /\
   cb.ce_return_buf = cenv.ce_return_buf /\ cb.ce_return_pc = cenv.ce_return_pc /\
   cb.ce_imm_alloca = cenv.ce_imm_alloca` by
    fs[cenv_top_ext_def, compile_env_component_equality] >>
  fs[ghost_inv_at_mods_def, imm_section_dead_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all if_pop_lookup >> strip_tac >>
      qpat_x_assum `!name entry p sz. lookup_scopes _ (sc :: _) = _ /\ _ ==> _`
        (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >> simp[]) >>
  Cases_on `d` >- fs[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME ds) _ _ _ _` >> PairCases_on `ds` >>
  fs[return_buf_ptr_def]
QED

Theorem if_pop_local_region[local]:
  cenv_top_ext cenv cb (sc :: rest) /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
  local_region (cenv with ce_module := src) rest u n b sz ==>
  local_region (cb with ce_module := src) (sc :: rest) u n b sz
Proof
  simp[local_region_def] >> strip_tac >> drule_all if_pop_lookup >> strip_tac >>
  qexistsl_tac [`entry`, `p`] >> simp[]
QED

Theorem if_pop_immutable_frame[local]:
  immutable_frame_mods func cb cx (ee with scopes := sc :: ee.scopes) u /\
  cenv_top_ext cenv cb (sc :: ee.scopes) /\
  (!n. n IN FDOM sc ==> lookup_scopes n ee.scopes = NONE) ==>
  immutable_frame_mods func cenv cx ee u
Proof
  strip_tac >>
  `cb.ce_modules = cenv.ce_modules /\ cb.ce_module_vars = cenv.ce_module_vars /\
   cb.ce_module_var_type = cenv.ce_module_var_type /\ cb.ce_is_ctor = cenv.ce_is_ctor` by
    fs[cenv_top_ext_def, compile_env_component_equality] >>
  `!src n b sz. local_region (cenv with ce_module := src) ee.scopes u n b sz ==>
     local_region (cb with ce_module := src) (sc :: ee.scopes) u n b sz` by
    (rpt gen_tac >> strip_tac >> irule if_pop_local_region >> simp[] >>
     qexists_tac `cenv` >> simp[]) >>
  fs[immutable_frame_mods_def] >> conj_tac
  >- (qpat_x_assum `immutables_rel_mods _ _ _ _ _` mp_tac >>
      simp[immutables_rel_mods_def, immutables_rel_def]) >>
  fs[immutable_alloca_sep_mods_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >>
  simp[immutable_alloca_sep_def, immutable_decl_sep_alt] >>
  strip_tac >> conj_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE
   (rpt gen_tac >> strip_tac >> first_x_assum irule >> qexists_tac `id` >>
    first_x_assum irule >> simp[]))
QED

Theorem if_jump_immutable_frame[local]:
  immutable_frame_mods func cenv cx ee (jump_to lbl u) <=>
  immutable_frame_mods func cenv cx ee u
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def, immutables_rel_def, immutable_alloca_sep_def,
       jump_to_def, local_region_def, lookup_var_def]
QED

Theorem if_jump_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx ee G tn (jump_to lbl u) <=>
  ghost_inv_at_mods D lo d cenv cx ee G tn u
Proof
  simp[ghost_inv_at_mods_def, jump_to_def, ptr_covers_def, stor_taint_ok_at_def,
       lookup_var_def, allocas_from_def] >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  qmatch_goalsub_rename_tac `return_buf_ptr (SOME ds) _ _ _ _` >>
  PairCases_on `ds` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

(* The condition supplies its frame at its own horizon. The successful
   forced read is used to justify the starting relation at that horizon. *)
Theorem if_finish_condition_frame[local]:
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL (BoolV b), mid) /\
  storage_trace_domain cx st0 mid.storage_trace /\ local_ptrs_reserved cenv sa /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       expr_post_mods H ctx func cenv cx e es sa cond s0 mid (BoolV b) op t) ==>
  alloca_frame cenv es sa s0 cenv (mid with scopes := FEMPTY :: mid.scopes) (jump_to lbl t) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x (jump_to lbl t) = SOME w) /\
  (!aid ba. FLOOKUP s0.vs_allocas aid = SOME ba ==> FLOOKUP (jump_to lbl t).vs_allocas aid = SOME ba)
Proof
  strip_tac >> qabbrev_tac `H = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H mid.storage_trace` by fs[storage_trace_domain_def, Abbr `H`] >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 H es.storage_trace` by (drule_all valid_horizon_frame >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` drule >> simp[]) >>
  `expr_post_mods H ctx func cenv cx e es sa cond s0 mid (BoolV b) op t` by
    (first_assum irule >> simp[]) >>
  fs[expr_post_mods_def] >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by (drule eval_read_preserves_scopes_dom >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv mid t` by (drule_all expr_post_alloca_frame >> simp[]) >>
  conj_tac
  >- (irule alloca_frame_same_state >>
      qexists_tac `t` >> fs[alloca_frame_def, local_region_def, lookup_scopes_def, jump_to_def] >>
      first_assum ACCEPT_TAC) >>
  fs[expr_post_def, lookup_var_def, jump_to_def] >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem if_storage_scope[local]:
  storage_well_formed_on cx (ee with scopes := rest) r <=> storage_well_formed_on cx ee r
Proof
  irule storage_well_formed_on_backends >> simp[]
QED

(* The suffix endpoint does not depend on the choice of valid horizon.
   A successful target landing with Break/Continue has no exit jump. *)
Theorem if_arm_finish_mods:
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL (BoolV b), mid) /\
  storage_trace_domain cx st0 mid.storage_trace /\ local_ptrs_reserved cenv sa /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       expr_post_mods H ctx func cenv cx e es sa cond s0 mid (BoolV b) op t /\
       s0.vs_alloca_next <= t.vs_alloca_next /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) /\
  sa.cs_next_var <= entry.cs_next_var /\ sa.cs_next_id <= entry.cs_next_id /\
  last.cs_next_var <= sb.cs_next_var /\
  (~block_is_terminated last ==>
   emit_inst JMP [Label xl] [] last = ((), after) /\ fn_has_code last after func /\
   sb.cs_current_bb = xl /\ sb.cs_current_insts = []) ==>
  !res ee G tn u.
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       ?sc. (\es' . ?cb.
          stmt_lands lctx last res u /\ ~u.vs_halted /\
          (res = INL () ==> ~block_is_terminated last /\ cb = cenvb) /\
          cenv_top_ext cenv cb es'.scopes /\
          stmt_state_rel H ctx func cb cx es' u /\
          immutable_frame_mods func cb cx es' u /\
          storage_well_formed_on cx es' (FST H) /\
          return_buf_frame d cb last u /\ alloca_history func u /\
          return_buf_sep d cb es' u /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          (jump_to lbl t).vs_alloca_next <= u.vs_alloca_next /\
          ghost_inv_at_mods (DF H) lo d cb cx es' G tn u /\
          (!x w. not_fresh_at entry x /\ lookup_var x (jump_to lbl t) = SOME w ==>
                 lookup_var x u = SOME w) /\
          (!aid ba. FLOOKUP (jump_to lbl t).vs_allocas aid = SOME ba ==>
                    FLOOKUP u.vs_allocas aid = SOME ba) /\
          (!x. not_fresh_at entry x ==>
               FLOOKUP G x = FLOOKUP G1 x /\ op_taint tn (Var x) = op_taint tn1 (Var x)) /\
          alloca_frame cenv (mid with scopes := FEMPTY :: mid.scopes) entry (jump_to lbl t) cb es' u /\
          (!aid off sz i.
             FLOOKUP (jump_to lbl t).vs_allocas aid = SOME (off, sz) /\ aid < entry.cs_next_id /\
             (!n ba sz'. local_region cenv (mid with scopes := FEMPTY :: mid.scopes).scopes
                           (jump_to lbl t) n ba sz' ==> off + sz <= ba \/ ba + sz' <= off) /\
             off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn1.t_mem))
         (ee with scopes := sc :: ee.scopes) /\
       !n. n IN FDOM sc ==> lookup_scopes n ee.scopes = NONE) ==>
    ?v G' tn'. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (u,G,tn) [] (OK v,G',tn') /\
      ?cf. stmt_lands lctx sb res v /\ ~v.vs_halted /\
          (res = INL () ==> ~block_is_terminated sb /\ cf = cenv) /\
          cenv_top_ext cenv cf ee.scopes /\
          stmt_state_rel H ctx func cf cx ee v /\
          immutable_frame_mods func cf cx ee v /\
          storage_well_formed_on cx ee (FST H) /\
          return_buf_frame d cf sb v /\ alloca_history func v /\
          return_buf_sep d cf ee v /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\
          s0.vs_alloca_next <= v.vs_alloca_next /\
          ghost_inv_at_mods (DF H) lo d cf cx ee G' tn' v /\
          (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                 lookup_var x v = SOME w) /\
          (!aid ba. FLOOKUP s0.vs_allocas aid = SOME ba ==>
                    FLOOKUP v.vs_allocas aid = SOME ba) /\
          (!x. not_fresh_at sa x ==>
               FLOOKUP G' x = FLOOKUP G0 x /\ op_taint tn' (Var x) = op_taint tn0 (Var x)) /\
          alloca_frame cenv es sa s0 cf ee v /\
          (!aid off sz i.
             FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
             (!n ba sz'. local_region cenv es.scopes s0 n ba sz' ==>
                         off + sz <= ba \/ ba + sz' <= off) /\
             off <= i /\ i < off + sz /\ i IN tn'.t_mem ==> i IN tn0.t_mem)
Proof
  strip_tac >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       expr_post_mods H ctx func cenv cx e es sa cond s0 mid (BoolV b) op t` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule_all if_finish_condition_frame >> disch_then (qspec_then `lbl` strip_assume_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  simp[] >> strip_tac >>
  qx_genl_tac [`res`, `ee`, `G`, `tn`, `u`] >> strip_tac >>
  qexistsl_tac [`if res = INL () then jump_to xl u else u`, `G`, `tn`] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` drule >>
  simp[] >> disch_then (qx_choose_then `sc` strip_assume_tac) >>
  `stmt_state_rel H ctx func cenv cx ee u` by
    (qpat_assum `stmt_state_rel H ctx func cb cx _ u`
       (mp_then Any mp_tac stmt_state_rel_pop_top_ext) >>
     disch_then (qspecl_then [`cenv`, `sc`, `ee.scopes`] mp_tac) >> simp[]) >>
  `immutable_frame_mods func cenv cx ee u` by (drule_all if_pop_immutable_frame >> simp[]) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx ee G tn u` by (drule_all if_pop_ghost >> simp[]) >>
  `storage_well_formed_on cx ee (FST H)` by fs[if_storage_scope] >>
  `return_buf_sep d cenv ee u` by (drule_all return_buf_sep_pop >> simp[]) >>
  `return_buf_frame d cenv sb u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cb`, `u`, `last`] >>
     simp[] >> drule cenv_top_ext_return_buf >> simp[]) >>
  `alloca_frame cenv (mid with scopes := FEMPTY :: mid.scopes) entry (jump_to lbl t) cenv ee u` by
    (qpat_assum `alloca_frame _ _ entry _ cb _ u` (mp_then Any mp_tac alloca_frame_pop) >>
     disch_then (qspecl_then [`sc`, `ee.scopes`, `cenv`] mp_tac) >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv ee u` by (drule_all alloca_frame_trans >> simp[]) >>
  `!aid off sz i.
     FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
     (!n ba sz'. local_region cenv es.scopes s0 n ba sz' ==>
                off + sz <= ba \/ ba + sz' <= off) /\
     off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem` by
    (match_mp_tac (Q.INST
       [`c1` |-> `cenv`, `e1` |-> `mid with scopes := FEMPTY :: mid.scopes`,
        `s1` |-> `jump_to lbl t`, `sa1` |-> `entry`, `tn1` |-> `tn1`]
       alloca_taint_kept_trans) >>
     fs[ghost_kept_at_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w` by
    (rpt strip_tac >> `not_fresh_at entry x` by (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     qpat_x_assum `!x w. not_fresh_at entry x /\ _ ==> _` irule >> simp[]) >>
  `!aid ba. FLOOKUP s0.vs_allocas aid = SOME ba ==> FLOOKUP u.vs_allocas aid = SOME ba` by
    (rpt strip_tac >> qpat_x_assum `!aid ba. FLOOKUP (jump_to lbl t).vs_allocas aid = _ ==> _`
       irule >> simp[]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by fs[jump_to_def] >>
  `!x. not_fresh_at sa x ==>
       FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at entry x` by (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     fs[ghost_kept_at_def]) >>
  Cases_on `res = INL ()`
  >- (gvs[stmt_lands_def] >>
      `allocas_from lo u` by fs[ghost_inv_at_mods_def] >>
      conj_tac
      >- (irule emit_jmp_origin_ptr >> simp[] >> qexistsl_tac [`last`, `after`] >> simp[]) >>
      `alloca_history func (jump_to sb.cs_current_bb u)` by
        (irule alloca_history_jump >> simp[jump_to_def] >> qexists_tac `u` >> simp[]) >>
      `alloca_frame cenv es sa s0 cenv ee (jump_to sb.cs_current_bb u)` by
        (irule alloca_frame_same_state >> qexists_tac `u` >> simp[jump_to_def]) >>
      `(allocas_below_fmp (jump_to sb.cs_current_bb u) <=> allocas_below_fmp u)` by
        simp[allocas_below_fmp_def, jump_to_def] >>
      simp[stmt_lands_def, stmt_state_rel_jump_to, if_jump_immutable_frame, if_jump_ghost,
           block_is_terminated_def, return_buf_frame_jump_to, return_buf_sep_jump, cenv_top_ext_refl] >>
      fs[jump_to_def, lookup_var_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `stmt_lands lctx sb res u` by
    (qpat_x_assum `stmt_lands _ _ _ _` mp_tac >> simp[stmt_lands_def]) >>
  asm_simp_tac std_ss [] >>
  conj_tac >- (irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  qexists_tac `cenv` >> simp[cenv_top_ext_refl] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
