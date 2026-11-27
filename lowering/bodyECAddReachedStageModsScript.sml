(* Adapt the two actual linked operand landings to the ECAdd launch. *)
Theory bodyECAddReachedStageMods
Ancestors
  bodyECArithOperandsMods bodyECArithTailMods bodyECAddStageMods
  bodyECHeldPointMods bodyECAddSecondPointMods bodyECArithOperandReadyMods
  exprSimFullBundleProps exprLoweringProps bodyInvCodeProps bodyInvModuleProps
  abiBufferAllocationCode exprSimPrecompiles stateRelProj loweringStateRelDefs
  vyperStorageFootprint venomState words
Libs monadsyntax

(* Take the two boundaries directly from the producers, so the adapter cannot
   silently use a different cut or stage layout. *)
val operands = bodyECArithOperandsModsTheory.ec_arith_from_tail_mods;
val (ambient, _) = dest_imp (concl operands);
val ambient_parts = strip_conj ambient;
val (cuts, cut_rule) = strip_forall (List.last ambient_parts);
val (reached, _) = dest_imp cut_rule;
val staged = rand (concl bodyECArithTailModsTheory.ec_arith_tail_from_staging_mods);
val ambient_add = Term.subst [``bt:builtin`` |-> ``ECAdd``]
  (list_mk_conj (List.take (tl ambient_parts, length ambient_parts - 2)));
val reached_add = Term.subst [``bt:builtin`` |-> ``ECAdd``] reached;
val staged_add = Term.subst [``bt:builtin`` |-> ``ECAdd``,
  ``addr:256 word`` |-> ``6w:256 word``, ``an:256 word`` |-> ``128w:256 word``] staged;
val launch_add = ``?p q. ^staged_add /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 x t2 /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v2 y t2 /\
  eval_operand x t2 = SOME p /\ eval_operand y t2 = SOME q``;
val reached_to_launch_add = list_mk_forall (cuts, mk_imp (reached_add,launch_add));

Theorem ecadd_stage_from_reached_mods:
  ^ambient_add ==> ^reached_to_launch_add
Proof
  BETA_TAC >> simp_tac bool_ss [COND_CLAUSES] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac
    (SIMP_RULE bool_ss [] (Q.INST [`bt` |-> `ECAdd`] ec_arith_operand_ready_mods)) >>
  `post_value_type cenv e1 = expr_type e1` by
    (irule ecadd_operand_post_type >> fs[] >> metis_tac[]) >>
  `post_value_type cenv e2 = expr_type e2` by
    (irule ecadd_operand_post_type >> fs[] >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon es2.storage_trace) es2.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> valid_horizon _ _ H _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es1.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon es2.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
   expr_type e2 = ArrayT (BaseT (UintT 256)) (Fixed 2)` by simp[] >>
  drule_then assume_tac exprBodyPrePropsTheory.expr_body_pre_mods_inv >>
  drule_all_then (qx_choosel_then [`pv`,`pw`,`lp`] strip_assume_tac) ec_held_point_at_second_cut_mods >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
     expr_post_mods H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 y t2 /\
     expr_store_bound cx (post_value_type cenv e2) v2 y t2 /\
     ptr_val_ok cx (post_value_type cenv e2) v2 y G2 tn2 t2` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!K. valid_horizon _ _ K es2.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> asm_rewrite_tac[]) >>
  drule_all_then (qx_choosel_then [`qv`,`qw`,`lq`] strip_assume_tac) ecadd_second_point_at_cut_mods >>
  qpat_x_assum `x = Var pv` SUBST_ALL_TAC >>
  qpat_x_assum `y = Var qv` SUBST_ALL_TAC >>
  qpat_assum `expr_sim_full_code _ (s2,sb,shadow_s2,shadow_sb)`
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_code_def]) >>
  `(lo <> 0 ==> !z. cenv.ce_imm_alloca = SOME (Var z) ==> not_fresh_at s2 z)` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC local_ptrs_reserved_imm_base) >>
  qpat_assum `compile_ecadd_points _ _ s2 = _`
    (mp_then (Pos hd) mp_tac ecadd_stage_with_suffix_mods) >>
  disch_then (fn stage => qpat_assum `compile_ecadd_points _ _ shadow_s2 = _`
    (mp_then (Pos hd) mp_tac stage)) >>
  disch_then (fn stage =>
    qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> stmt_state_rel _ _ _ _ _ _ t2 /\ _`
      (mp_then (Pat `stmt_state_rel`) mp_tac stage)) >>
  disch_then (drule_all_then (qspec_then `PG` mp_tac)) >>
  disch_then (qx_choosel_then
    [`ib`,`ca`,`out_cut`,`ob`,`sm`,`shm`,`srcbuf`,`dst`,`gv`,`cv`,`bb`,`wi`,`wo`,`u`,`Gu`,`tnu`]
    strip_assume_tac) >>
  suspend "packet"
QED

Resume ecadd_stage_from_reached_mods[packet]:
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `es2.outcomes = SOME u.vs_outcomes` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ es2 u`
       (mp_tac o MATCH_MP stmt_state_rel_state_rel) >> simp[state_rel_def]) >>
  qpat_assum `ci_mono s2 sm` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `out_cut.cs_next_id < sb.cs_next_id` by
    (qpat_assum `compile_alloc_buffer 64 out_cut = _`
       (strip_assume_tac o MATCH_MP compile_alloc_buffer_code) >>
     drule_then strip_assume_tac computed_suffix_shape >> decide_tac) >>
  `w2n (128w:256 word) = 128` by simp[dimword_def] >>
  qexistsl_tac [`pw`,`qw`] >>
  reverse conj_tac >- asm_rewrite_tac[eval_operand_def] >>
  qexistsl_tac [`sm`,`res`,`out_cut`,`gv`,`cv`,`srcbuf`,`dst`,`wi`,`wo`,`bb`,`u`,`Gu`,`tnu`] >>
  asm_rewrite_tac[eval_operand_def,exprLoweringTheory.as_stack_val_def] >>
  conj_tac
  >- (qpat_x_assum `isPREFIX (emitted_insts sm sb) _` mp_tac >> asm_rewrite_tac[]) >>
  conj_tac
  >- (`ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops` by
        (drule_then SUBST1_TAC contract_inv_cenv_modules >> fs[bodyInvSplitTheory.module_body_inv_def]) >>
      qpat_assum `!src tops. ALOOKUP cenv.ce_modules src = SOME tops /\ _ ==> _`
        (qspecl_then [`cenv.ce_module`,`tops`] mp_tac) >>
      asm_rewrite_tac[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!K. valid_horizon _ _ K es2.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  asm_rewrite_tac[]
QED

Finalise ecadd_stage_from_reached_mods
