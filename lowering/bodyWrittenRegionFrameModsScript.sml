(* A constructor write changes one qualified immutable, within its layout. *)
Theory bodyWrittenRegionFrameMods
Ancestors
  bodyFullPostsMods bodyInvSplit bodyInvCodeProps immutableRegionFrameProps
  immutableRegionWriteProps exprLoweringProps loweringSlice loweringStateRelDefs
  valueEncodingProps valueEncodingProofs abiDecodeStaticProps bodyPtrDefs
  compileEnv vyperTypeInitialState vyperState venomState finite_map pred_set arithmetic

Theorem updated_immutable_lookup[local]:
  FLOOKUP (get_source_immutables src (update_immutable owner id tv v imms)) name =
    if (src,name) = (owner,id) then SOME (tv,v)
    else FLOOKUP (get_source_immutables src imms) name
Proof
  Cases_on `src = owner`
  >- (Cases_on `name = id` >>
      simp[update_immutable_def, get_source_immutables_set_same, FLOOKUP_UPDATE]) >>
  simp[update_immutable_preserves_other_source]
QED

Theorem written_region_alloca_sep[local]:
  immutable_alloca_sep_mods func cenv cx es s /\ cenv.ce_is_ctor /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  ALOOKUP ee.immutables cx.txn.target = SOME new_imms /\
  (!src name rt v. FLOOKUP (get_source_immutables src new_imms) name = SOME (rt,v) ==>
                   ?old. FLOOKUP (get_source_immutables src imms) name = SOME (rt,old)) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (!name b sz. local_region cenv ee.scopes t name b sz ==>
               local_region cenv es.scopes s name b sz) ==>
  immutable_alloca_sep_mods func cenv cx ee t
Proof
  strip_tac >>
  qpat_assum `immutable_alloca_sep_mods _ _ _ _ _`
    (assume_tac o REWRITE_RULE [immutable_alloca_sep_mods_def]) >>
  rw[immutable_alloca_sep_mods_def] >>
  qpat_x_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss())
      [immutable_alloca_sep_def, immutable_decl_sep_alt])) >>
  simp[immutable_alloca_sep_def, immutable_decl_sep_alt] >>
  `!src name b sz. local_region (cenv with ce_module := src) ee.scopes t name b sz ==>
                    local_region (cenv with ce_module := src) es.scopes s name b sz` by
    fs[local_region_def] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!src name rt v. _ ==> ?old. _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `cenv.ce_is_ctor ==> !name tv v off. _ ==> _`
    (mp_tac o UNDISCH) >>
  simp[] >> disch_then (drule_all_then strip_assume_tac) >>
  simp[] >> metis_tac[]
QED

Theorem written_region_other_value[local]:
  immutable_value_admissible tv v /\
  val_in_memory tv v at mem /\
  immutable_value_bytes_rel tv v (mem_bytes_at at (type_memory_size tv) mem) /\
  regions_disjoint off span at (type_memory_size tv) /\
  off <= dest /\ dest + bytes <= off + span /\
  mem_agree_outside {j | dest <= j /\ j < dest + bytes} mem mem' ==>
  val_in_memory tv v at mem' /\
  immutable_value_bytes_rel tv v (mem_bytes_at at (type_memory_size tv) mem')
Proof
  strip_tac >>
  `mem_bytes_at at (type_memory_size tv) mem =
   mem_bytes_at at (type_memory_size tv) mem'` by
    (irule mem_bytes_at_bytewise >> rpt strip_tac >>
     qpat_assum `mem_agree_outside _ _ _`
       (irule o REWRITE_RULE [mem_agree_outside_def]) >>
     fs[regions_disjoint_def] >> decide_tac) >>
  `val_wf tv v` by metis_tac[immutable_admissible_val_wf] >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  irule val_in_memory_mem_agree >> simp[] >>
  qexistsl_tac [`type_memory_size tv`, `mem`] >> simp[]
QED

Theorem written_region_values[local]:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  cenv.ce_is_ctor /\ dead_lo_ok_mods H D lo cenv cx /\
  immutables_rel_mods cenv cx.txn.target cenv.ce_is_ctor es s /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  ALOOKUP ee.immutables cx.txn.target = SOME (update_immutable owner id tv v imms) /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  immutable_region_mods mods owner id off (type_memory_size tv) /\
  off <= dest /\ dest + bytes <= off + type_memory_size tv /\
  mem_agree_outside {j | dest <= j /\ j < dest + bytes} s.vs_memory t.vs_memory /\
  immutable_value_admissible tv v /\ val_in_memory tv v off t.vs_memory /\
  immutable_value_bytes_rel tv v (mem_bytes_at off (type_memory_size tv) t.vs_memory) ==>
  immutables_rel_mods cenv cx.txn.target cenv.ce_is_ctor ee t
Proof
  strip_tac >>
  `!src name at rt.
     (src,name) <> (owner,id) /\
     immutable_region_mods mods src name at (type_memory_size rt) ==>
     regions_disjoint off (type_memory_size tv) at (type_memory_size rt)` by
    (drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
       contract_inv_immutable_section_layout >> metis_tac[]) >>
  qpat_x_assum `immutables_rel_mods _ _ _ _ _`
    (assume_tac o REWRITE_RULE [immutables_rel_mods_def]) >>
  simp[immutables_rel_mods_def, immutables_rel_def] >>
  qx_genl_tac [`src`,`tops`] >> disch_tac >>
  qx_genl_tac [`name`,`rt`,`old`,`at`] >> strip_tac >>
  qpat_x_assum `FLOOKUP (get_source_immutables _ (update_immutable _ _ _ _ _)) _ = _`
    (mp_tac o REWRITE_RULE [updated_immutable_lookup]) >>
  Cases_on `(src,name) = (owner,id)`
  >- (gvs[] >> metis_tac[optionTheory.SOME_11, compileEnvTheory.var_location_11]) >>
  asm_rewrite_tac[] >> strip_tac >>
  `immutable_region_mods mods src name at (type_memory_size rt)` by
    (drule_all_then strip_assume_tac immutable_region_value_layout_mods >> simp[]) >>
  `regions_disjoint off (type_memory_size tv) at (type_memory_size rt)` by
    (first_x_assum irule >> qexistsl_tac [`name`,`src`] >> simp[]) >>
  `immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es s` by
    (qpat_assum `!src tops. _ ==> immutables_rel _ _ _ _ _ _`
       (qspecl_then [`src`,`tops`] mp_tac) >> simp[]) >>
  qpat_x_assum `immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es s`
    (qspecl_then [`name`,`rt`,`old`,`at`] mp_tac o
      CONV_RULE (DEPTH_CONV BETA_CONV) o REWRITE_RULE [immutables_rel_def, LET_THM]) >>
  simp[] >> strip_tac >>
  irule written_region_other_value >> simp[] >>
  qexistsl_tac [`bytes`,`dest`,`s.vs_memory`,`off`,`type_memory_size tv`] >>
  simp[] >> metis_tac[ADD_COMM]
QED

(* The write window can be a strict subrange of the root. Deadness is
   rechecked over the whole root, since a changed length word can change
   which bytes of that root are live even outside the write window. *)
Theorem written_region_frame_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  cenv.ce_is_ctor /\ dead_lo_ok_mods H D lo cenv cx /\
  immutable_frame_mods func cenv cx es s /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (tv,old) /\
  ALOOKUP ee.immutables cx.txn.target = SOME (update_immutable owner id tv v imms) /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  off <= dest /\ dest + bytes <= off + type_memory_size tv /\
  mem_agree_outside {j | dest <= j /\ j < dest + bytes} s.vs_memory t.vs_memory /\
  immutable_value_admissible tv v /\ val_in_memory tv v off t.vs_memory /\
  immutable_value_bytes_rel tv v (mem_bytes_at off (type_memory_size tv) t.vs_memory) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (!name b sz. local_region cenv ee.scopes t name b sz ==>
               local_region cenv es.scopes s name b sz) /\
  (!j. j < lo /\ j IN M1 ==> imm_section_dead_mods cenv (mem_bytes_at 0 lo s.vs_memory) j) /\
  (!j. j < lo /\ ~(off <= j /\ j < off + type_memory_size tv) /\
       j IN M2 ==> j IN M1) /\
  (!j. off <= j /\ j < off + type_memory_size tv /\ j IN M2 ==>
       mem_dead_bytes (mem_bytes_at 0 lo t.vs_memory) off tv j) ==>
  immutable_frame_mods func cenv cx ee t /\
  (!j. j < lo /\ j IN M2 ==> imm_section_dead_mods cenv (mem_bytes_at 0 lo t.vs_memory) j)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac immutable_region_value_layout_mods >>
  qpat_x_assum `immutable_frame_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def]) >>
  conj_tac
  >- (rewrite_tac[immutable_frame_mods_def] >> conj_tac
      >- drule_all_then ACCEPT_TAC written_region_values >>
      irule written_region_alloca_sep >> simp[] >>
      qexistsl_tac [`es`,`imms`,`s`] >>
      simp[updated_immutable_lookup] >>
      rpt gen_tac >> IF_CASES_TAC >> gvs[] >> metis_tac[]) >>
  `!j. j < lo /\ ~(off <= j /\ j < off + type_memory_size tv) ==>
       EL j (mem_bytes_at 0 lo t.vs_memory) = EL j (mem_bytes_at 0 lo s.vs_memory)` by
    (rpt strip_tac >>
     `mem_bytes_at j 1 s.vs_memory = mem_bytes_at j 1 t.vs_memory` by
       (qpat_assum `mem_agree_outside _ _ _`
          (irule o REWRITE_RULE [mem_agree_outside_def]) >>
        simp[] >> decide_tac) >>
     pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]) >>
  match_mp_tac (GEN_ALL (SIMP_RULE (srw_ss()) [LENGTH_mem_bytes_at]
    (Q.INST [`sec1` |-> `mem_bytes_at 0 lo s.vs_memory`,
             `sec2` |-> `mem_bytes_at 0 lo t.vs_memory`] immutable_section_replace_mods))) >>
  goal_assum (drule_at (Pat `contract_inv _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `immutable_region_mods _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP env.bare_globals _ = _`)) >>
  qexistsl_tac [`s`,`M1`] >>
  fs[DE_MORGAN_THM] >> conj_tac >> first_assum ACCEPT_TAC
QED
