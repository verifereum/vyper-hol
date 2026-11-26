(* Install a widened copy at the selected subpath, not at the local root. *)
Theory bodyAssignLocalWidenInstallAtPathMods
Ancestors
  bodyAssignLocalStoreCutsMods bodyLocalTypedCopyPathMods bodyInvCodeProps
  exprSimHypsDefs stmtSimDeclTypedCode wideningZeroLayout vyperPlaceFrames
  bodyLocalCopyWritesMods bodyMemoryDefs bodyFullShared wordArgsPtr
  vyperStorageFootprint stmtSimDefs freshWrites arithmetic loweringStateRelDefs
  stmtLowering exprSimProps compileEnv bodyPtrDefs loweringPosts venomState
  fragGasOriginPtr typedMemoryCopy ptrDiscipline finite_map words
  bodyFullPostsMods bodyInvSplit exprLoweringProps bodyFullShadowBodyInv

Theorem assign_local_widen_install_at_path_mods:
  compile_assign_value cenv (Var xd) LocMemory (Var xs) F loc dty sty
    (type_memory_bytes cenv dty) sm = ((),sb) /\
  ~is_word_type dty /\ ~is_word_type sty /\ ~is_bytestring_type dty /\
  ~(dty = sty \/ tuple_memory_layout_eq dty sty) /\
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env ee /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME ptv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv dty = type_memory_size ptv /\
  value_has_type stv v /\ value_has_type ptv v /\ val_wf stv v /\ val_wf ptv v /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ alloca_history func s /\
  ~block_is_terminated sm /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  not_fresh_at sm xs /\ not_fresh_at sm xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn xd s (type_memory_size ptv) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size ptv < dimword (:256) /\
  (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (type_memory_size ptv = 0 \/ w2n dw + type_memory_size ptv <= s.vs_alloca_next) /\
  (loc = SOME LocMemory ==> expr_val_at cenv cx sty start sm ee v (Var xs) s) /\
  (loc <> SOME LocMemory /\ 0 < type_memory_size stv ==>
    w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size ptv <= w2n sw) /\
  lookup_scopes id ee.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\ lookup_var p s = SOME w /\
  not_fresh_at sm p /\ mem_path_offset entry.type path = SOME (k,ptv) /\
  well_formed_type_value entry.type /\ value_has_type entry.type entry.value /\
  w2n dw = w2n w + k /\ k + type_memory_size ptv <= cap /\ lo <= w2n dw /\
  write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm s /\ return_buf_sep d cenv ee s /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x b. not_fresh_at sa x /\ lookup_var x s0 = SOME b ==> lookup_var x s = SOME b) /\
  (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP s.vs_allocas aid = SOME a) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\ alloca_frame cenv es sa s0 cenv ee s /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee s /\ immutable_frame_mods func cenv cx ee s /\
     storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) ==>
  ?f Gf tf. !H. valid_horizon cx st0 H ff.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK f,Gf,tf) /\
    local_assign_normal_mods DF lo d lctx sb cenv cenv H ctx func cx
      (ff with gas_obs := []) f Gf tf s0 sa es G0 tn0 (INL ())
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    (drule contract_inv_acyclic_struct_metadata >> simp[]) >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,len). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       len = type_memory_size tv) fields)` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_sim_inv_mods_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `~block_is_terminated sb` by
    (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`)
       compile_assign_value_typed_open >> disch_then irule >> simp[]) >>
  (* Zero source size forces equal types, handled by the equal-layout route. *)
  `0 < type_memory_size stv` by
    (Cases_on `type_memory_size stv = 0`
     >- (drule_all type_widens_to_zero_layout >> strip_tac >> gvs[]) >>
     decide_tac) >>
  `type_memory_size stv < dimword (:256)` by
    (irule LESS_EQ_LESS_TRANS >> qexists_tac `w2n sw + type_memory_size stv` >>
     simp[LESS_EQ_ADD]) >>
  `local_region cenv ee.scopes s id (w2n w) cap` by
    (pure_rewrite_tac[local_region_def] >> qexistsl_tac [`entry`,`p`,`w`] >> simp[]) >>
  `loc = SOME LocMemory ==>
     expr_val_at cenv cx sty start sm ee v (Var xs) s /\
     ?b len. b <= w2n dw /\ w2n dw + type_memory_size ptv <= b + len /\
       ((?name. local_region cenv ee.scopes s name b len) \/
        ?aid. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len))` by
    (strip_tac >> conj_tac >- (first_x_assum irule >> simp[]) >>
     qexistsl_tac [`w2n w`,`cap`] >> conj_tac >- decide_tac >>
     conj_tac >- decide_tac >> disj1_tac >> qexists_tac `id` >> first_assum ACCEPT_TAC) >>
  `loc <> SOME LocMemory ==>
    w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size ptv <= w2n sw` by simp[] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` (drule_then (assume_tac o CONJUNCT1))) >>
  suspend "physical"
QED

Resume assign_local_widen_install_at_path_mods[physical]:
  drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`) local_typed_copy_path_mods >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (mp_tac o Q.INST [`explicit` |-> `explicit`,`PG` |-> `PG`,
     `cap` |-> `type_memory_size ptv`,`start` |-> `start`,
     `dtv` |-> `ptv`,`stv` |-> `stv`,`v` |-> `v`,`sw` |-> `sw`,`dw` |-> `dw`,
     `G` |-> `G`,`tn` |-> `tn`,`lo` |-> `lo`] o SPEC_ALL) >>
  impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  disch_then (qx_choosel_then [`u`,`sc`,`Gu`,`tu`,`f`,`Gf`,`tf`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "snapshot_frame"
QED

Resume assign_local_widen_install_at_path_mods[snapshot_frame]:
  `ff.storage_trace = ee.storage_trace` by
    (drule write_memory_place_frame >> disch_then strip_assume_tac >> simp[]) >>
  `lookup_var p u = SOME w` by
    (qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `p` mp_tac) >> simp[]) >>
  `!x w'. not_fresh_at sm x /\ lookup_var x s = SOME w' ==> lookup_var x u = SOME w'` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `return_buf_frame d cenv sc u` by
    (irule return_buf_frame_frame >> goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >> simp[]) >>
  `return_buf_sep d cenv ee u` by
    (irule return_buf_sep_transport >>
     reverse conj_tac >- (qexistsl_tac [`cenv`,`ee`,`s`] >> simp[]) >>
     rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     qpat_assum `return_buf_frame (SOME _) _ sm s`
       (strip_assume_tac o SIMP_RULE std_ss [return_buf_frame_def]) >>
     qpat_assum `return_buf_sep (SOME _) _ _ s`
       (assume_tac o CONJUNCT1 o SIMP_RULE std_ss [bodySimFullTheory.return_buf_sep_def]) >>
     simp[allocas_from_def] >> rpt strip_tac >>
     qpat_assum `!aid off len. FLOOKUP u.vs_allocas aid = SOME (off,len) ==> _`
       (drule_then strip_assume_tac)
     >- (qpat_assum `allocas_from _ s`
           (drule_then mp_tac o REWRITE_RULE [allocas_from_def]) >> simp[]) >>
     decide_tac) >>
  suspend "stage_ghost"
QED

Resume assign_local_widen_install_at_path_mods[stage_ghost]:
  (* Install against the store-prefix cut, then compose with the statement entry. *)
  `ghost_kept_at lo cenv ee sm G tn s Gu tu` by
    (pure_rewrite_tac[ghost_kept_at_def] >> rpt conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >> simp[])
     >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  `local_region cenv ee.scopes u id (w2n w) cap` by simp[] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  qexistsl_tac [`f`,`Gf`,`tf`] >> gen_tac >> disch_tac >> conj_tac
  >- (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `DF H` ACCEPT_TAC)) >>
  `valid_horizon cx st0 H ee.storage_trace` by
    (qpat_assum `ff.storage_trace = _` (once_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `stmt_state_rel H ctx func cenv cx ee u /\ immutable_frame_mods func cenv cx ee u /\
   ghost_inv_at_mods (DF H) lo d cenv cx ee Gu tu u` by
    (rpt conj_tac
     >- (qpat_assum `!h. stmt_state_rel h _ _ _ _ _ s ==> _` irule >> simp[])
     >- (qpat_assum `immutable_frame_mods _ _ _ _ s ==> _` irule >> simp[]) >>
     qpat_assum `!D d. ghost_inv_at_mods D _ d _ _ _ _ _ s ==> _` irule >> simp[]) >>
  suspend "install"
QED

Resume assign_local_widen_install_at_path_mods[install]:
  mp_tac (Q.INST [`D` |-> `DF H`, `s` |-> `u`, `sm` |-> `sc`, `t` |-> `f`,
    `G` |-> `Gu`, `tn` |-> `tu`, `bytes` |-> `type_memory_size ptv`,
    `sa` |-> `sm`, `s0` |-> `s`, `es` |-> `ee`, `G0` |-> `G`, `tn0` |-> `tn`]
    (SPEC_ALL (INST_TYPE [``:'a`` |-> ``:256``]
      bodyAssignLocalInstallModsTheory.assign_local_install_post_mods))) >>
  qpat_assum `w2n dw = _` (pure_rewrite_tac o single o SYM) >>
  impl_tac >-
    (conj_tac >-
       (strip_tac >> irule local_copy_immutable_frame_mods >>
        qexistsl_tac [`w2n w`,`type_memory_size ptv`,`cap`,`w2n dw`,`ee`,`id`,`u`,`sc`] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (simp[] >> NO_TAC) >>
     gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sc x ==> lookup_var x f = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  disch_then (qx_choose_then `ce` (map_every assume_tac o CONJUNCTS)) >>
  suspend "compose"
QED

Resume assign_local_widen_install_at_path_mods[compose]:
  qpat_x_assum `ce = cenv` SUBST_ALL_TAC >>
  `alloca_frame cenv es sa s0 cenv ff f` by
    (irule alloca_frame_trans >> qexistsl_tac [`cenv`,`ee`,`s`,`sm`] >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  simp[local_assign_normal_at_cut_mods, exprSimWordArgsTheory.stmt_state_rel_gas_obs,
       return_buf_sep_gas_obs] >>
  rpt conj_tac
  >- suspend "obs_immutable"
  >- suspend "obs_storage"
  >- suspend "obs_ghost"
  >- suspend "old_operands" >>
  suspend "protected_scratch"
QED

Resume assign_local_widen_install_at_path_mods[obs_immutable]:
  qpat_assum `immutable_frame_mods _ _ _ ff f` mp_tac >>
  simp_tac (srw_ss()) [immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
       loweringStateRelDefsTheory.immutables_rel_def] >>
  strip_tac >> rpt gen_tac >> rpt disch_tac >>
  qpat_assum `!src tops. ALOOKUP _ src = SOME tops ==> immutable_decl_sep _ _ _ _ _ _ /\ _`
    (drule_then (mp_tac o CONJUNCT2)) >> simp[]
QED
Resume assign_local_widen_install_at_path_mods[obs_storage]:
  mp_tac (Q.INST [`st` |-> `ff`, `st'` |-> `ff with gas_obs := []`,
    `regions` |-> `FST (H : (bool # 256 word # type_value) list # num list)`]
    (SPEC_ALL (INST_TYPE [``:'a`` |-> ``:256``] storage_well_formed_on_backends))) >> simp[]
QED
Resume assign_local_widen_install_at_path_mods[obs_ghost]:
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ ff _ _ f` mp_tac >>
  simp_tac (srw_ss()) [ghost_inv_at_mods_def] >> strip_tac >> first_assum ACCEPT_TAC
QED
Resume assign_local_widen_install_at_path_mods[old_operands]:
  rpt strip_tac >>
  qpat_assum `ghost_kept_at _ _ es _ _ _ _ _ _`
    (mp_tac o Q.SPEC `x` o CONJUNCT1 o REWRITE_RULE [ghost_kept_at_def]) >>
  qpat_assum `!x. not_fresh_at sm x ==> FLOOKUP Gf x = _ /\ _`
    (qspec_then `x` mp_tac) >> simp[]
QED
Resume assign_local_widen_install_at_path_mods[protected_scratch]:
  rpt strip_tac >>
  `i IN tn.t_mem` by
    (qpat_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = _ /\ _ ==> i IN tn.t_mem`
       (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
     impl_tac >-
       (simp[] >> qpat_assum `alloca_frame _ _ _ _ _ ee s`
          (mp_tac o Q.SPECL [`aid`,`off`,`sz`] o REWRITE_RULE [alloca_frame_def]) >>
        impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
        disch_then (ACCEPT_TAC o CONJUNCT2)) >>
     simp[]) >>
  qpat_assum `ghost_kept_at _ _ es _ _ _ _ _ _`
    (mp_tac o Q.SPECL [`aid`,`off`,`sz`,`i`] o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [ghost_kept_at_def]) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED

Finalise assign_local_widen_install_at_path_mods
