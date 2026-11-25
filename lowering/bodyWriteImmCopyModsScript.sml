(* Restore the linked immutable region after a staged constructor copy. *)
Theory bodyWriteImmCopyMods
Ancestors
  bodyWrittenRegionFrameMods immutableDeployAssignMemoryFrame
  immutableRegionWriteProps immutableRegionDeadProps
  bodyPtrBytestringBuiltinsWindowGhost valueTypingMemoryProps
  abiCanonicalHeadSize valueEncodingDefs valueEncodingProps valueEncodingProofs
  exprSimProps exprSimHypsDefs bodyInvCodeProps bodyFullShadowBodyInv
  loweringSlice loweringStateRelDefs compileEnv vyperState venomState
  abiDecodeStaticProps bodyPtrDefs bodyInvSplit ctorDeployDeadSection
  bodyFullPostsMods immutableRegionFrameProps immutableRegionTypingProps
  bodyFullImmutablePathStore immutableBytestringPath immutableWordStorePath
  immutableAssignEmpty vyperTypeDefaults calldataTypedRobustPtr
  bodyMemoryDefs bodyFullShared bodySimFull gasOutcomeFullPostMods
  exprLoweringProps immutableDeployAssignStateFrame stateRelProj
  vyperPlaceFrames bodyImmutableAugAssignExec stmtSimDefs freshWrites
  ptrDiscipline vyperTyping alist finite_map pred_set arithmetic words venomMemProps

Theorem copy_outside_slice[local]:
  mem_agree_outside {j | dest <= j /\ j < dest + bytes} m m' /\
  (b + n <= dest \/ dest + bytes <= b) ==>
  mem_bytes_at b n m' = mem_bytes_at b n m
Proof
  strip_tac >> sym_tac >> irule mem_bytes_at_bytewise >> rpt strip_tac >>
  qpat_assum `mem_agree_outside _ _ _`
    (irule o REWRITE_RULE [mem_agree_outside_def]) >>
  simp[] >> decide_tac
QED

Theorem immutable_copy_path_representation[local]:
  well_formed_type_value itv /\ value_has_type itv old /\
  value_has_type ptv v /\ mem_path_offset itv path = SOME (k,ptv) /\
  assign_subscripts itv old path (Replace v) = INL new /\
  val_in_memory itv old off m /\
  (!m0. mem_agree_outside dirty m' m0 ==> val_in_memory ptv v (off+k) m0) /\
  mem_agree_outside {j | off+k <= j /\ j < off+k+type_memory_size ptv} m m' ==>
  immutable_value_admissible itv new /\ val_in_memory itv new off m' /\
  immutable_value_bytes_rel itv new (mem_bytes_at off (type_memory_size itv) m')
Proof
  strip_tac >>
  `val_in_memory ptv v (off+k) m'` by
    (first_assum irule >> simp[mem_agree_outside_def]) >>
  irule immutable_value_bytes_rel_replace_path >>
  simp[] >> qexistsl [`k`,`m`,`old`,`path`,`ptv`,`v`] >>
  `k + off = off + k` by decide_tac >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  drule copy_outside_slice >> disch_then (irule o SPEC_ALL) >> simp[]
QED

Theorem copy_root_dead_at[local]:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  immutable_region_mods mods owner id off (type_memory_size itv) /\
  FLOOKUP env.bare_globals (owner,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\
  off <= j /\ j < off + type_memory_size itv /\
  imm_section_dead_mods cenv sec j ==>
  mem_dead_bytes sec off itv j
Proof
  strip_tac >>
  drule_all_then (fn th => fs[th]) imm_section_dead_mods_regions >>
  rename1 `immutable_region_mods mods src name at (type_memory_size tv)` >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  Cases_on `(src,name) = (owner,id)`
  >- (`at = off` by metis_tac[optionTheory.SOME_11, compileEnvTheory.var_location_11] >>
      gvs[]) >>
  `regions_disjoint off (type_memory_size itv) at (type_memory_size tv)` by metis_tac[] >>
  drule_then strip_assume_tac (cj 1 mem_dead_bytes_range) >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem copy_bounded_slice[local]:
  b + n <= lo ==>
  mem_bytes_at b n (mem_bytes_at 0 lo m) = mem_bytes_at b n m
Proof
  simp[valueEncodingDefsTheory.mem_bytes_at_bounded,
       abiCanonicalHeadSizeTheory.mem_bytes_at_window]
QED

Theorem copy_path_dirty_dead[local]:
  well_formed_type_value itv /\ value_has_type itv old /\ value_has_type ptv v /\
  mem_path_offset itv path = SOME (k,ptv) /\
  assign_subscripts itv old path (Replace v) = INL new /\
  val_in_memory itv old off m /\ off + type_memory_size itv <= lo /\
  (!m0. mem_agree_outside M2 m' m0 ==> val_in_memory ptv v (off+k) m0) /\
  mem_agree_outside {j | off+k <= j /\ j < off+k+type_memory_size ptv} m m' /\
  (!j. off <= j /\ j < off + type_memory_size itv /\
       (j < off+k \/ off+k+type_memory_size ptv <= j) /\ j IN M2 ==>
       mem_dead_bytes (mem_bytes_at 0 lo m) off itv j) ==>
  !j. off <= j /\ j < off + type_memory_size itv /\ j IN M2 ==>
    mem_dead_bytes (mem_bytes_at 0 lo m') off itv j
Proof
  strip_tac >> drule_then strip_assume_tac mem_path_offset_sound >>
  `off+k+type_memory_size ptv <= lo` by decide_tac >>
  `val_in_memory itv old off (mem_bytes_at 0 lo m)` by
    (irule val_in_memory_mem_agree >> simp[value_has_type_memory_wf] >>
     qexistsl [`type_memory_size itv`,`m`] >>
     simp[val_footprint_le,value_has_type_memory_wf,copy_bounded_slice]) >>
  `!m0. mem_agree_outside M2 (mem_bytes_at 0 lo m') m0 ==>
        val_in_memory ptv v (off+k) m0` by
    (match_mp_tac (GEN_ALL robust_val_in_memory_window_transport) >>
     qexistsl [`m'`,`type_memory_size ptv`,`M2`] >>
     simp[val_footprint_le,value_has_type_memory_wf,copy_bounded_slice]) >>
  `!j. off <= j /\ j < off + type_memory_size itv /\
       (j < off+k \/ off+k+type_memory_size ptv <= j) ==>
       EL j (mem_bytes_at 0 lo m') = EL j (mem_bytes_at 0 lo m)` by
    (rpt strip_tac >>
     `mem_bytes_at j 1 m' = mem_bytes_at j 1 m` by
       (irule copy_outside_slice >> qexistsl [`type_memory_size ptv`,`off+k`] >>
        simp[] >> decide_tac) >>
     pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]) >>
  match_mp_tac (GEN_ALL immutable_replace_path_dirty_dead) >>
  qexistsl [`v`,`mem_bytes_at 0 lo m`,`ptv`,`path`,`old`,`new`,`k`] >>
  `k + off = off + k /\ k + (off + type_memory_size ptv) =
     off + k + type_memory_size ptv` by decide_tac >>
  pure_asm_rewrite_tac[LENGTH_mem_bytes_at] >>
  simp[NoAsms] >> rpt strip_tac >> first_x_assum irule >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem immutable_copy_linked_frame[local]:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  cenv.ce_is_ctor /\ dead_lo_ok_mods H D lo cenv cx /\
  immutable_frame_mods func cenv cx es s /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,old) /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  value_has_type itv old /\ value_has_type ptv v /\
  mem_path_offset itv path = SOME (k,ptv) /\
  write_place cx (ImmutablePlace owner id path) v es = (INL (),fin) /\
  (!m. mem_agree_outside M2 t.vs_memory m ==> val_in_memory ptv v (off+k) m) /\
  mem_agree_outside {j | off+k <= j /\ j < off+k+type_memory_size ptv}
    s.vs_memory t.vs_memory /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (!name b sz. local_region cenv fin.scopes t name b sz ==>
               local_region cenv es.scopes s name b sz) /\
  (!j. j < lo /\ j IN M1 ==> imm_section_dead_mods cenv (mem_bytes_at 0 lo s.vs_memory) j) /\
  (!j. ~(off+k <= j /\ j < off+k+type_memory_size ptv) /\ j IN M2 ==> j IN M1) ==>
  immutable_frame_mods func cenv cx fin t /\
  (!j. j < lo /\ j IN M2 ==> imm_section_dead_mods cenv (mem_bytes_at 0 lo t.vs_memory) j)
Proof
  strip_tac >> drule_all_then strip_assume_tac immutable_region_value_layout_mods >>
  drule_all_then strip_assume_tac immutable_path_write_source >>
  `ALOOKUP fin.immutables cx.txn.target = SOME (update_immutable owner id itv new imms)` by simp[] >>
  `val_in_memory itv old off s.vs_memory` by
    (drule_then assume_tac contract_inv_cenv_modules >>
     qpat_assum `immutable_region_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [immutable_region_mods_def]) >>
     qpat_assum `immutable_frame_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def,immutables_rel_mods_def]) >>
     `immutables_rel cenv cx.txn.target owner cenv.ce_is_ctor es s` by
       (first_x_assum irule >> qexists_tac `tops` >> simp[]) >>
     qpat_x_assum `immutables_rel _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [immutables_rel_def,LET_THM]) >>
     simp[] >> disch_then (qspecl_then [`id`,`itv`,`old`,`off`] mp_tac) >> simp[]) >>
  drule_all_then strip_assume_tac immutable_copy_path_representation >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `!j. off <= j /\ j < off+type_memory_size itv /\ j IN M2 ==>
       mem_dead_bytes (mem_bytes_at 0 lo t.vs_memory) off itv j` by
    (match_mp_tac (GEN_ALL copy_path_dirty_dead) >>
     qexistsl [`v`,`ptv`,`path`,`old`,`new`,`s.vs_memory`,`k`] >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     `j < lo` by decide_tac >>
     `j IN M1` by (first_x_assum irule >> asm_rewrite_tac[] >> decide_tac) >>
     `imm_section_dead_mods cenv (mem_bytes_at 0 lo s.vs_memory) j` by
       (first_x_assum irule >> asm_rewrite_tac[]) >>
     drule_all_then ACCEPT_TAC copy_root_dead_at) >>
  mp_tac (Q.INST [`tv` |-> `itv`,`v` |-> `new`,
    `dest` |-> `off+k`,`bytes` |-> `type_memory_size ptv`,
    `ee` |-> `fin`,`M1` |-> `M1`,`M2` |-> `M2`] written_region_frame_mods) >>
  impl_tac >- (asm_rewrite_tac[] >> conj_tac >- decide_tac >>
    conj_tac >- decide_tac >> rpt strip_tac >>
    first_x_assum irule >> asm_rewrite_tac[] >> decide_tac) >>
  disch_then ACCEPT_TAC
QED

(* The physical copy theorem supplies all disjoint slices, including the
   one-byte slices needed by the linked immutable region rule. *)
Theorem copy_store_window[local]:
  immutable_path_store_post (lo,explicit,ctx,func,PG) dest ptv v
    sa sb (s,G,tn) (t,G',tn') ==>
  mem_agree_outside {j | dest <= j /\ j < dest + type_memory_size ptv}
    s.vs_memory t.vs_memory
Proof
  simp[immutable_path_store_post_def,mem_agree_outside_def] >>
  strip_tac >> gen_tac >> strip_tac >> sym_tac >>
  first_x_assum irule >> fs[regions_disjoint_def] >> decide_tac
QED

Theorem copy_store_locals_disjoint[local]:
  contract_inv mods exps ctx cenv cx /\
  immutable_frame_mods func cenv cx es s /\ cenv.ce_is_ctor /\
  immutable_region_mods mods owner id off (type_memory_size itv) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,old) /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  mem_path_offset itv path = SOME (k,ptv) ==>
  !name b n. local_region cenv es.scopes s name b n ==>
    regions_disjoint b n (off+k) (type_memory_size ptv)
Proof
  strip_tac >> drule_then assume_tac contract_inv_cenv_modules >>
  fs[immutable_region_mods_def] >>
  `immutable_alloca_sep func (cenv with ce_module := owner) cx es s` by
    fs[immutable_frame_mods_def,immutable_alloca_sep_mods_def] >>
  `!name b n. local_region cenv es.scopes s name b n ==>
       regions_disjoint off (type_memory_size itv) b n` by
    (qpat_x_assum `immutable_alloca_sep _ _ _ _ _`
       (mp_tac o REWRITE_RULE [immutable_alloca_sep_def]) >>
     simp[] >> strip_tac >> rpt strip_tac >>
     `local_region (cenv with ce_module := owner) es.scopes s name b n` by
       fs[local_region_def] >> metis_tac[]) >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  rpt strip_tac >> first_x_assum drule >> simp[regions_disjoint_def] >> decide_tac
QED

Theorem copy_store_ghost[local]:
  immutable_path_store_post (lo,explicit,ctx,func,PG) dest ptv v
    sa sb (s,G,tn) (t,G',tn') /\
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!name b n. local_region cenv es.scopes s name b n ==>
    regions_disjoint b n dest (type_memory_size ptv)) /\
  fin.scopes = es.scopes /\
  (!key. D.d_imm key = UNIV) /\
  (!j. j < lo /\ j IN tn'.t_mem ==>
       imm_section_dead_mods cenv (mem_bytes_at 0 lo t.vs_memory) j) ==>
  ghost_inv_at_mods D lo d cenv cx fin G' tn' t
Proof
  strip_tac >>
  qpat_x_assum `immutable_path_store_post _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_path_store_post_def]) >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient` by
    (qpat_assum `t with <|vs_vars := _; vs_memory := _; vs_immutables := _;
      vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory /\
    (!i. b <= i /\ i < b+len /\ i IN tn'.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     `regions_disjoint b len dest (type_memory_size ptv)` by
       (qpat_assum `!name b n. local_region _ _ _ name b n ==> regions_disjoint _ _ _ _`
          (drule_then ACCEPT_TAC)) >>
     conj_tac >- (first_x_assum irule >> first_assum ACCEPT_TAC) >>
     rpt strip_tac >> first_x_assum irule >> fs[regions_disjoint_def] >> decide_tac) >>
  `stor_taint_ok_at D tn' t` by fs[stor_taint_ok_at_def] >>
  `ghost_inv_at D 0 d cenv cx es G tn s` by
    (simp[ghost_inv_at_def,allocas_from_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at D 0 d cenv cx fin G' tn' t` by
    (irule ghost_inv_at_local_window_transport >>
     simp[allocas_from_def,mem_bytes_at_def] >>
     qexistsl [`G`,`es`,`func`,`s`,`sa`,`tn`] >>
     simp[] >>
     qpat_assum `!name b len. local_region _ _ _ name b len ==> _ /\\ _`
       (ACCEPT_TAC o REWRITE_RULE [mem_bytes_at_def])) >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
  `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==>
       FLOOKUP G' x = NONE /\ op_taint tn' (Var x) = {}` by
    (rpt strip_tac >> drule_all_then assume_tac local_ptrs_reserved_imm_base >> simp[]) >>
  gvs[ghost_inv_at_mods_def,allocas_from_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem copy_store_local_ptrs[local]:
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!a n. regions_disjoint a n dest (type_memory_size ptv) ==>
       mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
  (!name b n. local_region cenv es.scopes s name b n ==>
        regions_disjoint b n dest (type_memory_size ptv)) ==>
  local_ptrs_rel func cenv es.scopes t
Proof
  strip_tac >> irule localPtrsPropsTheory.local_ptrs_rel_mem_agree >>
  qexists_tac `s` >> simp[] >> conj_tac
  >- (rpt strip_tac >> sym_tac >> first_x_assum irule >> first_x_assum drule >> simp[]) >>
  rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]
QED

(* Use the active frame, not the written owner, for stmt_state_rel. *)
Theorem copy_store_stmt_state[local]:
  immutable_path_store_post (lo,explicit,ctx,func,PG) dest ptv v
    sa sb (s,G,tn) (t,G',tn') /\
  immutable_frame_mods func cenv cx fin t /\
  ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops /\
  local_ptrs_reserved cenv sa /\
  local_ptrs_rel func cenv fin.scopes t /\
  fin = es with immutables := imms /\
  stmt_state_rel H ctx func cenv cx es s ==>
  stmt_state_rel H ctx func cenv cx fin t
Proof
  strip_tac >>
  qpat_x_assum `immutable_path_store_post _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_path_store_post_def]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp /\
   t.vs_labels = s.vs_labels /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
   t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
   t.vs_requests = s.vs_requests /\ t.vs_pending_deletions = s.vs_pending_deletions /\
   t.vs_code = s.vs_code` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _; vs_immutables := _;
       vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `immutable_alloca_sep func cenv cx fin t /\
   immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor fin t` by
    (fs[immutable_frame_mods_def,immutable_alloca_sep_mods_def,immutables_rel_mods_def] >>
     `cenv with ce_module := cenv.ce_module = cenv` by
       simp[compile_env_component_equality] >>
     qpat_x_assum `!src ts. _ ==> immutable_alloca_sep _ _ _ _ _`
       (qspecl_then [`cenv.ce_module`,`tops`] mp_tac) >> asm_rewrite_tac[]) >>
  `immutable_base_zero cenv t` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >>
     fs[stmt_state_rel_def,local_ptrs_reserved_def] >> metis_tac[]) >>
  irule stmt_state_rel_allocas_frame >> simp[] >>
  reverse conj_tac >- (qexistsl [`es`,`s`] >> simp[]) >>
  gvs[state_rel_def,stmt_state_rel_def,storage_rel_def,transient_rel_def,
      accounts_rel_def,logs_rel_def,contract_storage_def,contract_transient_def]
QED

Theorem immutable_copy_writeback_mods:
  immutable_path_store_post (lo,explicit,ctx,func,PG) (off+k) ptv v
    sa sb (s,G,tn) (t,G',tn') /\
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  cenv.ce_is_ctor /\ dead_lo_ok_mods H D lo cenv cx /\
  immutable_frame_mods func cenv cx es s /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,old) /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  value_has_type itv old /\ value_has_type ptv v /\
  mem_path_offset itv path = SOME (k,ptv) /\
  write_place cx (ImmutablePlace owner id path) v es = (INL (),fin) /\
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ return_buf_sep d cenv es s /\
  sa.cs_next_var <= sb.cs_next_var ==>
  immutable_frame_mods func cenv cx fin t /\
  ghost_inv_at_mods D lo d cenv cx fin G' tn' t /\
  (!H tops. ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops /\
      stmt_state_rel H ctx func cenv cx es s ==>
      stmt_state_rel H ctx func cenv cx fin t) /\
  return_buf_frame d cenv sb t /\ return_buf_sep d cenv fin t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (!aid a n. FLOOKUP s.vs_allocas aid = SOME (a,n) ==>
       mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)
Proof
  strip_tac >> drule_then assume_tac copy_store_window >>
  drule_all_then strip_assume_tac immutable_region_value_layout_mods >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `(!j. j < lo /\ j IN tn.t_mem ==>
        imm_section_dead_mods cenv (mem_bytes_at 0 lo s.vs_memory) j) /\
   (!aid a n. FLOOKUP s.vs_allocas aid = SOME (a,n) ==> lo <= a)` by
    (fs[ghost_inv_at_mods_def,allocas_from_def] >> first_assum ACCEPT_TAC) >>
  qpat_assum `immutable_path_store_post _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_path_store_post_def]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `t with <|vs_vars := _; vs_memory := _; vs_immutables := _;
      vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `fin.scopes = es.scopes` by drule_then ACCEPT_TAC write_immutable_place_scopes >>
  `!name b sz. local_region cenv fin.scopes t name b sz ==>
               local_region cenv es.scopes s name b sz` by
    (simp[local_region_def] >> rpt strip_tac >>
     `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
     metis_tac[]) >>
  `immutable_frame_mods func cenv cx fin t /\
   (!j. j < lo /\ j IN tn'.t_mem ==>
        imm_section_dead_mods cenv (mem_bytes_at 0 lo t.vs_memory) j)` by
    drule_all_then ACCEPT_TAC immutable_copy_linked_frame >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    (Cases_on `d` >> fs[loweringPostsTheory.return_buf_frame_def] >>
     rename1 `return_buf_frame (SOME buf) _ _ _` >> Cases_on `buf` >>
     fs[loweringPostsTheory.return_buf_frame_def] >> rpt strip_tac >> gvs[]) >>
  `!name b n. local_region cenv es.scopes s name b n ==>
        regions_disjoint b n (off+k) (type_memory_size ptv)` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC copy_store_locals_disjoint) >>
  `!key. D.d_imm key = UNIV` by fs[dead_lo_ok_mods_def] >>
  `ghost_inv_at_mods D lo d cenv cx fin G' tn' t` by
    drule_all_then ACCEPT_TAC copy_store_ghost >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at _ x ==> _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `local_ptrs_rel func cenv fin.scopes t` by
    (asm_rewrite_tac[] >> drule_all_then ACCEPT_TAC copy_store_local_ptrs) >>
  `?imms'. fin = es with immutables := imms'` by
    drule_then ACCEPT_TAC write_immutable_place_frame >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`s`,`sa`] >> simp[] >> metis_tac[]) >>
  `return_buf_sep d cenv fin t` by
    (irule return_buf_sep_transport >> reverse conj_tac
     >- (qexistsl [`cenv`,`es`,`s`] >> asm_rewrite_tac[]) >>
     rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     fs[return_buf_sep_def,allocas_from_def] >> first_assum ACCEPT_TAC) >>
  `!aid a n. FLOOKUP s.vs_allocas aid = SOME (a,n) ==>
       mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory` by
    (rpt strip_tac >>
     `lo <= a` by
       (qpat_assum `!aid a n. FLOOKUP s.vs_allocas aid = SOME (a,n) ==> lo <= a`
          (drule_then ACCEPT_TAC)) >>
     `regions_disjoint a n (off+k) (type_memory_size ptv)` by
       (simp[regions_disjoint_def] >> decide_tac) >>
     first_x_assum irule >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt strip_tac >> drule_all_then ACCEPT_TAC copy_store_stmt_state) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* A length-only initialization writes one word, not the payload capacity. *)
Theorem immutable_empty_path_store_mods:
  compile_imm_store_word imm dst (Lit 0w) sa = ((),sb) /\
  has_length_word ty /\ evaluate_type tenv ty = SOME tv /\
  eval_operand dst s = SOME (n2w off) /\ op_taint tn dst = {} /\
  op_prov G dst = NONE /\ off + 32 <= lo /\ lo <= s.vs_alloca_next /\
  lo < dimword (:256) /\
  (!base. imm = SOME base ==> eval_operand base s = SOME 0w /\
    op_taint tn base = {} /\ op_prov G base = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q Gf tf. immutable_path_store_post (lo,explicit,ctx,func,PG) off tv
               (default_value tv) sa sb (s,G,tn) (q,Gf,tf) /\
    mem_agree_outside {j | off <= j /\ j < off + 32} s.vs_memory q.vs_memory
Proof
  strip_tac >>
  `w2n (n2w off:bytes32) = off` by (simp[w2n_n2w,LESS_MOD] >> decide_tac) >>
  `w2n (n2w off:bytes32) + 32 <= lo` by simp[] >>
  `eval_operand (Lit 0w) s = SOME 0w /\ op_taint tn (Lit 0w) = {} /\
   (!x. Lit 0w = Var x ==> not_fresh_at sa x)` by simp[eval_operand_def,op_taint_def] >>
  drule_all immutable_word_store_path_clean >>
  disch_then (strip_assume_tac o Q.INST [`PG` |-> `PG`,`explicit` |-> `explicit`]
              o SPEC_ALL) >>
  rename1 `u.vs_memory = _` >> rename1 `tf.t_stor = tn.t_stor` >>
  qabbrev_tac `q = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `mem_word_at off q.vs_memory = 0w` by
    (simp[Abbr `q`] >>
     simp[mem_word_at_eq_mload,mload_mstore_same]) >>
  `32 <= type_memory_size tv` by (drule_all immutable_assign_empty_representation >> simp[]) >>
  `!m. mem_agree_outside tf.t_mem q.vs_memory m ==> val_in_memory tv (default_value tv) off m` by
    (gen_tac >> strip_tac >>
     `mem_bytes_at off 32 m = mem_bytes_at off 32 q.vs_memory` by
       (sym_tac >> irule mem_bytes_at_bytewise >> fs[mem_agree_outside_def] >>
        rpt strip_tac >> first_x_assum irule >> decide_tac) >>
     `mem_word_at off m = 0w` by fs[abiStaticAggregatePropsTheory.mem_word_at_bytes] >>
     drule_all immutable_assign_empty_representation >> simp[]) >>
  qexistsl [`q`,`Gf`,`tf`] >>
  `u.vs_current_bb = s.vs_current_bb /\ u.vs_halted = s.vs_halted` by
    (qpat_assum `(u with <|vs_vars := _; vs_memory := _; vs_immutables := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  reverse conj_tac
  >- (simp[mem_agree_outside_def,Abbr `q`] >> gen_tac >> strip_tac >> sym_tac >>
      irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  simp[immutable_path_store_post_def,Abbr `q`,mstore_memory_nondecreasing,
       blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
  conj_tac >-
    (qpat_assum `(u with <|vs_vars := _; vs_memory := _; vs_immutables := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >>
  fs[regions_disjoint_def] >> decide_tac
QED
