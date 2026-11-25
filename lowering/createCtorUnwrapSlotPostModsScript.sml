(* Read the nonword result and its frames at the supplied slot-copy endpoint. *)
Theory createCtorUnwrapSlotPostMods
Ancestors
  createCtorUnwrapSlotPost createExprSizeExitDefsMods
  bodyFullUnwrapSlotFrame bodyFullUnwrapSlotPost exprSimProps exprPtrUnwrapAllocSemantic exprPtrUnwrapStorage
  exprPtrUnwrapStoragePost exprPtrUnwrapAllocationFrame exprPtrUnwrapAllocation
  exprPtrUnwrapAllocSeparation exprPtrUnwrapRetained exprSimCopy exprSimUnwrapProps
  exprSimPtrTopLevelStorageCopy exprSimStorageCopy exprSimAbiEncodeMemoryLength
  exprPtrUnwrapEnsureShape copyExecution slotCopyExecution bufferAllocationExecution
  assignTuplePtrAlloc storageNormalizationOwnershipPtr fragGasOriginPtrDead
  exprLowering compileEnv context emitHelper exprLoweringProps exprSimAlloc
  localPtrsProps freshWrites bodyPtrDefs bodyPtrMakeArrayExternalCaller
  exprPtrUnwrapStorageSource
  loweringPosts loweringStateRelDefs ptrDiscipline venomState venomExecSemantics
  valueEncodingProps vyperStorageFootprint finite_map pred_set words arithmetic

(* At the observed slot-copy endpoint, transport the linked immutable frame
   through the registered allocation u and the copy z. The caller supplies
   lookup preservation at sb for u and z separately, and bytes outside dst. *)
val ctor_slot_immutable_frame_tac =
  `exec_alloca (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s (n2w nb : bytes32) = OK u` by
    (qpat_assum `step_inst_base _ _ = OK u`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [step_inst_base_def])) >>
  `!src name b len. local_region (cenv with ce_module := src) ee.scopes u name b len <=>
                     local_region (cenv with ce_module := src) ee.scopes s name b len` by
    (rpt gen_tac >>
     `local_region cenv ee.scopes u name b len <=> local_region cenv ee.scopes s name b len` by
       (irule copy_buffer_local_region_frame >> qexists_tac `sb` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `local_region cenv ee.scopes _ name b len <=> _`
       (fn th => simp_tac (srw_ss())
         [local_region_def, REWRITE_RULE[local_region_def] th])) >>
  `!src name b len. local_region (cenv with ce_module := src) ee.scopes z name b len <=>
                     local_region (cenv with ce_module := src) ee.scopes s name b len` by
    (rpt gen_tac >>
     `local_region cenv ee.scopes z name b len <=> local_region cenv ee.scopes s name b len` by
       (irule copy_buffer_local_region_frame >> qexists_tac `sb` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `local_region cenv ee.scopes _ name b len <=> _`
       (fn th => simp_tac (srw_ss())
         [local_region_def, REWRITE_RULE[local_region_def] th])) >>
  qpat_x_assum `immutable_frame_mods _ _ _ _ s`
    (strip_assume_tac o REWRITE_RULE[bodyFullPostsModsTheory.immutable_frame_mods_def,
       bodyInvSplitTheory.immutable_alloca_sep_mods_def,
       bodyInvSplitTheory.immutables_rel_mods_def]) >>
  `!src tops. ALOOKUP cenv.ce_modules src = SOME tops ==>
              immutable_alloca_sep func (cenv with ce_module := src) cx ee u` by
    (rpt gen_tac >> strip_tac >> irule immutable_alloca_sep_exec_alloca >>
     goal_assum (drule_at (Pat `exec_alloca _ _ _ = _`)) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  simp[bodyFullPostsModsTheory.immutable_frame_mods_def, bodyInvSplitTheory.immutable_alloca_sep_mods_def,
       bodyInvSplitTheory.immutables_rel_mods_def] >> reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> irule immutable_alloca_sep_fields >>
      qexistsl_tac [`u`,`ee`] >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!src tops. _ ==> immutables_rel _ _ _ _ _ s` (drule_then assume_tac) >>
  Cases_on `cenv.ce_is_ctor`
  >- (qpat_x_assum `immutables_rel _ _ src _ _ s`
        (assume_tac o SIMP_RULE (srw_ss()) [immutables_rel_def, LET_THM]) >>
      simp[immutables_rel_def] >> rpt gen_tac >> strip_tac >>
      qpat_assum `!name tv v byte_offset. FLOOKUP cenv.ce_module_vars _ = _ /\ _ ==> _`
        (drule_all_then (fn facts =>
           qpat_assum `cenv.ce_is_ctor` (fn ctor =>
             strip_assume_tac (SIMP_RULE (srw_ss()) [ctor] facts)))) >>
      `regions_disjoint byte_offset (type_memory_size tv) (w2n dst) nb` by
        (qpat_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ u`
           (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [immutable_alloca_sep_def])) >>
         qpat_x_assum `cenv.ce_is_ctor ==> _` (drule_then assume_tac) >>
         qpat_assum `!name tv v off. FLOOKUP cenv.ce_module_vars _ = _ /\ _ ==> _ /\ _`
           (drule_all_then strip_assume_tac) >>
         qpat_assum `!inst b sz. _ ==> regions_disjoint _ _ _ _`
           (qspec_then `mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]` mp_tac) >>
         simp[venomInstTheory.mk_inst_def] >> metis_tac[]) >>
      `mem_bytes_at byte_offset (type_memory_size tv) z.vs_memory =
       mem_bytes_at byte_offset (type_memory_size tv) s.vs_memory` by
        (qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _` irule >>
         fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
      simp[] >> irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
      conj_tac >- metis_tac[loweringSliceTheory.immutable_admissible_val_wf] >>
      qexistsl_tac [`type_memory_size tv`, `s.vs_memory`] >> simp[]) >>
  qpat_x_assum `immutables_rel _ _ src _ _ s` mp_tac >>
  simp_tac (srw_ss()) [immutables_rel_def, LET_THM] >>
  simp[]

(* Transport ordinary ghost fields at a zero prefix, then restore the
   linked immutable prefix with the exterior copy frame at the real lo. *)
val ctor_slot_copy_linked_ghost_tac =
  `ghost_inv_at (DF H) 0 d cenv cx ee G tn s` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ G tn s`
       (strip_assume_tac o REWRITE_RULE[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
     simp[ghost_inv_at_def, allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at (DF H) 0 d cenv cx ee Gf tnf z` by
    (irule unwrap_slot_copy_ghost_inv_at_mono >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[allocas_from_def] >>
     qexistsl [`G`, `func`, `nb`, `s`, `sa`, `w2n dst`, `tn`] >>
     `nb + w2n dst = w2n dst + nb` by simp[ADD_COMM] >>
     qpat_x_assum `nb + w2n dst = w2n dst + nb` (fn th => pure_rewrite_tac[th]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (qpat_assum `!a k. _ ==> mem_bytes_at a k z.vs_memory = mem_bytes_at a k s.vs_memory`
       (qspecl_then [`0`, `lo`] mp_tac) >> simp[]) >>
  `!j. j < lo /\ j IN tnf.t_mem ==> j IN tn.t_mem` by
    (rpt strip_tac >>
     qpat_assum `!j. _ \/ _ ==> j IN tnf.t_mem ==> _` irule >>
     simp[] >> decide_tac) >>
  `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==>
     FLOOKUP Gf x = NONE /\ op_taint tnf (Var x) = {}` by
    (gen_tac >> strip_tac >>
     `not_fresh_at sa x` by
       (irule local_ptrs_reserved_imm_base >> qexists `cenv` >> simp[]) >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ G tn s`
       (strip_assume_tac o REWRITE_RULE[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
     qpat_assum `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `!i. i < lo /\ i IN tnf.t_mem ==>
     imm_section_dead_mods cenv (mem_bytes_at 0 lo z.vs_memory) i` by
    (gen_tac >> strip_tac >>
     `i IN tn.t_mem` by (qpat_assum `!j. j < lo /\ j IN tnf.t_mem ==> _` irule >> simp[]) >>
     qpat_assum `mem_bytes_at 0 lo z.vs_memory = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ G tn s`
       (strip_assume_tac o REWRITE_RULE[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
     qpat_assum `!i. _ ==> imm_section_dead_mods _ _ i` irule >> simp[]) >>
  qpat_assum `ghost_inv_at _ 0 _ _ _ _ Gf tnf z`
    (strip_assume_tac o REWRITE_RULE[ghost_inv_at_def]) >>
  rewrite_tac[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC

Theorem ctor_slot_copy_effects_mods[local]:
  (loc = LocStorage \/ loc = LocTransient) /\ nb = 32*n /\
  (n <> 1 ==> ?cv ds.
     toplevel_copy_inv cv ds root src loc a (w2n dst) n allocated G0 tn0 n Gf tnf z /\
     (!x. not_fresh_at mid x ==> ~MEM x ds)) /\
  (n = 1 ==>
     z = (mstore (w2n dst) (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) allocated a)
       (update_var (STRING #"%" (toString mid.cs_next_var))
         (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) allocated a) allocated)
           with vs_inst_idx := k) /\
     tnf.t_mem = (tn0.t_mem DIFF {j | w2n dst <= j /\ j < w2n dst+32}) UNION
       {w2n dst+b | b IN key_taint (if loc=LocStorage then tn0.t_stor else tn0.t_trans) a} /\
     tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm /\
     (!x. x <> STRING #"%" (toString mid.cs_next_var) ==>
        FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x))) ==>
  copy_static z = copy_static allocated /\
  LENGTH allocated.vs_memory <= LENGTH z.vs_memory /\
  (!off len. off+len <= w2n dst \/ w2n dst+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len allocated.vs_memory) /\
  (!x. not_fresh_at mid x ==>
    lookup_var x z = lookup_var x allocated /\ FLOOKUP Gf x = FLOOKUP G0 x /\
    op_taint tnf (Var x) = op_taint tn0 (Var x)) /\
  (!j. j < n ==> mem_word_at (w2n dst+32*j) z.vs_memory =
    slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) allocated (a+n2w j)) /\
  (!j b. j < n /\ b < 32 /\ w2n dst+32*j+b IN tnf.t_mem ==>
    b IN key_taint (if loc=LocStorage then tn0.t_stor else tn0.t_trans) (a+n2w j)) /\
  (!q. ~(w2n dst <= q /\ q < w2n dst+nb) /\ q IN tnf.t_mem ==> q IN tn0.t_mem) /\
  tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> Cases_on `n = 1`
  >- suspend "single" >> suspend "loop"
QED

Resume ctor_slot_copy_effects_mods[single]:
  qpat_x_assum `loc = LocStorage \/ loc = LocTransient` kall_tac >>
  qpat_x_assum `(_ = 1 ==> _)` (drule_then strip_assume_tac) >> gvs[] >>
  `!x. not_fresh_at mid x ==> x <> STRING #"%" (toString mid.cs_next_var)` by
    simp[not_fresh_at_def] >>
  rpt conj_tac
  >- simp[copy_static_def, mstore_def, write_memory_with_expansion_def, update_var_def]
  >- (qmatch_goalsub_abbrev_tac `mstore off w r` >>
      mp_tac (Q.INST [`s` |-> `r`, `off` |-> `off`, `w` |-> `w`]
        abi_encode_mstore_memory_length) >>
      simp[Abbr `r`, update_var_def])
  >- (rpt gen_tac >> disch_tac >> dep_rewrite.DEP_REWRITE_TAC [mstore_mem_bytes_at_disjoint] >>
      conj_tac >- decide_tac >> simp[update_var_def])
  >- (rpt strip_tac >>
      simp[mstore_def, write_memory_with_expansion_def, update_var_def, lookup_var_def,
           FLOOKUP_UPDATE] >> metis_tac[])
  >- simp[mstore_mem_word_at_same, WORD_ADD_0]
  >- (simp[WORD_ADD_0] >> metis_tac[]) >>
  rpt strip_tac >> gvs[key_taint_def] >> decide_tac
QED

Resume ctor_slot_copy_effects_mods[loop]:
  qpat_x_assum `(_ <> 1 ==> _)` (drule_then strip_assume_tac) >>
  drule toplevel_copy_inv_content >>
  disch_then (strip_assume_tac o REWRITE_RULE [storage_copy_inv_def, copy_prefix_def]) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `nb = 32*n` SUBST1_TAC >> first_assum ACCEPT_TAC)
  >- (fs[toplevel_copy_inv_def, storage_copy_frame_def] >> metis_tac[])
  >- (rpt strip_tac >>
      `mem_word_at (w2n dst+32*j) z.vs_memory =
       copy_runtime_word loc allocated (a+n2w j)` by metis_tac[] >>
      Cases_on `loc=LocStorage` >> gvs[copy_runtime_word_def, slot_copy_word_def])
  >- suspend "loop_taint"
  >- (rpt strip_tac >> drule toplevel_copy_inv_memory_taint >>
      simp[toplevel_copy_taint_bound_def, toplevel_copy_region_def,
           toplevel_copy_translated_taint_def, SUBSET_DEF] >>
      disch_then (qspec_then `q` mp_tac) >> simp[] >> strip_tac >> gvs[]) >>
  fs[toplevel_copy_inv_def]
QED

Resume ctor_slot_copy_effects_mods[loop_taint]:
  rpt strip_tac >> drule toplevel_copy_inv_memory_taint >>
  simp[toplevel_copy_taint_bound_def, toplevel_copy_region_def,
       toplevel_copy_translated_taint_def, SUBSET_DEF] >>
  disch_then (qspec_then `w2n dst+32*j+b` mp_tac) >>
  `w2n dst <= w2n dst+32*j+b /\ w2n dst+32*j+b < w2n dst+32*n` by decide_tac >>
  simp[] >> strip_tac >>
  rename1 `(a+n2w i,r) IN toplevel_copy_source_taint loc ts` >>
  `i = j /\ r = b` by intLib.COOPER_TAC >>
  qpat_x_assum `(a+n2w i,r) IN _` mp_tac >>
  simp[key_taint_def, toplevel_copy_source_taint_def]
QED

Finalise ctor_slot_copy_effects_mods[local]

Theorem ctor_unwrap_slot_endpoint_post_mods:
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type (post_value_type cenv e) /\
  compile_expr cenv ty e sa = (LocatedValue t p,sm) /\
  compile_ensure_in_memory p.ptr_operand p.ptr_location nb n
    cenv.ce_is_ctor cenv.ce_imm_alloca sb = (op,sc) /\
  read_result cx tv ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  nb = type_memory_bytes cenv (post_value_type cenv e) /\
  nb = type_memory_size rty /\ n = type_slot_size rty /\ nb < dimword (:256) /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_inst_ids_distinct func /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  ptr_vv_ok cx (post_value_type cenv e) tv (LocatedValue t p) ee G tn s /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_operand p.ptr_operand s = SOME a /\
  fn_has_code sb mid func /\ fn_has_code mid sc func /\
  u = update_var root dst (buffer_allocation_fields s sb.cs_next_id nb) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  allocated = u with vs_inst_idx := SUC s.vs_inst_idx /\
  G0 = step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
  tn0 = step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  op = Var root /\ dst = n2w (buffer_allocation_base s sb.cs_next_id) /\
  compile_alloc_buffer nb sb = (buf,mid) /\ buf.buf_operand = Var root /\
  gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tnf) /\
  (n <> 1 ==> ?cv ds.
    toplevel_copy_inv cv ds root p.ptr_operand p.ptr_location a (w2n dst) n allocated G0 tn0 n Gf tnf z /\
    (!x. not_fresh_at mid x ==> ~MEM x ds) /\ ~z.vs_halted) /\
  (n = 1 ==>
    z = (mstore (w2n dst) (slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) allocated a)
      (update_var (STRING #"%" (toString mid.cs_next_var))
        (slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) allocated a) allocated)
            with vs_inst_idx := LENGTH sc.cs_current_insts) /\
    tnf.t_mem = (tn0.t_mem DIFF {j | w2n dst <= j /\ j < w2n dst+32}) UNION
      {w2n dst+b | b IN key_taint (if p.ptr_location=LocStorage then tn0.t_stor else tn0.t_trans) a} /\
    tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm /\
    (!x. x <> STRING #"%" (toString mid.cs_next_var) ==>
       FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x))) ==>
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tnf) /\
     expr_post_mods H ctx func cenv cx e es sa sc s0 ee v op z /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee Gf tnf z) /\
  vv_at cenv cx (post_value_type cenv e) sa sc ee tv
    (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z /\
  vv_own cenv cx (post_value_type cenv e) sb sc ee (Value v)
    (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z /\
  expr_store_bound cx (post_value_type cenv e) v op z /\
  ptr_val_ok cx (post_value_type cenv e) v op Gf tnf z /\ ptr_buf_ok cenv e op Gf z /\
  (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
       eval_operand op z = SOME w ==> w2n w + type_memory_size rt <= z.vs_alloca_next) /\
  (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
  wb_frame cenv ee ee sb s z /\ ghost_kept_at lo cenv ee sb G tn s Gf tnf /\
  ghost_kept_at lo cenv es sa Gi ti s0 Gf tnf
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `nb = 32*n` by simp[type_memory_size_slots] >>
  `copy_static z = copy_static allocated /\
   LENGTH allocated.vs_memory <= LENGTH z.vs_memory /\
   (!off len. off+len <= w2n dst \/ w2n dst+nb <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len allocated.vs_memory) /\
   (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x allocated /\
     FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x)) /\
   (!j. j < n ==> mem_word_at (w2n dst+32*j) z.vs_memory =
     slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) allocated (a+n2w j)) /\
   (!j b. j < n /\ b < 32 /\ w2n dst+32*j+b IN tnf.t_mem ==>
     b IN key_taint (if p.ptr_location=LocStorage then tn0.t_stor else tn0.t_trans) (a+n2w j)) /\
   (!q. ~(w2n dst <= q /\ q < w2n dst+nb) /\ q IN tnf.t_mem ==> q IN tn0.t_mem) /\
   tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm` by
    (irule ctor_slot_copy_effects_mods >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexistsl [`root`, `p.ptr_operand`] >> metis_tac[]) >>
     conj_tac >- (qexists `LENGTH sc.cs_current_insts` >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `p.ptr_location <> LocCode` by
    (qpat_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >> simp[]) >>
  `vv_place_ptr_mods cenv cx ee s tv (LocatedValue t p) ==>
   vv_place_ptr cenv cx ee s tv (LocatedValue t p)` by
    (Cases_on `tv` >> simp[bodyFullPostsModsTheory.vv_place_ptr_mods_def] >>
     rename1 `vv_place_ptr _ _ _ _ (PlaceR place) (LocatedValue _ _)` >> Cases_on `place` >>
     simp[bodyFullPostsModsTheory.vv_place_ptr_mods_def, vv_place_ptr_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post H ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE[bodyFullPostsModsTheory.vv_post_mods_def])) >>
     `vv_holds cenv cx (post_value_type cenv e) tv (LocatedValue t p) ee s` by
       (qpat_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
        qpat_assum `p.ptr_location <> LocCode` (fn th =>
          simp_tac (srw_ss()) [bodyFullPostsModsTheory.vv_holds_mods_def, th])) >>
     rewrite_tac[vv_post_def] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `vv_place_ptr_mods _ _ _ _ _ _ ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  suspend "alloc"
QED

Resume ctor_unwrap_slot_endpoint_post_mods[alloc]:
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[storage_trace_domain_def, Abbr `H0`] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `stmt_state_rel H0 ctx func cenv cx ee s` by fs[vv_post_def] >>
  `immutable_frame_mods func cenv cx ee s` by fs[bodyFullPostsModsTheory.vv_post_mods_def] >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists `sm` >> simp[]) >>
  `sb.cs_next_id < sc.cs_next_id` by suspend "ensure_id" >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  drule abiBufferAllocationCodeTheory.compile_alloc_buffer_code >> strip_tac >>
  `root = STRING #"%" (toString sb.cs_next_var)` by
    (qpat_assum `buf.buf_operand = Var root` mp_tac >> simp[]) >>
  `not_fresh_at mid root` by simp[not_fresh_at_def] >>
  `!x. not_fresh_at sb x ==> x <> root /\ not_fresh_at mid x` by
    (rpt strip_tac >> fs[not_fresh_at_def] >> decide_tac) >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by
    (drule_all exprSimAllocTheory.buffer_alloc_code >> simp[]) >>
  drule_all alloca_step_exterior_ghost_ptr >>
  qpat_assum `G0 = _` (fn gth =>
    qpat_assum `tn0 = _` (fn tth =>
      disch_then (qspecl_then [`tn`, `PG`, `G`]
        (strip_assume_tac o REWRITE_RULE [GSYM gth, GSYM tth])))) >>
  suspend "copy_frame"
QED

Resume ctor_unwrap_slot_endpoint_post_mods[ensure_id]:
  qpat_assum `p.ptr_location = LocStorage \/ _` mp_tac >>
  qpat_assum `compile_alloc_buffer nb sb = _` mp_tac >>
  qpat_assum `compile_ensure_in_memory _ _ _ _ _ _ sb = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  fs[compile_ensure_in_memory_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `n = 1` >>
  gvs[compile_storage_to_memory_def, compile_transient_to_memory_def,
      GSYM compile_slot_to_memory_def, compile_slot_to_memory_shape,
      slot_copy_final_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, emit_def, fresh_var_def, fresh_id_def,
      compile_alloc_buffer_def] >> pairarg_tac >> gvs[]
QED

Resume ctor_unwrap_slot_endpoint_post_mods[copy_frame]:
  `copy_static allocated = copy_static u /\ allocated.vs_memory = u.vs_memory /\
   (!x. lookup_var x allocated = lookup_var x u)` by
    simp[Once (GSYM EQ_IMP_THM), copy_static_def, lookup_var_def] >>
  `copy_static z = copy_static u` by simp[] >>
  `!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `x <> root /\ not_fresh_at mid x` by
       (qpat_assum `!x. not_fresh_at sb x ==> _` (drule_then ACCEPT_TAC)) >>
     qpat_assum `!x. not_fresh_at mid x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. x <> root ==> _` (drule_then strip_assume_tac) >>
     simp[Once (GSYM EQ_IMP_THM)]) >>
  `!off len. off+len <= w2n dst \/ w2n dst+nb <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _`
       (drule_then mp_tac) >> simp[]) >>
  `!q. ~(w2n dst <= q /\ q < w2n dst+nb) /\ q IN tnf.t_mem ==> q IN tn.t_mem` by
    (rpt gen_tac >> strip_tac >>
     `q IN tn0.t_mem` by
       (qpat_assum `!q. _ /\ q IN tnf.t_mem ==> _` irule >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!i. ~(_ <= i /\ _) ==> _` (drule_then mp_tac) >>
     disch_then (fn th => irule (iffLR th)) >> first_assum ACCEPT_TAC) >>
  qpat_assum `copy_static z = copy_static u` (mp_then Any strip_assume_tac copy_static_fields) >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP z.vs_allocas aid = SOME entry` by
    (qpat_assum `z.vs_allocas = u.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `FLOOKUP z.vs_allocas sb.cs_next_id = SOME (w2n dst,nb)` by
    (qpat_assum `z.vs_allocas = u.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `eval_operand op z = SOME dst` by
    (`lookup_var root u = SOME dst` by
        (qpat_assum `u = _` SUBST1_TAC >> simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
     qpat_assum `!x. not_fresh_at mid x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `op = Var root` SUBST1_TAC >>
     rewrite_tac[eval_operand_def] >>
     qpat_assum `lookup_var root z = lookup_var root allocated` SUBST1_TAC >>
     qpat_assum `!x. lookup_var x allocated = lookup_var x u` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `ptr_covers G0 tn0 root allocated nb` by
    (drule_all unwrap_alloc_output_coverage >> simp[]) >>
  `ptr_covers Gf tnf root z nb` by
    (qpat_assum `!x. not_fresh_at mid x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `lookup_var root z = _` (fn vth =>
       qpat_assum `FLOOKUP Gf root = _` (fn gth =>
         qpat_assum `op_taint tnf (Var root) = _` (fn tth =>
           rewrite_tac[ptr_covers_def, vth, gth, tth]))) >>
     qpat_assum `ptr_covers G0 tn0 root allocated nb`
       (ACCEPT_TAC o REWRITE_RULE[ptr_covers_def])) >>
  suspend "source_value"
QED

Resume ctor_unwrap_slot_endpoint_post_mods[source_value]:
  qabbrev_tac `tr = (p.ptr_location = LocTransient)` >>
  `p.ptr_location = slot_loc tr /\ p.ptr_location <> LocMemory` by
    (qpat_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >>
     simp[slot_loc_def, Abbr `tr`]) >>
  `post_value_type cenv e = expr_type e /\ lowered_value_type cenv e = expr_type e` by
    (conj_tac >- (drule_all external_located_post_type >> simp[]) >>
     drule_all external_located_lowered_type >> simp[]) >>
  drule_all vv_post_storage_source >> strip_tac >>
  `storage_holds cx tr (post_value_type cenv e) (Value v) a ee s` by
    (qpat_assum `storage_holds _ _ _ (Value _) _ _ _` mp_tac >>
     qpat_assum `t = post_value_type cenv e` mp_tac >>
     qpat_assum `read_result cx tv ee = (INL v,ee)` mp_tac >>
     qpat_x_assum `read_result cx tv ee = (INL v',ee)` mp_tac >>
     qpat_assum `eval_operand p.ptr_operand s = SOME a` mp_tac >>
     qpat_x_assum `eval_operand p.ptr_operand s = SOME a'` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> strip_tac >> gvs[]) >>
  `allocated.vs_accounts = s.vs_accounts /\ allocated.vs_transient = s.vs_transient /\
   allocated.vs_call_ctx = s.vs_call_ctx /\
   tn0.t_stor = tn.t_stor /\ tn0.t_trans = tn.t_trans /\ tn0.t_imm = tn.t_imm` by
    simp[buffer_allocation_fields_frame, update_var_def, normalization_alloca_key_taints] >>
  `!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==> val_in_memory rty v (w2n dst) mem` by
    suspend "robust" >>
  `val_wf rty v /\ val_footprint rty v <= nb /\ val_store_size rty v <= nb` by
    (`read_result cx (Value v) ee = (INL v,ee)` by
       simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
     drule_all storage_holds_value_bounds >> strip_tac >>
     `val_store_size rty v <= type_memory_size rty` by
       (irule exprSimPropsTheory.val_store_size_le >> first_assum ACCEPT_TAC) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z` by suspend "semantics" >>
  suspend "frames"
QED

Resume ctor_unwrap_slot_endpoint_post_mods[robust]:
  `ptr_vv_ok cx (post_value_type cenv e) (Value v) (LocatedValue t p) ee G tn s` by
    (qpat_assum `ptr_vv_ok _ _ tv _ _ _ _ _` mp_tac >>
     qpat_assum `p.ptr_location <> LocMemory` (fn th =>
       simp_tac (srw_ss()) [ptr_vv_ok_def, th])) >>
  `?v'. read_result cx (Value v) ee = (INL v',ee) /\
       !mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==> val_in_memory rty v' (w2n dst) mem` by
    (irule unwrap_storage_copied_robust >>
     goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
     qexistsl [`tr`, `a`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`!j b. _ ==> b IN key_taint _ _`,
        `!j. j < n ==> mem_word_at _ _ = _`,
        `n = type_slot_size rty`, `p.ptr_location = slot_loc tr`,
        `allocated.vs_accounts = s.vs_accounts`,
        `allocated.vs_transient = s.vs_transient`, `allocated.vs_call_ctx = s.vs_call_ctx`,
        `tn0.t_stor = tn.t_stor`, `tn0.t_trans = tn.t_trans`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `tr` >>
     simp[slot_loc_def, slot_copy_word_def, sload_def, tload_def,
          contract_storage_def, contract_transient_def]) >>
  qpat_assum `read_result cx (Value v) ee = (INL _,ee)`
    (SUBST1_TAC o SIMP_RULE (srw_ss()) [vyperStateTheory.read_result_def, vyperStateTheory.return_def]) >>
  first_assum ACCEPT_TAC
QED

Resume ctor_unwrap_slot_endpoint_post_mods[semantics]:
  rpt gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  `vv_post H ctx func cenv cx e es sa sb s0 ee (Value v) (LocatedValue t p) s` by
    (`vv_post H ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s` by
       (irule vv_post_read_result >> qexists `tv` >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `vv_post H _ _ _ _ _ _ _ sm _ _ (Value v) _ _` mp_tac >>
     qpat_assum `p.ptr_location <> LocMemory` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[vv_post_def, vv_at_def, vv_own_def] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_def] >>
  qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ s` kall_tac >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  `val_in_memory rty v (w2n dst) z.vs_memory` by simp[mem_agree_outside_def] >>
  qpat_assum `vv_post H _ _ _ _ _ _ _ sb _ _ (Value v) _ _`
    (mp_then Any mp_tac copy_buffer_post_transport_physical) >>
  disch_then irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- decide_tac
  >- decide_tac
  >- (qexists `mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]` >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[venomInstTheory.mk_inst_def]) >>
  qexistsl [`mid`, `nb`, `rty`, `u`, `dst`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (decide_tac >> NO_TAC) >>
  TRY (qpat_assum `allocated.vs_memory = u.vs_memory` (SUBST1_TAC o SYM) >>
       first_assum ACCEPT_TAC >> NO_TAC) >>
  rpt strip_tac >>
  qpat_assum `!x. not_fresh_at mid x ==> _` (drule_then strip_assume_tac) >> simp[]
QED

Resume ctor_unwrap_slot_endpoint_post_mods[frames]:
  `buffer_allocation_base s sb.cs_next_id = w2n dst` by
    (qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ u` kall_tac >>
     drule_all unwrap_alloc_site_bound >> strip_tac >>
     `buffer_allocation_base s sb.cs_next_id < dimword (:256)` by decide_tac >>
     simp[w2n_n2w]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods (DF H0) _ _ _ _ _ G tn s`
       (strip_assume_tac o REWRITE_RULE[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `lo <= w2n dst` by
    (qpat_assum `allocas_from lo s` mp_tac >>
     qpat_assum `lo <= s.vs_alloca_next` mp_tac >>
     qpat_assum `buffer_allocation_base s sb.cs_next_id = _` (mp_tac o SYM) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[buffer_allocation_base_def, allocas_from_def] >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >> simp[] >>
     rename1 `SOME site` >> PairCases_on `site` >> simp[] >> metis_tac[]) >>
  `w2n dst + nb <= z.vs_alloca_next` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ u` mp_tac >>
     qpat_assum `FLOOKUP u.vs_allocas sb.cs_next_id = _` mp_tac >>
     qpat_assum `z.vs_alloca_next = u.vs_alloca_next` SUBST1_TAC >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
          venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[ADD_COMM]) >>
  `!name b len. local_region cenv ee.scopes s name b len ==>
      w2n dst+nb <= b \/ b+len <= w2n dst` by suspend "locals" >>
  `!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\ aid < sb.cs_next_id ==>
      b+len <= w2n dst \/ w2n dst+nb <= b` by
    (rpt strip_tac >> qpat_assum `!id b len. _ ==> regions_disjoint _ _ _ _` drule_all >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[regions_disjoint_def] >> decide_tac) >>
  `immutable_frame_mods func cenv cx ee z` by suspend "immutables" >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at_mods (DF H) lo d cenv cx ee Gf tnf z` by suspend "ghost_inv" >>
  `wb_frame cenv ee ee sb s z` by suspend "writeback" >>
  `ghost_kept_at lo cenv ee sb G tn s Gf tnf` by suspend "kept_current" >>
  `ghost_kept_at lo cenv es sa Gi ti s0 Gf tnf` by suspend "kept_original" >>
  suspend "finish"
QED

Resume ctor_unwrap_slot_endpoint_post_mods[locals]:
  rpt strip_tac >>
  `local_region cenv ee.scopes u name b len` by
    (irule (iffRL (SPEC_ALL copy_buffer_local_region_frame)) >>
     qexistsl [`s`,`sb`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!name b len. local_region cenv ee.scopes u name b len ==> _` (drule_then mp_tac) >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[regions_disjoint_def] >> decide_tac
QED

Resume ctor_unwrap_slot_endpoint_post_mods[immutables]:
  `!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sb x ==> lookup_var x z = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `u.vs_data_section = s.vs_data_section` by
    (qpat_assum `u = update_var _ _ _` SUBST1_TAC >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
     simp[update_var_def, buffer_allocation_fields_def]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`immutable_frame_mods _ _ _ _ s`, `local_ptrs_reserved cenv sb`,
     `!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s`,
     `!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s`,
     `step_inst_base _ s = OK u`, `MEM (mk_inst sb.cs_next_id ALLOCA _ _) _`,
     `FLOOKUP u.vs_allocas sb.cs_next_id = SOME (w2n dst,nb)`,
     `z.vs_allocas = u.vs_allocas`, `z.vs_alloca_next = u.vs_alloca_next`,
     `z.vs_data_section = u.vs_data_section`, `u.vs_data_section = s.vs_data_section`,
     `!off len. _ ==> mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  ctor_slot_immutable_frame_tac
QED

Resume ctor_unwrap_slot_endpoint_post_mods[ghost_inv]:
  rpt gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s`
    (drule_then strip_assume_tac) >>
  `local_ptrs_rel func cenv ee.scopes s` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[stmt_state_rel_def, state_rel_def]) >>
  `allocas_from lo z` by suspend "allocas_from" >>
  `lo <= z.vs_alloca_next` by decide_tac >>
  `stor_taint_ok_at (DF H) tnf z` by suspend "stor_taints" >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> disch_tac >>
     `not_fresh_at sb x` by
       (irule not_fresh_at_mono >> qexists `sa` >> conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at sb x ==> lookup_var _ _ = _ /\ _` (drule_then ACCEPT_TAC)) >>
  `!j. j < w2n dst \/ w2n dst+nb <= j ==> j IN tnf.t_mem ==> j IN tn.t_mem` by
    (qpat_assum `!q. _ /\ q IN tnf.t_mem ==> q IN tn.t_mem` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[NOT_LESS, NOT_LESS_EQUAL]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s`, `local_ptrs_reserved cenv sa`,
     `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`,
     `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`,
     `local_ptrs_rel func cenv ee.scopes s`,
     `!name b len. local_region cenv ee.scopes s name b len ==> _`,
     `!x. not_fresh_at sa x ==> lookup_var x z = _ /\ _`,
     `!off len. _ ==> mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory`,
     `!j. j < w2n dst \/ w2n dst+nb <= j ==> j IN tnf.t_mem ==> j IN tn.t_mem`,
     `lo <= w2n dst`, `stor_taint_ok_at (DF H) tnf z`,
     `allocas_from lo z`, `lo <= z.vs_alloca_next`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  ctor_slot_copy_linked_ghost_tac
QED

Resume ctor_unwrap_slot_endpoint_post_mods[allocas_from]:
  qpat_assum `z.vs_allocas = u.vs_allocas` mp_tac >>
  qpat_assum `u = update_var _ _ _` mp_tac >>
  qpat_assum `allocas_from lo s` mp_tac >>
  qpat_assum `buffer_allocation_base s sb.cs_next_id = _` mp_tac >>
  qpat_assum `lo <= w2n dst` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
  simp[allocas_from_def, update_var_def, buffer_allocation_fields_def] >> rpt strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
  gvs[FLOOKUP_UPDATE, buffer_allocation_base_def, AllCaseEqs()] >> metis_tac[]
QED

Resume ctor_unwrap_slot_endpoint_post_mods[stor_taints]:
  `z.vs_immutables = s.vs_immutables` by
    (qpat_assum `copy_static z = copy_static u`
       (mp_tac o AP_TERM ``\s:venom_state. s.vs_immutables``) >>
     qpat_assum `u = update_var _ _ _` SUBST1_TAC >> POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
     simp[copy_static_def, update_var_def, buffer_allocation_fields_def]) >>
  qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ G tn s`
    (strip_assume_tac o REWRITE_RULE[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
  qpat_assum `stor_taint_ok_at (DF H) tn s` mp_tac >>
  PURE_REWRITE_TAC[stor_taint_ok_at_def] >>
  qpat_assum `z.vs_immutables = s.vs_immutables` SUBST1_TAC >>
  qpat_assum `z.vs_accounts = u.vs_accounts` SUBST1_TAC >>
  qpat_assum `z.vs_transient = u.vs_transient` SUBST1_TAC >>
  qpat_assum `z.vs_call_ctx = u.vs_call_ctx` SUBST1_TAC >>
  qpat_assum `u = update_var _ _ _` SUBST1_TAC >>
  qpat_assum `tnf.t_stor = tn0.t_stor` SUBST1_TAC >>
  qpat_assum `tnf.t_trans = tn0.t_trans` SUBST1_TAC >>
  qpat_assum `tnf.t_imm = tn0.t_imm` SUBST1_TAC >>
  qpat_assum `tn0.t_stor = tn.t_stor` SUBST1_TAC >>
  qpat_assum `tn0.t_trans = tn.t_trans` SUBST1_TAC >>
  qpat_assum `tn0.t_imm = tn.t_imm` SUBST1_TAC >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[buffer_allocation_fields_frame, update_var_def] >>
  Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >> simp[buffer_allocation_fields_def]
QED

Resume ctor_unwrap_slot_endpoint_post_mods[writeback]:
  irule unwrap_slot_copy_wb_frame >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!x. not_fresh_at sb x ==> lookup_var _ _ = _ /\ _`
        (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  qexistsl [`nb`, `w2n dst`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_assum `!name b len. local_region cenv ee.scopes s name b len ==> _`
        (drule_then mp_tac) >> POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  rpt strip_tac >>
  qpat_assum `!aid b len. _ ==> b+len <= w2n dst \/ _` (drule_all_then ACCEPT_TAC)
QED

Resume ctor_unwrap_slot_endpoint_post_mods[kept_current]:
  rewrite_tac[ghost_kept_at_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!x. not_fresh_at sb x ==> lookup_var _ _ = _ /\ _` drule >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!q. _ /\ q IN tnf.t_mem ==> q IN tn.t_mem` irule >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  (qpat_assum `!aid b len. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _` (drule_all_then mp_tac) ORELSE
   qpat_assum `!name b len. local_region cenv ee.scopes s name b len ==> _` (drule_then mp_tac)) >>
  qpat_assum `i < _ + _` mp_tac >> qpat_assum `_ <= i` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac
QED

Resume ctor_unwrap_slot_endpoint_post_mods[kept_original]:
  `!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id ==>
     w2n dst+nb <= off \/ off+len <= w2n dst` by
    (rpt strip_tac >>
     `FLOOKUP s.vs_allocas aid = SOME (off,len)` by fs[vv_post_def] >>
     `aid < sb.cs_next_id` by decide_tac >>
     qpat_assum `!aid b len. _ ==> b+len <= w2n dst \/ _` (drule_all_then strip_assume_tac) >>
     decide_tac) >>
  `!name off len. local_region cenv es.scopes s0 name off len ==>
     w2n dst+nb <= off \/ off+len <= w2n dst` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes s name off len` by
       (irule local_region_frame_fwd >> qexistsl [`s0`,`sa`,`es.scopes`] >> fs[vv_post_def]) >>
     qpat_assum `!name b len. local_region cenv ee.scopes s name b len ==> _`
       (drule_then ACCEPT_TAC)) >>
  irule unwrap_slot_copy_ghost_kept_at >> qexistsl [`G`,`tn`] >> rpt conj_tac
  >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac
  >> TRY (`not_fresh_at sb x` by (irule not_fresh_at_mono >> qexists `sa` >> conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
       qpat_assum `!x. not_fresh_at sb x ==> lookup_var _ _ = _ /\ _` drule >> simp[] >> NO_TAC) >>
  qpat_assum `!q. _ /\ q IN tnf.t_mem ==> q IN tn.t_mem` irule >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  TRY (decide_tac >> NO_TAC) >>
  (qpat_assum `!aid off len. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _` (drule_all_then strip_assume_tac) ORELSE
   qpat_assum `!name off len. local_region cenv es.scopes s0 name off len ==> _` (drule_then strip_assume_tac)) >>
  decide_tac
QED

Resume ctor_unwrap_slot_endpoint_post_mods[finish]:
  `ptr_val_ok cx (post_value_type cenv e) v op Gf tnf z /\ ptr_buf_ok cenv e op Gf z` by
    (`eval_operand (Var root) z = SOME dst` by
       (qpat_assum `op = Var root` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
     qpat_assum `op = Var root` SUBST1_TAC >>
     irule unwrap_storage_pointer_posts >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`nb`, `rty`, `dst`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `nb = type_memory_bytes cenv _` mp_tac >>
     qpat_assum `nb = type_memory_size rty` mp_tac >>
     qpat_assum `post_value_type cenv e = expr_type e` mp_tac >>
     qpat_assum `lowered_value_type cenv e = expr_type e` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[LESS_EQ_REFL]) >>
  `!name b len. local_region cenv ee.scopes z name b len ==>
      w2n dst+nb <= b \/ b+len <= w2n dst` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes s name b len` by
       (irule (iffLR (SPEC_ALL copy_buffer_local_region_frame)) >>
        qexistsl [`sb`,`z`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        rpt strip_tac >> qpat_assum `!x. not_fresh_at sb x ==> lookup_var _ _ = _ /\ _` drule >> simp[]) >>
     qpat_assum `!name b len. local_region cenv ee.scopes s name b len ==> _` (drule_then ACCEPT_TAC)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> disch_tac >> conj_tac
      >- (irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
      conj_tac
      >- (rewrite_tac[bodyFullPostsModsTheory.expr_post_mods_def] >>
          reverse conj_tac >- first_assum ACCEPT_TAC >>
          qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ z`
            (drule_then ACCEPT_TAC)) >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at_mods (DF H) _ _ _ _ _ Gf tnf z`
        (drule_then ACCEPT_TAC))
  >- suspend "vv_at"
  >- suspend "vv_own"
  >- (qpat_assum `evaluate_type _ _ = SOME rty` mp_tac >>
      qpat_assum `eval_operand op z = SOME dst` mp_tac >>
      qpat_assum `val_store_size rty v <= nb` mp_tac >>
      qpat_assum `w2n dst+nb <= z.vs_alloca_next` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[exprSimMemDefsTheory.expr_store_bound_def] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  qpat_assum `evaluate_type _ _ = SOME rty` mp_tac >>
  qpat_assum `lowered_value_type cenv e = expr_type e` mp_tac >>
  qpat_assum `post_value_type cenv e = expr_type e` mp_tac >>
  qpat_assum `eval_operand op z = SOME dst` mp_tac >>
  qpat_assum `nb = type_memory_size rty` mp_tac >>
  qpat_assum `w2n dst+nb <= z.vs_alloca_next` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]
QED

Resume ctor_unwrap_slot_endpoint_post_mods[vv_at]:
  `sa.cs_next_id <= sb.cs_next_id` by decide_tac >>
  qpat_assum `sa.cs_next_id <= sb.cs_next_id` mp_tac >>
  qpat_assum `read_result cx tv ee = (INL v,ee)` mp_tac >>
  qpat_assum `evaluate_type _ _ = SOME rty` mp_tac >>
  qpat_assum `FLOOKUP z.vs_allocas sb.cs_next_id = _` mp_tac >>
  qpat_assum `!name b len. local_region _ _ z _ _ _ ==> _` mp_tac >>
  qpat_assum `eval_operand op z = SOME dst` mp_tac >>
  qpat_assum `val_wf rty v` mp_tac >>
  qpat_assum `val_footprint rty v <= nb` mp_tac >>
  qpat_assum `sb.cs_next_id < sc.cs_next_id` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[vv_at_def, mk_ptr_def] >> rpt strip_tac >> disj1_tac >>
  qexistsl [`sb.cs_next_id`, `w2n dst`, `nb`] >> simp[] >> metis_tac[]
QED

Resume ctor_unwrap_slot_endpoint_post_mods[vv_own]:
  qpat_assum `evaluate_type _ _ = SOME rty` mp_tac >>
  qpat_assum `FLOOKUP z.vs_allocas sb.cs_next_id = _` mp_tac >>
  qpat_assum `!name b len. local_region _ _ z _ _ _ ==> _` mp_tac >>
  qpat_assum `eval_operand op z = SOME dst` mp_tac >>
  qpat_assum `val_footprint rty v <= nb` mp_tac >>
  qpat_assum `sb.cs_next_id < sc.cs_next_id` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[vv_own_def, mk_ptr_def, vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  rpt strip_tac >> disj1_tac >>
  qexistsl [`sb.cs_next_id`, `w2n dst`, `nb`] >> simp[] >> metis_tac[]
QED

Finalise ctor_unwrap_slot_endpoint_post_mods
