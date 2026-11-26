(* Transport the reached VV through the caller's ALLOCA and unwrap it
   at the actual successor cursor. *)
Theory bodyFullExtCallDefaultUnwrapMods
Ancestors
  bodyExtDefaultUnwrapIdentityMods bodyExtDefaultUnwrapSlotMods
  bodyExtDefaultUnwrapCodeMods bodyExtKeywordDefaultAllocResourcesMods
  bodyAttributeReadOperandMods bodyPtrMakeArrayExternalCaller
  assignBasePtrBoundary exprSimCopy exprSimMemDefs exprSimIfExpWidenedAdapter
  bodyFullPostsMods bodyFullShadowBodyInv bodyFullHashKeccakFixed
  loweringPosts bodyPtrDefs ptrDiscipline valueCopyBytes
  valueTypingMemoryProps vyperStorageFootprint stateRelProj
  exprLoweringProps exprOperandVar freshWrites compileEnv
  fragGasOriginPtr fragGasPathFrameMem loweringStateRelDefs
  venomMemDefs venomState context finite_map words arithmetic

Theorem unwrap_vv_cursor[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv u /\
  sm.cs_next_id <= sn.cs_next_id ==>
  vv_post_mods H ctx func ce cx e es sa sn s0 ee tv vv u
Proof
  disch_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  asm_rewrite_tac[vv_post_mods_def] >> conj_tac
  >- (irule vv_at_alloc_mono_frame >> qexistsl [`u`,`sm`] >> simp[]) >>
  strip_tac >> irule vv_own_alloc_mono_frame >> qexistsl [`u`,`sm`] >> simp[]
QED

Theorem unwrap_window_disjoint[local]:
  alloca_inv u /\ FLOOKUP u.vs_allocas dst = SOME (d,n) /\
  (!name b len. local_region ce ee.scopes u name b len ==>
    regions_disjoint d n b len) /\
  (f = 0 \/
   (?aid b len. aid <> dst /\ FLOOKUP u.vs_allocas aid = SOME (b,len) /\
      b <= i /\ i + f <= b + len) \/
   (?name b len. local_region ce ee.scopes u name b len /\
      b <= i /\ i + f <= b + len)) ==>
  f = 0 \/ regions_disjoint d n i f
Proof
  strip_tac >- simp[] >> disj2_tac >> pure_rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >-
    (fs[alloca_inv_def,allocas_non_overlapping_def] >>
     qpat_assum `!a1 a2 b1 sz1 b2 sz2. _ ==> _`
       (drule_all_then strip_assume_tac) >> decide_tac) >>
  qpat_assum `!name b len. local_region _ _ _ _ _ _ ==> _`
    (drule_then (strip_assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
  decide_tac
QED

Theorem extcall_default_unwrap_store_entry_mods:
  compile_expr cenv ty e sa = (vv,sm) /\
  unwrap_value cenv vv sn = (op,sc) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id < sn.cs_next_id /\
  fn_has_code sn sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~is_word_type (post_value_type cenv e) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv /\
  type_memory_bytes cenv (post_value_type cenv e) = type_memory_size ptv /\
  type_memory_size ptv < 2**64 /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
  type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
  (post_value_type cenv e = lowered_value_type cenv e \/
   is_bytestring_type (post_value_type cenv e) /\
   is_bytestring_type (lowered_value_type cenv e)) /\
  (!v. read_result cx tv ee = (INL v,ee) ==>
       value_has_type ptv v /\ value_has_type ltv v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  vv_post_mods (storage_trace_horizon ee.storage_trace)
    ctx func cenv cx e es sa sm s0 ee tv vv s /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv u /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee Ga ta u) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 ==> ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
       ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                 val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 Ga ta /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func u /\ lo <= s.vs_alloca_next /\
  s.vs_alloca_next <= u.vs_alloca_next /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
  u.vs_inst_idx = LENGTH sn.cs_current_insts /\
  u with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
            vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx |> = s /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Ga x = FLOOKUP G x /\ op_taint ta (Var x) = op_taint tn (Var x)) /\
  ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\
  not_fresh_at sn q /\ lookup_var q u = SOME dw /\ ptr_covers Ga ta q u n /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n dw,n) /\
  FLOOKUP Ga q = SOME (w2n dw,n) /\ w2n dw + n <= u.vs_alloca_next /\
  (!name b len. local_region cenv ee.scopes u name b len ==>
      regions_disjoint (w2n dw) n b len) ==>
  ?v z G' tn' sw.
    read_result cx tv ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Ga,ta) [] (OK z,G',tn') /\
       expr_post_mods H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' z) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    ghost_kept_at lo cenv ee sn Ga ta u G' tn' /\
    wb_frame cenv ee ee sn u z /\
    (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x u /\
         FLOOKUP G' x = FLOOKUP Ga x /\ op_taint tn' (Var x) = op_taint ta (Var x)) /\
    alloca_history func z /\ allocas_from lo z /\ lo <= z.vs_alloca_next /\
    u.vs_alloca_next <= z.vs_alloca_next /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    z.vs_alloca_next < dimword (:256) /\
    z.vs_labels = u.vs_labels /\ ~z.vs_halted /\
    z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    not_fresh_at sc q /\ lookup_var q z = SOME dw /\ ptr_covers G' tn' q z n /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,n) /\
    FLOOKUP G' q = SOME (w2n dw,n) /\ w2n dw + n <= z.vs_alloca_next /\
    (!name b len. local_region cenv ee.scopes z name b len ==>
       regions_disjoint (w2n dw) n b len) /\
    eval_operand op z = SOME sw /\
    (!x. op = Var x ==> not_fresh_at sc x) /\
    ptr_mem_ok cx (post_value_type cenv e) v op G' tn' z /\
    value_has_type ltv v /\ val_wf ltv v /\
    (!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
         val_in_memory ltv v (w2n sw) mem) /\
    (type_memory_size ltv <> 0 ==>
       (?x. op = Var x /\ ptr_covers G' tn' x z (type_memory_size ltv)) /\
       w2n sw + type_memory_size ltv <= z.vs_alloca_next) /\
    (val_footprint ptv v = 0 \/
     regions_disjoint (w2n dw) n (w2n sw) (val_footprint ptv v))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `?v. read_result cx tv ee = (INL v,ee)` by
    (qpat_assum `vv_post_mods H0 _ _ _ _ _ _ _ _ _ _ _ _ u`
      (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule_then (qx_choosel_then [`v`,`w`] strip_assume_tac) attribute_read_operand_mods >>
     qexists `v` >> first_assum ACCEPT_TAC) >>
  `u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels` by
    (qpat_assum `u with <| vs_vars := _; vs_allocas := _;
                          vs_alloca_next := _; vs_inst_idx := _ |> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
   op_prov Ga (vv_operand vv) = op_prov G (vv_operand vv) /\
   op_taint ta (vv_operand vv) = op_taint tn (vv_operand vv)` by
    (Cases_on `vv_operand vv` >> simp[eval_operand_def,op_prov_def,op_taint_def] >>
     metis_tac[]) >>
  `value_has_type ptv v` by simp[] >>
  drule_all_then (map_every assume_tac o CONJUNCTS)
    ext_kw_default_alloc_unwrap_resources_mods >>
  `sm.cs_next_id <= sn.cs_next_id /\ sa.cs_next_id <= sn.cs_next_id /\
   sa.cs_next_var <= sn.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv sn` by
    (irule local_ptrs_reserved_next_var >> qexists `sm` >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sn x` by
    metis_tac[not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func cenv cx e es sa sn s0 ee tv vv u /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee Ga ta u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     conj_tac >- (irule unwrap_vv_cursor >> qexists `sm` >> asm_rewrite_tac[]) >>
     first_assum ACCEPT_TAC) >>
  `sn.cs_next_var <= sc.cs_next_var` by
    (qspecl_then [`cenv`,`vv`,`sn`] mp_tac ci_mono_unwrap_value >> simp[ci_mono_def]) >>
  `!x. op = Var x ==> not_fresh_at sc x` by
    (`(case vv of StackValue _ a => !x. a = Var x ==> not_fresh_at sn x
                 | LocatedValue _ p => !x. p.ptr_operand = Var x ==> not_fresh_at sn x)` by
        (Cases_on `vv` >> fs[vv_operand_def]) >>
     rpt strip_tac >> drule_all_then ACCEPT_TAC compiler_unwrap_value_var) >>
  Q.SUBGOAL_THEN `?z Gf tf sw.
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Ga,ta) [] (OK z,Gf,tf) /\
        expr_post_mods H ctx func cenv cx e es sa sc s0 ee v op z /\
        ghost_inv_at_mods (DF H) lo d cenv cx ee Gf tf z) /\
     ghost_kept_at lo cenv es sa Gi ti s0 Gf tf /\
     ghost_kept_at lo cenv ee sn Ga ta u Gf tf /\ wb_frame cenv ee ee sn u z /\
     (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x u /\
       FLOOKUP Gf x = FLOOKUP Ga x /\ op_taint tf (Var x) = op_taint ta (Var x)) /\
     (!aid row. FLOOKUP u.vs_allocas aid = SOME row ==> FLOOKUP z.vs_allocas aid = SOME row) /\
     alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
     z.vs_labels = u.vs_labels /\ ~z.vs_halted /\
     z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
     eval_operand op z = SOME sw /\ ptr_val_ok cx (post_value_type cenv e) v op Gf tf z /\
     ptr_buf_ok cenv e op Gf z /\
     (type_memory_size ltv <> 0 ==> w2n sw + type_memory_size ltv <= z.vs_alloca_next) /\
     (val_footprint ptv v = 0 \/
       (?aid b len. aid <> sm.cs_next_id /\ FLOOKUP z.vs_allocas aid = SOME (b,len) /\
         b <= w2n sw /\ w2n sw + val_footprint ptv v <= b + len) \/
       (?name b len. local_region cenv ee.scopes z name b len /\
         b <= w2n sw /\ w2n sw + val_footprint ptv v <= b + len))`
    (qx_choosel_then [`z`,`Gf`,`tf`,`sw`] (map_every assume_tac o CONJUNCTS))
  >- suspend "branches" >>
  suspend "store_entry"
QED

Resume extcall_default_unwrap_store_entry_mods[branches]:
  Cases_on `(?tag x. vv = StackValue tag x) \/
    (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory)`
  >- suspend "identity" >>
  `?tag p. vv = LocatedValue tag p /\ p.ptr_location <> LocMemory` by
    (Cases_on `vv` >> fs[]) >>
  qpat_x_assum `~((?tag x. _) \/ _)` kall_tac >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  `p.ptr_location <> LocCalldata` by
    (qpat_assum `vv_post_mods H0 _ _ _ _ _ _ _ sm _ _ _ _ u`
       (mp_tac o REWRITE_RULE [vv_post_mods_def]) >>
     Cases_on `p.ptr_location` >> simp[vv_holds_mods_def,vv_holds_def]) >>
  `post_value_type cenv e = lowered_value_type cenv e` by
    (drule_all external_located_lowered_type >> simp[post_value_type_lowered]) >>
  `ltv = ptv` by fs[] >>
  qpat_x_assum `ltv = ptv` SUBST_ALL_TAC >>
  Cases_on `p.ptr_location = LocCode` >- suspend "code" >>
  Q.SUBGOAL_THEN `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` assume_tac
  >- (Cases_on `p.ptr_location` >> fs[]) >>
  suspend "slot"
QED

Resume extcall_default_unwrap_store_entry_mods[identity]:
  drule_all default_unwrap_identity_prefix_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`a`,`sw`] (map_every assume_tac o CONJUNCTS))))) >>
  `a = v` by fs[] >> qpat_x_assum `a = v` SUBST_ALL_TAC >>
  `ptr_buf_ok cenv e op Ga u` by
    (qpat_assum `op = vv_operand vv` SUBST1_TAC >>
     qpat_assum `(?tag x. vv = StackValue tag x) \/ _` strip_assume_tac >>
     fs[vv_operand_def]) >>
  `type_memory_size ltv <> 0 ==> w2n sw + type_memory_size ltv <= u.vs_alloca_next` by
    (qpat_x_assum `eval_operand (vv_operand vv) u = eval_operand _ s` kall_tac >>
     qpat_x_assum `vv_store_bound _ _ _ _ _ _ u`
       (mp_tac o cj 2 o REWRITE_RULE [vv_store_bound_def]) >>
     qpat_assum `op = vv_operand vv` SUBST_ALL_TAC >>
     qpat_assum `(?tag x. vv = StackValue tag x) \/ _` strip_assume_tac >>
     fs[vv_operand_def] >>
     disch_then (qspec_then `sw` mp_tac) >> simp[]) >>
  qpat_x_assum `!name b len. local_region cenv ee.scopes u name b len <=> _` kall_tac >>
  qexistsl [`u`,`Ga`,`ta`,`sw`] >> asm_rewrite_tac[] >> simp[] >>
  qpat_x_assum `val_footprint ptv v = 0 \/ _` strip_assume_tac
  >- simp[]
  >- (disj2_tac >> disj1_tac >> qexistsl [`aid`,`b`,`len`] >> simp[] >> decide_tac) >>
  disj2_tac >> disj2_tac >> qexistsl [`name`,`b`,`len`] >> fs[]
QED

(* The source allocation was made at sn, strictly after the destination. *)
val finish_materialized_unwrap =
  `a = v` by fs[] >> qpat_x_assum `a = v` SUBST_ALL_TAC >>
  qpat_x_assum `op = Var root` kall_tac >>
  `val_footprint ptv v <= type_memory_size ptv` by simp[exprSimPropsTheory.val_footprint_le] >>
  qexistsl [`z`,`Gf`,`tf`,`sw`] >> asm_rewrite_tac[] >>
  disj2_tac >> disj1_tac >> qexistsl [`sn.cs_next_id`,`w2n sw`,`type_memory_size ptv`] >>
  asm_rewrite_tac[] >> decide_tac;

Resume extcall_default_unwrap_store_entry_mods[code]:
  `cenv.ce_is_ctor ==> ?val. read_result cx tv ee = (INL val,ee) /\
     !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
            eval_operand p.ptr_operand u = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside ta.t_mem u.vs_memory mem ==>
         val_in_memory rt val (w2n w) mem)` by
    (qpat_assum `cenv.ce_is_ctor /\ _ ==> ?a. _ /\ !rt w. _ /\ eval_operand _ u = _ ==> _`
       mp_tac >> simp[NoAsms,vv_location_def,vv_operand_def] >>
     qpat_assum `p.ptr_location = LocCode` SUBST1_TAC >> simp[NoAsms]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sn x` by fs[vv_operand_def] >>
  `type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_size ptv` by simp[] >>
  drule_all (Q.INST [`sm` |-> `sn`, `s` |-> `u`, `G` |-> `Ga`, `tn` |-> `ta`]
    default_unwrap_code_prefix_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`a`,`z`,`Gf`,`tf`,`root`,`sw`] (map_every assume_tac o CONJUNCTS))) >>
  finish_materialized_unwrap
QED

Resume extcall_default_unwrap_store_entry_mods[slot]:
  drule_all (Q.INST [`s` |-> `u`, `G` |-> `Ga`, `tn` |-> `ta`]
    default_unwrap_slot_prefix_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`a`,`z`,`Gf`,`tf`,`sw`,`root`] (map_every assume_tac o CONJUNCTS))) >>
  finish_materialized_unwrap
QED

Resume extcall_default_unwrap_store_entry_mods[store_entry]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
    (qspec_then `H0` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `stmt_state_rel H0 ctx func cenv cx ee z` by
    (qpat_assum `expr_post_mods H0 _ _ _ _ _ _ _ _ _ _ _ _ z`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
     first_assum ACCEPT_TAC) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  `z.vs_alloca_next < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >> disch_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt)) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `s0.vs_alloca_next <= z.vs_alloca_next /\ w2n dw + n <= z.vs_alloca_next` by decide_tac >>
  `not_fresh_at sc q` by
    (irule not_fresh_at_mono >> qexists `sn` >> simp[]) >>
  qpat_assum `!x. not_fresh_at sn x ==> lookup_var x z = _ /\ _`
    (qspec_then `q` (drule_then strip_assume_tac)) >>
  `ptr_covers Gf tf q z n` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >> qexistsl [`Ga`,`u`,`ta`] >> simp[]) >>
  `FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,n)` by
    (qpat_assum `!aid row. FLOOKUP u.vs_allocas aid = SOME row ==> _` irule >> simp[]) >>
  `!name b len. local_region cenv ee.scopes z name b len ==>
     regions_disjoint (w2n dw) n b len` by
    (qpat_x_assum `!name b len. local_region cenv ee.scopes u name b len <=> _` kall_tac >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!name b len. local_region cenv ee.scopes u name b len ==> _` irule >>
     qexists `name` >>
     `!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x u` by simp[] >>
     drule_all copy_buffer_local_region_frame >>
     disch_then (qspecl_then [`ee.scopes`,`name`,`b`,`len`] mp_tac) >> simp[]) >>
  `ptr_mem_ok cx (post_value_type cenv e) v op Gf tf z /\ op_taint tf op = {}` by
    fs[ptr_val_ok_def] >>
  `value_has_type ltv v` by simp[] >>
  `val_wf ltv v` by simp[value_has_type_memory_wf] >>
  qexistsl [`v`,`z`,`Gf`,`tf`,`sw`] >> asm_rewrite_tac[] >>
  conj_tac >- suspend "layout" >>
  conj_tac >- suspend "capacity" >>
  suspend "separation"
QED

Resume extcall_default_unwrap_store_entry_mods[layout]:
  gen_tac >> disch_tac >>
  `val_in_memory ptv v (w2n sw) mem` by
    (qpat_assum `ptr_mem_ok _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
     disch_then (qspecl_then [`ptv`,`sw`] mp_tac) >> simp[]) >>
  qpat_x_assum `post_value_type cenv e = lowered_value_type cenv e \/ _` strip_assume_tac
  >- (fs[]) >>
  irule bytestring_val_in_memory_transfer >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`post_value_type cenv e`,`lowered_value_type cenv e`,`get_tenv cx`,`ptv`] >>
  asm_rewrite_tac[]
QED

Resume extcall_default_unwrap_store_entry_mods[capacity]:
  strip_tac >> conj_tac
  >- (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
      conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- (qexists `sw` >> simp[]) >>
      qexistsl [`cenv`,`e`] >> simp[GSYM NOT_ZERO_LT_ZERO]) >>
  simp[]
QED

Resume extcall_default_unwrap_store_entry_mods[separation]:
  irule unwrap_window_disjoint >> qexistsl [`cenv`,`sm.cs_next_id`,`ee`,`z`] >>
  asm_rewrite_tac[]
QED

Finalise extcall_default_unwrap_store_entry_mods
