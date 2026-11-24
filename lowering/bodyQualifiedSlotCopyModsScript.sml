(* The allocated part of a qualified storage/transient read. *)
Theory bodyQualifiedSlotCopyMods
Ancestors
  bodyFullPostsMods bodyFullToplevelSlotForce bodyFullUnwrapSlotOrigin
  bodyFullUnwrapSlotPost exprPtrUnwrapAllocSemantic exprPtrUnwrapAllocSeparation
  exprPtrUnwrapStoragePost exprPtrUnwrapRetained exprPtrUnwrapAllocationFrame
  exprSimPtrTopLevelStorageCopy exprSimStorageCopy exprPtrUnwrapRuntimeFrame
  assignTuplePtrAlloc bodyPtrBytestringBuiltinsAllocation
  exprPtrUnwrapEnsureShape fragGasOriginPtrDead loweringSlice
  exprSimVVFrame bodyFullHashKeccakFixed exprSimCopy bodyInvSplit
  exprLoweringProps venomInst loweringStateRelDefs bodyFullShadowBodyInv
  bodyPtrDefs ptrDiscipline exprSimProps finite_map pred_set
  bufferAllocationExecution venomExecSemantics compileEnv words arithmetic
  loweringPosts localPtrsProps slotCopyExecution venomState
  exprSimAbiEncodeMemoryLength exprPtrUnwrapAllocation exprSimAlloc
  exprPtrUnwrapAllocEntry frameActivationSeparation loweringHalt
  exprSimMemorySource context copyExecution emitHelper
  exprLowering valueEncodingProps vyperStorageFootprint exprSimUnwrap
  vyperState vyperAST exprPtrUnwrapStorageSource exprSimFieldLayout exprSimMemDefs
  storageNormalizationOwnershipPtr exprSimUnwrapProps venomMemDefs[qualified]
Libs
  dep_rewrite

Theorem slot_copy_immutable_frame[local]:
  immutable_frame_mods func cenv cx ee s /\
  exec_alloca (mk_inst aid ALLOCA [Lit (n2w nb)] [root]) s (n2w nb : bytes32) = OK u /\
  MEM (mk_inst aid ALLOCA [Lit (n2w nb)] [root]) (fn_insts func) /\
  FLOOKUP u.vs_allocas aid = SOME (dst,nb) /\
  z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next /\
  z.vs_data_section = s.vs_data_section /\ LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  (!src id b len. local_region (cenv with ce_module := src) ee.scopes u id b len ==>
    local_region (cenv with ce_module := src) ee.scopes s id b len) /\
  (!src id b len. local_region (cenv with ce_module := src) ee.scopes z id b len ==>
    local_region (cenv with ce_module := src) ee.scopes u id b len) /\
  (!off len. off+len <= dst \/ dst+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  immutable_frame_mods func cenv cx ee z
Proof
  strip_tac >>
  `immutable_alloca_sep_mods func cenv cx ee u` by
    (fs[immutable_frame_mods_def, immutable_alloca_sep_mods_def] >>
     rpt strip_tac >> irule immutable_alloca_sep_exec_alloca >>
     qexistsl [`mk_inst aid ALLOCA [Lit (n2w nb)] [root]`, `n2w nb : bytes32`, `s`] >>
     asm_rewrite_tac[] >> conj_tac
     >- (rpt strip_tac >> qexists `id` >> metis_tac[]) >>
     metis_tac[]) >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt strip_tac >> irule immutables_rel_mem_agree >> qexists `s` >> simp[] >>
      rpt strip_tac >> first_x_assum irule >>
      `immutable_alloca_sep func (cenv with ce_module := src) cx ee u` by metis_tac[] >>
      fs[immutable_alloca_sep_def] >>
      qpat_x_assum `cenv.ce_is_ctor ==> !name tv v off. _` mp_tac >>
      asm_rewrite_tac[] >>
      disch_then (qspecl_then [`name`, `tv`, `v`, `off`] mp_tac) >>
      asm_rewrite_tac[] >> strip_tac >>
      qpat_x_assum `!inst b sz. MEM _ _ /\ _ ==> regions_disjoint _ _ _ _`
        (qspecl_then [`mk_inst aid ALLOCA [Lit (n2w nb)] [root]`, `dst`, `nb`] mp_tac) >>
      simp[mk_inst_def, regions_disjoint_def]) >>
  rpt strip_tac >> irule immutable_alloca_sep_fields >>
  qexistsl [`u`, `ee`] >> simp[] >> metis_tac[]
QED

Theorem slot_copy_local_robust[local]:
  val_wf tv v /\ val_footprint tv v <= len /\
  mem_bytes_at b len z.vs_memory = mem_bytes_at b len s.vs_memory /\
  (!j. b <= j /\ j < b+len /\ j IN tf.t_mem ==> j IN tn.t_mem) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v b m) ==>
  !m. mem_agree_outside tf.t_mem z.vs_memory m ==> val_in_memory tv v b m
Proof
  strip_tac >> rpt gen_tac >> disch_tac >>
  qabbrev_tac `extra = tn.t_mem UNION (tf.t_mem DIFF {j | b <= j /\ j < b+len})` >>
  irule robustCopyTransportPtrTheory.robust_val_in_memory_copy_transport >>
  simp[] >> qexistsl [`s.vs_memory`, `z.vs_memory`, `len`, `b`, `tn.t_mem`, `extra`] >>
  simp[] >> conj_tac
  >- (simp[Abbr `extra`] >> rpt strip_tac >> decide_tac) >>
  fs[mem_agree_outside_def, Abbr `extra`] >> rpt strip_tac >>
  first_x_assum irule >> Cases_on `b <= i /\ i < b+len` >> gvs[] >> metis_tac[]
QED

Theorem slot_copy_linked_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx ee G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  local_ptrs_rel func cenv ee.scopes s /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
    dst+nb <= b \/ b+len <= dst) /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!off len. off+len <= dst \/ dst+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!j. j < dst \/ dst+nb <= j ==> (j IN tf.t_mem ==> j IN tn.t_mem)) /\
  lo <= dst /\ stor_taint_ok_at D tf z /\ allocas_from lo z /\ lo <= z.vs_alloca_next ==>
  ghost_inv_at_mods D lo d cenv cx ee Gf tf z
Proof
  strip_tac >>
  `mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (first_x_assum irule >> simp[]) >>
  fs[ghost_inv_at_mods_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
      conj_tac >- (fs[ptr_covers_def] >> metis_tac[]) >>
      rpt strip_tac >> `lookup_var p s = SOME w` by metis_tac[] >>
      `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
        (fs[local_ptrs_rel_def] >> metis_tac[]) >>
      `local_region cenv ee.scopes s name (w2n w) sz` by (simp[local_region_def] >> metis_tac[]) >>
      `dst+nb <= w2n w \/ w2n w+sz <= dst` by metis_tac[] >>
      (`val_footprint entry.type entry.value <= sz` by
         (irule LESS_EQ_TRANS >> qexists `type_memory_size entry.type` >> simp[val_footprint_le]) >>
       `mem_bytes_at (w2n w) sz z.vs_memory = mem_bytes_at (w2n w) sz s.vs_memory` by
         (qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _` irule >> decide_tac) >>
       `!j. w2n w <= j /\ j < w2n w+sz /\ j IN tf.t_mem ==> j IN tn.t_mem` by
         (qx_gen_tac `j` >> strip_tac >>
          qpat_assum `!j. j < dst \/ dst+nb <= j ==> _`
            (irule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >> simp[] >> decide_tac) >>
       irule slot_copy_local_robust >> simp[] >>
       qexistsl [`sz`, `s`, `tf`, `tn`, `z`] >> simp[] >> metis_tac[]))
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME arg) cenv Gf tf z` >> PairCases_on `arg` >>
      gvs[return_buf_ptr_def, ptr_covers_def] >> metis_tac[])
  >> rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]
QED

(* Project the counted loop and the one-word copy to the same effect interface. *)
Theorem slot_copy_effects[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  (n <> 1 ==> ?cv ds.
     toplevel_copy_inv cv ds root src loc key (w2n w) n a G0 tn0 n Gf tf z /\
     (!x. not_fresh_at mid x ==> ~MEM x ds)) /\
  (n = 1 ==>
     z = (mstore (w2n w) (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a key)
       (update_var (STRING #"%" (toString mid.cs_next_var))
         (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a key) a)
           with vs_inst_idx := k) /\
     tf.t_mem = (tn0.t_mem DIFF {j | w2n w <= j /\ j < w2n w+32}) UNION
       {w2n w+b | b IN key_taint (if loc=LocStorage then tn0.t_stor else tn0.t_trans) key} /\
     tf.t_stor = tn0.t_stor /\ tf.t_trans = tn0.t_trans /\ tf.t_imm = tn0.t_imm /\
     (!x. x <> STRING #"%" (toString mid.cs_next_var) ==>
        FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x))) ==>
  copy_static z = copy_static a /\
  LENGTH a.vs_memory <= LENGTH z.vs_memory /\
  (!off len. off+len <= w2n w \/ w2n w+32*n <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory) /\
  (!x. not_fresh_at mid x ==>
    lookup_var x z = lookup_var x a /\ FLOOKUP Gf x = FLOOKUP G0 x /\
    op_taint tf (Var x) = op_taint tn0 (Var x)) /\
  (!j. j < n ==> mem_word_at (w2n w+32*j) z.vs_memory =
    slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a (key+n2w j)) /\
  (!j b. j < n /\ b < 32 /\ w2n w+32*j+b IN tf.t_mem ==>
    b IN key_taint (if loc=LocStorage then tn0.t_stor else tn0.t_trans) (key+n2w j)) /\
  (!q. q < w2n w \/ w2n w+32*n <= q ==> q IN tf.t_mem ==> q IN tn0.t_mem) /\
  tf.t_stor = tn0.t_stor /\ tf.t_trans = tn0.t_trans /\ tf.t_imm = tn0.t_imm
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> Cases_on `n = 1`
  >- suspend "single" >> suspend "loop"
QED

Resume slot_copy_effects[single]:
  qpat_x_assum `loc = LocStorage \/ loc = LocTransient` kall_tac >>
  qpat_x_assum `(_ = 1 ==> _)` (drule_then strip_assume_tac) >> gvs[] >>
  `!x. not_fresh_at mid x ==> x <> STRING #"%" (toString mid.cs_next_var)` by
    simp[not_fresh_at_def] >>
  rpt conj_tac
  >- simp[copy_static_def, mstore_def, write_memory_with_expansion_def, update_var_def]
  >- (qmatch_goalsub_abbrev_tac `mstore off v r` >>
      mp_tac (Q.INST [`s` |-> `r`, `off` |-> `off`, `w` |-> `v`]
        abi_encode_mstore_memory_length) >> simp[Abbr `r`, update_var_def])
  >- (rpt gen_tac >> disch_tac >> dep_rewrite.DEP_REWRITE_TAC [mstore_mem_bytes_at_disjoint] >>
      conj_tac >- decide_tac >> simp[update_var_def])
  >- (rpt strip_tac >> simp[mstore_def, write_memory_with_expansion_def,
        update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[])
  >- simp[mstore_mem_word_at_same, WORD_ADD_0]
  >- (simp[WORD_ADD_0] >> metis_tac[]) >>
  rpt strip_tac >> gvs[key_taint_def] >> decide_tac
QED

Resume slot_copy_effects[loop]:
  qpat_x_assum `(_ <> 1 ==> _)` (drule_then strip_assume_tac) >>
  drule toplevel_copy_inv_content >>
  disch_then (strip_assume_tac o REWRITE_RULE [storage_copy_inv_def, copy_prefix_def]) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (fs[toplevel_copy_inv_def, storage_copy_frame_def] >> metis_tac[])
  >- (rpt strip_tac >>
      `mem_word_at (w2n w+32*j) z.vs_memory = copy_runtime_word loc a (key+n2w j)` by metis_tac[] >>
      Cases_on `loc=LocStorage` >> gvs[copy_runtime_word_def, slot_copy_word_def])
  >- suspend "loop_taint"
  >- (rpt strip_tac >> drule toplevel_copy_inv_memory_taint >>
      simp[toplevel_copy_taint_bound_def, toplevel_copy_region_def,
           toplevel_copy_translated_taint_def, SUBSET_DEF] >>
      disch_then (qspec_then `q` mp_tac) >> simp[] >> strip_tac >> gvs[] >> decide_tac) >>
  fs[toplevel_copy_inv_def]
QED

Resume slot_copy_effects[loop_taint]:
  rpt strip_tac >> drule toplevel_copy_inv_memory_taint >>
  simp[toplevel_copy_taint_bound_def, toplevel_copy_region_def,
       toplevel_copy_translated_taint_def, SUBSET_DEF] >>
  disch_then (qspec_then `w2n w+32*j+b` mp_tac) >>
  `w2n w <= w2n w+32*j+b /\ w2n w+32*j+b < w2n w+32*n` by decide_tac >>
  simp[] >> strip_tac >>
  rename1 `(key+n2w i,r) IN toplevel_copy_source_taint loc ts` >>
  `i = j /\ r = b` by intLib.COOPER_TAC >>
  qpat_x_assum `(key+n2w i,r) IN _` mp_tac >>
  simp[key_taint_def, toplevel_copy_source_taint_def]
QED

Finalise slot_copy_effects[local]

Theorem slot_copy_id_advances[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
  compile_alloc_buffer nb sa = (buf,mid) ==> sa.cs_next_id < sb.cs_next_id
Proof
  strip_tac >>
  fs[compile_ensure_in_memory_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `n = 1` >>
  gvs[compile_storage_to_memory_def, compile_transient_to_memory_def,
      GSYM compile_slot_to_memory_def, compile_slot_to_memory_shape,
      slot_copy_final_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, emit_def, fresh_var_def, fresh_id_def,
      compile_alloc_buffer_def] >> pairarg_tac >> gvs[]
QED

Theorem slot_vv_post_plain[local]:
  vv_post_mods H ctx func cenv cx e es sa sa s ee tv
    (LocatedValue t (mk_ptr (Lit key) (slot_loc tr))) s ==>
  vv_post H ctx func cenv cx e es sa sa s ee tv
    (LocatedValue t (mk_ptr (Lit key) (slot_loc tr))) s
Proof
  Cases_on `tr` >> simp[vv_post_mods_def, vv_post_def, vv_holds_mods_def,
      vv_place_ptr_mods_def, slot_loc_def, mk_ptr_def, AllCaseEqs()] >>
  Cases_on `tv` >> simp[] >> Cases_on `p` >> simp[vv_place_ptr_def]
QED

Theorem qualified_slot_copy_read_mods:
  ~is_word_type ann /\
  evaluate_type (get_tenv cx) ann = SOME rt /\
  type_memory_bytes cenv ann = type_memory_size rt /\
  type_memory_size rt < 2**64 /\
  compile_expr cenv ty (TopLevelName ann key) sa =
    (LocatedValue ann (mk_ptr (Lit slot) (slot_loc tr)),sa) /\
  unwrap_value cenv (LocatedValue ann (mk_ptr (Lit slot) (slot_loc tr))) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func cenv cx (TopLevelName ann key) es sa sa s0 ee tv
      (LocatedValue ann (mk_ptr (Lit slot) (slot_loc tr))) s0 /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G0 tn0 s0) /\
  storage_holds cx tr ann tv slot ee s0 /\
  ptr_vv_ok cx ann tv (LocatedValue ann (mk_ptr (Lit slot) (slot_loc tr))) ee G0 tn0 s0 /\
  alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z Gf tf. read_result cx tv ee = (INL v,ee) /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) [] (OK z,Gf,tf) /\
      expr_post_mods H ctx func cenv cx (TopLevelName ann key) es sa sb s0 ee v op z /\
      expr_store_bound cx ann v op z /\
      z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      s0.vs_alloca_next <= z.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee Gf tf z /\
      ptr_val_ok cx ann v op Gf tf z /\ ptr_buf_ok cenv (TopLevelName ann key) op Gf z /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[storage_trace_domain_def, Abbr `H0`] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx (TopLevelName ann key) es sa sa s0 ee tv
      (LocatedValue ann (mk_ptr (Lit slot) (slot_loc tr))) s0 /\
    stmt_state_rel H ctx func cenv cx ee s0` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (drule_then strip_assume_tac) >> metis_tac[slot_vv_post_plain, vv_post_mods_def]) >>
  `stmt_state_rel H0 ctx func cenv cx ee s0` by metis_tac[] >>
  `immutable_frame_mods func cenv cx ee s0 /\ allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> fs[vv_post_mods_def, ghost_inv_at_mods_def]) >>
  qabbrev_tac `n = type_slot_size rt` >> qabbrev_tac `nb = type_memory_size rt` >>
  `nb = 32*n /\ (nb+31) DIV 32 = n` by
    simp[Abbr `n`, Abbr `nb`, type_memory_size_slots, slot_count_of_memory_size] >>
  `nb < dimword (:256) /\ n < 2**256 /\ 32*n <= nb` by (fs[dimword_def] >> decide_tac) >>
  `compile_ensure_in_memory (Lit slot) (slot_loc tr) nb n
    cenv.ce_is_ctor cenv.ce_imm_alloca sa = (op,sb)` by
    (qpat_x_assum `nb = 32*n` kall_tac >>
     qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >> Cases_on `tr` >>
     simp[slot_loc_def, mk_ptr_def, unwrap_value_def]) >>
  Q.SUBGOAL_THEN `slot_loc tr = LocStorage \/ slot_loc tr = LocTransient` assume_tac
  >- (Cases_on `tr` >> simp[slot_loc_def]) >>
  `eval_operand (Lit slot) s0 = SOME slot /\ op_taint tn0 (Lit slot) = {} /\
    (!x. Lit slot = Var x ==> not_fresh_at sa x)` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all unwrap_ensure_slot_origin_execution >>
  disch_then (qspecl_then [`explicit`, `PG`, `G0`]
    (qx_choosel_then [`root`,`w`,`a`,`Ga`,`ta`,`Gf`,`tf`,`z`,`mid`,`buf`,`u`] strip_assume_tac)) >>
  suspend "effects"
QED

Resume qualified_slot_copy_read_mods[effects]:
  `copy_static z = copy_static a /\ LENGTH a.vs_memory <= LENGTH z.vs_memory /\
   (!off len. off+len <= w2n w \/ w2n w+32*n <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory) /\
   (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x a /\
     FLOOKUP Gf x = FLOOKUP Ga x /\ op_taint tf (Var x) = op_taint ta (Var x)) /\
   (!j. j < n ==> mem_word_at (w2n w+32*j) z.vs_memory =
      slot_copy_word (if slot_loc tr=LocStorage then SLOAD else TLOAD) a (slot+n2w j)) /\
   (!j b. j < n /\ b < 32 /\ w2n w+32*j+b IN tf.t_mem ==>
     b IN key_taint (if slot_loc tr=LocStorage then ta.t_stor else ta.t_trans) (slot+n2w j)) /\
   (!q. q < w2n w \/ w2n w+32*n <= q ==> q IN tf.t_mem ==> q IN ta.t_mem) /\
   tf.t_stor = ta.t_stor /\ tf.t_trans = ta.t_trans /\ tf.t_imm = ta.t_imm` by
    (irule slot_copy_effects >>
     conj_tac >- (qexistsl [`root`,`Lit slot`] >> metis_tac[]) >>
     conj_tac >- (qexists `LENGTH sb.cs_current_insts` >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  drule_all unwrap_alloc_semantic_frames >> strip_tac >>
  `copy_static z = copy_static u /\ a.vs_memory = u.vs_memory /\
   (!x. lookup_var x a = lookup_var x u)` by simp[copy_static_def, lookup_var_def] >>
  `sa.cs_next_id < sb.cs_next_id` by (drule_all slot_copy_id_advances >> simp[]) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `not_fresh_at mid root /\ (!x. not_fresh_at sa x ==> x <> root /\ not_fresh_at mid x)` by
    (rpt strip_tac >> metis_tac[operand_11]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by
    (drule_all buffer_alloc_code >> simp[NoAsms] >>
     `root = STRING #"%" (toString sa.cs_next_var)` by metis_tac[operand_11] >> simp[]) >>
  drule_all alloca_step_exterior_ghost_ptr >>
  qpat_assum `Ga = _` (fn gth => qpat_assum `ta = _` (fn tth =>
    disch_then (qspecl_then [`tn0`,`PG`,`G0`]
      (strip_assume_tac o PURE_REWRITE_RULE [GSYM gth,GSYM tth])))) >>
  suspend "physical"
QED

Resume qualified_slot_copy_read_mods[physical]:
  drule_at (Pat `copy_static z = copy_static u`) copy_static_fields >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s0 /\
    FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> x <> root /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at mid x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. x <> root ==> _` (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  `LENGTH s0.vs_memory <= LENGTH z.vs_memory` by
    (qpat_assum `LENGTH a.vs_memory <= LENGTH z.vs_memory` mp_tac >>
     qpat_assum `a.vs_memory = u.vs_memory` (rewrite_tac o single) >>
     qpat_assum `u.vs_memory = s0.vs_memory` (rewrite_tac o single) >> simp[]) >>
  `!off len. off+len <= w2n w \/ w2n w+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s0.vs_memory` by
    (qpat_assum `nb = 32*n` SUBST1_TAC >>
     qpat_assum `u.vs_memory = s0.vs_memory` (SUBST1_TAC o SYM) >>
     qpat_assum `a.vs_memory = u.vs_memory` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `!q. q < w2n w \/ w2n w+nb <= q ==> q IN tf.t_mem ==> q IN tn0.t_mem` by
    (rpt gen_tac >> disch_tac >> disch_tac >>
     `q IN ta.t_mem` by
       (qpat_assum `!q. _ ==> q IN tf.t_mem ==> q IN ta.t_mem`
          (qspec_then `q` irule) >>
        qpat_assum `nb = 32*n` (SUBST1_TAC o SYM) >> asm_rewrite_tac[]) >>
     `~(w2n w <= q /\ q < w2n w+nb)` by decide_tac >>
     qpat_assum `!i. ~(_ <= i /\ _) ==> _` (drule_then mp_tac) >>
     asm_rewrite_tac[]) >>
  `exec_alloca (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s0
    (n2w nb : bytes32) = OK u` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def]) >>
  `allocas_from lo z /\ lo <= w2n w /\ lo <= z.vs_alloca_next` by
    (`allocas_from lo u` by
       (irule (INST_TYPE [alpha |-> ``:256``] allocas_from_exec_alloca) >>
        qexistsl [`mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]`, `n2w nb : bytes32`, `s0`] >>
        asm_rewrite_tac[]) >>
     conj_tac >- (qpat_assum `z.vs_allocas = u.vs_allocas` (fn th => rewrite_tac[allocas_from_def,th]) >>
                  qpat_assum `allocas_from lo u` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
     conj_tac >- (qpat_assum `allocas_from lo u` (irule o REWRITE_RULE [allocas_from_def]) >>
                  qexistsl [`sa.cs_next_id`, `nb`] >> first_assum ACCEPT_TAC) >>
     decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (strip_tac >> qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ u` kall_tac >>
     drule_all unwrap_alloc_below_fmp >>
     qpat_assum `copy_static z = copy_static u` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rw[copy_static_def, venom_state_component_equality, allocas_below_fmp_def]) >>
  `eval_operand op z = SOME w` by
    (`lookup_var root u = SOME w` by
       (qpat_assum `u = _` SUBST1_TAC >> simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
     qpat_assum `!x. not_fresh_at mid x ==> _` (drule_then strip_assume_tac) >> simp[eval_operand_def]) >>
  `ptr_covers Gf tf root z nb` by
    (`ptr_covers Ga ta root a nb` by (drule_all unwrap_alloc_output_coverage >> simp[]) >>
     qpat_assum `!x. not_fresh_at mid x ==> _` (drule_then strip_assume_tac) >>
     fs[ptr_covers_def] >> metis_tac[]) >>
  suspend "value"
QED

Resume qualified_slot_copy_read_mods[value]:
  `a.vs_accounts = s0.vs_accounts /\ a.vs_transient = s0.vs_transient /\
   a.vs_call_ctx = s0.vs_call_ctx /\
   ta.t_stor = tn0.t_stor /\ ta.t_trans = tn0.t_trans /\ ta.t_imm = tn0.t_imm` by
    simp[buffer_allocation_fields_frame, update_var_def, normalization_alloca_key_taints] >>
  `?v. read_result cx tv ee = (INL v,ee) /\
   !m. mem_agree_outside tf.t_mem z.vs_memory m ==> val_in_memory rt v (w2n w) m` by
    (irule unwrap_storage_copied_robust >>
     goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
     qexistsl [`tr`,`slot`] >>
     qpat_x_assum `!j. j < n ==> _` mp_tac >>
     qpat_x_assum `!j b. _ ==> b IN key_taint _ _` mp_tac >>
     Cases_on `tr` >> simp[slot_loc_def, mk_ptr_def, eval_operand_def,
       Abbr `n`, slot_copy_word_def, sload_def, tload_def, contract_transient_def, contract_storage_def]) >>
  `val_wf rt v /\ val_footprint rt v <= nb` by
    (drule_all storage_holds_value_bounds >> simp[]) >>
  `val_in_memory rt v (w2n w) z.vs_memory` by
    (qpat_assum `!m. mem_agree_outside _ _ m ==> _` irule >> simp[mem_agree_outside_def]) >>
  `ptr_val_ok cx ann v op Gf tf z /\ ptr_buf_ok cenv (TopLevelName ann key) op Gf z` by
    (qpat_assum `op = Var root` SUBST1_TAC >>
     irule (SRULE [post_value_type_def, lowered_value_type_def, expr_type_def]
       (Q.INST [`e` |-> `TopLevelName ann key`] unwrap_storage_pointer_posts)) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`nb`, `rt`, `w`] >>
     qpat_assum `op = Var root` (SUBST1_TAC o SYM) >>
     asm_rewrite_tac[] >> simp[Abbr `nb`]) >>
  `expr_store_bound cx ann v op z` by
    (`w2n w + nb <= z.vs_alloca_next` by
       (qpat_assum `stmt_state_rel H0 _ _ _ _ _ u` mp_tac >>
        qpat_assum `FLOOKUP u.vs_allocas sa.cs_next_id = _` mp_tac >>
        qpat_assum `z.vs_alloca_next = u.vs_alloca_next` SUBST1_TAC >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
             venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[ADD_COMM]) >>
     `val_store_size rt v <= nb` by (drule val_store_size_le >> simp[]) >>
     `w2n w + val_store_size rt v <= z.vs_alloca_next` by decide_tac >>
     pure_rewrite_tac[expr_store_bound_def] >>
     qpat_assum `eval_operand op z = SOME w` (pure_rewrite_tac o single) >>
     qpat_assum `evaluate_type (get_tenv cx) ann = SOME rt` (pure_rewrite_tac o single) >>
     pop_assum mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  suspend "semantic"
QED

Resume qualified_slot_copy_read_mods[semantic]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post H ctx func cenv cx (TopLevelName ann key) es sa sb s0 ee v op z` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ s0` kall_tac >>
     qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ u` kall_tac >>
     drule_all unwrap_alloc_semantic_frames >> strip_tac >>
     drule_all vv_post_read_result >> strip_tac >>
     drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ (Value v) _ _`)
       copy_buffer_post_transport_physical >>
     disch_then (irule o SRULE [post_value_type_def, lowered_value_type_def, expr_type_def]) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (decide_tac >> NO_TAC) >>
     TRY (qexists `mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]` >>
          simp[mk_inst_def] >> NO_TAC) >>
     suspend "semantic_alloc") >>
  suspend "linked"
QED

Resume qualified_slot_copy_read_mods[semantic_alloc]:
  qexistsl [`mid`, `nb`, `rt`, `u`, `w`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[] >> NO_TAC) >>
  rpt strip_tac >>
  qpat_assum `!x. not_fresh_at mid x ==> lookup_var x z = _ /\ _` drule >> simp[]
QED

Resume qualified_slot_copy_read_mods[linked]:
  `!scopes name b len.
    (local_region cenv scopes u name b len <=> local_region cenv scopes s0 name b len) /\
    (local_region cenv scopes z name b len <=> local_region cenv scopes s0 name b len)` by
    (rpt gen_tac >> conj_tac >> irule copy_buffer_local_region_frame >>
     qexists `sa` >> asm_rewrite_tac[] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x z = _ /\ _` (drule_then strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  `z.vs_data_section = s0.vs_data_section /\ z.vs_immutables = s0.vs_immutables` by
    (`z.vs_immutables = u.vs_immutables` by
       (qpat_assum `copy_static z = copy_static u` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[copy_static_def, venom_state_component_equality]) >>
     qpat_assum `u = update_var _ _ _` SUBST_ALL_TAC >>
     Cases_on `FLOOKUP s0.vs_allocas sa.cs_next_id` >>
     fs[buffer_allocation_fields_def, update_var_def]) >>
  `immutable_frame_mods func cenv cx ee z` by
    (irule slot_copy_immutable_frame >>
     qexistsl [`sa.cs_next_id`, `w2n w`, `nb`, `root`, `s0`, `u`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt gen_tac >>
     qpat_assum `!scopes name b len. (_ <=> _) /\ (_ <=> _)`
       (qspecl_then [`ee.scopes`,`id`,`b`,`len`] mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[local_region_def] >> metis_tac[]) >>
  `!name b len. local_region cenv ee.scopes s0 name b len ==>
      regions_disjoint (w2n w) nb b len` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name b len. local_region cenv ee.scopes u name b len ==> _` irule >>
     qexists `name` >> qpat_assum `!scopes name b len. (_ <=> _) /\ (_ <=> _)`
       (qspecl_then [`ee.scopes`,`name`,`b`,`len`] mp_tac) >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf` by
    (pure_rewrite_tac[ghost_kept_at_def] >> rpt conj_tac
     >- (rpt gen_tac >> disch_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x z = _ /\ _`
           (drule_then strip_assume_tac) >> asm_rewrite_tac[])
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> regions_disjoint _ _ _ _`
           (drule_all_then mp_tac) >> simp[regions_disjoint_def] >> strip_tac >>
         qpat_assum `!q. q < w2n w \/ _ ==> q IN tf.t_mem ==> _`
           (irule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >> simp[] >> decide_tac)
     >> rpt gen_tac >> strip_tac >>
     rename1 `local_region cenv es.scopes s0 name b sz` >>
     `local_region cenv ee.scopes s0 name b sz` by
       (irule local_region_frame_fwd >> qexistsl [`s0`,`sa`,`es.scopes`] >> simp[]) >>
     qpat_assum `!name b len. local_region cenv ee.scopes s0 name b len ==> _`
       (drule_then mp_tac) >> simp[regions_disjoint_def] >> strip_tac >>
     qpat_assum `!q. q < w2n w \/ _ ==> q IN tf.t_mem ==> _`
       (irule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >> simp[] >> decide_tac) >>
  `local_ptrs_rel func cenv ee.scopes s0` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ s0` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[stmt_state_rel_def, state_rel_def]) >>
  `z.vs_accounts = s0.vs_accounts /\ z.vs_transient = s0.vs_transient /\
   z.vs_call_ctx = s0.vs_call_ctx` by
    (qpat_assum `u = update_var _ _ _` SUBST_ALL_TAC >>
     simp[buffer_allocation_fields_frame, update_var_def]) >>
  qexistsl [`v`,`z`,`Gf`,`tf`] >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  simp[expr_post_mods_def] >> rpt conj_tac
  >- (irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC)
  >> irule slot_copy_linked_ghost >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ s0`
        (mp_tac o SRULE [ghost_inv_at_mods_def]) >>
      pure_rewrite_tac[stor_taint_ok_at_def] >> asm_rewrite_tac[] >> simp[]) >>
  qexistsl [`G0`,`w2n w`,`func`,`nb`,`s0`,`sa`,`tn0`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[GSYM regions_disjoint_def] >> first_assum ACCEPT_TAC
QED

Finalise qualified_slot_copy_read_mods
