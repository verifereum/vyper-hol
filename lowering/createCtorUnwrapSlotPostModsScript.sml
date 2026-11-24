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
       (irule copy_buffer_local_region_frame >> qexists_tac `sb` >> simp[]) >>
     fs[local_region_def]) >>
  `!src name b len. local_region (cenv with ce_module := src) ee.scopes z name b len <=>
                     local_region (cenv with ce_module := src) ee.scopes s name b len` by
    (rpt gen_tac >>
     `local_region cenv ee.scopes z name b len <=> local_region cenv ee.scopes s name b len` by
       (irule copy_buffer_local_region_frame >> qexists_tac `sb` >> simp[]) >>
     fs[local_region_def]) >>
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
  cheat
QED
