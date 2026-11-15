(* Actual scratch regions delimit the memory and taint frame of sibling decoders. *)
Theory abiValidAllocatedMembersJoint
Ancestors
  abiValidAllocatedMemberJoin abiValidAllocatedMemberEntry
  abiValidAllocatedMembers abiDecoderContract abiDecoderLoop valueEncodingDefs
  abiValidAllocatedContract abiMalformedSiteFrame abiMalformedRecursiveInterface
  robustCopyTransportPtr valueEncoding valueEncodingProps bodyPtrDefs
  abiDecoderMemberInfos abiDecoderCoherence abiDecoderReentryPointer abiEncoder fragGasOriginPtr
  compileEnv venomState finite_map pred_set list arithmetic

Theorem abi_valid_allocated_members_nil_joint:
  abi_valid_allocated_members_entry H ce env sf [] [] [] ctx func cenv cx es
    st en base_op hi pos dst B L xs p d outsz ao vo dstid live ceiling s ==>
  abi_valid_allocated_members_post [] [] ctx func cenv cx es st en ceiling dstid
    (d+vo) 0 s s /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK s,G,tn))
Proof
  strip_tac >>
  qhdtm_assum `abi_valid_allocated_members_entry`
    (map_every assume_tac o CONJUNCTS o
      PURE_REWRITE_RULE [abi_valid_allocated_members_entry_def]) >>
  `st = en` by
    fs[abi_decoder_member_infos_def, Once compile_abi_decode_to_buf_def,
       comp_return_def] >> gvs[] >>
  simp[gas_origin_ptr_path_rules, abi_valid_allocated_members_post_def,
       val_in_memory_def, abi_decode_sim_refl, abi_valid_allocated_frame_refl] >>
  irule abi_malformed_resource_refl >> fs[abi_malformed_entry_def] >> metis_tac[]
QED

Theorem abi_valid_allocated_sibling_robust:
  abi_valid_allocated_frame sites d n s t /\ alloca_inv s /\
  abi_malformed_destination func cenv scopes dstid q k s /\
  dstid NOTIN sites /\ (q+k <= d \/ d+n <= q) /\
  val_wf tv v /\ val_footprint tv v <= k /\
  (!a. ~(d <= a /\ a < d+n) /\
    ~abi_malformed_site_range sites s t a 1 ==>
    (a IN dirty' <=> a IN dirty)) /\
  (!mem. mem_agree_outside dirty s.vs_memory mem ==>
    val_in_memory tv v q mem) ==>
  !mem. mem_agree_outside dirty' t.vs_memory mem ==>
    val_in_memory tv v q mem
Proof
  strip_tac >> rpt strip_tac >>
  qhdtm_assum `abi_malformed_destination`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_destination_def]) >>
  `!i. q <= i /\ i < q+val_footprint tv v ==>
    ~(d <= i /\ i < d+n) /\ ~abi_malformed_site_range sites s t i 1` by
    (gen_tac >> strip_tac >> conj_tac >- decide_tac >> strip_tac >>
     `b+sz <= i \/ i+1 <= b` by
       (mp_tac (abi_malformed_site_range_protected |> Q.INST
          [`aid` |-> `dstid`, `B` |-> `b`, `cap` |-> `sz`, `L` |-> `sz`,
           `s` |-> `s`, `t` |-> `t`, `at` |-> `i`, `n` |-> `1`,
           `sites` |-> `sites`]) >> simp[]) >>
     decide_tac) >>
  mp_tac (Q.SPECL [`dirty`, `dirty'`, `s.vs_memory`, `t.vs_memory`,
    `{a | (d <= a /\ a < d+n) \/ abi_malformed_site_range sites s t a 1}`,
    `tv`, `v`, `q`] robust_val_in_memory_exterior_frame) >>
  disch_then irule >> fs[abi_valid_allocated_frame_def] >> metis_tac[]
QED

Theorem abi_valid_allocated_taint_frame_trans:
  (!a. ~(d <= a /\ a < d+n) /\
    ~abi_malformed_site_range sites s t a 1 ==>
    (a IN dirty1 <=> a IN dirty0)) /\
  (!a. ~(d <= a /\ a < d+n) /\
    ~abi_malformed_site_range sites t u a 1 ==>
    (a IN dirty2 <=> a IN dirty1)) /\
  alloca_inv t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  t.vs_alloca_next <= u.vs_alloca_next /\
  (!id b sz. FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
    FLOOKUP s.vs_allocas id = SOME (b,sz) \/ s.vs_alloca_next <= b) ==>
  !a. ~(d <= a /\ a < d+n) /\
    ~abi_malformed_site_range sites s u a 1 ==>
    (a IN dirty2 <=> a IN dirty0)
Proof
  strip_tac >> rpt strip_tac >>
  `~abi_malformed_site_range sites t u a 1` by
    metis_tac[abi_valid_allocated_site_sequence] >>
  `~abi_malformed_site_range sites s t a 1` by
    (fs[abi_malformed_site_range_def] >> metis_tac[LESS_EQ_TRANS]) >>
  metis_tac[]
QED

Theorem abi_valid_allocated_members_cons_joint_post:
  abi_valid_allocated_members_entry H ce env sf (ty::tys) (tv::tvs) (v::vs)
    ctx func cenv cx es st en base_op hi pos dst B L xs p d outsz ao vo
    dstid live ceiling s /\
  abi_decode_member_setup dst pos MLOAD base_op hi
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) MLOAD base_op hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  compile_abi_decode_complex_elems dst pos MLOAD base_op hi
    (abi_decoder_member_infos sf ce tys)
    (ao+abi_embedded_static_size ce.ce_struct_fields ty)
    (vo+type_memory_bytes ce ty) end_st = ((),en) /\
  abi_decode_sim ctx func s u /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
    (abi_malformed_scratch_sites st en func) dstid s u /\
  abi_valid_allocated_post tv v ctx func cenv cx es middle end_st ceiling dstid
    (d+vo) (type_memory_bytes ce ty) u t /\
  abi_valid_allocated_members_post tvs vs ctx func cenv cx es end_st en ceiling dstid
    (d+(vo+type_memory_bytes ce ty)) (type_memory_size_list tvs) t r /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G0,tn0) [] (OK u,G1,tn1)) /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (u,G1,tn1) [] (OK t,G2,tn2)) /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (t,G2,tn2) [] (OK r,G3,tn3)) /\
  abi_malformed_destination func cenv es.scopes dstid (d+vo)
    (type_memory_bytes ce ty) t /\
  dstid NOTIN abi_malformed_scratch_sites end_st en func /\
  val_wf tv v /\ val_footprint tv v <= type_memory_bytes ce ty /\
  (!a. ~(d+(vo+type_memory_bytes ce ty) <= a /\
         a < d+(vo+type_memory_bytes ce ty)+type_memory_size_list tvs) /\
    ~abi_malformed_site_range (abi_malformed_scratch_sites end_st en func) t r a 1 ==>
    (a IN tn3.t_mem <=> a IN tn2.t_mem)) /\
  (!mem. mem_agree_outside tn2.t_mem t.vs_memory mem ==>
    val_in_memory tv v (d+vo) mem) /\
  (!mem. mem_agree_outside tn3.t_mem r.vs_memory mem ==>
    tuple_in_memory vs tvs (d+(vo+type_memory_bytes ce ty)) mem) ==>
  abi_valid_allocated_members_post (tv::tvs) (v::vs) ctx func cenv cx es
    st en ceiling dstid (d+vo) (type_memory_size_list (tv::tvs)) s r /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G0,tn0) [] (OK r,G3,tn3)) /\
  (!mem. mem_agree_outside tn3.t_mem r.vs_memory mem ==>
    tuple_in_memory (v::vs) (tv::tvs) (d+vo) mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_valid_allocated_members_cons_post >> strip_tac >>
  `!mem. mem_agree_outside tn3.t_mem r.vs_memory mem ==>
      val_in_memory tv v (d+vo) mem` by
    (mp_tac (abi_valid_allocated_sibling_robust |> Q.INST
       [`s` |-> `t`, `t` |-> `r`, `q` |-> `d+vo`,
        `scopes` |-> `es.scopes`,
        `k` |-> `type_memory_bytes ce ty`,
        `sites` |-> `abi_malformed_scratch_sites end_st en func`,
        `d` |-> `d+(vo+type_memory_bytes ce ty)`,
        `n` |-> `type_memory_size_list tvs`,
        `dirty` |-> `tn2.t_mem`, `dirty'` |-> `tn3.t_mem`]) >>
     (impl_tac >-
       (fs[abi_valid_allocated_members_post_def, abi_valid_allocated_post_def] >>
        imp_res_tac abi_malformed_resource_post_alloca_inv >>
        asm_rewrite_tac[])) >>
     simp[]) >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    (fs[abi_valid_allocated_members_entry_def, listTheory.LIST_REL_CONS1] >>
     drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac
  >- (rpt gen_tac >> metis_tac[gas_origin_ptr_path_append, APPEND]) >>
  simp[val_in_memory_def] >> metis_tac[]
QED
