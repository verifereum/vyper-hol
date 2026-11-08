(* Valid decoding over owned input/output allocations, with subrange writes. *)
Theory abiValidAllocatedContract
Ancestors
  abiMalformedRecursiveInterface abiMalformedSiteFrame abiDecoderCoherence
  abiDecodeStaticProps abiDecoderContract fragExec exprLoweringProps
  compileEnv venomState venomMemDefs finite_map pred_set words list arithmetic

Definition abi_valid_allocated_frame_def:
  abi_valid_allocated_frame sites d n (s:venom_state) (t:venom_state) <=>
    !a. ~(d <= a /\ a < d+n) /\
      ~abi_malformed_site_range sites s t a 1 ==>
      mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory
End

Definition abi_valid_allocated_entry_def:
  abi_valid_allocated_entry ce env sf ty tv v ctx func cenv cx es
      st en base_op hi src dst B L xs p d dstid live ceiling s <=>
    abi_decoder_coherent ce env sf ty tv /\
    compile_abi_decode_to_buf dst src MLOAD base_op hi
      (type_to_abi_dec_info sf ce ty) st = ((),en) /\
    fn_has_code st en func /\ fn_inst_ids_distinct func /\
    abi_malformed_entry ctx func cenv cx es st
      (abi_malformed_scratch_sites st en func) dstid live
      base_op hi src dst B L xs p d (type_memory_bytes ce ty) s /\
    p <= L /\
    vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP p xs) /\
    abi_to_vyper env ty (dec (vyper_to_abi_type env ty) (DROP p xs)) = SOME v /\
    (is_dynamic (vyper_to_abi_type env ty) \/
      p + static_length (vyper_to_abi_type env ty) <= L) /\
    fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition abi_valid_allocated_post_def:
  abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid d n s t <=>
    val_in_memory tv v d t.vs_memory /\ abi_decode_sim ctx func s t /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\ fresh_vars_wrt ceiling t /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s t /\
    abi_valid_allocated_frame (abi_malformed_scratch_sites st en func) d n s t /\
    (!id b sz. FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
       FLOOKUP s.vs_allocas id = SOME (b,sz) \/ s.vs_alloca_next <= b)
End

Theorem abi_valid_allocated_frame_refl:
  abi_valid_allocated_frame sites d n s s
Proof
  simp[abi_valid_allocated_frame_def]
QED

Theorem abi_valid_allocated_frame_weaken:
  abi_valid_allocated_frame child_sites cd cn s t /\ child_sites SUBSET sites /\
  d <= cd /\ cd+cn <= d+n ==>
  abi_valid_allocated_frame sites d n s t
Proof
  rw[abi_valid_allocated_frame_def] >> first_x_assum irule >>
  fs[abi_malformed_site_range_def, SUBSET_DEF] >> metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem abi_valid_allocated_frame_slice:
  abi_valid_allocated_frame sites d n s t /\
  (!a. q <= a /\ a < q+k ==> ~(d <= a /\ a < d+n) /\
     ~abi_malformed_site_range sites s t a 1) ==>
  mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory
Proof
  strip_tac >> irule mem_bytes_at_bytewise >>
  fs[abi_valid_allocated_frame_def] >> metis_tac[]
QED

(* A later cached slot is either an original slot or was allocated after
   the original frontier. This is the only allocation-growth premise. *)
Theorem abi_valid_allocated_site_sequence:
  alloca_inv t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  t.vs_alloca_next <= u.vs_alloca_next /\
  (!id b sz. FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
     FLOOKUP s.vs_allocas id = SOME (b,sz) \/ s.vs_alloca_next <= b) /\
  abi_malformed_site_range sites t u a 1 ==>
  abi_malformed_site_range sites s u a 1
Proof
  rw[abi_malformed_site_range_def]
  >- (first_x_assum drule >> strip_tac
      >- metis_tac[] >>
      fs[alloca_inv_def, alloca_next_valid_def] >>
      first_x_assum drule >> strip_tac >> disj2_tac >> decide_tac) >>
  disj2_tac >> decide_tac
QED

Theorem abi_valid_allocated_frame_trans:
  abi_valid_allocated_frame sites d n s t /\
  abi_valid_allocated_frame sites d n t u /\
  alloca_inv t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  t.vs_alloca_next <= u.vs_alloca_next /\
  (!id b sz. FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
     FLOOKUP s.vs_allocas id = SOME (b,sz) \/ s.vs_alloca_next <= b) ==>
  abi_valid_allocated_frame sites d n s u
Proof
  strip_tac >> simp[abi_valid_allocated_frame_def] >> rpt strip_tac >>
  `~abi_malformed_site_range sites t u a 1` by
    metis_tac[abi_valid_allocated_site_sequence] >>
  `~abi_malformed_site_range sites s t a 1` by
    (fs[abi_malformed_site_range_def] >> metis_tac[LESS_EQ_TRANS]) >>
  fs[abi_valid_allocated_frame_def] >> metis_tac[]
QED

Theorem abi_valid_allocated_frame_owned_slice:
  abi_valid_allocated_frame sites d n s t /\ alloca_inv s /\
  FLOOKUP s.vs_allocas aid = SOME (B,cap) /\ aid NOTIN sites /\
  B <= q /\ q+k <= B+cap /\ (q+k <= d \/ d+n <= q) ==>
  mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule abi_valid_allocated_frame_slice >>
  goal_assum (drule_at Any) >> rpt gen_tac >> disch_tac >> conj_tac
  >- decide_tac >>
  strip_tac >>
  `B+cap <= a \/ a+1 <= B` by
    (irule abi_malformed_site_range_protected >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  decide_tac
QED

Theorem abi_valid_allocated_frame_sibling:
  abi_valid_allocated_frame sites d n s t /\ alloca_inv s /\
  abi_malformed_destination func cenv scopes dstid q k s /\
  dstid NOTIN sites /\ (q+k <= d \/ d+n <= q) ==>
  mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory
Proof
  rw[abi_malformed_destination_def] >>
  irule abi_valid_allocated_frame_owned_slice >>
  simp[] >> qexistsl_tac [`b`, `inst.inst_id`, `sz`, `d`, `n`, `sites`] >>
  simp[]
QED

Theorem abi_valid_allocated_frame_scratch_free:
  abi_decode_frame d n s t ==> abi_valid_allocated_frame sites d n s t
Proof
  rw[abi_decode_frame_def, abi_valid_allocated_frame_def] >>
  first_x_assum irule >> decide_tac
QED

Theorem abi_valid_allocated_frame_source:
  abi_valid_allocated_frame sites d n s t /\ alloca_inv s /\
  abi_malformed_destination func cenv scopes dstid d n s /\
  FLOOKUP s.vs_allocas live = SOME (B,cap) /\ live <> dstid /\
  live NOTIN sites /\ L <= cap ==>
  mem_bytes_at B L t.vs_memory = mem_bytes_at B L s.vs_memory
Proof
  rw[abi_malformed_destination_def] >>
  `B+cap <= b \/ b+sz <= B` by
    (fs[alloca_inv_def, allocas_non_overlapping_def] >> metis_tac[]) >>
  irule abi_valid_allocated_frame_owned_slice >> simp[] >>
  qexistsl_tac [`B`, `live`, `cap`, `d`, `n`, `sites`] >> simp[] >> decide_tac
QED
