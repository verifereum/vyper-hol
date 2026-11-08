(* Scratch writes are authorized by actual sites or by the new frontier,
   never by an envelope inferred from instruction ids. *)
Theory abiMalformedSiteFrame
Ancestors
  abiMalformedIndexState abiMalformedResources abiMalformedCopyState
  abiMalformedPruneState abiDecoderReentry abiDecoderIndexInit
  exprLoweringProps localPtrsProps compileEnv valueCopy valueEncoding
  venomState venomMemDefs venomMemProps venomExecSemantics finite_map
  pred_set list arithmetic

Definition abi_malformed_site_range_def:
  abi_malformed_site_range sites s t at n <=>
    (?aid b sz. aid IN sites /\
       FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
       b <= at /\ at + n <= b + sz) \/
    (s.vs_alloca_next <= at /\ at + n <= t.vs_alloca_next)
End

Theorem abi_malformed_site_range_protected:
  alloca_inv s /\ aid NOTIN sites /\
  FLOOKUP s.vs_allocas aid = SOME (B,cap) /\ L <= cap /\
  abi_malformed_site_range sites s t at n ==>
  B + L <= at \/ at + n <= B
Proof
  rw[abi_malformed_site_range_def]
  >- (fs[alloca_inv_def, allocas_non_overlapping_def] >>
      `aid <> aid'` by metis_tac[] >>
      qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule_all >> decide_tac) >>
  fs[alloca_inv_def, alloca_next_valid_def] >>
  first_x_assum drule >> decide_tac
QED

Theorem abi_malformed_site_mcopy_protected:
  alloca_inv s /\ aid NOTIN sites /\
  FLOOKUP s.vs_allocas aid = SOME (B,cap) /\ L <= cap /\
  abi_malformed_site_range sites s t at n ==>
  mem_bytes_at B L (mcopy at src n s).vs_memory =
  mem_bytes_at B L s.vs_memory
Proof
  strip_tac >> irule mem_bytes_at_mcopy_disjoint >>
  drule_all abi_malformed_site_range_protected >> simp[]
QED

(* Determinism combines the existing execution/state and source-window
   boundaries, retaining their arbitrary site-reuse behavior. *)
Theorem abi_malformed_index_protected:
  abi_decode_index_init st = (ip,en) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) ==>
  ?t p. run_inst_seq (emitted_insts st en) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!live B cap L. live < st.cs_next_id /\
       FLOOKUP s.vs_allocas live = SOME (B,cap) /\ L <= cap ==>
       mem_bytes_at B L t.vs_memory = mem_bytes_at B L s.vs_memory)
Proof
  strip_tac >> drule_all abi_malformed_index_state >> strip_tac >>
  qexistsl_tac [`t`, `p`] >> simp[] >> rpt strip_tac >>
  drule_all abi_malformed_index_source_window >> strip_tac >> gvs[]
QED

Theorem abi_malformed_site_mload_protected:
  alloca_inv s /\ aid NOTIN sites /\
  FLOOKUP s.vs_allocas aid = SOME (A,32) /\
  abi_malformed_site_range sites s t at n ==>
  mload A (mcopy at src n s) = mload A s
Proof
  strip_tac >>
  `mem_bytes_at A 32 (mcopy at src n s).vs_memory =
   mem_bytes_at A 32 s.vs_memory` by
    (irule abi_malformed_site_mcopy_protected >>
     simp[] >> qexistsl_tac [`aid`, `32`, `sites`, `t`] >> simp[]) >>
  gvs[mload_def, mem_bytes_at_def]
QED

(* A child result site is not a live local pointer. Its recorded allocation,
   not its numeric position among ids, grants write authority. *)
Theorem abi_malformed_child_copy_frame:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= dst /\ dst + n <= b + sz /\
  live <> inst.inst_id /\ FLOOKUP s.vs_allocas live = SOME (B,cap) /\
  L <= cap ==>
  stmt_state_rel ctx func cenv cx es (mcopy dst src n s) /\
  mem_bytes_at B L (mcopy dst src n s).vs_memory =
    mem_bytes_at B L s.vs_memory /\
  (mcopy dst src n s).vs_allocas = s.vs_allocas
Proof
  strip_tac >> conj_tac
  >- (irule abi_malformed_mcopy_state_rel >>
      simp[] >> qexistsl_tac [`b`, `inst`, `sz`] >> simp[] >>
      rpt strip_tac >>
      `compileEnv$regions_disjoint b sz lb lsz` by
        (fs[stmt_state_rel_def, state_rel_def] >>
         drule_all local_ptrs_rel_alloca_disjoint >> simp[]) >>
      gvs[compileEnvTheory.regions_disjoint_def]) >>
  reverse conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
  irule mem_bytes_at_mcopy_disjoint >>
  `allocas_non_overlapping s` by gvs[stmt_state_rel_def, alloca_inv_def] >>
  fs[allocas_non_overlapping_def] >>
  first_x_assum drule_all >> decide_tac
QED

(* Two actual sites, followed by a child-sized write, including reuse.
   Both protected allocations predate the first site; there is no assumption
   that either site is absent, and no ordering of allocation addresses. *)
Theorem abi_malformed_two_sites_copy_probe:
  abi_decode_index_init st = (ip,en) /\
  abi_decode_index_init st2 = (ip2,en2) /\
  st.cs_next_id < st2.cs_next_id /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\ local_ptrs_reserved cenv st2 /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst st2.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st2.cs_next_var)]) (fn_insts func) /\
  live < st.cs_next_id /\ ancestor < st.cs_next_id /\
  FLOOKUP s.vs_allocas live = SOME (B,cap) /\ L <= cap /\
  FLOOKUP s.vs_allocas ancestor = SOME (A,32) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= dst /\ dst+n <= b+sz /\
  live <> inst.inst_id /\ ancestor <> inst.inst_id ==>
  ?t u. run_inst_seq (emitted_insts st en) s = OK t /\
    run_inst_seq (emitted_insts st2 en2) t = OK u /\
    stmt_state_rel ctx func cenv cx es (mcopy dst src n u) /\
    stmt_state_rel ctx func cenv cx es
      (abi_decoder_prune_vars st2.cs_next_var (mcopy dst src n u)) /\
    mem_bytes_at B L (mcopy dst src n u).vs_memory =
      mem_bytes_at B L s.vs_memory /\
    mload A (mcopy dst src n u) = mload A s /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP (mcopy dst src n u).vs_allocas aid = SOME entry)
Proof
  strip_tac >>
  qpat_assum `abi_decode_index_init st = _`
    (mp_then Any mp_tac abi_malformed_index_protected) >>
  simp[] >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st en) s = OK t` >>
  qpat_assum `abi_decode_index_init st2 = _`
    (mp_then Any mp_tac abi_malformed_index_protected) >>
  disch_then drule >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st2 en2) t = OK u` >>
  `FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) /\
   FLOOKUP u.vs_allocas live = SOME (B,cap) /\
   FLOOKUP u.vs_allocas ancestor = SOME (A,32)` by metis_tac[] >>
  `stmt_state_rel ctx func cenv cx es (mcopy dst src n u) /\
   mem_bytes_at B L (mcopy dst src n u).vs_memory = mem_bytes_at B L u.vs_memory` by
    (drule_all abi_malformed_child_copy_frame >> simp[]) >>
  `mem_bytes_at A 32 (mcopy dst src n u).vs_memory = mem_bytes_at A 32 u.vs_memory` by
    (irule mem_bytes_at_mcopy_disjoint >>
     `allocas_non_overlapping u` by gvs[stmt_state_rel_def, alloca_inv_def] >>
     fs[allocas_non_overlapping_def] >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule_all >> decide_tac) >>
  qexists_tac `u` >> simp[] >>
  conj_tac >- (irule abi_malformed_prune_state >> simp[]) >>
  `live < st2.cs_next_id /\ ancestor < st2.cs_next_id` by decide_tac >>
  `FLOOKUP t.vs_allocas live = SOME (B,cap) /\
   FLOOKUP t.vs_allocas ancestor = SOME (A,32)` by
    (conj_tac >> first_assum irule >> simp[]) >>
  qpat_assum `!live B cap L. _ ==> mem_bytes_at B L t.vs_memory = _`
    (qspecl_then [`live`, `B`, `cap`, `L`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!live B cap L. _ ==> mem_bytes_at B L t.vs_memory = _`
    (qspecl_then [`ancestor`, `A`, `32`, `32`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!live B cap L. _ ==> mem_bytes_at B L u.vs_memory = _`
    (qspecl_then [`live`, `B`, `cap`, `L`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!live B cap L. _ ==> mem_bytes_at B L u.vs_memory = _`
    (qspecl_then [`ancestor`, `A`, `32`, `32`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[] >> gvs[mload_def, mem_bytes_at_def] >>
  simp[mcopy_def] >> metis_tac[]
QED
