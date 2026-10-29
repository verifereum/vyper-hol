(* Child scratch excludes already-live ancestor slots. No execution claim. *)
Theory abiDecoderFootprint
Ancestors
  abiDecoderAllocation abiDecoderCode abiDecoderFrame finite_map pred_set
  list arithmetic venomExecSemantics venomState

Definition abi_decoder_child_scratch_def:
  abi_decoder_child_scratch ids b cap s =
    (s.vs_alloca_next,b + cap - s.vs_alloca_next) ::
    MAP (\id. case FLOOKUP s.vs_allocas id of
                NONE => (0,0) | SOME slot => slot) (SET_TO_LIST ids)
End

Theorem abi_decoder_budget_frontier:
  abi_decoder_budget first last b cap s ==>
  b <= s.vs_alloca_next /\ s.vs_alloca_next <= b + cap
Proof
  simp[abi_decoder_budget_def] >> decide_tac
QED

Theorem abi_decoder_child_scratch_disjoint:
  FINITE ids /\ s.vs_alloca_next <= b + cap /\
  (p + n <= s.vs_alloca_next \/ b + cap <= p) /\
  (!id q sz. id IN ids /\ FLOOKUP s.vs_allocas id = SOME (q,sz) ==>
       p + n <= q \/ q + sz <= p) ==>
  abi_footprint_disjoint p n (abi_decoder_child_scratch ids b cap s)
Proof
  rw[abi_decoder_child_scratch_def, abi_footprint_disjoint_def, MEM_MAP] >>
  gvs[] >>
  TRY (decide_tac >> NO_TAC) >>
  Cases_on `FLOOKUP s.vs_allocas id` >> gvs[] >>
  metis_tac[]
QED

Theorem abi_decoder_child_excludes_ancestor:
  abi_decoder_budget first last b cap s /\
  ids SUBSET abi_decoder_ids first last /\ FINITE ids /\
  ancestor IN abi_decoder_ids first last /\ ~(ancestor IN ids) /\
  FLOOKUP s.vs_allocas ancestor = SOME (p,32) ==>
  abi_footprint_disjoint p 32 (abi_decoder_child_scratch ids b cap s)
Proof
  strip_tac >>
  drule abi_decoder_budget_frontier >> strip_tac >>
  `p + 32 <= s.vs_alloca_next` by
    (qpat_assum `abi_decoder_budget _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[abi_decoder_budget_def] >> strip_tac >>
     qpat_x_assum `!id off sz. _ ==> sz = 32 /\ _` drule >>
     disch_then drule >> simp_tac std_ss []) >>
  irule abi_decoder_child_scratch_disjoint >> simp[] >>
  qpat_x_assum `abi_decoder_budget _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decoder_budget_def] >> strip_tac >>
  rpt strip_tac >>
  `id IN abi_decoder_ids first last` by metis_tac[SUBSET_DEF] >>
  `sz = 32` by metis_tac[] >>
  qpat_x_assum `sz = 32` SUBST_ALL_TAC >> metis_tac[]
QED

Theorem abi_decoder_child_allocation:
  abi_decoder_budget first last b cap s /\ FINITE ids /\
  ids SUBSET abi_decoder_ids first last /\ inst.inst_id IN ids /\
  inst.inst_outputs = [out] ==>
  ?t p base len. exec_alloca inst s (32w:bytes32) = OK t /\
    abi_decoder_budget first last b cap t /\
    lookup_var out t = SOME (n2w p) /\
    MEM (base,len) (abi_decoder_child_scratch ids b cap s) /\
    base <= p /\ p + 32 <= base + len
Proof
  strip_tac >>
  `inst.inst_id IN abi_decoder_ids first last` by metis_tac[SUBSET_DEF] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (drule_all abi_decoder_alloca32_fresh >> strip_tac >>
      qexistsl_tac [`t`, `s.vs_alloca_next`, `s.vs_alloca_next`,
        `b + cap - s.vs_alloca_next`] >>
      simp[abi_decoder_child_scratch_def] >> decide_tac) >>
  rename1 `SOME slot` >> PairCases_on `slot` >>
  drule_all abi_decoder_alloca32_reuse >> strip_tac >> gvs[] >>
  qexistsl_tac [`slot0`, `slot0`, `32`] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       abi_decoder_child_scratch_def, MEM_MAP] >>
  disj2_tac >> qexists_tac `inst.inst_id` >> simp[MEM_SET_TO_LIST]
QED

(* Generation interval certificates select exactly the child's sites. *)
Theorem abi_decoder_generated_child_allocation:
  abi_decoder_code child child_end /\
  abi_decoder_code_member inst child_end /\
  ~abi_decoder_code_member inst child /\ inst.inst_opcode = ALLOCA /\
  abi_decoder_budget first last b cap s /\
  abi_decoder_ids child.cs_next_id child_end.cs_next_id SUBSET
    abi_decoder_ids first last ==>
  ?out t p base len. inst.inst_outputs = [out] /\
    inst.inst_operands = [Lit 32w] /\
    exec_alloca inst s (32w:bytes32) = OK t /\
    abi_decoder_budget first last b cap t /\
    lookup_var out t = SOME (n2w p) /\
    MEM (base,len) (abi_decoder_child_scratch
      (abi_decoder_ids child.cs_next_id child_end.cs_next_id) b cap s) /\
    base <= p /\ p + 32 <= base + len
Proof
  strip_tac >> drule_all abi_decoder_code_alloca >> strip_tac >>
  `inst.inst_id IN abi_decoder_ids child.cs_next_id child_end.cs_next_id` by
    simp[abi_decoder_ids_def] >>
  `FINITE (abi_decoder_ids child.cs_next_id child_end.cs_next_id)` by simp[] >>
  drule_all abi_decoder_child_allocation >> strip_tac >>
  metis_tac[]
QED

(* Child output must also exclude the ancestor index. Source and initialized
   siblings are protected observations, not part of the scratch allowance. *)
Theorem abi_decoder_child_frame_protected:
  abi_decoder_budget first last b cap s /\ FINITE ids /\
  ids SUBSET abi_decoder_ids first last /\
  ancestor IN abi_decoder_ids first last /\ ~(ancestor IN ids) /\
  FLOOKUP s.vs_allocas ancestor = SOME (ip,32) /\
  (ip + 32 <= d \/ d + sz <= ip) /\
  abi_footprint_disjoint sb n
    ((d,sz)::abi_decoder_child_scratch ids b cap s) /\
  abi_footprint_disjoint prev k
    ((d,sz)::abi_decoder_child_scratch ids b cap s) /\
  abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch ids b cap s) s t ==>
  mload ip t = mload ip s /\
  mem_bytes_at sb n t.vs_memory = mem_bytes_at sb n s.vs_memory /\
  mem_bytes_at prev k t.vs_memory = mem_bytes_at prev k s.vs_memory
Proof
  strip_tac >> drule_all abi_decoder_child_excludes_ancestor >> strip_tac >>
  `abi_footprint_disjoint ip 32
     ((d,sz)::abi_decoder_child_scratch ids b cap s)` by
    (simp_tac std_ss [abi_footprint_disjoint_def, MEM] >>
     metis_tac[abi_footprint_disjoint_def]) >>
  metis_tac[abi_decode_footprint_frame_mload, abi_decode_footprint_frame_slice]
QED

Theorem abi_decoder_child_frame_count:
  abi_decode_footprint_frame fp s t /\
  abi_footprint_disjoint count_slot 32 fp /\
  abi_footprint_disjoint index_slot 32 fp ==>
  mload count_slot t = mload count_slot s /\
  mload index_slot t = mload index_slot s
Proof
  metis_tac[abi_decode_child_preserves_loop_slots]
QED

Theorem abi_decoder_parent_index_preserves_source_count:
  count_slot + 32 <= index_slot \/ index_slot + 32 <= count_slot ==>
  mload count_slot (mstore index_slot w s) = mload count_slot s
Proof
  strip_tac >>
  mp_tac (Q.INST [`bs` |-> `word_to_bytes (w:bytes32) T`]
    abi_decode_index_write_preserves_count) >>
  simp[byteTheory.LENGTH_word_to_bytes, write_memory_with_expansion_def,
       mstore_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

(* Caller boundary is conditional: absence of generated sites, sufficient
   credit, and live source/output below the frontier are explicit premises.
   No claim that canonical encoding or SSA freshness supplies these facts. *)
Theorem abi_decoder_caller_initialize:
  (!id. id IN abi_decoder_ids first last ==>
        FLOOKUP s.vs_allocas id = NONE) /\
  b <= s.vs_alloca_next /\
  s.vs_alloca_next + 32 * CARD (abi_decoder_ids first last) <= b + cap /\
  b + cap < dimword (:256) /\
  sb + n <= s.vs_alloca_next /\ d + sz <= s.vs_alloca_next ==>
  abi_decoder_budget first last b cap s /\
  abi_footprint_disjoint sb n
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
  abi_footprint_disjoint d sz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)
Proof
  strip_tac >>
  `abi_decoder_budget first last b cap s` by
    (irule abi_decoder_budget_empty >> simp[]) >>
  drule abi_decoder_budget_frontier >> strip_tac >> simp[] >>
  conj_tac >> irule abi_decoder_child_scratch_disjoint >> simp[] >>
  metis_tac[optionTheory.NOT_NONE_SOME]
QED
