(* Actual decoder scratch sites: finite windows and generated syntax. *)
Theory entryReachBodyScratchSites
Ancestors
  entryReachBodyScratchSet abiEncoderWindowContract actualDecoderSites
  abiDecoderCode abiDecoderAllocation pred_set arithmetic

Theorem entry_scratch_sites_finite:
  FINITE ids ==> FINITE (window_alloca_sites func ids)
Proof
  metis_tac[window_alloca_sites_subset, SUBSET_FINITE]
QED

Theorem entry_decoder_sites_finite[simp]:
  FINITE (window_alloca_sites func (abi_decoder_ids first last))
Proof
  simp[entry_scratch_sites_finite]
QED

Theorem entry_decoder_sites_interval_subset:
  first <= child_first /\ child_last <= last ==>
  window_alloca_sites func (abi_decoder_ids child_first child_last) SUBSET
  window_alloca_sites func (abi_decoder_ids first last)
Proof
  strip_tac >> irule window_alloca_sites_mono >>
  simp[abi_decoder_ids_def, SUBSET_DEF] >> rpt strip_tac >> decide_tac
QED

Theorem entry_scratch_sites_disjoint:
  DISJOINT ids other ==>
  DISJOINT (window_alloca_sites func ids) (window_alloca_sites func other)
Proof
  simp[window_alloca_sites_def, DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem entry_decoder_sites_ordered_disjoint:
  last <= next ==>
  DISJOINT (window_alloca_sites func (abi_decoder_ids first last))
    (window_alloca_sites func (abi_decoder_ids next stop))
Proof
  strip_tac >> irule entry_scratch_sites_disjoint >>
  simp[DISJOINT_DEF, EXTENSION, abi_decoder_ids_def] >> decide_tac
QED

Theorem entry_decoder_generated_site:
  abi_decoder_code st en /\ abi_decoder_code_member inst en /\
  ~abi_decoder_code_member inst st /\ inst.inst_opcode = ALLOCA /\
  MEM inst (fn_insts func) ==>
  inst.inst_id IN window_alloca_sites func
    (abi_decoder_ids st.cs_next_id en.cs_next_id) /\
  inst.inst_operands = [Lit 32w] /\ ?out. inst.inst_outputs = [out]
Proof
  strip_tac >> drule_all abi_decoder_code_alloca >> strip_tac >>
  simp[window_alloca_sites_def, abi_decoder_ids_def] >> metis_tac[]
QED
