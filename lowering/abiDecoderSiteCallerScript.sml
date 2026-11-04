(* Caller-owned function allocations supply the decoder's finite-site credit. *)
Theory abiDecoderSiteCaller
Ancestors
  abiDecoderSiteCharge abiDecoderSiteResources abiDecoderSiteMembership exprLoweringProps
  abiDecoderAppend abiDecoderCode finite_map pred_set arithmetic words

Theorem alloca_sites_stmt_budget:
  stmt_state_rel ctx func cenv cx es s /\ FINITE ids /\
  (!id. id IN ids ==> ?i. MEM i (fn_insts func) /\ i.inst_id = id /\
     i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit 32w]) ==>
  abi_decoder_site_budget ids
    (s.vs_alloca_next + 32 * CARD (ids DIFF FDOM s.vs_allocas)) s
Proof
  strip_tac >>
  `32 * CARD (ids DIFF FDOM s.vs_allocas) <= pending_alloca_size func s` by
    (irule alloca_sites_pending_charge >> simp[]) >>
  irule abi_decoder_site_budget_intro >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  simp[stmt_state_rel_def] >> strip_tac >> simp[] >>
  reverse conj_tac
  >- (qpat_x_assum `32 * _ <= _` mp_tac >>
      simp[CARD_DIFF] >> fs[alloca_room_def] >> decide_tac) >>
  rpt strip_tac >> qpat_x_assum `!id. id IN ids ==> _` drule >>
  strip_tac >>
  `sz = w2n (32w:bytes32)` by metis_tac[] >>
  gvs[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem abi_decoder_emitted_sites_stmt_budget:
  stmt_state_rel ctx func cenv cx es s /\
  cs_extends first last /\ fn_has_code first last func /\
  compiler_emits abi_decoder_alloc_shape first last ==>
  abi_decoder_site_budget (abi_decoder_emitted_sites lo hi first last)
    (s.vs_alloca_next + 32 * CARD
      (abi_decoder_emitted_sites lo hi first last DIFF FDOM s.vs_allocas)) s
Proof
  strip_tac >> irule alloca_sites_stmt_budget >>
  conj_tac >- simp[] >>
  qexistsl_tac [`cenv`, `ctx`, `cx`, `es`, `func`] >>
  simp[Excl "abi_decoder_emitted_sites_member"] >>
  metis_tac[abi_decoder_emitted_sites_fn_witness]
QED

Theorem abi_decoder_emitted_sites_raw_resources:
  stmt_state_rel ctx func cenv cx es s /\
  cs_extends first last /\ fn_has_code first last func /\
  compiler_emits abi_decoder_alloc_shape first last /\
  FLOOKUP s.vs_allocas source_id = SOME (source_base,source_cap) /\
  FLOOKUP s.vs_allocas output_id = SOME (d,outsz) /\
  source_id <> output_id /\ source_id < first.cs_next_id /\
  output_id < first.cs_next_id /\
  source_base <= sb /\ sb + len <= source_base + source_cap ==>
  sb + len < dimword (:256) /\ d + outsz < dimword (:256) /\
  abi_footprint_disjoint d outsz (abi_decoder_child_scratch
    (abi_decoder_emitted_sites first.cs_next_id last.cs_next_id first last) 0
    (s.vs_alloca_next + 32 * CARD
      (abi_decoder_emitted_sites first.cs_next_id last.cs_next_id first last
        DIFF FDOM s.vs_allocas)) s) /\
  abi_footprint_disjoint sb len ((d,outsz)::abi_decoder_child_scratch
    (abi_decoder_emitted_sites first.cs_next_id last.cs_next_id first last) 0
    (s.vs_alloca_next + 32 * CARD
      (abi_decoder_emitted_sites first.cs_next_id last.cs_next_id first last
        DIFF FDOM s.vs_allocas)) s)
Proof
  strip_tac >>
  drule_all abi_decoder_emitted_sites_stmt_budget >>
  disch_then (qspecl_then [`first.cs_next_id`, `last.cs_next_id`] assume_tac) >>
  irule abi_decoder_site_raw_resources >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`output_id`, `source_base`, `source_cap`, `source_id`] >>
  simp[]
QED

Theorem abi_decoder_compiled_stmt_budget:
  compile_abi_decode_to_buf dst src MLOAD hi info first = ((),last) /\
  fn_has_code first last func /\ stmt_state_rel ctx func cenv cx es s ==>
  abi_decoder_site_budget (abi_decoder_emitted_sites lo top first last)
    (s.vs_alloca_next + 32 * CARD
      (abi_decoder_emitted_sites lo top first last DIFF FDOM s.vs_allocas)) s
Proof
  strip_tac >>
  `cs_extends first last` by metis_tac[cs_extends_abi_decode] >>
  `compiler_emits abi_decoder_alloc_shape first
     (SND (compile_abi_decode_to_buf dst src MLOAD hi info first))` by
    (irule (cj 1 abi_decoder_emits_mutual) >> simp[]) >>
  gvs[] >>
  drule_all abi_decoder_emitted_sites_stmt_budget >>
  disch_then (qspecl_then [`lo`, `top`] mp_tac) >> simp[]
QED
