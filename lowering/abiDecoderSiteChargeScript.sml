(* Charge selected allocation IDs once, independently of repeated occurrences. *)
Theory abiDecoderSiteCharge
Ancestors
  abiDecoderSiteMembership exprLoweringProps pred_set list arithmetic

Theorem alloca_sites_list_charge:
  !xs ids. FINITE ids /\
    (!id. id IN ids ==> ?i. MEM i xs /\ i.inst_id = id /\
       alloca_lit_size i = 32) ==>
    32 * CARD ids <= SUM (MAP alloca_lit_size xs)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (`ids = {}` by (simp[EXTENSION] >> metis_tac[MEM]) >> simp[]) >>
  Cases_on `h.inst_id IN ids /\ alloca_lit_size h = 32`
  >- (`32 * CARD (ids DELETE h.inst_id) <= SUM (MAP alloca_lit_size xs)` by
        (first_x_assum irule >> simp[] >> rpt strip_tac >>
         first_x_assum drule >> simp[] >> metis_tac[]) >>
      `CARD ids = SUC (CARD (ids DELETE h.inst_id))` by
        (`ids = h.inst_id INSERT (ids DELETE h.inst_id)` by
           (gvs[] >> SET_TAC[]) >>
         pop_assum (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
         simp[]) >>
      qpat_x_assum `CARD ids = _` (fn th => pure_rewrite_tac[th]) >>
      gvs[] >> decide_tac) >>
  `32 * CARD ids <= SUM (MAP alloca_lit_size xs)` by
    (first_x_assum irule >> simp[] >> metis_tac[MEM]) >>
  simp[]
QED

Theorem alloca_sites_pending_charge:
  FINITE ids /\
  (!id. id IN ids ==> ?i. MEM i (fn_insts func) /\ i.inst_id = id /\
     i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit 32w]) ==>
  32 * CARD (ids DIFF FDOM s.vs_allocas) <= pending_alloca_size func s
Proof
  strip_tac >> rewrite_tac[pending_alloca_size_def] >>
  irule alloca_sites_list_charge >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> qexists_tac `i` >>
  simp[MEM_FILTER, alloca_lit_size_def, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem abi_decoder_emitted_sites_pending_charge:
  cs_extends first last /\ fn_has_code first last func /\
  compiler_emits abi_decoder_alloc_shape first last ==>
  32 * CARD (abi_decoder_emitted_sites lo hi first last DIFF FDOM s.vs_allocas)
    <= pending_alloca_size func s
Proof
  strip_tac >> irule alloca_sites_pending_charge >>
  simp[] >> rpt strip_tac >>
  `MEM i (fn_insts func)` by metis_tac[compiler_emitted_fn_member] >>
  drule_all abi_decoder_emitted_alloca >> strip_tac >>
  qexists_tac `i` >> simp[]
QED
