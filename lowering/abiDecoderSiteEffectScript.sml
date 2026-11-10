(* Strong, fixed-origin effects for actual-site decoder execution. *)
Theory abiDecoderSiteEffect
Ancestors
  valueEncodingDefs
  actualDecoderSites abiDecoderReentry valueEncodingProps valueEncoding
  localPtrsProps venomState instIdxIndep exprLoweringProps venomMemDefs finite_map pred_set words arithmetic list rich_list

Definition decode_static_frame_def:
  decode_static_frame s t <=>
    t = s with <|vs_memory := t.vs_memory; vs_vars := t.vs_vars;
      vs_prev_bb := t.vs_prev_bb; vs_current_bb := t.vs_current_bb;
      vs_inst_idx := t.vs_inst_idx; vs_allocas := t.vs_allocas;
      vs_alloca_next := t.vs_alloca_next|>
End

Definition decode_write_regions_def:
  decode_write_regions output scratch s =
    {a | ?id b n. (id = output \/ id IN scratch) /\
      FLOOKUP s.vs_allocas id = SOME (b,n) /\ b <= a /\ a < b+n}
End

Definition decode_protects_def:
  decode_protects writes regions <=>
    !p n a. (p,n) IN regions /\ p <= a /\ a < p+n ==> a NOTIN writes
End

Definition decode_memory_frame_def:
  decode_memory_frame writes s t <=>
    !p n. (!a. p <= a /\ a < p+n ==> a NOTIN writes) ==>
      mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory
End

Definition decode_site_effect_def:
  decode_site_effect ctx fn next writes s t <=>
    decode_site_resources ctx fn t /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    decode_static_frame s t /\ decode_memory_frame writes s t
End

Theorem decode_static_frame_refl:
  decode_static_frame s s
Proof
  simp[decode_static_frame_def]
QED

Theorem decode_static_frame_trans:
  decode_static_frame s t /\ decode_static_frame t u ==> decode_static_frame s u
Proof
  simp[decode_static_frame_def] >> rpt strip_tac >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >> gvs[]
QED

Theorem decode_memory_frame_refl:
  decode_memory_frame writes s s
Proof
  simp[decode_memory_frame_def]
QED

Theorem decode_memory_frame_trans:
  decode_memory_frame writes1 s t /\ decode_memory_frame writes2 t u ==>
  decode_memory_frame (writes1 UNION writes2) s u
Proof
  rw[decode_memory_frame_def] >> metis_tac[IN_UNION]
QED

Theorem decode_site_effect_refl:
  decode_site_resources ctx fn s ==> decode_site_effect ctx fn next writes s s
Proof
  simp[decode_site_effect_def, decode_static_frame_refl, decode_memory_frame_refl]
QED

Theorem decode_site_effect_trans:
  decode_site_effect ctx fn next writes1 s t /\
  decode_site_effect ctx fn next writes2 t u ==>
  decode_site_effect ctx fn next (writes1 UNION writes2) s u
Proof
  simp_tac bool_ss [decode_site_effect_def] >> strip_tac >>
  rpt conj_tac >> metis_tac[decode_static_frame_trans, decode_memory_frame_trans,
                           LESS_EQ_TRANS]
QED

Theorem decode_site_effect_resources:
  decode_site_effect ctx fn next writes s t ==> decode_site_resources ctx fn t
Proof
  simp[decode_site_effect_def]
QED

Theorem decode_site_effect_allocation:
  decode_site_effect ctx fn next writes s t /\
  FLOOKUP s.vs_allocas id = SOME (b,n) ==>
  FLOOKUP t.vs_allocas id = SOME (b,n)
Proof
  simp[decode_site_effect_def]
QED

Theorem decode_site_effect_protected:
  decode_site_effect ctx fn next writes s t /\ decode_protects writes regions /\
  (p,n) IN regions ==>
  mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory
Proof
  rw[decode_site_effect_def, decode_protects_def, decode_memory_frame_def] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem decode_protects_union:
  decode_protects writes1 regions /\ decode_protects writes2 regions ==>
  decode_protects (writes1 UNION writes2) regions
Proof
  simp[decode_protects_def, IN_UNION] >> metis_tac[]
QED

Theorem decode_memory_frame_write:
  {a | dst <= a /\ a < dst + LENGTH bs} SUBSET writes ==>
  decode_memory_frame writes s (write_memory_with_expansion dst bs s)
Proof
  rw[decode_memory_frame_def] >>
  Cases_on `bs = []`
  >- (gvs[write_memory_with_expansion_def, TAKE_DROP] >>
      IF_CASES_TAC >> simp[valueEncodingProofsTheory.mem_bytes_at_append_zero]) >>
  Cases_on `n = 0` >- simp[mem_bytes_at_def] >>
  `0 < LENGTH bs` by metis_tac[LENGTH_NIL, NOT_ZERO_LT_ZERO] >>
  irule write_memory_mem_bytes_at_disjoint >>
  fs[SUBSET_DEF] >>
  Cases_on `p + n <= dst` >- simp[] >>
  Cases_on `dst + LENGTH bs <= p` >- simp[] >>
  Cases_on `p <= dst`
  >- (first_x_assum (qspec_then `dst` mp_tac) >>
      first_x_assum (qspec_then `dst` mp_tac) >> simp[] >> decide_tac) >>
  first_x_assum (qspec_then `p` mp_tac) >>
  first_x_assum (qspec_then `p` mp_tac) >> simp[] >> decide_tac
QED

Theorem decode_site_resources_fields:
  decode_site_resources ctx fn s /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp ==>
  decode_site_resources ctx fn t
Proof
  rw[actualDecoderSitesTheory.decode_site_resources_def]
  >- (irule exprLoweringPropsTheory.alloca_room_fields >> metis_tac[])
  >- (irule alloca_inv_fields >> metis_tac[])
  >- (irule exprLoweringPropsTheory.fmp_room_fields >> metis_tac[]) >>
  metis_tac[]
QED

Theorem decode_site_effect_write:
  decode_site_resources ctx fn s /\
  {a | dst <= a /\ a < dst + LENGTH bs} SUBSET writes ==>
  decode_site_effect ctx fn next writes s (write_memory_with_expansion dst bs s)
Proof
  strip_tac >> simp_tac bool_ss [decode_site_effect_def] >>
  conj_tac
  >- (irule decode_site_resources_fields >> qexists `s` >>
      simp[write_memory_with_expansion_def]) >>
  conj_tac >- simp[write_memory_with_expansion_def] >>
  conj_tac >- simp[write_memory_with_expansion_def] >>
  conj_tac >- simp[write_memory_with_expansion_def, eval_operand_def, lookup_var_def] >>
  conj_tac >- simp[write_memory_with_expansion_def, decode_static_frame_def] >>
  irule decode_memory_frame_write >> simp[]
QED

Theorem decode_site_effect_live:
  decode_site_effect ctx fn next writes s t /\
  abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
  eval_operand op t = SOME w
Proof
  simp[decode_site_effect_def]
QED

Theorem decode_site_effect_static:
  decode_site_effect ctx fn next writes s t ==> decode_static_frame s t
Proof
  simp[decode_site_effect_def]
QED

Theorem decode_site_effect_frontier:
  decode_site_effect ctx fn next writes s t ==> s.vs_alloca_next <= t.vs_alloca_next
Proof
  simp[decode_site_effect_def]
QED

Theorem decode_write_regions_extension:
  decode_site_effect ctx fn next writes s t ==>
  decode_write_regions output scratch s SUBSET decode_write_regions output scratch t
Proof
  rw[decode_site_effect_def, decode_write_regions_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem decode_site_resources_inst_idx[simp]:
  decode_site_resources ctx fn (s with vs_inst_idx := ix) <=>
  decode_site_resources ctx fn s
Proof
  `fmp_room ctx fn (s with vs_inst_idx := ix) <=> fmp_room ctx fn s` by
    (irule fmp_room_fields_cong >> simp[]) >>
  simp[decode_site_resources_def, alloca_room_def, pending_alloca_size_def,
       alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem decode_site_effect_inst_idx[simp]:
  decode_site_effect ctx fn next writes s (t with vs_inst_idx := ix) <=>
  decode_site_effect ctx fn next writes s t
Proof
  simp[decode_site_effect_def, decode_static_frame_def, decode_memory_frame_def,
       instIdxIndepTheory.eval_op_inst_idx, venom_state_component_equality]
QED

Theorem decode_memory_frame_weaken:
  decode_memory_frame V s t /\ V SUBSET writes ==> decode_memory_frame writes s t
Proof
  rw[decode_memory_frame_def, SUBSET_DEF] >> first_x_assum irule >> metis_tac[]
QED

Theorem decode_site_effect_weaken:
  decode_site_effect ctx fn next V s t /\ V SUBSET writes ==>
  decode_site_effect ctx fn next writes s t
Proof
  simp[decode_site_effect_def] >> metis_tac[decode_memory_frame_weaken]
QED

Theorem decode_site_effect_threshold:
  decode_site_effect ctx fn child V s t /\ first <= child ==>
  decode_site_effect ctx fn first V s t
Proof
  simp[decode_site_effect_def] >> rpt strip_tac >>
  metis_tac[abi_decoder_operand_live_mono]
QED

Theorem decode_site_effect_fixed_origin:
  decode_site_effect ctx fn first writes origin s /\
  decode_site_effect ctx fn child V s t /\ first <= child /\ V SUBSET writes ==>
  decode_site_effect ctx fn first writes origin t
Proof
  strip_tac >>
  `decode_site_effect ctx fn first writes s t` by
    metis_tac[decode_site_effect_threshold, decode_site_effect_weaken] >>
  drule_all decode_site_effect_trans >> simp[]
QED

Theorem decode_site_effect_mload:
  decode_site_effect ctx fn next V s t /\ decode_protects V {(p,32)} ==>
  mload p t = mload p s
Proof
  strip_tac >>
  `mem_bytes_at p 32 t.vs_memory = mem_bytes_at p 32 s.vs_memory` by
    (`(p,32) IN {(p,32)}` by simp[] >>
     drule_all decode_site_effect_protected >> simp[]) >>
  gvs[mload_def, mem_bytes_at_def]
QED
