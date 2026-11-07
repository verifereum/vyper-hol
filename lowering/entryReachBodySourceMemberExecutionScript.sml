(* Source semantic advancement for the shared member execution engine. *)
Theory entryReachBodySourceMemberExecution
Ancestors
  entryReachBodySourceMemberCoreProbe entryReachBodyMemberExecutionCore
  entryReachBodySourceAggregateInputs entryReachBodySourceMemberEntry
  entryReachBodySourceProducer entryReachBodyCanonicalArrayChild
  entryReachBodyMemberPrefix entryReachBodyOwnedRegion
  entryReachBodyExactArrayLoop abiEncoderRegisteredEffect abiDecoderContract
  abiDecoderCoherence valueEncodingTyping valueEncoding list rich_list arithmetic pred_set
  entryReachBodyMemberSetup abiDecoderEmpty abiDecoderComplexHead abiDecoderOffset
  abiDecoderDynamic abiDecoderReentry abiEncoder compileEnv emitHelper

Theorem source_members_append[local]:
  !pre pt pa pv tys tvs avs vs.
  entry_source_members ce env sf pre pt pa pv /\
  entry_source_members ce env sf tys tvs avs vs ==>
  entry_source_members ce env sf (pre++tys) (pt++tvs) (pa++avs) (pv++vs)
Proof
  Induct >> Cases_on `pt` >> Cases_on `pa` >> Cases_on `pv` >>
  simp[entry_source_members_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem source_members_wf[local]:
  !tys tvs avs vs. entry_source_members ce env sf tys tvs avs vs ==>
  LIST_REL val_wf tvs vs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `avs` >> Cases_on `vs` >>
  simp[entry_source_members_def, entry_source_metadata_def] >> rpt gen_tac >> strip_tac >>
  conj_tac >- (irule (cj 1 value_has_type_val_wf) >> goal_assum (drule_at Any)) >>
  first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem source_member_prefix_extend[local]:
  entry_source_members ce env sf pre pt pa pv /\
  tuple_in_memory pv pt d s.vs_memory /\
  entry_owned_region oid root extent d outsz s /\
  SUM (MAP (type_memory_bytes ce) pre) <= outsz /\ oid NOTIN ids /\
  abi_encoder_registered_effect ids
    [(d + SUM (MAP (type_memory_bytes ce) pre),sz)] s t /\ alloca_inv t /\
  val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pre)) t.vs_memory ==>
  tuple_in_memory (pv++[v]) (pt++[tv]) d t.vs_memory
Proof
  strip_tac >>
  `LIST_REL val_wf pt pv` by metis_tac[source_members_wf] >>
  drule entry_source_members_lengths >> strip_tac >>
  drule entry_source_members_memory_sizes >> strip_tac >>
  irule entry_member_memory_extend >> metis_tac[]
QED

Theorem source_member_semantics_advance[local]:
  entry_source_members ce env sf pre pt pa pv /\
  entry_source_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  tuple_in_memory pv pt d s.vs_memory /\
  entry_owned_region oid root extent d
    (SUM (MAP (type_memory_bytes ce) (pre++ty::tys))) s /\ oid NOTIN ids /\
  abi_encoder_registered_effect ids
    [(d+SUM (MAP (type_memory_bytes ce) pre),type_memory_size tv)] s t /\
  alloca_inv t /\ val_in_memory tv v
    (d+SUM (MAP (type_memory_bytes ce) pre)) t.vs_memory ==>
  entry_source_members ce env sf (pre++[ty]) (pt++[tv]) (pa++[av]) (pv++[v]) /\
  entry_source_members ce env sf tys tvs avs vs /\
  tuple_in_memory (pv++[v]) (pt++[tv]) d t.vs_memory
Proof
  strip_tac >>
  `entry_source_members ce env sf [ty] [tv] [av] [v] /\
   entry_source_members ce env sf tys tvs avs vs` by fs[entry_source_members_def] >>
  `entry_source_members ce env sf (pre++[ty]) (pt++[tv]) (pa++[av]) (pv++[v])` by
    (irule source_members_append >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >> irule source_member_prefix_extend >>
  qpat_assum `abi_encoder_registered_effect _ _ s t` (irule_at Any) >>
  qpat_assum `entry_owned_region _ _ _ _ _ s` (irule_at Any) >>
  qpat_assum `entry_source_members _ _ _ pre _ _ _` (irule_at Any) >>
  simp[SUM_APPEND, MAP_APPEND]
QED

Theorem source_empty_member_endpoint[local]:
  abi_decoder_coherent ce env sf ty tv /\
  entry_source_metadata ce env sf ty tv (DecComplex T []) av v /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] /\
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w)
    (dec_info_needs_offset (DecComplex T [])) ao vo st = (ops,mid) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w)
    (DecComplex T []) mid = ((),last) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. entry_decode_path ctx fn s u /\ val_in_memory tv v (d+vo) u.vs_memory /\
    type_memory_size tv = 0 /\ entry_loop_fields s u /\
    abi_decoder_address_frame st.cs_next_var s u /\ fresh_vars_wrt limit_st u /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ ~u.vs_halted /\
    u.vs_current_bb = last.cs_current_bb /\ u.vs_inst_idx = LENGTH last.cs_current_insts
Proof
  strip_tac >>
  `last = mid` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_empty_complex_phases, abi_decode_complex_head_guard_def, comp_return_def]) >>
  gvs[] >>
  drule_all entry_source_empty_descriptor_value >> strip_tac >>
  `~dec_info_needs_offset (DecComplex T [])` by simp[abi_decoder_needs_offset_iff] >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  mp_tac (Q.INST [`dyn` |-> `F`, `mid` |-> `last`, `ctx` |-> `ctx`]
    entry_member_setup_endpoint) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >> qexists_tac `u` >> simp[]
QED
