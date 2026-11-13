Theory entryReachBodyRegistrationPrefixSupport
Ancestors
  entryReachBodyCanonicalArrayChild abiEncoderRegisteredEffect
  abiEncoderWindowContract abiDecoderAllocation venomState finite_map pred_set arithmetic

Theorem registration_empty_support:
  s.vs_allocas = FEMPTY ==>
  !id r. FLOOKUP s.vs_allocas id = SOME r ==> id < cut
Proof
  simp[]
QED

Theorem registration_support_absent:
  (!id r. FLOOKUP s.vs_allocas id = SOME r ==> id < cut) /\
  cut <= id ==> FLOOKUP s.vs_allocas id = NONE
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id` >> simp[] >>
  first_x_assum drule >> decide_tac
QED

Theorem registration_slot_support:
  (!id r. FLOOKUP initial.vs_allocas id = SOME r ==> id < k) /\
  k < lo /\ lo <= hi /\
  (!id. id <> k ==> FLOOKUP ready.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
  abi_encoder_registered_effect
    (window_alloca_sites fn (abi_decoder_ids lo hi)) outs ready t ==>
  !id r. FLOOKUP t.vs_allocas id = SOME r ==> id < hi
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `id = k` >- decide_tac >>
  Cases_on `id IN window_alloca_sites fn (abi_decoder_ids lo hi)`
  >- fs[window_alloca_sites_def, abi_decoder_ids_def] >>
  `FLOOKUP ready.vs_allocas id = SOME r` by
    (fs[abi_encoder_registered_effect_def] >> metis_tac[]) >>
  `FLOOKUP initial.vs_allocas id = SOME r` by metis_tac[] >>
  `id < k` by metis_tac[] >> decide_tac
QED

Theorem registration_result_support:
  (!id r. FLOOKUP initial.vs_allocas id = SOME r ==> id < k) /\
  k < first.cs_next_id /\ first.cs_next_id <= last.cs_next_id /\
  (!id. id <> k ==> FLOOKUP ready.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
  array_child_result ctx fn k root extent ambient
    (window_alloca_sites fn (abi_decoder_ids first.cs_next_id last.cs_next_id))
    b cap site limit first last cell tv value ready t ==>
  !id r. FLOOKUP t.vs_allocas id = SOME r ==> id < last.cs_next_id
Proof
  strip_tac >> fs[array_child_result_def] >>
  rpt gen_tac >> strip_tac >>
  irule registration_slot_support >>
  qexistsl [`fn`, `initial`, `k`, `first.cs_next_id`,
            `[(cell,type_memory_size tv)]`, `r`, `ready`, `t`] >> simp[]
QED
