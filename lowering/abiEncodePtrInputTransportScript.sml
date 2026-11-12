(* Robust encoder inputs depend only on clean observations in their window. *)
Theory abiEncodePtrInputTransport
Ancestors
  abiEncoderWindow representationCleanPtr valueEncodingProps bodyPtrDefs
  venomState venomMemDefs list arithmetic

Theorem abi_encode_robust_window_transport:
  (!mem. mem_agree_outside old_t old_mem mem ==>
     abi_encoder_window_input ei at av sb cap mem) /\
  (!i. sb <= i /\ i < sb+cap /\ i NOTIN old_t ==>
     i NOTIN new_t /\ mem_bytes_at i 1 new_mem = mem_bytes_at i 1 old_mem) ==>
  !mem. mem_agree_outside new_t new_mem mem ==>
    abi_encoder_window_input ei at av sb cap mem
Proof
  rpt strip_tac >>
  qabbrev_tac `s = (ARB:venom_state) with vs_memory := old_mem` >>
  qabbrev_tac `mix =
    (write_memory_with_expansion sb (mem_bytes_at sb cap mem) s).vs_memory` >>
  `mem_bytes_at sb cap mix = mem_bytes_at sb cap mem` by
    (qspec_then `sb` mp_tac write_memory_mem_bytes_at_same >>
     disch_then (qspecl_then [`mem_bytes_at sb cap mem`, `s`] mp_tac) >>
     simp[Abbr `mix`]) >>
  `mem_agree_outside old_t old_mem mix` by
    (simp[mem_agree_outside_def] >> rpt strip_tac >>
     Cases_on `sb <= i /\ i < sb+cap`
     >- (`mem_bytes_at i 1 mix = mem_bytes_at i 1 mem` by
           (irule mem_bytes_at_eq_byte >> goal_assum (drule_at Any) >> simp[]) >>
         fs[mem_agree_outside_def] >> metis_tac[]) >>
     sym_tac >> simp[Abbr `mix`] >>
     irule EQ_TRANS >> qexists `mem_bytes_at i 1 s.vs_memory` >>
     conj_tac
     >- (irule write_memory_mem_bytes_at_disjoint >> simp[] >> decide_tac) >>
     simp[Abbr `s`]) >>
  `abi_encoder_window_input ei at av sb cap mix` by metis_tac[] >>
  irule abi_encoder_window_input_bytewise >>
  qexists `mix` >> simp[] >> rpt strip_tac >>
  metis_tac[mem_bytes_at_eq_byte, ADD_COMM]
QED
