Theory bodyFullAbiDecodeStoreContents
Ancestors
  valueEncodingProps venomState venomExecSemantics list pair words

(* The currently mutable counter is excluded from snapshots.  Input bytes,
   enclosing counters and completed output prefixes are all covered by the
   same concrete disjoint-interval premise. *)
Theorem abi_decode_mstore_snapshots:
  EVERY (\(a,bytes). a + LENGTH bytes <= cell \/ cell + 32 <= a) snapshots /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) snapshots ==>
  EVERY (\(a,bytes).
    mem_bytes_at a (LENGTH bytes) (mstore cell w s).vs_memory = bytes) snapshots /\
  (mstore cell w s).vs_allocas = s.vs_allocas /\
  (mstore cell w s).vs_alloca_next = s.vs_alloca_next /\
  (!p. lookup_var p (mstore cell w s) = lookup_var p s)
Proof
  strip_tac >> conj_tac
  >- (fs[EVERY_MEM] >> gen_tac >> strip_tac >>
      rename1 `MEM item snapshots` >> PairCases_on `item` >>
      qpat_x_assum `!e. MEM e snapshots ==> _` (qspec_then `(item0,item1)` mp_tac) >>
      qpat_x_assum `!e. MEM e snapshots ==> _` (qspec_then `(item0,item1)` mp_tac) >>
      simp[] >> rpt strip_tac >>
      metis_tac[mstore_mem_bytes_at_disjoint]) >>
  simp[mstore_def, lookup_var_def]
QED

(* Memory addresses are naturals in mstore; word conversion constrains the
   stored value, not the address, so readback needs no address bound. *)
Theorem abi_decode_counter_store_value:
  mem_word_at cell (mstore cell (n2w (SUC j)) s).vs_memory = n2w (SUC j)
Proof
  simp[mstore_mem_word_at_same]
QED
