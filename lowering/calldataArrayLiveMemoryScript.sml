Theory calldataArrayLiveMemory
Ancestors
  valueEncodingDefs valueEncodingProofs logStoreDataOriginPtr
  abiStaticAggregateProps arithmetic

Theorem calldata_dynamic_array_live_memory:
  !etv maxn xs d mem mem' dead.
    val_in_memory (ArrayTV etv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d mem /\
    val_wf (ArrayTV etv (Dynamic maxn)) (ArrayV (DynArrayV xs)) /\
    mem_agree_outside dead mem mem' /\
    (!i. d <= i /\ i < d+32+LENGTH xs*type_memory_size etv ==> i NOTIN dead)
    ==>
    val_in_memory (ArrayTV etv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d mem'
Proof
  rpt strip_tac >> rename1 `mem_agree_outside excluded mem mem'` >>
  `mem_bytes_at d 32 mem = mem_bytes_at d 32 mem'` by
    (irule mem_agree_outside_window >>
     qexists_tac `excluded` >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> simp[]) >>
  `mem_bytes_at (d+32) (LENGTH xs * type_memory_size etv) mem =
   mem_bytes_at (d+32) (LENGTH xs * type_memory_size etv) mem'` by
    (irule mem_agree_outside_window >> qexists_tac `excluded` >>
     simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  gvs[val_in_memory_def, val_wf_def] >> conj_tac
  >- metis_tac[mem_word_at_bytes] >>
  irule (cj 3 val_in_memory_mem_agree_proof) >>
  simp[] >> qexists_tac `mem` >> simp[]
QED
