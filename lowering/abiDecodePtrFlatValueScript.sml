(* Semantic sensitivity excludes unused bytestring capacity. *)
Theory abiDecodePtrFlatValue
Ancestors
  exprPtrCleanBufferPost exprSimProps valueEncoding valueEncodingProps
  bodyPtrDefs venomState words list arithmetic vfmConstants
  abiDecodePtrMemberFrame exprSimBufferStore contractABI vyperTypeABI

Theorem clean_footprint_value_robust:
  val_in_memory tv v off mem /\ val_wf tv v /\
  (!i. off <= i /\ i < off+val_footprint tv v ==> i NOTIN dirty) ==>
  !mem'. mem_agree_outside dirty mem mem' ==> val_in_memory tv v off mem'
Proof
  rpt strip_tac >> irule val_in_memory_footprint_agree >>
  simp[] >> qexists_tac `mem` >> simp[] >>
  irule clean_window_memory_agree >> qexists_tac `dirty` >> simp[]
QED

(* Member robustness composes without requiring tuple padding to be clean. *)
Theorem abi_decode_tuple_robust_cons:
  (!mem'. mem_agree_outside dirty mem mem' ==> val_in_memory tv v off mem') /\
  (!mem'. mem_agree_outside dirty mem mem' ==>
    tuple_in_memory vs tvs (off+type_memory_size tv) mem') ==>
  !mem'. mem_agree_outside dirty mem mem' ==>
    tuple_in_memory (v::vs) (tv::tvs) off mem'
Proof
  simp[Once val_in_memory_def]
QED

Theorem abi_decode_window_value_robust:
  abi_decode_ptr_window G tn s root b m /\
  val_in_memory tv v (w2n b) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= m ==>
  !mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory tv v (w2n b) mem'
Proof
  rpt strip_tac >> irule clean_footprint_value_robust >> simp[] >>
  qexistsl_tac [`tn.t_mem`, `s.vs_memory`] >> simp[] >>
  fs[abi_decode_ptr_window_def] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

(* The runtime header determines the sensitive size, not the declared cap. *)
Theorem abi_decode_bytestring_value_footprint:
  is_bytestring_type ty /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ val_in_memory tv v p s.vs_memory /\
  val_wf tv v /\ type_memory_size tv < dimword(:256) ==>
  val_footprint tv v <= 32+contractABI$ceil32 (w2n (mload p s))
Proof
  strip_tac >> drule_all buffer_typed_bytestring_header >> strip_tac >>
  `val_store_size tv v <= type_memory_size tv /\
   val_footprint tv v <= val_store_size tv v` by
    metis_tac[val_store_size_le, val_footprint_le_store_size] >>
  `len <= 32 * word_size len` by simp[le_word_size_mul] >>
  `len < dimword(:256)` by decide_tac >>
  simp[w2n_n2w, contractABITheory.ceil32_def, word_size_def] >>
  fs[word_size_def]
QED
