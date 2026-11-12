(* Semantic support observes initialized live bytes, not spare array capacity. *)
Theory ctorDeployMemoryRunPtrPrefixCopySupport
Ancestors
  valueEncodingDefs
  ctorDeployMemoryRunPtrPrefixCanonical valueEncodingProps valueEncodingTyping
  abiDecoderCoherence abiDecoderTypedContract ptrDiscipline
  valueEncoding vyperTyping list pred_set

Theorem prefix_copy_capacity_support:
  val_in_memory tv v d m /\ val_wf tv v /\ type_memory_size tv <= n /\
  (!a. a IN range_bytes [(d,n)] ==>
       mem_bytes_at a 1 mem = mem_bytes_at a 1 m) ==>
  val_in_memory tv v d mem
Proof
  strip_tac >> irule val_in_memory_mem_agree >>
  conj_tac >- simp[] >> qexistsl [`n`,`m`] >> simp[] >>
  irule prefix_canonical_support_window >> qexists `range_bytes [(d,n)]` >>
  simp[range_bytes_def]
QED

Theorem prefix_copy_canonical_capacity_support:
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  val_in_memory tv v d m /\
  (!a. a IN range_bytes [(d,type_memory_bytes ce ty)] ==>
       mem_bytes_at a 1 mem = mem_bytes_at a 1 m) ==>
  val_in_memory tv v d mem
Proof
  strip_tac >>
  drule abi_decoder_coherent_header >> simp[abi_decoder_header_def] >> strip_tac >>
  `value_has_type tv v` by gvs[abi_decoder_metadata_def] >>
  drule (cj 1 value_has_type_val_wf) >> strip_tac >>
  irule prefix_copy_capacity_support >> simp[] >>
  qexistsl [`m`,`type_memory_bytes ce ty`] >> simp[]
QED

Theorem prefix_copy_elements_support:
  !vs d tv m mem.
  elems_in_memory vs d tv m /\ elems_val_wf vs tv /\
  (!a. a IN range_bytes [(d,LENGTH vs * type_memory_size tv)] ==>
       mem_bytes_at a 1 mem = mem_bytes_at a 1 m) ==>
  elems_in_memory vs d tv mem
Proof
  Induct >> simp[val_in_memory_def, val_wf_def] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule prefix_copy_capacity_support >> simp[] >>
      qexistsl [`m`,`type_memory_size tv`] >> simp[] >>
      rpt strip_tac >> first_x_assum irule >>
      gvs[range_bytes_def, arithmeticTheory.MULT_CLAUSES] >> decide_tac)
  >> first_x_assum irule >> simp[] >> qexists `m` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[range_bytes_def, arithmeticTheory.MULT_CLAUSES] >> decide_tac
QED

Theorem prefix_copy_dynarray_live_support:
  elems_val_wf vs tv /\
  val_in_memory (ArrayTV tv bd) (ArrayV (DynArrayV vs)) d m /\
  (!a. a IN range_bytes [(d,32+LENGTH vs * type_memory_size tv)] ==>
       mem_bytes_at a 1 mem = mem_bytes_at a 1 m) ==>
  val_in_memory (ArrayTV tv bd) (ArrayV (DynArrayV vs)) d mem
Proof
  strip_tac >> gvs[val_in_memory_def] >> conj_tac
  >- (`mem_bytes_at d 32 mem = mem_bytes_at d 32 m` by
        (irule prefix_canonical_support_window >>
         qexists `range_bytes [(d,32+LENGTH vs * type_memory_size tv)]` >>
         simp[range_bytes_def]) >>
      gvs[mem_word_at_def, GSYM mem_bytes_at_def])
  >> irule prefix_copy_elements_support >> simp[] >> qexists `m` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> gvs[range_bytes_def, arithmeticTheory.MULT_CLAUSES] >> decide_tac
QED

Theorem prefix_copy_range_finite:
  FINITE (range_bytes [(d,n)])
Proof
  irule SUBSET_FINITE_I >> qexists `count (d+n)` >>
  simp[range_bytes_def, SUBSET_DEF]
QED

Theorem prefix_copy_capacity_package:
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  val_in_memory tv v d m ==>
  FINITE (range_bytes [(d,type_memory_bytes ce ty)]) /\
  (!mem. (!a. a IN range_bytes [(d,type_memory_bytes ce ty)] ==>
       mem_bytes_at a 1 mem = mem_bytes_at a 1 m) ==>
     val_in_memory tv v d mem)
Proof
  strip_tac >> simp[prefix_copy_range_finite] >> rpt strip_tac >>
  irule prefix_copy_canonical_capacity_support >> metis_tac[]
QED

Theorem prefix_copy_dynarray_live_package:
  elems_val_wf vs tv /\ LENGTH vs <= maxn /\
  val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d m ==>
  FINITE (range_bytes [(d,32+LENGTH vs * type_memory_size tv)]) /\
  range_bytes [(d,32+LENGTH vs * type_memory_size tv)] SUBSET
    range_bytes [(d,type_memory_size (ArrayTV tv (Dynamic maxn)))] /\
  (!mem. (!a. a IN range_bytes [(d,32+LENGTH vs * type_memory_size tv)] ==>
       mem_bytes_at a 1 mem = mem_bytes_at a 1 m) ==>
     val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d mem)
Proof
  strip_tac >> simp[prefix_copy_range_finite] >> conj_tac
  >- (`LENGTH vs * type_memory_size tv <= maxn * type_memory_size tv` by
        simp[arithmeticTheory.LE_MULT_RCANCEL] >>
      simp[SUBSET_DEF, range_bytes_def, type_memory_size_def])
  >> rpt strip_tac >> irule prefix_copy_dynarray_live_support >>
  simp[] >> qexists `m` >> simp[arithmeticTheory.ADD_COMM]
QED

Theorem prefix_copy_canonical_dynarray_package:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) root_di av (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d m ==>
  FINITE (range_bytes [(d,32+LENGTH vs * type_memory_size tv)]) /\
  range_bytes [(d,32+LENGTH vs * type_memory_size tv)] SUBSET
    range_bytes [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))] /\
  (!mem. (!a. a IN range_bytes [(d,32+LENGTH vs * type_memory_size tv)] ==>
       mem_bytes_at a 1 mem = mem_bytes_at a 1 m) ==>
     val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d mem)
Proof
  strip_tac >>
  drule abi_decoder_coherent_header >> simp[abi_decoder_header_def] >> strip_tac >>
  `value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs))` by
    gvs[abi_decoder_metadata_def] >>
  `val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs))` by
    metis_tac[cj 1 value_has_type_val_wf] >>
  `elems_val_wf vs tv /\ LENGTH vs <= maxn` by gvs[val_wf_def] >>
  drule_all prefix_copy_dynarray_live_package >>
  simp[arithmeticTheory.ADD_COMM]
QED

val _ = export_theory();
