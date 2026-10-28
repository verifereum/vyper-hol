(*
 * Moving a value in memory (#636)
 *
 * val_in_memory lays a value out relative to its address, so when the
 * bytes at src + k and dst + k agree, every encoding predicate
 * (val_in_memory, fields_, elems_, kvs_ and tuple_in_memory) carries from
 * src to dst.  The footprint form needs only the footprint bytes to agree.
 *
 * TOP-LEVEL:
 *   val_in_memory_relocate_footprint — a value's footprint bytes at dst
 *     hold the value there
 *   encoding_relative_transport — the transport for all five predicates
 *   memory_bridge_window — padding memory so dst's bytes sit at src
 *
 * Helpers: memory_window_word, memory_relative_word,
 *   val_in_memory_relative_transport.
 *)
Theory exprSimMemoryTransport
Ancestors
  exprSim valueEncoding valueEncodingProps valueEncodingProofs list rich_list

Theorem memory_bridge_window:
  !src dst mem k n.
    mem_bytes_at (src + k) n (REPLICATE src 0w ++ DROP dst mem) =
    mem_bytes_at (dst + k) n mem
Proof
  simp[mem_bytes_at_def, DROP_APPEND2, DROP_DROP_T, arithmeticTheory.ADD_COMM]
QED

Theorem memory_window_word:
  !src dst mem mem'.
    mem_bytes_at src 32 mem = mem_bytes_at dst 32 mem' ==>
    mem_word_at src mem = mem_word_at dst mem'
Proof
  simp[mem_word_at_def, GSYM mem_bytes_at_def]
QED

Theorem memory_relative_word:
  !src dst mem mem'.
    (!k n. mem_bytes_at (src+k) n mem = mem_bytes_at (dst+k) n mem') ==>
    mem_word_at src mem = mem_word_at dst mem'
Proof
  rpt strip_tac >> irule memory_window_word >>
  first_x_assum (qspecl_then [`0`, `32`] mp_tac) >> simp[]
QED

Theorem encoding_relative_transport:
  (!tv v src mem dst mem'.
    val_in_memory tv v src mem /\
    (!k n. mem_bytes_at (src+k) n mem = mem_bytes_at (dst+k) n mem') ==>
    val_in_memory tv v dst mem') /\
  (!fs tvs src mem dst mem'.
    fields_in_memory fs tvs src mem /\
    (!k n. mem_bytes_at (src+k) n mem = mem_bytes_at (dst+k) n mem') ==>
    fields_in_memory fs tvs dst mem') /\
  (!vs src tv mem dst mem'.
    elems_in_memory vs src tv mem /\
    (!k n. mem_bytes_at (src+k) n mem = mem_bytes_at (dst+k) n mem') ==>
    elems_in_memory vs dst tv mem') /\
  (!kvs src tv mem dst mem'.
    kvs_in_memory kvs src tv mem /\
    (!k n. mem_bytes_at (src+k) n mem = mem_bytes_at (dst+k) n mem') ==>
    kvs_in_memory kvs dst tv mem') /\
  (!vs tvs src mem dst mem'.
    tuple_in_memory vs tvs src mem /\
    (!k n. mem_bytes_at (src+k) n mem = mem_bytes_at (dst+k) n mem') ==>
    tuple_in_memory vs tvs dst mem')
Proof
  ho_match_mp_tac val_in_memory_ind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >>
  drule memory_relative_word >> strip_tac
  >~ [`val_in_memory _ (BoolV _) _ _`]
  >- gvs[val_in_memory_def]
  >~ [`val_in_memory _ (IntV _) _ _`]
  >- gvs[val_in_memory_def]
  >~ [`val_in_memory _ (FlagV _) _ _`]
  >- gvs[val_in_memory_def]
  >~ [`val_in_memory _ (DecimalV _) _ _`]
  >- gvs[val_in_memory_def]
  >~ [`val_in_memory _ NoneV _ _`]
  >- simp[val_in_memory_def]
  >~ [`fields_in_memory [] _ _ _`]
  >- simp[val_in_memory_def]
  >~ [`elems_in_memory [] _ _ _`]
  >- simp[val_in_memory_def]
  >~ [`kvs_in_memory [] _ _ _`]
  >- simp[val_in_memory_def]
  >~ [`tuple_in_memory [] _ _ _`]
  >- simp[val_in_memory_def]
  >~ [`val_in_memory _ (BytesV _) _ _`]
  >- suspend "bytes"
  >~ [`val_in_memory _ (StringV _) _ _`]
  >- suspend "string"
  >~ [`val_in_memory _ (StructV _) _ _`]
  >- suspend "struct"
  >~ [`val_in_memory _ (ArrayV (DynArrayV _)) _ _`]
  >- suspend "dynamic"
  >~ [`val_in_memory _ (ArrayV (SArrayV _)) _ _`]
  >- suspend "sparse"
  >~ [`val_in_memory _ (ArrayV (TupleV _)) _ _`]
  >- suspend "tuple"
  >~ [`fields_in_memory (_::_) _ _ _`]
  >- suspend "fields"
  >~ [`elems_in_memory (_::_) _ _ _`]
  >- suspend "elems"
  >~ [`kvs_in_memory (_::_) _ _ _`]
  >- suspend "kvs"
  >> suspend "tuples"
QED

Resume encoding_relative_transport[bytes]:
  `mem_bytes_at (src+32) (LENGTH bs) mem =
   mem_bytes_at (dst+32) (LENGTH bs) mem'` by simp[] >>
  Cases_on `tv` >> gvs[val_in_memory_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Resume encoding_relative_transport[string]:
  gvs[val_in_memory_def]
QED

Resume encoding_relative_transport[struct]:
  Cases_on `tv` >> gvs[val_in_memory_def] >>
  first_x_assum irule >> simp[]
QED

Resume encoding_relative_transport[dynamic]:
  Cases_on `tv` >> gvs[val_in_memory_def] >>
  first_x_assum irule >> simp[] >> rpt gen_tac >>
  first_x_assum (qspecl_then [`k+32`, `n`] mp_tac) >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Resume encoding_relative_transport[sparse]:
  Cases_on `tv` >> gvs[val_in_memory_def] >>
  rpt strip_tac >>
  qpat_x_assum `!n i. _ ==> !dst' mem''. _`
    (qspecl_then [`n`, `i`] mp_tac) >> simp[] >>
  disch_then irule >> rpt gen_tac >>
  first_x_assum (qspecl_then [`i * type_memory_size t + k`, `n'`] mp_tac) >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Resume encoding_relative_transport[tuple]:
  Cases_on `tv` >> gvs[val_in_memory_def] >>
  first_x_assum irule >> simp[]
QED

Resume encoding_relative_transport[fields]:
  Cases_on `tvs`
  >- (gvs[val_in_memory_def] >> first_x_assum irule >> simp[] >>
      rpt gen_tac >>
      first_x_assum (qspecl_then [`type_memory_size (BaseTV BoolT)+k`, `n`] mp_tac) >>
      simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  PairCases_on `h` >> gvs[val_in_memory_def] >>
  first_x_assum irule >> simp[] >> rpt gen_tac >>
  first_x_assum (qspecl_then [`type_memory_size h1+k`, `n`] mp_tac) >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Resume encoding_relative_transport[elems]:
  gvs[val_in_memory_def] >> first_x_assum irule >> simp[] >>
  rpt gen_tac >>
  first_x_assum (qspecl_then [`type_memory_size tv+k`, `n`] mp_tac) >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Resume encoding_relative_transport[kvs]:
  gvs[val_in_memory_def] >> first_x_assum irule >> simp[] >>
  rpt gen_tac >>
  first_x_assum (qspecl_then [`k * type_memory_size tv+k'`, `n`] mp_tac) >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Resume encoding_relative_transport[tuples]:
  Cases_on `tvs`
  >- (gvs[val_in_memory_def] >> first_x_assum irule >> simp[] >>
      rpt gen_tac >>
      first_x_assum (qspecl_then [`type_memory_size (BaseTV BoolT)+k`, `n`] mp_tac) >>
      simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  gvs[val_in_memory_def] >> first_x_assum irule >> simp[] >>
  rpt gen_tac >>
  first_x_assum (qspecl_then [`type_memory_size h+k`, `n`] mp_tac) >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Finalise encoding_relative_transport

Theorem val_in_memory_relative_transport:
  !tv v src mem dst mem'.
    val_in_memory tv v src mem /\
    (!k n. mem_bytes_at (src+k) n mem = mem_bytes_at (dst+k) n mem') ==>
    val_in_memory tv v dst mem'
Proof
  ACCEPT_TAC (cj 1 encoding_relative_transport)
QED

Theorem val_in_memory_relocate_footprint:
  !tv v src dst mem mem'.
    val_in_memory tv v src mem /\ val_wf tv v /\
    mem_bytes_at src (val_footprint tv v) mem =
      mem_bytes_at dst (val_footprint tv v) mem' ==>
    val_in_memory tv v dst mem'
Proof
  rpt strip_tac >>
  qabbrev_tac `bridge = REPLICATE src 0w ++ DROP dst mem'` >>
  `!k n. mem_bytes_at (src+k) n bridge = mem_bytes_at (dst+k) n mem'` by
    simp[Abbr `bridge`, memory_bridge_window] >>
  `mem_bytes_at src (val_footprint tv v) mem =
   mem_bytes_at src (val_footprint tv v) bridge` by
    (first_x_assum (qspecl_then [`0`, `val_footprint tv v`] mp_tac) >> simp[]) >>
  `val_in_memory tv v src bridge` by
    (irule val_in_memory_footprint_agree >> simp[] >> qexists_tac `mem` >> simp[]) >>
  irule val_in_memory_relative_transport >>
  qexistsl_tac [`bridge`, `src`] >> simp[]
QED
