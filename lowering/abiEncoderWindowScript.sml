(* Source windows bound bytes read, while member offsets retain the declared
   layout. A final bytestring member need not occupy its full capacity. *)
Theory abiEncoderWindow
Ancestors
  abiEncoderOpenInput abiEncoderInput contractABI valueEncoding
  words list rich_list arithmetic abiEncoderInputFrame valueEncodingProofs abiDecodeRanges

Inductive abi_encoder_window_input:
[window_word:]
  (!at av sb cap mem.
    has_type at av /\ ~is_dynamic at /\ static_length at = 32 /\
    32 <= cap /\ mem_bytes_at sb 32 mem = enc at av ==>
    abi_encoder_window_input AbiPrimWord at av sb cap mem)
[window_copy:]
  (!sz at av sb cap mem.
    has_type at av /\ ~is_dynamic at /\ static_length at = sz /\
    sz <= cap /\ mem_bytes_at sb sz mem = enc at av ==>
    abi_encoder_window_input (AbiCopy sz) at av sb cap mem)
[window_bytes:]
  (!maxlen at bs sb cap mem.
    (at = Bytes NONE \/ at = String) /\ has_type at (BytesV bs) /\
    LENGTH bs <= maxlen /\ 32 + LENGTH bs <= cap /\
    mem_word_at sb mem = n2w (LENGTH bs) /\
    mem_bytes_at (sb + 32) (LENGTH bs) mem = bs ==>
    abi_encoder_window_input (AbiBytestring maxlen) at (BytesV bs)
      sb cap mem)
[window_array:]
  (!ei abi_sz mem_sz dyn ct avs sb cap mem.
    valid_length NONE avs /\
    abi_sz = abi_member_head_size ct /\ dyn = is_dynamic ct /\
    32 <= cap /\ mem_word_at sb mem = n2w (LENGTH avs) /\
    (!i. i < LENGTH avs ==>
      ?child_cap.
        child_cap <= mem_sz /\
        32 + i * mem_sz + child_cap <= cap /\
        abi_encoder_window_input ei ct (EL i avs)
          (sb + 32 + i * mem_sz) child_cap mem) ==>
    abi_encoder_window_input (AbiDynArray ei abi_sz mem_sz dyn)
      (Array NONE ct) (ListV avs) sb cap mem)
[window_complex:]
  (!infos at ats avs sb cap mem.
    abi_encoder_tuple_type at ats /\
    LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs /\
    (!i ei abi_sz mem_sz dyn.
      i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      abi_sz = abi_member_head_size (EL i ats) /\
      dyn = is_dynamic (EL i ats) /\
      ?child_cap.
        child_cap <= mem_sz /\
        abi_encoder_member_span (TAKE i infos) + child_cap <= cap /\
        abi_encoder_window_input ei (EL i ats) (EL i avs)
          (sb + abi_encoder_member_span (TAKE i infos)) child_cap mem) ==>
    abi_encoder_window_input (AbiComplex infos) at (ListV avs)
      sb cap mem)
End

Theorem abi_encoder_window_input_capacity:
  abi_encoder_window_input ei at av sb cap mem /\ cap <= larger ==>
  abi_encoder_window_input ei at av sb larger mem
Proof
  strip_tac >>
  qpat_x_assum `abi_encoder_window_input _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [abi_encoder_window_input_cases]) >>
  gvs[] >> ONCE_REWRITE_TAC [abi_encoder_window_input_cases] >>
  asm_simp_tac (srw_ss()) [LET_THM] >>
  gvs[AC ADD_COMM ADD_ASSOC, MULT_COMM]
  >>~- ([`abi_encoder_tuple_type at ats`],
        qexists_tac `ats` >> simp[] >> metis_tac[LESS_EQ_TRANS]) >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem abi_encoder_window_input_valid:
  !ei at av sb cap mem. abi_encoder_window_input ei at av sb cap mem ==>
    abi_encoder_structural_valid at av
Proof
  ho_match_mp_tac abi_encoder_window_input_ind >> rpt strip_tac
  >- metis_tac[cj 1 abi_encoder_structural_valid_rules]
  >- metis_tac[cj 1 abi_encoder_structural_valid_rules]
  >- metis_tac[cj 1 abi_encoder_structural_valid_rules]
  >- metis_tac[cj 1 abi_encoder_structural_valid_rules]
  >- (irule (cj 3 abi_encoder_structural_valid_rules) >> metis_tac[]) >>
  irule (cj 2 abi_encoder_structural_valid_rules) >>
  qexists_tac `ats` >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
  Cases_on `EL i infos` >> PairCases_on `r` >> metis_tac[]
QED

Theorem abi_encoder_window_word_iff:
  abi_encoder_window_input AbiPrimWord at av sb cap mem <=>
  has_type at av /\ ~is_dynamic at /\ static_length at = 32 /\
  32 <= cap /\ mem_bytes_at sb 32 mem = enc at av
Proof
  simp[Once abi_encoder_window_input_cases]
QED

Theorem abi_encoder_window_copy_iff:
  abi_encoder_window_input (AbiCopy sz) at av sb cap mem <=>
  has_type at av /\ ~is_dynamic at /\ static_length at = sz /\
  sz <= cap /\ mem_bytes_at sb sz mem = enc at av
Proof
  simp[Once abi_encoder_window_input_cases] >> metis_tac[]
QED

Theorem abi_encoder_window_bytes_iff:
  abi_encoder_window_input (AbiBytestring maxlen) at av sb cap mem <=>
  ?bs. av = BytesV bs /\ (at = Bytes NONE \/ at = String) /\
    has_type at (BytesV bs) /\ LENGTH bs <= maxlen /\
    32 + LENGTH bs <= cap /\ mem_word_at sb mem = n2w (LENGTH bs) /\
    mem_bytes_at (sb + 32) (LENGTH bs) mem = bs
Proof
  simp[Once abi_encoder_window_input_cases] >> metis_tac[]
QED

Theorem abi_encoder_window_array_iff:
  abi_encoder_window_input (AbiDynArray ei abi_sz mem_sz dyn) at av sb cap mem <=>
  ?ct avs. at = Array NONE ct /\ av = ListV avs /\
    valid_length NONE avs /\ abi_sz = abi_member_head_size ct /\
    dyn = is_dynamic ct /\ 32 <= cap /\
    mem_word_at sb mem = n2w (LENGTH avs) /\
    (!i. i < LENGTH avs ==>
      ?child_cap. child_cap <= mem_sz /\
        32 + i * mem_sz + child_cap <= cap /\
        abi_encoder_window_input ei ct (EL i avs)
          (sb + 32 + i * mem_sz) child_cap mem)
Proof
  simp[Once abi_encoder_window_input_cases] >> metis_tac[]
QED

Theorem abi_encoder_window_complex_iff:
  abi_encoder_window_input (AbiComplex infos) at av sb cap mem <=>
  ?ats avs. av = ListV avs /\ abi_encoder_tuple_type at ats /\
    LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs /\
    (!i ei abi_sz mem_sz dyn.
      i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      abi_sz = abi_member_head_size (EL i ats) /\
      dyn = is_dynamic (EL i ats) /\
      ?child_cap. child_cap <= mem_sz /\
        abi_encoder_member_span (TAKE i infos) + child_cap <= cap /\
        abi_encoder_window_input ei (EL i ats) (EL i avs)
          (sb + abi_encoder_member_span (TAKE i infos)) child_cap mem)
Proof
  simp[Once abi_encoder_window_input_cases] >> metis_tac[]
QED

Theorem abi_encoder_window_input_mem_agree:
  !ei at av sb cap mem. abi_encoder_window_input ei at av sb cap mem ==>
  !mem'. mem_bytes_at sb cap mem = mem_bytes_at sb cap mem' ==>
    abi_encoder_window_input ei at av sb cap mem'
Proof
  ho_match_mp_tac abi_encoder_window_input_ind >> rpt conj_tac
  >- (rpt strip_tac >> irule window_word >> simp[] >>
      drule abi_encoder_window_slice >>
      disch_then (qspecl_then [`0`, `32`] mp_tac) >> simp[])
  >- (rpt strip_tac >> irule window_copy >> simp[] >>
      drule abi_encoder_window_slice >>
      disch_then (qspecl_then [`0`, `sz`] mp_tac) >> simp[])
  >- (rpt strip_tac >> (irule window_bytes >> simp[] >>
      conj_tac
      >- (drule abi_encoder_window_word >>
          disch_then (qspec_then `0` mp_tac) >> simp[]) >>
      drule abi_encoder_window_slice >>
      disch_then (qspecl_then [`32`, `LENGTH bs`] mp_tac) >> simp[]))
  >- (rpt strip_tac >> irule window_array >> simp[] >>
      reverse conj_tac
      >- (drule abi_encoder_window_word >>
          disch_then (qspec_then `0` mp_tac) >> simp[]) >>
      rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >>
      simp[] >> strip_tac >> rename1 `small <= mem_sz` >>
      qexists_tac `small` >> simp[] >>
      first_x_assum irule >>
      irule EQ_SYM >> irule abi_encoder_window_slice >>
      qexists_tac `cap` >> simp[AC ADD_COMM ADD_ASSOC]) >>
  rpt strip_tac >> irule window_complex >> simp[] >>
  qexists_tac `ats` >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`i`, `ei`, `abi_sz`, `mem_sz`, `dyn`] mp_tac) >>
  simp[] >> strip_tac >> simp[] >> rename1 `small <= mem_sz` >>
  qexists_tac `small` >> simp[] >>
  first_x_assum irule >>
  irule EQ_SYM >> irule abi_encoder_window_slice >>
  qexists_tac `cap` >> simp[]
QED

Theorem abi_encoder_window_input_bytewise:
  abi_encoder_window_input ei at av sb cap mem /\
  (!a. sb <= a /\ a < sb + cap ==>
    mem_bytes_at a 1 mem' = mem_bytes_at a 1 mem) ==>
  abi_encoder_window_input ei at av sb cap mem'
Proof
  strip_tac >> drule abi_encoder_window_input_mem_agree >>
  disch_then irule >> irule EQ_SYM >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `sb + x` mp_tac) >> simp[] >>
  disch_then (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]
QED

Theorem abi_encoder_window_array_child:
  abi_encoder_window_input (AbiDynArray ei abi_sz mem_sz dyn)
    (Array NONE ct) (ListV avs) sb cap mem /\ i < LENGTH avs ==>
  ?child_cap. child_cap <= mem_sz /\
    sb + 32 + i * mem_sz + child_cap <= sb + cap /\
    abi_encoder_window_input ei ct (EL i avs)
      (sb + 32 + i * mem_sz) child_cap mem
Proof
  simp[abi_encoder_window_array_iff] >> rpt strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
  strip_tac >> rename1 `small <= mem_sz` >> qexists_tac `small` >>
  simp[] >> decide_tac
QED

Theorem abi_encoder_window_complex_child:
  abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb cap mem /\
  i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
  ?ats child_cap.
    abi_encoder_tuple_type at ats /\ LENGTH infos = LENGTH ats /\
    LENGTH ats = LENGTH avs /\
    abi_sz = abi_member_head_size (EL i ats) /\
    dyn = is_dynamic (EL i ats) /\ child_cap <= mem_sz /\
    sb + abi_encoder_member_span (TAKE i infos) + child_cap <= sb + cap /\
    abi_encoder_window_input ei (EL i ats) (EL i avs)
      (sb + abi_encoder_member_span (TAKE i infos)) child_cap mem
Proof
  simp[abi_encoder_window_complex_iff] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`i`, `ei`, `abi_sz`, `mem_sz`, `dyn`] mp_tac) >>
  simp[] >> strip_tac >> rename1 `small <= mem_sz` >>
  qexistsl_tac [`ats`, `small`] >> simp[] >> decide_tac
QED

Theorem abi_encoder_window_complex_nil:
  abi_encoder_window_input (AbiComplex []) (Tuple tys) (ListV avs) sb cap mem <=>
  tys = [] /\ avs = []
Proof
  simp[abi_encoder_window_complex_iff, abi_encoder_tuple_type_def] >>
  metis_tac[LENGTH_NIL]
QED

Theorem abi_encoder_window_input_empty_memory:
  abi_encoder_window_input ei at av sb 0 mem ==>
  abi_encoder_window_input ei at av sb 0 mem'
Proof
  strip_tac >> irule abi_encoder_window_input_bytewise >>
  qexists_tac `mem` >> simp[]
QED

Theorem abi_encoder_window_singleton_bytes:
  (ct = Bytes NONE \/ ct = String) /\ has_type ct (BytesV bs) /\
  LENGTH bs <= maxlen /\ 32 + LENGTH bs <= mem_sz /\
  mem_word_at sb mem = n2w (LENGTH bs) /\
  mem_bytes_at (sb + 32) (LENGTH bs) mem = bs ==>
  abi_encoder_window_input
    (AbiComplex [(AbiBytestring maxlen,32,mem_sz,T)])
    (Tuple [ct]) (ListV [BytesV bs]) sb (32 + LENGTH bs) mem
Proof
  strip_tac >> simp[abi_encoder_window_complex_iff,
    abi_encoder_tuple_type_def, abi_encoder_member_span_def,
    abi_member_head_size_def, is_dynamic_def] >>
  qexists_tac `32 + LENGTH bs` >> simp[abi_encoder_window_bytes_iff] >>
  gvs[has_type_def]
QED

Theorem abi_encoder_open_input_window:
  !ei at av sb cap mem. abi_encoder_open_input ei at av sb cap mem ==>
  abi_encoder_window_input ei at av sb cap mem
Proof
  ho_match_mp_tac abi_encoder_open_input_ind >> rpt conj_tac
  >- (rpt strip_tac >> irule window_word >> simp[])
  >- (rpt strip_tac >> irule window_copy >> simp[])
  >- (rpt strip_tac >> irule window_bytes >> simp[])
  >- (rpt strip_tac >> irule window_array >> simp[] >>
      rpt strip_tac >>
      qexists_tac `mem_sz` >> simp[] >>
      reverse conj_tac
      >- (first_x_assum drule >>
          simp_tac (srw_ss()) [AC ADD_COMM ADD_ASSOC]) >>
      `32 + i * mem_sz + mem_sz <= cap` by
        (irule abi_encoder_array_slot_bound >>
         qexists_tac `LENGTH avs` >> simp[MULT_COMM]) >> decide_tac) >>
  rpt strip_tac >> irule window_complex >> simp[] >>
  qexists_tac `ats` >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`i`, `ei`, `abi_sz`, `mem_sz`, `dyn`] mp_tac) >>
  simp[] >> strip_tac >> simp[] >> qexists_tac `mem_sz` >> simp[] >>
  `i < LENGTH infos` by simp[] >>
  drule_all abi_encoder_member_slot_bound >> decide_tac
QED

Theorem abi_encoder_open_bytes_actual_window:
  abi_encoder_open_input (AbiBytestring maxlen) ct (BytesV bs) sb cap mem ==>
  abi_encoder_window_input (AbiBytestring maxlen) ct (BytesV bs)
    sb (32 + LENGTH bs) mem
Proof
  simp[Once abi_encoder_open_input_cases, abi_encoder_window_bytes_iff] >>
  metis_tac[]
QED
