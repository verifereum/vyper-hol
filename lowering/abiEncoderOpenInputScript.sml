(* Cardinality-free aggregate source windows.  Leaf premises are unchanged;
   dynamic arrays still require a representable runtime element count. *)
Theory abiEncoderOpenInput
Ancestors
  abiEncoderInput
  abiDecodeRanges abiCanonicalWindows valueEncoding contractABI list rich_list arithmetic byte words

Inductive abi_encoder_structural_valid:
[typed:]
  (!at av. has_type at av ==> abi_encoder_structural_valid at av)
[tuple:]
  (!at ats avs.
    abi_encoder_tuple_type at ats /\ LENGTH ats = LENGTH avs /\
    (!i. i < LENGTH ats ==>
      abi_encoder_structural_valid (EL i ats) (EL i avs)) ==>
    abi_encoder_structural_valid at (ListV avs))
[structural_array:]
  (!ct avs. valid_length NONE avs /\
    (!i. i < LENGTH avs ==> abi_encoder_structural_valid ct (EL i avs)) ==>
    abi_encoder_structural_valid (Array NONE ct) (ListV avs))
End

Inductive abi_encoder_open_input:
[word:]
  (!at av sb cap mem.
    has_type at av /\ ~is_dynamic at /\ static_length at = 32 /\ 32 <= cap /\
    mem_bytes_at sb 32 mem = enc at av ==>
    abi_encoder_open_input AbiPrimWord at av sb cap mem)
[copy:]
  (!sz at av sb cap mem.
    has_type at av /\ ~is_dynamic at /\ static_length at = sz /\ sz <= cap /\
    mem_bytes_at sb sz mem = enc at av ==>
    abi_encoder_open_input (AbiCopy sz) at av sb cap mem)
[bytes:]
  (!maxlen at bs sb cap mem.
    (at = Bytes NONE \/ at = String) /\ has_type at (BytesV bs) /\
    LENGTH bs <= maxlen /\ 32 + LENGTH bs <= cap /\
    mem_word_at sb mem = n2w (LENGTH bs) /\
    mem_bytes_at (sb + 32) (LENGTH bs) mem = bs ==>
    abi_encoder_open_input (AbiBytestring maxlen) at (BytesV bs) sb cap mem)
[open_array:]
  (!ei abi_sz mem_sz dyn ct avs sb cap mem.
    valid_length NONE avs /\
    abi_sz = abi_member_head_size ct /\ dyn = is_dynamic ct /\
    32 + LENGTH avs * mem_sz <= cap /\
    mem_word_at sb mem = n2w (LENGTH avs) /\
    (!i. i < LENGTH avs ==>
      abi_encoder_open_input ei ct (EL i avs) (sb + 32 + i * mem_sz) mem_sz mem) ==>
    abi_encoder_open_input (AbiDynArray ei abi_sz mem_sz dyn)
      (Array NONE ct) (ListV avs) sb cap mem)
[complex:]
  (!infos at ats avs sb cap mem.
    abi_encoder_tuple_type at ats /\
    LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs /\
    abi_encoder_member_span infos <= cap /\
    (!i ei abi_sz mem_sz dyn. i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      abi_sz = abi_member_head_size (EL i ats) /\ dyn = is_dynamic (EL i ats) /\
      abi_encoder_open_input ei (EL i ats) (EL i avs)
        (sb + abi_encoder_member_span (TAKE i infos)) mem_sz mem) ==>
    abi_encoder_open_input (AbiComplex infos) at (ListV avs) sb cap mem)
End

Theorem abi_encoder_input_open:
  !ei at av sb cap mem. abi_encoder_input ei at av sb cap mem ==>
    abi_encoder_open_input ei at av sb cap mem
Proof
  ho_match_mp_tac abi_encoder_input_ind >> rpt strip_tac >>
  FIRST (map irule (CONJUNCTS abi_encoder_open_input_rules)) >>
  gvs[has_type_def] >> metis_tac[]
QED

Theorem abi_encoder_open_input_capacity:
  abi_encoder_open_input ei at av sb cap mem /\ cap <= larger ==>
  abi_encoder_open_input ei at av sb larger mem
Proof
  strip_tac >>
  qpat_x_assum `abi_encoder_open_input _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [abi_encoder_open_input_cases]) >>
  gvs[] >> ONCE_REWRITE_TAC [abi_encoder_open_input_cases] >>
  asm_simp_tac (srw_ss()) [LET_THM] >>
  gvs[AC ADD_COMM ADD_ASSOC, MULT_COMM]
  >>~- ([`abi_encoder_tuple_type at ats`],
        qexists_tac `ats` >> gvs[] >> decide_tac) >>
  decide_tac
QED

Theorem abi_encoder_open_input_valid:
  !ei at av sb cap mem. abi_encoder_open_input ei at av sb cap mem ==>
    abi_encoder_structural_valid at av
Proof
  ho_match_mp_tac abi_encoder_open_input_ind >> rpt strip_tac
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

Theorem abi_encoder_open_complex_iff:
  abi_encoder_open_input (AbiComplex infos) at av sb cap mem <=>
  ?ats avs. av = ListV avs /\ abi_encoder_tuple_type at ats /\
    LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs /\
    abi_encoder_member_span infos <= cap /\
    (!i ei abi_sz mem_sz dyn. i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      abi_sz = abi_member_head_size (EL i ats) /\ dyn = is_dynamic (EL i ats) /\
      abi_encoder_open_input ei (EL i ats) (EL i avs)
        (sb + abi_encoder_member_span (TAKE i infos)) mem_sz mem)
Proof
  simp[Once abi_encoder_open_input_cases] >> metis_tac[]
QED

Theorem abi_encoder_open_complex_nil:
  abi_encoder_open_input (AbiComplex []) (Tuple tys) (ListV avs) sb cap mem <=>
  tys = [] /\ avs = []
Proof
  simp[abi_encoder_open_complex_iff, abi_encoder_tuple_type_def,
       abi_encoder_member_span_def] >> metis_tac[LENGTH_NIL]
QED

Theorem abi_encoder_open_complex_cons:
  abi_encoder_open_input (AbiComplex ((ei,abi_sz,mem_sz,dyn)::infos))
    (Tuple (ty::tys)) (ListV (av::avs)) sb cap mem ==>
  abi_sz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  abi_encoder_open_input ei ty av sb mem_sz mem /\
  abi_encoder_open_input (AbiComplex infos) (Tuple tys) (ListV avs)
    (sb+mem_sz) (abi_encoder_member_span infos) mem
Proof
  simp[abi_encoder_open_complex_iff, abi_encoder_tuple_type_def] >>
  disch_then strip_assume_tac >>
  first_assum (qspec_then `0` mp_tac) >>
  simp_tac (srw_ss()) [abi_encoder_member_span_def] >> strip_tac >>
  simp[abi_encoder_member_span_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  simp_tac (srw_ss()) [abi_encoder_member_span_def, ADD_ASSOC] >>
  gvs[]
QED

(* The numerical layout boundary only needs static child lengths, not an
   aggregate cardinality bound. *)
Definition abi_encoder_layout_valid_def:
  abi_encoder_layout_valid at av <=>
    (~is_dynamic at ==> LENGTH (enc at av) = static_length at)
End

Theorem abi_encoder_open_enc_tuple_length:
  !ts vs hl tl hds tls.
    LIST_REL abi_encoder_layout_valid ts vs ==>
    LENGTH (enc_tuple hl tl ts vs hds tls) =
      SUM (MAP LENGTH hds) + SUM (MAP LENGTH tls) +
      SUM (MAP abi_member_head_size ts) +
      SUM (MAP2 abi_member_tail_size ts vs)
Proof
  Induct_on `ts` >> Cases_on `vs` >>
  simp[LIST_REL_EL_EQN, Once enc_def, LENGTH_FLAT, REV_REVERSE_LEM,
       MAP_REVERSE, SUM_REVERSE, SUM_APPEND] >>
  rpt strip_tac >> Cases_on `is_dynamic h'` >>
  gvs[abi_encoder_layout_valid_def, abi_member_head_size_def,
      abi_member_tail_size_def, LENGTH_word_to_bytes]
QED

Theorem abi_encoder_open_tuple_length:
  LIST_REL abi_encoder_layout_valid ts vs ==>
  LENGTH (enc (Tuple ts) (ListV vs)) =
    SUM (MAP abi_member_head_size ts) + SUM (MAP2 abi_member_tail_size ts vs)
Proof
  simp[Once enc_def] >> strip_tac >>
  drule abi_encoder_open_enc_tuple_length >> simp[]
QED

Theorem abi_encoder_open_static_tuple_size:
  !ts vs. ~any_dynamic ts /\ LENGTH ts = LENGTH vs ==>
  SUM (MAP abi_member_head_size ts) + SUM (MAP2 abi_member_tail_size ts vs) =
    static_length (Tuple ts)
Proof
  Induct >> Cases_on `vs` >>
  simp[is_dynamic_def, abi_member_head_size_def, abi_member_tail_size_def,
       static_length_def] >> rpt strip_tac >> res_tac >> simp[]
QED

Theorem abi_encoder_open_replicate_static:
  !n ct. static_length (Tuple (REPLICATE n ct)) = n * static_length ct
Proof
  Induct >> simp[REPLICATE, static_length_def, MULT_CLAUSES]
QED

Theorem abi_encoder_open_replicate_dynamic:
  !n ct. ~is_dynamic ct ==> ~any_dynamic (REPLICATE n ct)
Proof
  Induct >> simp[REPLICATE, is_dynamic_def]
QED

Theorem abi_encoder_structural_valid_layout:
  !at av. abi_encoder_structural_valid at av ==> abi_encoder_layout_valid at av
Proof
  ho_match_mp_tac abi_encoder_structural_valid_ind >> rpt strip_tac
  >- (simp[abi_encoder_layout_valid_def] >> strip_tac >>
      irule (cj 1 enc_has_static_length) >> simp[])
  >- (`LIST_REL abi_encoder_layout_valid ats avs` by
        simp[LIST_REL_EL_EQN] >>
      `LENGTH (enc (Tuple ats) (ListV avs)) =
       SUM (MAP abi_member_head_size ats) + SUM (MAP2 abi_member_tail_size ats avs)` by
        (irule abi_encoder_open_tuple_length >> simp[]) >>
      gvs[abi_encoder_tuple_type_def, abi_encoder_layout_valid_def,
          is_dynamic_def] >> rpt strip_tac
      >- metis_tac[abi_encoder_open_static_tuple_size] >>
      `~any_dynamic (REPLICATE (LENGTH avs) ct)` by
        metis_tac[abi_encoder_open_replicate_dynamic] >>
      drule abi_encoder_open_static_tuple_size >>
      disch_then (qspec_then `avs` mp_tac) >>
      simp[abi_encoder_open_replicate_static]) >>
  simp[abi_encoder_layout_valid_def, is_dynamic_def]
QED

Theorem abi_encoder_open_heads_length:
  !tys vs hl tl. LIST_REL abi_encoder_layout_valid tys vs ==>
  LENGTH (FLAT (abi_tuple_heads hl tl tys vs)) = SUM (MAP abi_member_head_size tys)
Proof
  Induct >> Cases_on `vs` >> simp[abi_tuple_heads_def] >>
  rpt strip_tac >> rename1 `abi_encoder_layout_valid ty av` >>
  Cases_on `is_dynamic ty` >>
  gvs[abi_encoder_layout_valid_def, abi_member_head_size_def]
QED

Theorem abi_encoder_structural_list_layout:
  LIST_REL abi_encoder_structural_valid tys avs ==>
  LIST_REL abi_encoder_layout_valid tys avs
Proof
  simp[LIST_REL_EL_EQN] >> metis_tac[abi_encoder_structural_valid_layout]
QED

Theorem abi_encoder_open_members_layout:
  LIST_REL abi_encoder_structural_valid (pre++ty::tys) (pvs++av::avs) /\
  LENGTH pre = LENGTH pvs /\
  hl = head_lengths (pre++ty::tys) 0 /\ ho = SUM (MAP abi_member_head_size pre) /\
  abi_sz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  LENGTH (enc (Tuple (pre++ty::tys)) (ListV (pvs++av::avs))) <= output_size ==>
  abi_encoder_structural_valid ty av /\ LIST_REL abi_encoder_structural_valid tys avs /\
  ho = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  SUM (MAP2 abi_member_tail_size pre pvs) = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  ho+abi_sz <= hl /\ hl+SUM (MAP2 abi_member_tail_size pre pvs) <= output_size /\
  (~dyn ==> ho+LENGTH (enc ty av) <= hl) /\
  (dyn ==> ho+32 <= hl /\ hl+SUM (MAP2 abi_member_tail_size pre pvs)+LENGTH (enc ty av) <= output_size)
Proof
  disch_then strip_assume_tac >>
  `LIST_REL abi_encoder_layout_valid (pre++ty::tys) (pvs++av::avs)` by
    (irule abi_encoder_structural_list_layout >> simp[]) >>
  `LIST_REL abi_encoder_layout_valid pre pvs /\ abi_encoder_layout_valid ty av /\
   LIST_REL abi_encoder_layout_valid tys avs /\
   abi_encoder_structural_valid ty av /\ LIST_REL abi_encoder_structural_valid tys avs` by
    gvs[LIST_REL_APPEND_EQ] >>
  `ho+abi_sz <= hl` by simp[head_lengths_acc, MAP_APPEND, SUM_APPEND] >>
  `LENGTH (enc (Tuple (pre++ty::tys)) (ListV (pvs++av::avs))) =
    hl+SUM (MAP2 abi_member_tail_size pre pvs)+abi_member_tail_size ty av+
    SUM (MAP2 abi_member_tail_size tys avs)` by
    (asm_simp_tac bool_ss [abi_encoder_open_tuple_length, head_lengths_acc,
      MAP_APPEND, MAP2_APPEND, SUM_APPEND, MAP, MAP2, SUM, ADD_CLAUSES,
      AC ADD_COMM ADD_ASSOC]) >>
  `LENGTH tys = LENGTH avs` by metis_tac[LIST_REL_LENGTH] >>
  simp[abi_encoder_open_heads_length, abi_tuple_tails_length] >>
  Cases_on `is_dynamic ty` >>
  gvs[abi_encoder_layout_valid_def, abi_member_head_size_def, abi_member_tail_size_def] >>
  decide_tac
QED

Theorem abi_encoder_open_complex_cons_intro:
  abi_sz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  abi_encoder_open_input ei ty av sb mem_sz mem /\
  abi_encoder_open_input (AbiComplex infos) (Tuple tys) (ListV avs)
    (sb+mem_sz) (abi_encoder_member_span infos) mem /\
  mem_sz+abi_encoder_member_span infos <= cap ==>
  abi_encoder_open_input (AbiComplex ((ei,abi_sz,mem_sz,dyn)::infos))
    (Tuple (ty::tys)) (ListV (av::avs)) sb cap mem
Proof
  simp[abi_encoder_open_complex_iff, abi_encoder_tuple_type_def] >>
  disch_then strip_assume_tac >> simp[abi_encoder_member_span_def] >>
  conj_tac >- gvs[abi_encoder_member_span_def] >>
  rpt gen_tac >> Cases_on `i` >>
  simp_tac (srw_ss()) [abi_encoder_member_span_def, ADD_ASSOC] >>
  strip_tac >> gvs[abi_encoder_member_span_def] >>
  metis_tac[ADD_COMM, ADD_ASSOC]
QED

Theorem abi_encoder_open_zero_prefix:
  !n sb mem. mem_word_at sb mem = 0w ==>
  abi_encoder_open_input
    (AbiComplex (REPLICATE n (AbiCopy 0,0,0,F) ++ [(AbiBytestring 0,32,32,T)]))
    (Tuple (REPLICATE n (Tuple []) ++ [Bytes NONE]))
    (ListV (REPLICATE n (ListV []) ++ [BytesV []])) sb 32 mem
Proof
  Induct
  >- (rpt strip_tac >> simp[REPLICATE] >>
      irule abi_encoder_open_complex_cons_intro >>
      simp[abi_encoder_open_complex_nil, abi_encoder_member_span_def,
           abi_member_head_size_def, is_dynamic_def] >>
      ONCE_REWRITE_TAC [abi_encoder_open_input_cases] >>
      simp[has_type_def, valid_length_def, mem_bytes_at_def]) >>
  rpt strip_tac >> simp[REPLICATE] >>
  irule abi_encoder_open_complex_cons_intro >>
  simp[abi_encoder_member_span_def, abi_member_head_size_def, is_dynamic_def,
       static_length_def, SUM_APPEND] >>
  irule abi_encoder_input_open >>
  simp[abi_encoder_input_copy_iff, has_type_def, valid_length_def,
       is_dynamic_def, static_length_def, enc_def, REV_DEF, mem_bytes_at_def]
QED

Theorem abi_encoder_open_giant_zero_prefix:
  mem_word_at sb mem = 0w ==>
  abi_encoder_open_input
    (AbiComplex (REPLICATE (dimword (:256)) (AbiCopy 0,0,0,F) ++
      [(AbiBytestring 0,32,32,T)]))
    (Tuple (REPLICATE (dimword (:256)) (Tuple []) ++ [Bytes NONE]))
    (ListV (REPLICATE (dimword (:256)) (ListV []) ++ [BytesV []])) sb 32 mem
Proof
  strip_tac >> irule abi_encoder_open_zero_prefix >> simp[]
QED
