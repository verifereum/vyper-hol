(* Aggregate byte transport is independent of ABI value cardinality typing. *)
Theory abiEncoderSourceAggregate
Ancestors
  abiEncoderSourceTransport abiEncoderSourceWindow abiCallerStaticMemory
  abiEncoderOpenInput abiEncoderInput abiDecodeRanges contractABI list rich_list arithmetic

Theorem abi_encoder_enc_tuple_cong:
  !ats cts avs rvs hl tl hds tls.
    LENGTH ats = LENGTH cts /\ LENGTH ats = LENGTH avs /\ LENGTH avs = LENGTH rvs /\
    (!i. i < LENGTH ats ==>
      is_dynamic (EL i ats) = is_dynamic (EL i cts) /\
      enc (EL i ats) (EL i avs) = enc (EL i cts) (EL i rvs)) ==>
    enc_tuple hl tl ats avs hds tls = enc_tuple hl tl cts rvs hds tls
Proof
  Induct >> Cases_on `cts` >> Cases_on `avs` >> Cases_on `rvs` >>
  simp[Once enc_def] >> rpt strip_tac >>
  qpat_assum `!i. i < SUC _ ==> _` (qspec_then `0` mp_tac) >>
  simp_tac (srw_ss()) [] >> strip_tac >> gvs[] >> first_x_assum irule >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `SUC i` mp_tac) >> simp[]
QED

Theorem abi_encoder_head_lengths_cong:
  !ats cts. LENGTH ats = LENGTH cts /\
    (!i. i < LENGTH ats ==>
      abi_member_head_size (EL i ats) = abi_member_head_size (EL i cts)) ==>
    head_lengths ats a = head_lengths cts a
Proof
  Induct >> Cases_on `cts` >> simp[head_lengths_acc] >> rpt strip_tac >>
  qpat_assum `!i. i < SUC _ ==> _` (qspec_then `0` mp_tac) >>
  simp_tac (srw_ss()) [] >> strip_tac >> simp[] >>
  qpat_x_assum `!cts. _ ==> head_lengths _ _ = _`
    (mp_tac o SRULE [head_lengths_acc]) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `SUC i` mp_tac) >> simp[]
QED

Theorem abi_encoder_tuple_encoding_cong:
  LENGTH ats = LENGTH cts /\ LENGTH ats = LENGTH avs /\ LENGTH avs = LENGTH rvs /\
  (!i. i < LENGTH ats ==>
    is_dynamic (EL i ats) = is_dynamic (EL i cts) /\
    abi_member_head_size (EL i ats) = abi_member_head_size (EL i cts) /\
    enc (EL i ats) (EL i avs) = enc (EL i cts) (EL i rvs)) ==>
  enc (Tuple ats) (ListV avs) = enc (Tuple cts) (ListV rvs)
Proof
  strip_tac >>
  `head_lengths ats 0 = head_lengths cts 0` by
    (irule abi_encoder_head_lengths_cong >> simp[]) >>
  simp[Once enc_def] >> irule abi_encoder_enc_tuple_cong >> simp[]
QED

Definition source_rep_def:
  source_rep env t ei ct <=>
    (!tv. evaluate_type env t = SOME tv ==>
      is_dynamic ct = is_dynamic (vyper_to_abi_type env t) /\
      abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type env t)) /\
    (!tv v av sb mem.
      evaluate_type env t = SOME tv /\ value_has_type tv v /\
      vyper_to_abi env t v = SOME av /\ val_in_memory tv v sb mem ==>
      ?rv. enc ct rv = enc (vyper_to_abi_type env t) av /\
        abi_encoder_open_input ei ct rv sb (type_memory_size tv) mem)
End

Definition source_reps_def:
  source_reps env ts infos cts <=>
    LENGTH ts = LENGTH infos /\ LENGTH ts = LENGTH cts /\
    (!i ei abi_sz mem_sz dyn.
      i < LENGTH ts /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      source_rep env (EL i ts) ei (EL i cts) /\
      abi_sz = abi_member_head_size (EL i cts) /\
      dyn = is_dynamic (EL i cts) /\
      ?tv. evaluate_type env (EL i ts) = SOME tv /\
        mem_sz = type_memory_size tv)
End

Theorem source_rep_metadata:
  source_rep env t ei ct /\ evaluate_type env t = SOME tv ==>
  is_dynamic ct = is_dynamic (vyper_to_abi_type env t) /\
  abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type env t)
Proof
  rw[source_rep_def] >> metis_tac[]
QED

Theorem source_rep_transport:
  source_rep env t ei ct /\ evaluate_type env t = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env t v = SOME av /\
  val_in_memory tv v sb mem ==>
  ?rv. enc ct rv = enc (vyper_to_abi_type env t) av /\
    abi_encoder_open_input ei ct rv sb (type_memory_size tv) mem
Proof
  rw[source_rep_def] >> metis_tac[]
QED

Theorem source_reps_nil:
  source_reps env [] [] []
Proof
  simp[source_reps_def]
QED

Theorem source_reps_index:
  source_reps env ts infos cts /\ i < LENGTH ts /\
  EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
  source_rep env (EL i ts) ei (EL i cts) /\
  abi_sz = abi_member_head_size (EL i cts) /\ dyn = is_dynamic (EL i cts) /\
  ?tv. evaluate_type env (EL i ts) = SOME tv /\ mem_sz = type_memory_size tv
Proof
  simp[source_reps_def]
QED

Theorem source_reps_cons:
  source_rep env t ei ct /\ abi_sz = abi_member_head_size ct /\
  dyn = is_dynamic ct /\ evaluate_type env t = SOME tv /\
  mem_sz = type_memory_size tv /\ source_reps env ts infos cts ==>
  source_reps env (t::ts) ((ei,abi_sz,mem_sz,dyn)::infos) (ct::cts)
Proof
  simp[source_reps_def] >> rpt strip_tac >> Cases_on `i` >> gvs[] >>
  metis_tac[]
QED

Theorem abi_encoder_dynamic_empty_input:
  abi_encoder_open_input (AbiComplex [])
    (Array (SOME 0) (Bytes NONE)) (ListV []) sb cap mem
Proof
  simp[abi_encoder_open_complex_iff, abi_encoder_tuple_type_def,
       abi_encoder_member_span_def]
QED

Theorem abi_encoder_dynamic_empty_classification:
  is_dynamic (Array (SOME 0) (Bytes NONE)) /\
  enc (Array (SOME 0) (Bytes NONE)) (ListV []) = []
Proof
  EVAL_TAC
QED

Theorem source_reps_lengths:
  source_reps env ts infos cts ==>
  LENGTH infos = LENGTH ts /\ LENGTH cts = LENGTH ts
Proof
  simp[source_reps_def]
QED

Theorem source_reps_span:
  source_reps env ts infos cts /\ LENGTH tvs = LENGTH ts /\
  (!i. i < LENGTH ts ==> evaluate_type env (EL i ts) = SOME (EL i tvs)) ==>
  abi_encoder_member_span (TAKE k infos) =
    SUM (MAP type_memory_size (TAKE k tvs))
Proof
  strip_tac >>
  `MAP (\(_,_,n,_). n) infos = MAP type_memory_size tvs` suffices_by
    (simp[abi_encoder_member_span_def, MAP_TAKE]) >>
  irule LIST_EQ >> simp[] >>
  drule source_reps_lengths >> strip_tac >> simp[] >> rpt strip_tac >>
  rename1 `i < LENGTH ts` >>
  Cases_on `EL i infos` >> PairCases_on `r` >>
  drule_all source_reps_index >> strip_tac >> gvs[EL_MAP]
QED

Theorem source_reps_full_span:
  source_reps env ts infos cts /\ LENGTH tvs = LENGTH ts /\
  (!i. i < LENGTH ts ==> evaluate_type env (EL i ts) = SOME (EL i tvs)) ==>
  abi_encoder_member_span infos = SUM (MAP type_memory_size tvs)
Proof
  strip_tac >> drule_all source_reps_span >>
  disch_then (qspec_then `LENGTH ts` mp_tac) >>
  drule source_reps_lengths >> strip_tac >> simp[TAKE_LENGTH_ID_rwt]
QED

Theorem source_reps_members:
  source_reps env ts infos cts /\ LENGTH tvs = LENGTH ts /\
  LENGTH vs = LENGTH ts /\ LENGTH avs = LENGTH ts /\
  (!i. i < LENGTH ts ==>
    evaluate_type env (EL i ts) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i vs) /\
    vyper_to_abi env (EL i ts) (EL i vs) = SOME (EL i avs) /\
    val_in_memory (EL i tvs) (EL i vs)
      (sb+SUM (MAP type_memory_size (TAKE i tvs))) mem) ==>
  ?rvs. LENGTH rvs = LENGTH ts /\
    (!i. i < LENGTH ts ==>
      enc (EL i cts) (EL i rvs) = enc (vyper_to_abi_type env (EL i ts)) (EL i avs)) /\
    (!i ei abi_sz mem_sz dyn.
      i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      abi_sz = abi_member_head_size (EL i cts) /\ dyn = is_dynamic (EL i cts) /\
      abi_encoder_open_input ei (EL i cts) (EL i rvs)
        (sb+abi_encoder_member_span (TAKE i infos)) mem_sz mem)
Proof
  strip_tac >>
  `!i. i < LENGTH ts ==> evaluate_type env (EL i ts) = SOME (EL i tvs)` by simp[] >>
  drule_all source_reps_span >> disch_tac >>
  `!i. i < LENGTH ts ==> ?rv.
    enc (EL i cts) rv = enc (vyper_to_abi_type env (EL i ts)) (EL i avs) /\
    !ei abi_sz mem_sz dyn. EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      abi_sz = abi_member_head_size (EL i cts) /\ dyn = is_dynamic (EL i cts) /\
      abi_encoder_open_input ei (EL i cts) rv
        (sb+abi_encoder_member_span (TAKE i infos)) mem_sz mem` by
    (rpt strip_tac >>
     qpat_assum `!i. i < LENGTH ts ==> _` (qspec_then `i` mp_tac) >>
     simp_tac (srw_ss()) [] >> strip_tac >>
     Cases_on `EL i infos` >> PairCases_on `r` >>
     drule_all source_reps_index >> strip_tac >> gvs[] >>
     simp[] >> irule source_rep_transport >>
     simp[] >> qexists_tac `EL i vs` >> simp[]) >>
  qpat_x_assum `!i. _ ==> ?rv. _` mp_tac >>
  CONV_TAC (LAND_CONV (BINDER_CONV (HO_REWR_CONV (GSYM RIGHT_EXISTS_IMP_THM)))) >>
  CONV_TAC (LAND_CONV (HO_REWR_CONV SKOLEM_THM)) >>
  disch_then (qx_choose_then `f` assume_tac) >>
  qexists_tac `GENLIST f (LENGTH ts)` >> simp[] >>
  drule source_reps_lengths >> strip_tac >> rpt strip_tac >>
  qpat_x_assum `!i. i < LENGTH ts ==> enc _ (f i) = _ /\ _`
    (qspec_then `i` mp_tac) >> simp[]
QED

Theorem abi_encoder_source_complex_input:
  abi_encoder_tuple_type ct cts /\ LENGTH infos = LENGTH cts /\
  LENGTH cts = LENGTH rvs /\ abi_encoder_member_span infos <= cap /\
  (!i ei abi_sz mem_sz dyn.
    i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
    abi_sz = abi_member_head_size (EL i cts) /\ dyn = is_dynamic (EL i cts) /\
    abi_encoder_open_input ei (EL i cts) (EL i rvs)
      (sb+abi_encoder_member_span (TAKE i infos)) mem_sz mem) ==>
  abi_encoder_open_input (AbiComplex infos) ct (ListV rvs) sb cap mem
Proof
  strip_tac >> simp[abi_encoder_open_complex_iff] >>
  qexists_tac `cts` >> simp[]
QED

Theorem abi_encoder_tuple_type_encoding:
  abi_encoder_tuple_type at ats /\ LENGTH ats = LENGTH avs ==>
  enc at (ListV avs) = enc (Tuple ats) (ListV avs)
Proof
  rw[abi_encoder_tuple_type_def] >> gvs[] >> simp[Once enc_def]
QED

Theorem abi_encoder_tuple_type_encoding_cong:
  abi_encoder_tuple_type at ats /\ abi_encoder_tuple_type ct cts /\
  LENGTH ats = LENGTH cts /\ LENGTH ats = LENGTH avs /\ LENGTH avs = LENGTH rvs /\
  (!i. i < LENGTH ats ==>
    is_dynamic (EL i ats) = is_dynamic (EL i cts) /\
    abi_member_head_size (EL i ats) = abi_member_head_size (EL i cts) /\
    enc (EL i ats) (EL i avs) = enc (EL i cts) (EL i rvs)) ==>
  enc at (ListV avs) = enc ct (ListV rvs)
Proof
  strip_tac >>
  `enc at (ListV avs) = enc (Tuple ats) (ListV avs)` by
    (irule abi_encoder_tuple_type_encoding >> simp[]) >>
  `enc ct (ListV rvs) = enc (Tuple cts) (ListV rvs)` by
    (irule abi_encoder_tuple_type_encoding >> simp[]) >>
  metis_tac[abi_encoder_tuple_encoding_cong]
QED

Theorem abi_encoder_dynamic_array_encoding_cong:
  LENGTH avs = LENGTH rvs /\ is_dynamic at = is_dynamic ct /\
  abi_member_head_size at = abi_member_head_size ct /\
  (!i. i < LENGTH avs ==> enc at (EL i avs) = enc ct (EL i rvs)) ==>
  enc (Array NONE at) (ListV avs) = enc (Array NONE ct) (ListV rvs)
Proof
  strip_tac >>
  `head_lengths (REPLICATE (LENGTH avs) at) 0 =
   head_lengths (REPLICATE (LENGTH rvs) ct) 0` by
    (irule abi_encoder_head_lengths_cong >> simp[EL_REPLICATE]) >>
  gvs[] >> simp[Once enc_def] >> irule abi_encoder_enc_tuple_cong >> simp[EL_REPLICATE]
QED

Theorem source_rep_static_copy:
  evaluate_type env ty = SOME tv /\ ~is_dynamic (vyper_to_abi_type env ty) ==>
  ?ct. source_rep env ty (AbiCopy (type_memory_size tv)) ct
Proof
  strip_tac >> drule_all abi_encoder_uniform_static_source >>
  disch_then (qx_choose_then `ct` strip_assume_tac) >>
  drule_all abi_caller_static_memory >> strip_tac >>
  qexists_tac `ct` >> simp[source_rep_def, abi_member_head_size_def] >>
  metis_tac[]
QED

(* Retained tags do not reconstruct axiom provenance erased by .dat loading. *)
val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SOURCE_AGGREGATE_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("source aggregate admission dependency: " ^ name)
  end)
  [("tuple_acc", abi_encoder_enc_tuple_cong),
   ("heads", abi_encoder_head_lengths_cong),
   ("tuple_bytes", abi_encoder_tuple_encoding_cong),
   ("rep_metadata", source_rep_metadata),
   ("rep_transport", source_rep_transport),
   ("reps_nil", source_reps_nil),
   ("reps_index", source_reps_index),
   ("reps_cons", source_reps_cons),
   ("dynamic_empty_input", abi_encoder_dynamic_empty_input),
   ("dynamic_empty_classification", abi_encoder_dynamic_empty_classification),
   ("lengths", source_reps_lengths),
   ("prefix_span", source_reps_span),
   ("full_span", source_reps_full_span),
   ("members", source_reps_members),
   ("complex", abi_encoder_source_complex_input),
   ("tuple_type_bytes", abi_encoder_tuple_type_encoding),
   ("tuple_type_cong", abi_encoder_tuple_type_encoding_cong),
   ("array_cong", abi_encoder_dynamic_array_encoding_cong),
   ("static_copy", source_rep_static_copy)];
