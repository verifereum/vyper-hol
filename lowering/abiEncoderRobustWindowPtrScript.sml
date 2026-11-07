(* Robust source windows: canonical child capacities and protected transport. *)
Theory abiEncoderRobustWindowPtr
Ancestors abiEncoderWindow abiEncoderInput abiEncoderBufferFrame bodyPtrDefs valueEncodingProofs list arithmetic

Theorem abi_encoder_robust_window_capacity:
  (!m. mem_agree_outside ta mem m ==>
    abi_encoder_window_input ei at av p cap m) /\ cap <= larger ==>
  !m. mem_agree_outside ta mem m ==>
    abi_encoder_window_input ei at av p larger m
Proof
  metis_tac[abi_encoder_window_input_capacity]
QED

Theorem abi_encoder_robust_window_complex_child:
  (!m. mem_agree_outside ta mem m ==>
    abi_encoder_window_input (AbiComplex infos) at (ListV avs) p cap m) /\
  i < LENGTH infos /\ EL i infos = (ei,asz,msz,dyn) /\
  abi_encoder_tuple_type at ats /\ LENGTH infos = LENGTH ats ==>
  !m. mem_agree_outside ta mem m ==>
    abi_encoder_window_input ei (EL i ats) (EL i avs)
      (p + abi_encoder_member_span (TAKE i infos))
      (MIN msz (cap - abi_encoder_member_span (TAKE i infos))) m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >>
  rewrite_tac[abi_encoder_window_complex_iff] >> strip_tac >>
  `ats = ats'` by metis_tac[abi_encoder_tuple_type_unique] >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  irule abi_encoder_window_input_capacity >>
  goal_assum (drule_at Any) >> simp[MIN_DEF] >> decide_tac
QED

Theorem abi_encoder_robust_window_array_child:
  (!m. mem_agree_outside ta mem m ==>
    abi_encoder_window_input (AbiDynArray ei asz msz dyn)
      (Array NONE ct) (ListV avs) p cap m) /\ i < LENGTH avs ==>
  !m. mem_agree_outside ta mem m ==>
    abi_encoder_window_input ei ct (EL i avs) (p + 32 + i * msz)
      (MIN msz (cap - (32 + i * msz))) m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >>
  rewrite_tac[abi_encoder_window_array_iff] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  irule abi_encoder_window_input_capacity >>
  goal_assum (drule_at Any) >> simp[MIN_DEF] >> decide_tac
QED

Theorem mem_bytes_at_singleton:
  !mem a. mem_bytes_at a 1 mem =
    [if a < LENGTH mem then EL a mem else 0w]
Proof
  rpt gen_tac >> irule LIST_EQ >> simp[] >>
  mp_tac (Q.SPECL [`a`,`1`,`mem`,`0`] EL_mem_bytes_at) >> simp[]
QED

Theorem protected_memory_patch:
  !ta ua mem next p cap m.
    (!a. p <= a /\ a < p+cap ==>
      mem_bytes_at a 1 next = mem_bytes_at a 1 mem /\
      (a IN ua <=> a IN ta)) /\
    mem_agree_outside ua next m ==>
    ?patched. mem_agree_outside ta mem patched /\
      mem_bytes_at p cap patched = mem_bytes_at p cap m
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `GENLIST (\a. if p <= a /\ a < p+cap then
      EL 0 (mem_bytes_at a 1 m) else EL 0 (mem_bytes_at a 1 mem))
      (MAX (LENGTH mem) (p+cap))` >>
  conj_tac
  >- (rewrite_tac[mem_agree_outside_def] >> rpt strip_tac >>
      rename1 `a NOTIN ta` >>
      Cases_on `p <= a /\ a < p+cap`
      >- (qpat_x_assum `!a. _ ==> _` (qspec_then `a` mp_tac) >>
          asm_rewrite_tac[] >> strip_tac >>
          `a < MAX (LENGTH mem) (p+cap)` by simp[MAX_DEF] >>
          `a NOTIN ua` by metis_tac[] >>
          `mem_bytes_at a 1 next = mem_bytes_at a 1 m` by
            metis_tac[mem_agree_outside_def] >>
          simp[mem_bytes_at_singleton, EL_GENLIST] >>
          metis_tac[mem_bytes_at_singleton, listTheory.HD]) >>
      simp[mem_bytes_at_singleton, EL_GENLIST] >>
      Cases_on `a < MAX (LENGTH mem) (p+cap)` >>
      gvs[MAX_DEF]) >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `i < cap` >>
  `p+i < MAX (LENGTH mem) (p+cap)` by simp[MAX_DEF] >>
  simp[EL_mem_bytes_at, EL_GENLIST, mem_bytes_at_singleton]
QED

Theorem abi_encoder_robust_window_transport:
  (!m. mem_agree_outside ta mem m ==>
    abi_encoder_window_input ei at av p cap m) /\
  (!a. p <= a /\ a < p+cap ==>
    mem_bytes_at a 1 next = mem_bytes_at a 1 mem /\
    (a IN ua <=> a IN ta)) ==>
  !m. mem_agree_outside ua next m ==>
    abi_encoder_window_input ei at av p cap m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  drule_all protected_memory_patch >> strip_tac >>
  qpat_x_assum `!m. _ ==> abi_encoder_window_input _ _ _ _ _ _` drule >>
  strip_tac >> drule abi_encoder_window_input_mem_agree >>
  disch_then irule >> asm_rewrite_tac[]
QED

Theorem abi_encoder_robust_window_empty:
  !ta mem p cap.
    !m. mem_agree_outside ta mem m ==>
      abi_encoder_window_input (AbiComplex []) (Tuple []) (ListV []) p cap m
Proof
  simp[abi_encoder_window_complex_iff, abi_encoder_tuple_type_def]
QED

Theorem abi_encoder_robust_window_singleton:
  (!m. mem_agree_outside ta mem m ==>
    abi_encoder_window_input ei at av p cap m) /\ cap <= msz /\
  asz = abi_member_head_size at /\ dyn = is_dynamic at ==>
  !m. mem_agree_outside ta mem m ==>
    abi_encoder_window_input (AbiComplex [(ei,asz,msz,dyn)])
      (Tuple [at]) (ListV [av]) p cap m
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  rewrite_tac[abi_encoder_window_complex_iff] >>
  qexists_tac `[at]` >> simp[abi_encoder_tuple_type_def] >>
  qexists_tac `cap` >> simp[abi_encoder_member_span_def]
QED
