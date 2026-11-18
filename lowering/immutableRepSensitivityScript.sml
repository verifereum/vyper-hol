(* Dirty bytes of a robust immutable memory representation are dead. *)
Theory immutableRepSensitivity
Ancestors
  immSectionDead representationCleanPtr bodyPtrDefs valueEncoding
  valueEncodingDefs valueEncodingProofs valueEncodingTyping
  exprSimAggregateEncoding vyperValue vyperTyping vyperAST
  arithmetic words list alist pair pred_set

Theorem body_assign_immutable_sensitivity_dynamic[local]:
  (!v a mem dirty.
    well_formed_type_value tv /\
    (value_has_type tv v \/ v = default_value tv) /\ val_wf tv v /\
    (!m. mem_agree_outside dirty mem m ==> val_in_memory tv v a m) ==>
    !j. j < type_memory_size tv /\ a+j IN dirty ==>
      mem_dead_bytes mem a tv (a+j)) ==>
  !n v a mem dirty.
    well_formed_type_value (ArrayTV tv (Dynamic n)) /\
    (value_has_type (ArrayTV tv (Dynamic n)) v \/
      v = default_value (ArrayTV tv (Dynamic n))) /\
    val_wf (ArrayTV tv (Dynamic n)) v /\
    (!m. mem_agree_outside dirty mem m ==>
      val_in_memory (ArrayTV tv (Dynamic n)) v a m) ==>
    !j. j < type_memory_size (ArrayTV tv (Dynamic n)) /\ a+j IN dirty ==>
      mem_dead_bytes mem a (ArrayTV tv (Dynamic n)) (a+j)
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >> disch_tac >>
  `value_has_type (ArrayTV tv (Dynamic n)) v` by
    metis_tac[default_value_well_typed] >>
  fs[] >>
  `?vs. v = ArrayV (DynArrayV vs)` by
    (Cases_on `v` >> gvs[default_value_def, value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def]) >>
  gvs[] >>
  `well_formed_type_value tv /\ n < dimword(:256) /\ LENGTH vs <= n` by
    gvs[well_formed_type_value_def, val_wf_def] >>
  `!m. mem_agree_outside dirty mem m ==> mem_word_at a m = n2w (LENGTH vs)` by
    (rpt strip_tac >> first_x_assum drule >> simp[val_in_memory_def]) >>
  drule robust_mem_word_at_clean >> strip_tac >>
  `mem_word_at a mem = n2w (LENGTH vs)` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `LENGTH vs < dimword(:256)` by decide_tac >>
  `w2n (mem_word_at a mem) = LENGTH vs` by simp[] >>
  gen_tac >> strip_tac >>
  `32 <= j` by
    (Cases_on `j < 32` >> simp[] >>
     first_x_assum (qspec_then `a+j` mp_tac) >> simp[]) >>
  Cases_on `type_memory_size tv = 0`
  >- gvs[type_memory_size_def] >>
  Cases_on `n = 0` >- gvs[type_memory_size_def] >>
  `0 < type_memory_size tv` by decide_tac >>
  qabbrev_tac `k = (j-32) DIV type_memory_size tv` >>
  qabbrev_tac `r = (j-32) MOD type_memory_size tv` >>
  `j-32 = k * type_memory_size tv + r /\ r < type_memory_size tv` by
    metis_tac[DIVISION] >>
  `k < n` by
    (simp[Abbr `k`, DIV_LT_X] >> gvs[type_memory_size_def]) >>
  `j = 32 + k * type_memory_size tv + r` by decide_tac >>
  simp[Once mem_dead_bytes_def] >> qexists_tac `k` >> simp[] >>
  Cases_on `k < LENGTH vs`
  >- (simp[] >>
      `value_has_type tv (EL k vs)` by
        fs[value_has_type_def, all_have_type_EVERY, EVERY_EL] >>
      `val_wf tv (EL k vs)` by metis_tac[value_has_type_val_wf] >>
      `!m. mem_agree_outside dirty mem m ==>
        val_in_memory tv (EL k vs) (a+32+k*type_memory_size tv) m` by
        (rpt strip_tac >> irule elems_in_memory_EL >> simp[] >>
         qpat_x_assum `!m. _ ==> val_in_memory _ (ArrayV _) _ _` drule >>
         simp[val_in_memory_def]) >>
      qpat_x_assum `!v a mem dirty. _` (qspecl_then
        [`EL k vs`, `a+32+k*type_memory_size tv`, `mem`, `dirty`] mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (qspec_then `r` mp_tac) >>
      gvs[AC ADD_ASSOC ADD_COMM]) >>
  simp[RIGHT_ADD_DISTRIB] >> decide_tac
QED

Theorem body_assign_immutable_sensitivity_base[local]:
  (!bt v a mem dirty.
     well_formed_type_value (BaseTV bt) /\
     (value_has_type (BaseTV bt) v \/ v = default_value (BaseTV bt)) /\
     val_wf (BaseTV bt) v /\
     (!m. mem_agree_outside dirty mem m ==>
          val_in_memory (BaseTV bt) v a m) ==>
     !j. j < type_memory_size (BaseTV bt) /\ a+j IN dirty ==>
          mem_dead_bytes mem a (BaseTV bt) (a+j)) /\
  (!n v a mem dirty.
     well_formed_type_value (FlagTV n) /\
     (value_has_type (FlagTV n) v \/ v = default_value (FlagTV n)) /\
     val_wf (FlagTV n) v /\
     (!m. mem_agree_outside dirty mem m ==>
          val_in_memory (FlagTV n) v a m) ==>
     !j. j < type_memory_size (FlagTV n) /\ a+j IN dirty ==>
          mem_dead_bytes mem a (FlagTV n) (a+j)) /\
  (!v a mem dirty.
     well_formed_type_value NoneTV /\
     (value_has_type NoneTV v \/ v = default_value NoneTV) /\
     val_wf NoneTV v /\
     (!m. mem_agree_outside dirty mem m ==>
          val_in_memory NoneTV v a m) ==>
     !j. j < type_memory_size NoneTV /\ a+j IN dirty ==>
          mem_dead_bytes mem a NoneTV (a+j))
Proof
  conj_tac
  >- (Cases_on `bt` >> rpt gen_tac
      >~ [`BaseTV (BytesT bd)`]
      >- (Cases_on `bd` >> Cases_on `v` >>
          simp[value_has_type_def, default_value_def]
          >- (rpt strip_tac >>
              drule robust_val_in_memory_bytes_clean >> simp[] >>
              disch_then (qspec_then `a+j` mp_tac) >>
              gvs[type_memory_size_def]) >>
          rpt strip_tac >>
          drule robust_val_in_memory_bytes_clean >> simp[] >> strip_tac >>
          qpat_assum `!m. mem_agree_outside _ _ _ ==> _`
            (qspec_then `mem` mp_tac) >>
          simp_tac (srw_ss()) [mem_agree_outside_def, val_in_memory_def] >> strip_tac >>
          gvs[well_formed_type_value_def] >>
          simp[mem_dead_bytes_def] >>
          rpt (first_x_assum (qspec_then `a+j` mp_tac)) >>
          simp[] >> decide_tac) >>
      Cases_on `v` >> simp[value_has_type_def, default_value_def]
      >~ [`BaseTV (StringT n)`]
      >- (rpt strip_tac >>
          drule robust_val_in_memory_string_clean >> strip_tac >>
          qpat_assum `!m. mem_agree_outside _ _ _ ==> _`
            (qspec_then `mem` mp_tac) >>
          simp_tac (srw_ss())
            [mem_agree_outside_def, val_in_memory_def, LENGTH_MAP] >> strip_tac >>
          gvs[well_formed_type_value_def] >> simp[mem_dead_bytes_def] >>
          rpt (first_x_assum (qspec_then `a+j` mp_tac)) >>
          simp[] >> decide_tac)
      >~ [`BytesV bs`]
      >- (rpt strip_tac >>
          drule robust_val_in_memory_bytes_clean >> simp[] >>
          disch_then (qspec_then `a+j` mp_tac) >>
          gvs[type_memory_size_def]) >>
      rpt strip_tac >> gvs[val_in_memory_def] >> drule robust_mem_word_at_clean >> simp[] >>
      disch_then (qspec_then `a+j` mp_tac) >>
      gvs[type_memory_size_def]) >>
  conj_tac
  >- (rpt gen_tac >> Cases_on `v` >>
      simp[value_has_type_def, default_value_def] >> rpt strip_tac >>
      gvs[val_in_memory_def] >> drule robust_mem_word_at_clean >>
      simp[] >> disch_then (qspec_then `a+j` mp_tac) >>
      gvs[type_memory_size_def]) >>
  simp[type_memory_size_def]
QED

Theorem body_assign_immutable_sensitivity_tuple_list[local]:
  !tvs vs a mem dirty.
    EVERY well_formed_type_value tvs /\
    (values_have_types tvs vs \/ vs = MAP default_value tvs) /\
    tuple_val_wf vs tvs /\
    (!m. mem_agree_outside dirty mem m ==> tuple_in_memory vs tvs a m) /\
    (!tv. MEM tv tvs ==> !v a mem dirty.
      well_formed_type_value tv /\
      (value_has_type tv v \/ v = default_value tv) /\
      val_wf tv v /\
      (!m. mem_agree_outside dirty mem m ==> val_in_memory tv v a m) ==>
      !j. j < type_memory_size tv /\ a+j IN dirty ==>
        mem_dead_bytes mem a tv (a+j)) ==>
    !j. j < type_memory_size_list tvs /\ a+j IN dirty ==>
      mem_dead_bytes_list mem a tvs (a+j)
Proof
  Induct >> simp[type_memory_size_def] >>
  gen_tac >> Cases_on `vs` >>
  simp[value_has_type_def, val_wf_def, val_in_memory_def, type_memory_size_def] >>
  rpt strip_tac >>
  simp[Once mem_dead_bytes_def] >>
  (Cases_on `j < type_memory_size h`
  >- (disj1_tac >>
      qpat_x_assum `!tv. tv = h \/ _ ==> _` (qspec_then `h` mp_tac) >>
      simp[] >>
      disch_then (qspecl_then [`h'`, `a`, `mem`, `dirty`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  disj2_tac >>
  qpat_x_assum `!vs a mem dirty. _`
    (qspecl_then [`t`, `a + type_memory_size h`, `mem`, `dirty`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qspec_then `j - type_memory_size h` mp_tac) >>
  `a + type_memory_size h + (j - type_memory_size h) = a+j` by decide_tac >>
  simp[])
QED

Theorem body_assign_immutable_sensitivity_tuple[local]:
  !tvs.
    (!tv. MEM tv tvs ==> !v a mem dirty.
      well_formed_type_value tv /\
      (value_has_type tv v \/ v = default_value tv) /\ val_wf tv v /\
      (!m. mem_agree_outside dirty mem m ==> val_in_memory tv v a m) ==>
      !j. j < type_memory_size tv /\ a+j IN dirty ==>
        mem_dead_bytes mem a tv (a+j)) ==>
    !v a mem dirty.
      well_formed_type_value (TupleTV tvs) /\
      (value_has_type (TupleTV tvs) v \/ v = default_value (TupleTV tvs)) /\
      val_wf (TupleTV tvs) v /\
      (!m. mem_agree_outside dirty mem m ==>
        val_in_memory (TupleTV tvs) v a m) ==>
      !j. j < type_memory_size (TupleTV tvs) /\ a+j IN dirty ==>
        mem_dead_bytes mem a (TupleTV tvs) (a+j)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `v` >>
  simp[value_has_type_def, default_value_def, default_value_tuple_MAP] >>
  rename1 `ArrayV arr` >> Cases_on `arr` >>
  simp[value_has_type_def, val_wf_def, val_in_memory_def,
       well_formed_type_value_def, type_memory_size_def, mem_dead_bytes_def] >>
  rpt strip_tac >> irule body_assign_immutable_sensitivity_tuple_list >>
  simp[] >> metis_tac[]
QED

Theorem body_assign_immutable_sensitivity_field_list[local]:
  !fields vs a mem dirty.
    EVERY (well_formed_type_value o SND) fields /\
    (struct_has_type fields vs \/
     vs = MAP (\(name,tv). (name,default_value tv)) fields) /\
    fields_val_wf vs fields /\
    (!m. mem_agree_outside dirty mem m ==> fields_in_memory vs fields a m) /\
    (!name tv. MEM (name,tv) fields ==> !v a mem dirty.
      well_formed_type_value tv /\
      (value_has_type tv v \/ v = default_value tv) /\
      val_wf tv v /\
      (!m. mem_agree_outside dirty mem m ==> val_in_memory tv v a m) ==>
      !j. j < type_memory_size tv /\ a+j IN dirty ==>
        mem_dead_bytes mem a tv (a+j)) ==>
    !j. j < type_memory_size_fields fields /\ a+j IN dirty ==>
      mem_dead_bytes_fields mem a fields (a+j)
Proof
  Induct >> simp[type_memory_size_def] >>
  gen_tac >> PairCases_on `h` >> gen_tac >> Cases_on `vs`
  >- simp[value_has_type_def] >>
  PairCases_on `h` >>
  simp[value_has_type_def, val_wf_def, val_in_memory_def, type_memory_size_def] >>
  rpt strip_tac >>
  simp[Once mem_dead_bytes_def] >>
  (Cases_on `j < type_memory_size h1`
  >- (disj1_tac >>
      qpat_x_assum `!name tv. _` (qspecl_then [`h0`, `h1`] mp_tac) >>
      simp[] >>
      disch_then (qspecl_then [`h1'`, `a`, `mem`, `dirty`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  disj2_tac >>
  qpat_x_assum `!vs a mem dirty. _`
    (qspecl_then [`t`, `a + type_memory_size h1`, `mem`, `dirty`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qspec_then `j - type_memory_size h1` mp_tac) >>
  `a + type_memory_size h1 + (j - type_memory_size h1) = a+j` by decide_tac >>
  simp[])
QED

Theorem body_assign_immutable_sensitivity_struct[local]:
  !fields.
    (!name tv. MEM (name,tv) fields ==> !v a mem dirty.
      well_formed_type_value tv /\
      (value_has_type tv v \/ v = default_value tv) /\ val_wf tv v /\
      (!m. mem_agree_outside dirty mem m ==> val_in_memory tv v a m) ==>
      !j. j < type_memory_size tv /\ a+j IN dirty ==>
        mem_dead_bytes mem a tv (a+j)) ==>
    !v a mem dirty.
      well_formed_type_value (StructTV fields) /\
      (value_has_type (StructTV fields) v \/ v = default_value (StructTV fields)) /\
      val_wf (StructTV fields) v /\
      (!m. mem_agree_outside dirty mem m ==>
        val_in_memory (StructTV fields) v a m) ==>
      !j. j < type_memory_size (StructTV fields) /\ a+j IN dirty ==>
        mem_dead_bytes mem a (StructTV fields) (a+j)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `v` >>
  simp[value_has_type_def, default_value_def, default_value_struct_MAP] >>
  simp[val_wf_def, val_in_memory_def, well_formed_type_value_def,
       type_memory_size_def, mem_dead_bytes_def] >>
  rpt strip_tac >> irule body_assign_immutable_sensitivity_field_list >>
  simp[] >> metis_tac[]
QED

Theorem body_assign_immutable_sensitivity_fixed[local]:
  (!v a mem dirty.
     well_formed_type_value tv /\
     (value_has_type tv v \/ v = default_value tv) /\ val_wf tv v /\
     (!m. mem_agree_outside dirty mem m ==> val_in_memory tv v a m) ==>
     !j. j < type_memory_size tv /\ a + j IN dirty ==>
       mem_dead_bytes mem a tv (a+j)) ==>
  !n v a mem dirty.
     well_formed_type_value (ArrayTV tv (Fixed n)) /\
     (value_has_type (ArrayTV tv (Fixed n)) v \/
      v = default_value (ArrayTV tv (Fixed n))) /\
     val_wf (ArrayTV tv (Fixed n)) v /\
     (!m. mem_agree_outside dirty mem m ==>
       val_in_memory (ArrayTV tv (Fixed n)) v a m) ==>
     !j. j < type_memory_size (ArrayTV tv (Fixed n)) /\ a+j IN dirty ==>
       mem_dead_bytes mem a (ArrayTV tv (Fixed n)) (a+j)
Proof
  disch_tac >> rpt gen_tac >> disch_tac >>
  `?kvs. v = ArrayV (SArrayV kvs) /\ sparse_has_type tv n kvs` by
    (Cases_on `v` >> gvs[value_has_type_def, default_value_def] >>
     rename1 `ArrayV arr` >> Cases_on `arr` >>
     gvs[value_has_type_def]) >>
  `well_formed_type_value tv` by fs[well_formed_type_value_def] >>
  `!m. mem_agree_outside dirty mem m ==>
       val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) a m`
    by metis_tac[] >>
  qpat_x_assum `well_formed_type_value (ArrayTV _ _) /\ _` kall_tac >>
  gvs[type_memory_size_def] >> rpt strip_tac >>
  `0 < type_memory_size tv` by
    (Cases_on `type_memory_size tv = 0` >> gvs[]) >>
  `j DIV type_memory_size tv < n` by simp[DIV_LT_X] >>
  `j = j DIV type_memory_size tv * type_memory_size tv +
       j MOD type_memory_size tv /\ j MOD type_memory_size tv < type_memory_size tv`
    by metis_tac[DIVISION] >>
  qpat_x_assum `!m. mem_agree_outside dirty mem m ==> _`
    (assume_tac o SRULE [Once val_in_memory_def]) >>
  `?w. (value_has_type tv w \/ w = default_value tv) /\ val_wf tv w /\
       (!m. mem_agree_outside dirty mem m ==>
         val_in_memory tv w (a + (j DIV type_memory_size tv) * type_memory_size tv) m)` by
    (Cases_on `ALOOKUP kvs (j DIV type_memory_size tv)`
     >- (qexists_tac `default_value tv` >>
         simp[val_wf_default_value_proof] >> metis_tac[]) >>
     rename1 `ALOOKUP kvs _ = SOME w` >>
     `value_has_type tv w` by metis_tac[sparse_has_type_lookup] >>
     qexists_tac `w` >>
     simp[value_has_type_val_wf] >> metis_tac[kvs_in_memory_lookup, MULT_COMM]) >>
  `a + (j DIV type_memory_size tv) * type_memory_size tv +
     j MOD type_memory_size tv = a+j` by decide_tac >>
  `mem_dead_bytes mem (a + (j DIV type_memory_size tv) * type_memory_size tv)
      tv (a+j)` by
    (first_x_assum
       (qspecl_then [`w`, `a + (j DIV type_memory_size tv) * type_memory_size tv`,
                    `mem`, `dirty`] mp_tac) >>
     (impl_tac >- metis_tac[]) >>
     disch_then (qspec_then `j MOD type_memory_size tv` mp_tac) >>
     qpat_assum `a + _ + _ = a+j` (fn th => rewrite_tac[th]) >> simp[]) >>
  simp[mem_dead_bytes_def] >> metis_tac[MULT_COMM]
QED

Theorem body_assign_immutable_rep_sensitivity_mutual[local]:
  (!tv v a mem dirty.
    well_formed_type_value tv /\
    (value_has_type tv v \/ v = default_value tv) /\ val_wf tv v /\
    (!m. mem_agree_outside dirty mem m ==> val_in_memory tv v a m) ==>
    !j. j < type_memory_size tv /\ a+j IN dirty ==>
      mem_dead_bytes mem a tv (a+j)) /\
  (!tvs tv. MEM tv tvs ==> !v a mem dirty.
    well_formed_type_value tv /\
    (value_has_type tv v \/ v = default_value tv) /\ val_wf tv v /\
    (!m. mem_agree_outside dirty mem m ==> val_in_memory tv v a m) ==>
    !j. j < type_memory_size tv /\ a+j IN dirty ==>
      mem_dead_bytes mem a tv (a+j)) /\
  (!(fields : (identifier # type_value) list) name tv. MEM (name,tv) fields ==> !v a mem dirty.
    well_formed_type_value tv /\
    (value_has_type tv v \/ v = default_value tv) /\ val_wf tv v /\
    (!m. mem_agree_outside dirty mem m ==> val_in_memory tv v a m) ==>
    !j. j < type_memory_size tv /\ a+j IN dirty ==>
      mem_dead_bytes mem a tv (a+j))
Proof
  ho_match_mp_tac type_memory_size_ind >> rpt conj_tac
  >>~- ([`BaseTV _`], metis_tac[body_assign_immutable_sensitivity_base])
  >>~- ([`FlagTV _`], metis_tac[body_assign_immutable_sensitivity_base])
  >~ [`NoneTV`] >- metis_tac[body_assign_immutable_sensitivity_base]
  >~ [`TupleTV _`]
  >- (gen_tac >> disch_tac >>
      MATCH_MP_TAC body_assign_immutable_sensitivity_tuple >>
      first_assum ACCEPT_TAC)
  >~ [`ArrayTV _ (Fixed _)`]
  >- (rpt gen_tac >> disch_tac >>
      MATCH_MP_TAC body_assign_immutable_sensitivity_fixed >>
      first_assum ACCEPT_TAC)
  >~ [`ArrayTV _ (Dynamic _)`]
  >- (rpt gen_tac >> disch_tac >>
      MATCH_MP_TAC body_assign_immutable_sensitivity_dynamic >>
      first_assum ACCEPT_TAC)
  >~ [`StructTV _`]
  >- (gen_tac >> disch_tac >>
      MATCH_MP_TAC body_assign_immutable_sensitivity_struct >>
      first_assum ACCEPT_TAC)
  >> simp[] >> metis_tac[]
QED

Theorem body_assign_immutable_rep_sensitivity:
  !tv v a mem dirty.
    well_formed_type_value tv /\
    (value_has_type tv v \/ v = default_value tv) /\ val_wf tv v /\
    (!m. mem_agree_outside dirty mem m ==> val_in_memory tv v a m) ==>
    !j. j < type_memory_size tv /\ a+j IN dirty ==>
      mem_dead_bytes mem a tv (a+j)
Proof
  metis_tac[body_assign_immutable_rep_sensitivity_mutual]
QED
