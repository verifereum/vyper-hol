(* The source annotation bounds the value; the operand capacities size
   the buffer actually allocated by the Concat lowering. *)
Theory bodyConcatResultEncodingMods
Ancestors
  bodyConcatCutsMods exprLowering compileEnv exprSimProps loweringPosts
  valueEncodingDefs valueEncodingTyping valueEncodingProps
  vyperTypeConversions vyperTyping vfmConstants arithmetic list words

Theorem concat_payload_length_bound[local]:
  !tenv ty tv v.
    ((?bd. ty = BaseT (BytesT bd)) \/ (?m. ty = BaseT (StringT m))) /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
    LENGTH (concat_payload_mods v) <= concat_payload_capacity ty
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule evaluate_type_BaseT_SOME >> strip_tac >> gvs[]
  >- (Cases_on `bd` >> Cases_on `v` >>
      gvs[value_has_type_def,concat_payload_mods_def,concat_payload_capacity_def]) >>
  Cases_on `v` >>
  gvs[value_has_type_def,concat_payload_mods_def,concat_payload_capacity_def]
QED

Theorem concat_payloads_length_bound[local]:
  !args vs.
    EVERY (\t. (?bd. t = BaseT (BytesT bd)) \/ (?m. t = BaseT (StringT m)))
      (MAP expr_type args) /\
    LIST_REL (\e v. ?tv. evaluate_type tenv (expr_type e) = SOME tv /\
                          value_has_type tv v) args vs ==>
    LENGTH (FLAT (MAP concat_payload_mods vs)) <=
    SUM (MAP concat_payload_capacity (MAP expr_type args))
Proof
  Induct
  >- (Cases >> simp[]) >>
  gen_tac >> Cases >> simp[] >> strip_tac >>
  `LENGTH (concat_payload_mods h') <= concat_payload_capacity (expr_type h)` by
    (irule concat_payload_length_bound >> conj_tac >- metis_tac[] >>
     qexistsl [`tenv`,`tv`] >> simp[]) >>
  first_x_assum drule_all >> decide_tac
QED

Theorem concat_result_encoding_mods:
  !cenv cx a n args vs tv v p B bsz s.
    ((a = BaseT (BytesT (Dynamic n)) /\
      EVERY (\t. ?bd. t = BaseT (BytesT bd)) (MAP expr_type args)) \/
     (a = BaseT (StringT n) /\
      EVERY (\t. ?m. t = BaseT (StringT m)) (MAP expr_type args))) /\
    LIST_REL (\e x. ?te. evaluate_type (get_tenv cx) (expr_type e) = SOME te /\
                          value_has_type te x) args vs /\
    evaluate_type (get_tenv cx) a = SOME tv /\ value_has_type tv v /\
    concat_payload_mods v = p /\ p = FLAT (MAP concat_payload_mods vs) /\
    bsz = concat_alloc_size (MAP expr_type args) /\ B + bsz < dimword (:256) /\
    mload B s = n2w (LENGTH p) /\ mem_bytes_at (B + 32) (LENGTH p) s.vs_memory = p ==>
    ~is_word_type a /\ val_wf tv v /\ val_footprint tv v = 32 + LENGTH p /\
    val_store_size tv v <= bsz /\ val_in_memory tv v B s.vs_memory /\
    type_memory_bytes cenv (lowered_value_type cenv (Builtin a (Concat n) args)) <= bsz
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (\t. (?bd. t = BaseT (BytesT bd)) \/ (?m. t = BaseT (StringT m)))
     (MAP expr_type args)` by
    (qpat_x_assum `(_ /\ _) \/ (_ /\ _)` strip_assume_tac >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `LENGTH p <= SUM (MAP concat_payload_capacity (MAP expr_type args))` by
    (qpat_assum `p = FLAT _` (SUBST1_TAC) >>
     irule concat_payloads_length_bound >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `get_tenv cx` >> first_assum ACCEPT_TAC) >>
  `32 + 32 * word_size (LENGTH p) <= bsz` by
    (drule word_size_monotone >>
     qpat_assum `bsz = _` SUBST1_TAC >>
     simp[concat_alloc_size_def,MAX_LE,word_size_def] >> decide_tac) >>
  `val_wf tv v` by simp[value_has_type_val_wf] >>
  qpat_x_assum `(_ /\ _) \/ (_ /\ _)` strip_assume_tac >>
  qpat_x_assum `a = _` SUBST_ALL_TAC >>
  drule evaluate_type_BaseT_SOME >> disch_then SUBST_ALL_TAC >>
  Cases_on `v` >>
  gvs[value_has_type_def,concat_payload_mods_def,val_footprint_def,val_store_size_def,
      val_in_memory_def,mem_word_at_eq_mload,is_word_type_def,lowered_value_type_def,
      concat_buffer_type_def,type_memory_bytes_def,concat_alloc_size_def,
      MAP_MAP_o,combinTheory.o_DEF,MAX_LE] >>
  qpat_assum `MAP _ _ = FLAT _` (mp_tac o AP_TERM ``LENGTH : word8 list -> num``) >>
  simp[]
QED
