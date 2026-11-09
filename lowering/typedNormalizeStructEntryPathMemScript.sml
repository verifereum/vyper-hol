(* Finite memory-path entry for nominal typed stores. *)
Theory typedNormalizeStructEntryPathMem
Ancestors
  typedNormalizeTupleEntryPathMem typedNormalizeStructMetadata
  typedNormalizeStructSemanticMem typedCopyDomain vyperTypeArgFits
  valueEncodingProofs valueEncodingTyping context tupleTypedLoad list rich_list words
  typedMemoryCopy compileEnv valueEncoding vyperTypeABI typedNormalizeFields
  vyperValue vyperTyping vyperTypeSystem abiTupleValueEncoding

Theorem nominal_store_ordered_fields[local]:
  acyclic_struct_metadata ce.ce_struct_fields /\
  FLOOKUP ce.ce_struct_fields (nsid_to_string name) = SOME fields /\
  (!fname fty sz. MEM (fname,fty,sz) fields ==>
    ALOOKUP fields fname = SOME (fty,sz) /\ sz = type_memory_bytes ce fty) /\
  compile_store_memory_typed ce dst (StructT name) src (StructT name) sa = ((),sb) ==>
  compile_typed_copy_fields ce dst src (MAP (FST o SND) fields)
    (MAP (FST o SND) fields) 0 0 sa = ((),sb)
Proof
  strip_tac >>
  `compile_struct_typed_copy ce dst src fields fields 0 0 =
    compile_typed_copy_fields ce dst src (MAP (FST o SND) fields)
      (MAP (FST o SND) fields) 0 0` by
    (irule normalize_struct_as_fields >> metis_tac[]) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
    is_bytestring_type_def, get_struct_fields_def]
QED

Theorem typed_store_struct_entry_path_mem:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_rank ce.ce_struct_fields (StructT name) = rank /\
  type_widens_to tenv sty (StructT name) /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv (StructT name) = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  compile_store_memory_typed ce dst (StructT name) src sty sa = ((),sb) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n sw + type_memory_size stv < dimword(:256) /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw) /\
  phi_prefix_length sa.cs_current_insts = 0 /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) /\
  (!dty sty dtv stv v dst src sa sb s dw sw.
    type_rank ce.ce_struct_fields dty < rank /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    compile_store_memory_typed ce dst dty src sty sa = ((),sb) /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv <= s.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
    w2n sw + type_memory_size stv < dimword(:256) /\
    w2n dw + type_memory_size dtv < dimword(:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
      w2n dw + type_memory_size dtv <= w2n sw) /\
    phi_prefix_length sa.cs_current_insts = 0 /\
    fn_has_code sa sb fn /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
    (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) ==>
    ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
        mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
        vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
        vs_prev_bb := s.vs_prev_bb|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory) ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all normalize_struct_metadata >> strip_tac >>
  qpat_x_assum `sty = _` SUBST_ALL_TAC >>
  qpat_x_assum `stv = _` SUBST_ALL_TAC >>
  qpat_x_assum `dtv = _` SUBST_ALL_TAC >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  qpat_x_assum `names = _` SUBST_ALL_TAC >>
  `LENGTH fields = LENGTH tvs` by metis_tac[LENGTH_MAP] >>
  `type_memory_size (StructTV (ZIP (MAP FST fields,tvs))) = type_memory_size_list tvs` by
    simp[type_memory_size_def, type_memory_size_fields_zip] >>
  `compile_typed_copy_fields ce dst src (MAP (FST o SND) fields)
     (MAP (FST o SND) fields) 0 0 sa = ((),sb)` by
    (irule nominal_store_ordered_fields >> simp[] >> metis_tac[]) >>
  qabbrev_tac `DT = MAP (FST o SND) fields` >>
  `!ty. MEM ty DT ==> type_rank ce.ce_struct_fields ty < rank` by
    (qpat_x_assum `!dty sty dtv stv v dst src sa sb s dw sw. _` kall_tac >>
     simp[Abbr `DT`, MEM_MAP, pairTheory.FORALL_PROD] >>
     rpt strip_tac >> gvs[] >> PairCases_on `y` >>
     qpat_x_assum `!fname fty sz. _` drule >> simp[]) >>
  `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) DT tvs` by
    (irule OPT_MMAP_LIST_REL >> simp[Abbr `DT`]) >>
  `LIST_REL (type_widens_to tenv) DT DT` by
    simp[LIST_REL_EL_EQN, type_widens_to_refl] >>
  qabbrev_tac `d = \i. w2n dw + SUM (MAP (type_memory_bytes ce) (TAKE i DT))` >>
  qabbrev_tac `h = \i. w2n sw + SUM (MAP (type_memory_bytes ce) (TAKE i DT))` >>
  qpat_assum `!dty sty dtv stv v dst src sa sb s dw sw. _`
    (mp_then Any mp_tac (Q.INST [`d` |-> `d`, `h` |-> `h`,
      `a` |-> `w2n (sw:256 word)`, `b` |-> `w2n (dw:256 word)`]
      typed_ordered_fields_child_rank_path_mem)) >>
  disch_then (drule_at (Pat `LIST_REL (type_widens_to tenv) _ _`)) >>
  disch_then (drule_at (Pat `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) DT tvs`)) >>
  disch_then (drule_at (Pat `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) DT tvs`)) >>
  disch_then (qspec_then `vs` mp_tac) >>
  disch_then (qspecl_then [`sw`, `h`, `dw`, `d`] mp_tac) >>
  qpat_x_assum `!dty sty dtv stv v dst src sa sb s dw sw. _` kall_tac >>
  fs[Abbr `DT`] >> disch_tac >>
  qpat_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac (SRULE [] normalize_tuple_semantic_path_mem)) >>
  disch_then (drule_at (Pat `LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) DT tvs`)) >>
  disch_then (drule_at (Pat `LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) DT tvs`)) >>
  disch_then (qspecl_then [`vs`, `s`, `h`, `fn`, `d`, `ctx`, `w2n dw`, `w2n sw`] mp_tac) >>
  `d (LENGTH (MAP (FST o SND) fields)) = w2n dw + type_memory_size_list tvs /\
   h (LENGTH (MAP (FST o SND) fields)) = w2n sw + type_memory_size_list tvs` by
    (qpat_assum `LIST_REL _ (MAP (FST o SND) fields) tvs` (mp_then Any assume_tac abiCallerTupleLayoutTheory.abi_caller_memory_size_list) >>
     simp[Abbr `d`, Abbr `h`, TAKE_LENGTH_TOO_LONG] >> metis_tac[]) >>
  (impl_tac >- (fs[Abbr `d`, Abbr `h`, val_in_memory_def,
     fields_in_memory_tuple, MAP_ZIP] >> conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC)) >>
  strip_tac >> qexistsl [`t`, `g`] >>
  simp[val_in_memory_def, fields_in_memory_tuple, MAP_ZIP] >> gvs[]
QED
