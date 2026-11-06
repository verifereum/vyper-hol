(* Nominal constructor entry for destination-rank memory induction. *)
Theory typedNormalizeStructEntryMem
Ancestors
  typedNormalizeStructSemanticMem typedNormalizeStructMetadata
  typedMemoryCopy typedCopyMetadata valueEncodingTyping vyperTypeArgFits
  vyperTypeABI vyperValue vyperTyping vyperTypeDefaults valueEncoding
  list rich_list arithmetic words venomState compileEnv memContinuation
  tupleTypedLoad valueEncodingProofs context

Theorem typed_store_struct_mem_cont:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty (StructT name) /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv (StructT name) = SOME dtv /\
  value_has_type dtv v /\ val_wf dtv v /\
  (!ty tv cv sd se dp sp u dw sw.
    type_rank ce.ce_struct_fields ty < type_rank ce.ce_struct_fields (StructT name) /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv cv /\ val_wf tv cv /\
    compile_store_memory_typed ce dp ty sp ty sd = ((),se) /\
    eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
    (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
    fn_has_code sd se fn /\
    (emitted_blocks sd se <> [] ==>
      ?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0) /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    w2n dw + type_memory_size tv <= u.vs_alloca_next /\
    w2n sw + type_memory_size tv <= u.vs_alloca_next /\
    w2n dw + type_memory_size tv < dimword(:256) /\
    w2n sw + type_memory_size tv < dimword(:256) /\
    (w2n sw + type_memory_size tv <= w2n dw \/
      w2n dw + type_memory_size tv <= w2n sw) /\
    val_in_memory tv cv (w2n sw) u.vs_memory ==>
    ?t. mem_cont_sim ctx fn u t /\ ~t.vs_halted /\
      t.vs_current_bb = se.cs_current_bb /\
      t.vs_inst_idx = LENGTH se.cs_current_insts /\
      val_in_memory tv cv (w2n dw) t.vs_memory /\
      (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size tv <= p ==>
        mem_bytes_at p k t.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sd.cs_current_bb; vs_inst_idx := LENGTH sd.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sd x ==> lookup_var x t = lookup_var x u)) /\
  compile_store_memory_typed ce dst (StructT name) src sty sa = ((),sb) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n sw + type_memory_size stv < dimword(:256) /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw) /\
  (emitted_blocks sa sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) ==>
  ?t. mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s
Proof
    disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all normalize_struct_metadata >> strip_tac >>
  qpat_x_assum `sty = _` SUBST_ALL_TAC >>
  qpat_x_assum `stv = _` SUBST_ALL_TAC >>
  qpat_x_assum `dtv = _` SUBST_ALL_TAC >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  qpat_x_assum `names = _` SUBST_ALL_TAC >>
  `type_memory_size (StructTV (ZIP (MAP FST fields,tvs))) =
    type_memory_size_list tvs` by
    simp[type_memory_size_def, type_memory_size_fields_zip] >>
  `LENGTH fields = LENGTH tvs` by metis_tac[LENGTH_MAP] >>
  `SUM (MAP (type_memory_bytes ce) (MAP (FST o SND) fields)) =
    type_memory_size_list tvs` by
    (drule tuple_prefix_sizes >> disch_then (qspec_then `LENGTH fields` mp_tac) >>
     simp[type_memory_size_list_sum, TAKE_LENGTH_TOO_LONG]) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _`
    (mp_tac o SRULE [Once compile_store_memory_typed_def, is_word_type_def,
      is_bytestring_type_def, get_struct_fields_def]) >> strip_tac >>
  pure_rewrite_tac[val_in_memory_def, type_value_case_def] >>
  qpat_assum `type_memory_size (StructTV _) = _`
    (fn th => pure_rewrite_tac[th]) >>
  BETA_TAC >>
  qpat_assum `val_in_memory (StructTV _) _ _ _`
    (assume_tac o SRULE [val_in_memory_def]) >>
  qpat_x_assum `type_memory_size (StructTV _) = _` SUBST_ALL_TAC >>
  irule normalize_struct_semantic_cont >>
  simp[] >>
  qexistsl_tac [`w2n sw`, `ce`,
    `\i. w2n dw + SUM (MAP (type_memory_bytes ce) (TAKE i (MAP (FST o SND) fields)))`,
    `dst`, `fields`,
    `\i. w2n sw + SUM (MAP (type_memory_bytes ce) (TAKE i (MAP (FST o SND) fields)))`,
    `src`, `fields`] >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- suspend "children" >>
  qpat_x_assum `!ty tv cv sd se dp sp u dw sw. _` kall_tac >>
  gvs[TAKE_LENGTH_TOO_LONG, ADD_COMM] >> metis_tac[]
QED
Resume typed_store_struct_mem_cont[children]:
  qpat_x_assum `!ty tv cv sd se dp sp u dw sw. _` mp_tac >>
  qpat_x_assum `!fname fty sz. _` mp_tac >>
  qpat_x_assum `OPT_MMAP _ _ = SOME tvs` mp_tac >>
  qpat_x_assum `LIST_REL (\ty tv. type_memory_bytes ce ty = _) _ _` mp_tac >>
  qpat_x_assum `LIST_REL val_wf _ _` mp_tac >>
  qpat_x_assum `values_have_types _ _` mp_tac >>
  qpat_x_assum `LENGTH fields = LENGTH tvs` mp_tac >>
  rpt (pop_assum kall_tac) >> ntac 7 disch_tac >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv)
    (MAP (FST o SND) fields) tvs` by
    (irule OPT_MMAP_LIST_REL >> simp[]) >>
  `evaluate_type tenv (EL i (MAP (FST o SND) fields)) = SOME (EL i tvs) /\
   value_has_type (EL i tvs) (EL i vs) /\ val_wf (EL i tvs) (EL i vs) /\
   type_memory_bytes ce (EL i (MAP (FST o SND) fields)) =
     type_memory_size (EL i tvs)` by
    (qpat_x_assum `!ty tv cv sd se dp sp u dw sw. _` kall_tac >>
     fs[abiTupleValueEncodingTheory.abi_values_have_types, LIST_REL_EL_EQN]) >>
  `type_rank ce.ce_struct_fields (EL i (MAP (FST o SND) fields)) <
    type_rank ce.ce_struct_fields (StructT name)` by
    (qpat_x_assum `!ty tv cv sd se dp sp u dw sw. _` kall_tac >>
     `i < LENGTH fields` by metis_tac[] >>
     `MEM (EL i fields) fields` by simp[EL_MEM] >>
     qpat_x_assum `!fname fty sz. _`
       (qspecl_then [`FST (EL i fields)`, `FST (SND (EL i fields))`,
         `SND (SND (EL i fields))`] mp_tac) >>
     simp[EL_MAP]) >>
  `SUM (MAP (type_memory_bytes ce)
      (TAKE (SUC i) (MAP (FST o SND) fields))) =
    SUM (MAP (type_memory_bytes ce) (TAKE i (MAP (FST o SND) fields))) +
      type_memory_size (EL i tvs)` by
    (qpat_x_assum `!ty tv cv sd se dp sp u dw sw. _` kall_tac >>
     `i < LENGTH (MAP (FST o SND) fields)` by simp[] >>
     drule typedNormalizeFieldsTheory.normalize_prefix_step >>
     disch_then (qspec_then `type_memory_bytes ce` mp_tac) >> simp[]) >>
  qpat_x_assum `!fname fty sz. MEM (fname,fty,sz) fields ==> _` kall_tac >>
  qpat_x_assum `OPT_MMAP _ _ = SOME tvs` kall_tac >>
  rpt (qhdtm_x_assum `LIST_REL` kall_tac) >>
  qpat_x_assum `values_have_types _ _` kall_tac >>
  suspend "apply_child"
QED
Resume typed_store_struct_mem_cont[apply_child]:
  qmatch_goalsub_abbrev_tac `off + w2n dw` >>
  qabbrev_tac `d = off + w2n dw` >> qabbrev_tac `a = off + w2n sw` >>
  `d + type_memory_size (EL i tvs) <= u.vs_alloca_next /\
   a + type_memory_size (EL i tvs) <= u.vs_alloca_next /\
   d + type_memory_size (EL i tvs) < dimword(:256) /\
   a + type_memory_size (EL i tvs) < dimword(:256) /\
   (a + type_memory_size (EL i tvs) <= d \/
    d + type_memory_size (EL i tvs) <= a)` by
    (qpat_x_assum `!ty tv cv sd se dp sp u dw sw. _` kall_tac >>
     simp[Abbr `d`, Abbr `a`] >> decide_tac) >>
  `d < dimword(:256) /\ a < dimword(:256)` by decide_tac >>
  `w2n (n2w d : 256 word) = d /\ w2n (n2w a : 256 word) = a` by simp[] >>
  qpat_x_assum `!ty tv cv sd se dp sp u dw sw. _`
    (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `value_has_type _ _`)) >>
  disch_then (drule_at (Pat `eval_operand dp _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand sp _ = _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  `off + (type_memory_size (EL i tvs) + w2n dw) =
    d + type_memory_size (EL i tvs)` by
    (simp[Abbr `d`] >> decide_tac) >>
  qexists_tac `t` >> simp[] >> first_assum ACCEPT_TAC
QED
Finalise typed_store_struct_mem_cont
