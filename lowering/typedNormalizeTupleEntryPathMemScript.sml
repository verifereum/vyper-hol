(* Tuple metadata and finite semantic entries for typed memory stores. *)
Theory typedNormalizeTupleEntryPathMem
Ancestors
  typedNormalizeArrayEntryPathMem typedNormalizeFieldPathMem
  typedNormalizeFieldRepresentation typedNormalizeTupleSemanticMem
  typedMemoryCopy typedCopyDomain typedCopyMetadata tupleTypedLoad
  vyperTypeSystem vyperTypeArgFits vyperTyping context compileEnv
  valueEncoding valueEncodingProps valueEncodingProofs vyperValue
  abiTupleValueEncoding vyperTypeABI list rich_list arithmetic words
  abiDecoderFrame typedNormalizeFields typedNormalizeLayout exprLoweringProps

Theorem typed_tuple_entry_metadata[local]:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty (TupleT tys) /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv (TupleT tys) = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v ==>
  ?stys stvs dtvs vs.
    sty = TupleT stys /\ stv = TupleTV stvs /\ dtv = TupleTV dtvs /\
    v = ArrayV (TupleV vs) /\
    LIST_REL (type_widens_to tenv) stys tys /\
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) stys stvs /\
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys dtvs /\
    LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) stys stvs /\
    LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) tys dtvs /\
    LENGTH tys = LENGTH stys /\ LENGTH tys = LENGTH dtvs /\
    LENGTH stys = LENGTH stvs /\ LENGTH vs = LENGTH tys /\
    values_have_types stvs vs /\ values_have_types dtvs vs /\
    EVERY2 val_wf stvs vs /\ EVERY2 val_wf dtvs vs
Proof
  strip_tac >>
  `?stys. sty = TupleT stys` by metis_tac[typed_copy_tuple_widening] >>
  qpat_x_assum `sty = TupleT stys` SUBST_ALL_TAC >>
  qpat_x_assum `evaluate_type tenv (TupleT stys) = SOME stv` mp_tac >>
  simp[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >> strip_tac >>
  qpat_x_assum `evaluate_type tenv (TupleT tys) = SOME dtv` mp_tac >>
  simp[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >> strip_tac >>
  qpat_x_assum `TupleTV _ = stv` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `TupleTV _ = dtv` (SUBST_ALL_TAC o SYM) >>
  Cases_on `v` >> gnvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gnvs[value_has_type_def] >>
  `LIST_REL (type_widens_to tenv) stys tys` by
    (irule typed_copy_tuple_children_widen >> conj_tac >- metis_tac[] >>
     drule typed_copy_tuple_widening >> simp[] >> strip_tac >> simp[]) >>
  `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) stys tvs /\
   LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs'` by
    (conj_tac >> irule OPT_MMAP_LIST_REL >> simp[]) >>
  `LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) stys tvs /\
   LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) tys tvs'` by
    (conj_tac >> fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
     irule typed_copy_memory_size >> qexists `tenv` >> simp[] >> metis_tac[]) >>
  fs[LIST_REL_EL_EQN, val_wf_def, abi_values_have_types] >>
  metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]
QED

(* Convert whole tuple windows to child windows without exposing prefix
   arithmetic in the recursive callback consumer. *)
Theorem typed_tuple_child_windows[local]:
  LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) DT dtvs /\
  LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) ST stvs /\
  LENGTH DT = LENGTH ST /\
  (!j. d j = b + SUM (MAP (type_memory_bytes ce) (TAKE j DT))) /\
  (!j. h j = a + SUM (MAP (type_memory_bytes ce) (TAKE j ST))) /\
  (a + type_memory_size_list stvs <= b \/ b + type_memory_size_list dtvs <= a) /\
  b + type_memory_size_list dtvs < dimword(:256) /\
  a + type_memory_size_list stvs < dimword(:256) /\ i < LENGTH DT ==>
  d i + type_memory_size (EL i dtvs) = d (SUC i) /\
  h i + type_memory_size (EL i stvs) = h (SUC i) /\
  d (SUC i) < dimword(:256) /\ h (SUC i) < dimword(:256) /\
  (h (SUC i) <= d i \/ d (SUC i) <= h i) /\
  d i < dimword(:256) /\ h i < dimword(:256)
Proof
  strip_tac >>
  `d i + type_memory_size (EL i dtvs) = d (SUC i) /\
   d (SUC i) <= d (LENGTH DT) /\ b <= d i` by
    (irule normalize_tuple_child_interval >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists `ce` >> simp[]) >>
  `i < LENGTH ST` by metis_tac[] >>
  `h i + type_memory_size (EL i stvs) = h (SUC i) /\
   h (SUC i) <= h (LENGTH ST) /\ a <= h i` by
    (irule normalize_tuple_child_interval >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists `ce` >> simp[]) >>
  `d (LENGTH DT) = b + type_memory_size_list dtvs /\
   h (LENGTH ST) = a + type_memory_size_list stvs` by
    (qpat_assum `LIST_REL _ DT dtvs`
       (mp_then Any assume_tac abiCallerTupleLayoutTheory.abi_caller_memory_size_list) >>
     qpat_assum `LIST_REL _ ST stvs`
       (mp_then Any assume_tac abiCallerTupleLayoutTheory.abi_caller_memory_size_list) >>
     conj_tac
     >- (qpat_assum `!j. d j = _` (qspec_then `LENGTH DT` mp_tac) >>
         simp_tac std_ss [TAKE_LENGTH_TOO_LONG] >> metis_tac[]) >>
     qpat_assum `!j. h j = _` (qspec_then `LENGTH ST` mp_tac) >>
     simp_tac std_ss [TAKE_LENGTH_TOO_LONG] >> metis_tac[]) >>
  `h (LENGTH DT) = h (LENGTH ST)` by metis_tac[] >>
  decide_tac
QED

Theorem normalize_tuple_semantic_path_mem:
  LENGTH DT = LENGTH ST /\ LENGTH DT = LENGTH dtvs /\
  LENGTH ST = LENGTH stvs /\ LENGTH vs = LENGTH DT /\
  LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) DT dtvs /\
  LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) ST stvs /\
  EVERY2 val_wf stvs vs /\ EVERY2 val_wf dtvs vs /\
  (!i. d i = b + SUM (MAP (type_memory_bytes ce) (TAKE i DT))) /\
  (!i. h i = a + SUM (MAP (type_memory_bytes ce) (TAKE i ST))) /\
  (h (LENGTH DT) <= b \/ d (LENGTH DT) <= a) /\
  d (LENGTH DT) <= s.vs_alloca_next /\ h (LENGTH DT) <= s.vs_alloca_next /\
  d (LENGTH DT) < dimword(:256) /\ h (LENGTH DT) < dimword(:256) /\
  tuple_in_memory vs stvs a s.vs_memory /\
  (!i sd se dp sp u.
    i < LENGTH DT /\
    compile_store_memory_typed ce dp (EL i DT) sp (EL i ST) sd = ((),se) /\
    eval_operand dp u = SOME (n2w (d i)) /\
    eval_operand sp u = SOME (n2w (h i)) /\
    (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
    phi_prefix_length sd.cs_current_insts = 0 /\ fn_has_code sd se fn /\
    (?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    d (SUC i) <= u.vs_alloca_next /\ h (SUC i) <= u.vs_alloca_next /\
    val_in_memory (EL i stvs) (EL i vs) (h i) u.vs_memory ==>
    ?v g. gas_path_mem ctx fn u g (OK v) /\
      val_in_memory (EL i dtvs) (EL i vs) (d i) v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      abi_decode_footprint_frame [(d i,type_memory_bytes ce (EL i DT))] u v /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      sd.cs_next_var <= se.cs_next_var /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) /\
  compile_typed_copy_fields ce dst src DT ST 0 0 sa = ((),sb) /\
  phi_prefix_length sa.cs_current_insts = 0 /\
  (?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME (n2w b) /\ eval_operand src s = SOME (n2w a) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tuple_in_memory vs dtvs b t.vs_memory /\
    (!p k. p+k <= b \/ b+type_memory_size_list dtvs <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    sa.cs_next_var <= sb.cs_next_var /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac (BETA_RULE (Q.INST
      [`TS` |-> `\i. EL i stvs`, `TD` |-> `\i. EL i dtvs`,
       `VS` |-> `\i. EL i vs`, `VD` |-> `\i. EL i vs`]
      normalize_tuple_fields_memory_path_mem))) >>
  disch_then (fn th => qpat_assum `!i sd se dp sp u. _` (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`s`, `b`, `a`] mp_tac) >>
  qpat_x_assum `!i sd se dp sp u. _` kall_tac >>
  (impl_tac >-
    (simp_tac bool_ss [ADD_CLAUSES] >>
     ntac 3 (conj_tac >- simp[]) >>
     (conj_tac >- (fs[abi_footprint_disjoint_def] >> gvs[])) >>
     ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >-
       (gen_tac >> strip_tac >> conj_tac >- gvs[LIST_REL_EL_EQN] >>
        `i < LENGTH ST` by metis_tac[] >>
        drule normalize_prefix_step >>
        disch_then (qspec_then `type_memory_bytes ce` assume_tac) >>
        gvs[LIST_REL_EL_EQN])) >>
     (conj_tac >-
       (gen_tac >> strip_tac >> conj_tac >- gvs[LIST_REL_EL_EQN] >>
        drule normalize_prefix_step >>
        disch_then (qspec_then `type_memory_bytes ce` assume_tac) >>
        gvs[LIST_REL_EL_EQN])) >>
     (conj_tac >-
       (rpt strip_tac >> drule tuple_in_memory_EL >>
        disch_then (qspec_then `i` mp_tac) >>
        qpat_assum `LIST_REL _ ST stvs`
          (mp_then Any (qspec_then `i` assume_tac) tuple_prefix_sizes) >> simp[])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> qexistsl [`t`, `g`] >> simp[] >>
  conj_tac
  >- (irule normalize_tuple_compiler_offsets >> conj_tac >- simp[] >>
      qexistsl [`ce`, `DT`] >> simp[] >> rpt strip_tac >>
      qpat_x_assum `!i. i < LENGTH DT ==> val_in_memory _ _ _ _`
        (qspec_then `j` mp_tac) >> simp[]) >>
  qpat_assum `LIST_REL _ DT dtvs` (mp_then Any
    (qspec_then `LENGTH DT` assume_tac) tuple_prefix_sizes) >>
  `SUM (MAP (type_memory_bytes ce) DT) = type_memory_size_list dtvs` by
    (gvs[type_memory_size_list_sum, TAKE_LENGTH_TOO_LONG]) >>
  qpat_x_assum `abi_decode_footprint_frame _ _ _` mp_tac >>
  simp[abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[ADD_COMM, GSYM type_memory_size_list_sum]
QED

Theorem typed_ordered_fields_child_rank_path_mem:
  LIST_REL (type_widens_to tenv) ST DT /\
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) ST stvs /\
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) DT dtvs /\
  LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) DT dtvs /\
  LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) ST stvs /\
  values_have_types stvs vs /\ values_have_types dtvs vs /\
  EVERY2 val_wf stvs vs /\ EVERY2 val_wf dtvs vs /\
  LENGTH DT = LENGTH ST /\
  (!ty. MEM ty DT ==> type_rank ce.ce_struct_fields ty < rank) /\
  (!j. d j = b + SUM (MAP (type_memory_bytes ce) (TAKE j DT))) /\
  (!j. h j = a + SUM (MAP (type_memory_bytes ce) (TAKE j ST))) /\
  (a + type_memory_size_list stvs <= b \/ b + type_memory_size_list dtvs <= a) /\
  b + type_memory_size_list dtvs < dimword(:256) /\
  a + type_memory_size_list stvs < dimword(:256) /\
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
    (?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
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
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)) ==>
  !i sd se dp sp u.
    i < LENGTH DT /\
    compile_store_memory_typed ce dp (EL i DT) sp (EL i ST) sd = ((),se) /\
    eval_operand dp u = SOME (n2w (d i)) /\
    eval_operand sp u = SOME (n2w (h i)) /\
    (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
    phi_prefix_length sd.cs_current_insts = 0 /\ fn_has_code sd se fn /\
    (?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    d (SUC i) <= u.vs_alloca_next /\ h (SUC i) <= u.vs_alloca_next /\
    val_in_memory (EL i stvs) (EL i vs) (h i) u.vs_memory ==>
    ?v g. gas_path_mem ctx fn u g (OK v) /\
      val_in_memory (EL i dtvs) (EL i vs) (d i) v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      abi_decode_footprint_frame [(d i,type_memory_bytes ce (EL i DT))] u v /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      sd.cs_next_var <= se.cs_next_var /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `d i + type_memory_size (EL i dtvs) = d (SUC i) /\
   h i + type_memory_size (EL i stvs) = h (SUC i) /\
   d (SUC i) < dimword(:256) /\ h (SUC i) < dimword(:256) /\
   (h (SUC i) <= d i \/ d (SUC i) <= h i) /\
   d i < dimword(:256) /\ h i < dimword(:256)` by
    (irule typed_tuple_child_windows >> qexistsl [`DT`, `ST`, `a`, `b`, `ce`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `type_rank ce.ce_struct_fields (EL i DT) < rank` by
    (qpat_x_assum `!ty. MEM ty DT ==> _` irule >> simp[EL_MEM]) >>
  `evaluate_type tenv (EL i ST) = SOME (EL i stvs) /\
   evaluate_type tenv (EL i DT) = SOME (EL i dtvs) /\
   type_widens_to tenv (EL i ST) (EL i DT) /\
   value_has_type (EL i stvs) (EL i vs) /\
   value_has_type (EL i dtvs) (EL i vs) /\
   val_wf (EL i stvs) (EL i vs) /\ val_wf (EL i dtvs) (EL i vs) /\
   type_memory_bytes ce (EL i DT) = type_memory_size (EL i dtvs)` by
    (qpat_x_assum `!dty sty dtv stv v dst src sa sb s dw sw. _` kall_tac >>
     fs[LIST_REL_EL_EQN, abi_values_have_types]) >>
  qpat_x_assum `!j. d j = _` kall_tac >>
  qpat_x_assum `!j. h j = _` kall_tac >>
  qpat_x_assum `!dty sty dtv stv v dst src sa sb s dw sw. _`
    (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dp _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand sp _ = _`)) >>
  disch_then (qspecl_then [`EL i dtvs`, `EL i stvs`, `EL i vs`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  strip_tac >> qexistsl [`t`, `g`] >>
  `sd.cs_next_var <= se.cs_next_var` by
    metis_tac[cj 1 ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  qpat_assum `_ = u` (assume_tac o SRULE [] o Q.AP_TERM `\z. z.vs_call_ctx`) >>
  qpat_assum `_ = u` (assume_tac o SRULE [] o Q.AP_TERM `\z. z.vs_data_section`) >>
  gvs[abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
  metis_tac[ADD_COMM]
QED

Theorem typed_store_tuple_entry_path_mem:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_rank ce.ce_struct_fields (TupleT tys) = rank /\
  type_widens_to tenv sty (TupleT tys) /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv (TupleT tys) = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  compile_store_memory_typed ce dst (TupleT tys) src sty sa = ((),sb) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n sw + type_memory_size stv < dimword(:256) /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw) /\
  phi_prefix_length sa.cs_current_insts = 0 /\
  (?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) /\
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
    (?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
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
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)) ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_tuple_entry_metadata >>
  disch_then (qx_choose_then `ST` (qx_choose_then `stvs`
    (qx_choose_then `dtvs` (qx_choose_then `vs` strip_assume_tac)))) >>
  qpat_x_assum `sty = TupleT ST` SUBST_ALL_TAC >>
  qpat_x_assum `stv = TupleTV stvs` SUBST_ALL_TAC >>
  qpat_x_assum `dtv = TupleTV dtvs` SUBST_ALL_TAC >>
  qpat_x_assum `v = ArrayV (TupleV vs)` SUBST_ALL_TAC >>
  `compile_typed_copy_fields ce dst src tys ST 0 0 sa = ((),sb)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def]) >>
  `!ty. MEM ty tys ==> type_rank ce.ce_struct_fields ty < rank` by
    (gen_tac >> strip_tac >> qpat_x_assum `type_rank _ (TupleT _) = rank`
      (SUBST1_TAC o SYM) >> irule member_rank_lt_tuple >> simp[]) >>
  qabbrev_tac `d = \i. w2n dw + SUM (MAP (type_memory_bytes ce) (TAKE i tys))` >>
  qabbrev_tac `h = \i. w2n sw + SUM (MAP (type_memory_bytes ce) (TAKE i ST))` >>
  qpat_assum `!dty sty dtv stv v dst src sa sb s dw sw. _`
    (mp_then Any mp_tac (Q.INST [`d` |-> `d`, `h` |-> `h`,
      `a` |-> `w2n (sw:256 word)`, `b` |-> `w2n (dw:256 word)`]
      typed_ordered_fields_child_rank_path_mem)) >>
  disch_then (drule_at (Pat `LIST_REL (type_widens_to tenv) _ _`)) >>
  disch_then (drule_at (Pat `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) ST stvs`)) >>
  disch_then (drule_at (Pat `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys dtvs`)) >>
  disch_then (qspec_then `vs` mp_tac) >>
  disch_then (qspecl_then [`sw`, `h`, `dw`, `d`] mp_tac) >>
  qpat_x_assum `!dty sty dtv stv v dst src sa sb s dw sw. _` kall_tac >>
  fs[type_memory_size_def] >>
  disch_tac >>
  qpat_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac (SRULE [] normalize_tuple_semantic_path_mem)) >>
  disch_then (drule_at (Pat `LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) tys dtvs`)) >>
  disch_then (drule_at (Pat `LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) ST stvs`)) >>
  disch_then (qspecl_then [`vs`, `s`, `h`, `fn`, `d`, `ctx`, `w2n dw`, `w2n sw`] mp_tac) >>
  `d (LENGTH tys) = w2n dw + type_memory_size_list dtvs /\
   h (LENGTH tys) = w2n sw + type_memory_size_list stvs` by
    (qpat_assum `LIST_REL _ tys dtvs` (mp_then Any assume_tac abiCallerTupleLayoutTheory.abi_caller_memory_size_list) >>
     qpat_assum `LIST_REL _ ST stvs` (mp_then Any assume_tac abiCallerTupleLayoutTheory.abi_caller_memory_size_list) >>
     simp[Abbr `d`, Abbr `h`, TAKE_LENGTH_TOO_LONG] >> metis_tac[]) >>
  (impl_tac >- (fs[Abbr `d`, Abbr `h`, val_in_memory_def] >>
    conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC)) >>
  strip_tac >> qexistsl [`t`, `g`] >> simp[val_in_memory_def] >>
  qpat_x_assum `!p k. _` mp_tac >> simp[ADD_COMM]
QED
