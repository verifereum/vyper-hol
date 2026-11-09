(* Constructor metadata and finite semantic entries for typed array stores. *)
Theory typedNormalizeArrayEntryPathMem
Ancestors
  typedNormalizeScalarEntryPathMem typedNormalizeSemanticPathMem
  typedNormalizeDynarrayPathMem typedMemoryCopy typedCopyDomain
  vyperTypeSystem vyperTypeArgFits vyperTyping context compileEnv
  valueEncoding valueEncodingProps vyperValue arithmetic words exprLowering

Theorem typed_array_entry_metadata[local]:
  type_widens_to tenv sty (ArrayT elem bd) /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv (ArrayT elem bd) = SOME dtv ==>
  ?se sb sev dev.
    sty = ArrayT se sb /\ stv = ArrayTV sev sb /\ dtv = ArrayTV dev bd /\
    evaluate_type tenv se = SOME sev /\ evaluate_type tenv elem = SOME dev /\
    type_widens_to tenv se elem /\
    bound_length bd < dimword(:256) /\
    ((?n m. sb = Dynamic n /\ bd = Dynamic m /\ n <= m) \/
     (?n. sb = Fixed n /\ bd = Fixed n))
Proof
  strip_tac >> drule typed_copy_array_source >> strip_tac >> gvs[] >>
  drule typed_copy_array_widening >> strip_tac >>
  `bound_length bd < dimword(:256)` by metis_tac[typed_copy_array_count_bound] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_widens_to tenv se elem` by
    (qpat_x_assum `type_widens_to _ (ArrayT _ _) _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
       evaluate_type_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem typed_store_sarray_bulk_path_mem[local]:
  type_memory_bytes ce dt = type_memory_bytes ce st /\
  ~is_abi_dynamic ce.ce_struct_fields dt /\
  type_widens_to tenv st dt /\
  evaluate_type tenv st = SOME stv /\ evaluate_type tenv dt = SOME dtv /\
  type_memory_bytes ce dt = type_memory_size dtv /\
  compile_copy_sarray_typed ce dst dt src st cap sa = ((),sb) /\
  0 < cap /\ 0 < type_memory_size dtv /\ val_wf (ArrayTV stv (Fixed cap)) v /\
  val_in_memory (ArrayTV stv (Fixed cap)) v (w2n sw) s.vs_memory /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  w2n sw + type_memory_size (ArrayTV stv (Fixed cap)) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (ArrayTV dtv (Fixed cap)) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (ArrayTV dtv (Fixed cap)) < dimword(:256) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory (ArrayTV dtv (Fixed cap)) v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size (ArrayTV dtv (Fixed cap)) <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> `stv = dtv` by metis_tac[typed_copy_static_widening] >> gvs[] >>
  `0 < type_memory_size (ArrayTV dtv (Fixed cap))` by
    simp[type_memory_size_def, type_memory_size_slots] >>
  `type_memory_size (ArrayTV dtv (Fixed cap)) < dimword(:256)` by decide_tac >>
  `compile_copy_memory dst src (type_memory_size (ArrayTV dtv (Fixed cap))) sa = ((),sb)` by
    (qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, type_memory_size_def]) >>
  drule typed_store_bulk_path_mem >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  disch_then (qspecl_then [`v`, `fn`, `ctx`] mp_tac) >> simp[]
QED

(* One specialization of the uniform rank hypothesis serves both array loops. *)
Theorem typed_array_child_rank_path_mem[local]:
  type_rank ce.ce_struct_fields dt < rank /\
  type_widens_to tenv st dt /\
  evaluate_type tenv st = SOME stv /\ evaluate_type tenv dt = SOME dtv /\
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
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)) ==>
  !cv sp dp sc ec u sw dw.
    val_wf stv cv /\ val_wf dtv cv /\
    value_has_type stv cv /\ value_has_type dtv cv /\
    compile_store_memory_typed ce dp dt sp st sc = ((),ec) /\
    fn_has_code sc ec fn /\
    (!x. sp = Var x \/ dp = Var x ==> not_fresh_at sc x) /\
    phi_prefix_length sc.cs_current_insts = 0 /\
    (?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
      phi_prefix_length entry.bb_instructions = 0) /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    eval_operand sp u = SOME sw /\ eval_operand dp u = SOME dw /\
    val_in_memory stv cv (w2n sw) u.vs_memory /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    w2n sw + type_memory_size stv < dimword(:256) /\
    w2n dw + type_memory_size dtv < dimword(:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
      w2n dw + type_memory_size dtv <= w2n sw) ==>
    ?t g. gas_path_mem ctx fn u g (OK t) /\ ~t.vs_halted /\
      t.vs_current_bb = ec.cs_current_bb /\ t.vs_inst_idx = LENGTH ec.cs_current_insts /\
      val_in_memory dtv cv (w2n dw) t.vs_memory /\
      (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
        mem_bytes_at p k t.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!dty sty dtv stv v dst src sa sb s dw sw. _` irule >>
  simp[] >> qexistsl [`dp`, `dt`, `sp`, `stv`, `st`, `sw`] >>
  simp[ADD_COMM] >> metis_tac[]
QED

Theorem typed_store_sarray_entry_path_mem:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_rank ce.ce_struct_fields (ArrayT dt (Fixed cap)) = rank /\
  type_widens_to tenv st dt /\
  evaluate_type tenv st = SOME stv /\ evaluate_type tenv dt = SOME dtv /\
  compile_copy_sarray_typed ce dst dt src st cap sa = ((),sb) /\
  0 < cap /\ 0 < type_memory_size dtv /\ cap < dimword(:256) /\
  value_has_type (ArrayTV stv (Fixed cap)) v /\
  value_has_type (ArrayTV dtv (Fixed cap)) v /\
  val_wf (ArrayTV stv (Fixed cap)) v /\ val_wf (ArrayTV dtv (Fixed cap)) v /\
  val_in_memory (ArrayTV stv (Fixed cap)) v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size (ArrayTV stv (Fixed cap)) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (ArrayTV dtv (Fixed cap)) <= s.vs_alloca_next /\
  w2n sw + type_memory_size (ArrayTV stv (Fixed cap)) < dimword(:256) /\
  w2n dw + type_memory_size (ArrayTV dtv (Fixed cap)) < dimword(:256) /\
  (w2n sw + type_memory_size (ArrayTV stv (Fixed cap)) <= w2n dw \/
    w2n dw + type_memory_size (ArrayTV dtv (Fixed cap)) <= w2n sw) /\
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
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)) ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory (ArrayTV dtv (Fixed cap)) v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size (ArrayTV dtv (Fixed cap)) <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_rank ce.ce_struct_fields dt < rank` by
    gvs[Once type_rank_def] >>
  `type_memory_bytes ce st = type_memory_size stv /\
   type_memory_bytes ce dt = type_memory_size dtv` by
    (conj_tac >> irule typed_copy_memory_size >>
     qexists `tenv` >> simp[] >> metis_tac[]) >>
  mp_tac (Q.INST [`st` |-> `st`, `dt` |-> `dt`,
    `stv` |-> `stv`, `dtv` |-> `dtv`] typed_array_child_rank_path_mem) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  Cases_on `type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt`
  >- (pop_assum strip_assume_tac >>
      drule_all typed_store_sarray_bulk_path_mem >> simp[]) >>
  drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)
    normalize_sarray_semantic_path_mem >>
  disch_then (drule_at (Pat `evaluate_type _ st = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dt = _`)) >>
  disch_then (drule_at (Pat `val_in_memory (ArrayTV _ _) _ _ _`)) >>
  disch_then (qspecl_then [`fn`, `ctx`] mp_tac) >>
  disch_then (qspec_then `w2n dw` mp_tac) >>
  simp[] >>
  (impl_tac >-
    ((conj_tac >- (qpat_x_assum `~(_ /\ ~is_abi_dynamic _ _)` mp_tac >> simp[])) >>
     (conj_tac >- metis_tac[]) >>
     qpat_x_assum `!dty sty dtv stv v dst src sa sb s dw sw. _` kall_tac >>
     qpat_x_assum `!cv sp dp sc ec u sw dw. _` mp_tac >> simp[ADD_COMM])) >>
  strip_tac >> qexistsl [`t`, `g`] >> gvs[] >> first_assum ACCEPT_TAC
QED

Theorem typed_store_dynarray_slow_entry_path_mem[local]:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_rank ce.ce_struct_fields (ArrayT dt (Dynamic cap)) = rank /\
  type_widens_to tenv st dt /\
  evaluate_type tenv st = SOME stv /\ evaluate_type tenv dt = SOME dtv /\
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  scap <= cap /\ cap < dimword(:256) /\
  value_has_type (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) <= s.vs_alloca_next /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword(:256) /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) < dimword(:256) /\
  (w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw \/
    w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) <= w2n sw) /\
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
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)) ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size (ArrayTV dtv (Dynamic cap)) <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_rank ce.ce_struct_fields dt < rank` by
    gvs[Once type_rank_def] >>
  `type_memory_bytes ce st = type_memory_size stv /\
   type_memory_bytes ce dt = type_memory_size dtv` by
    (conj_tac >> irule typed_copy_memory_size >>
     qexists `tenv` >> simp[] >> metis_tac[]) >>
  mp_tac (Q.INST [`st` |-> `st`, `dt` |-> `dt`,
    `stv` |-> `stv`, `dtv` |-> `dtv`] typed_array_child_rank_path_mem) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  drule_at (Pat `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _`)
    normalize_dynarray_semantic_path_mem >>
  disch_then (drule_at (Pat `val_in_memory (ArrayTV _ _) _ _ _`)) >>
  disch_then (qspecl_then [`fn`, `dtv`, `ctx`, `w2n dw`] mp_tac) >>
  simp[] >>
  (impl_tac >-
    ((conj_tac >- (qpat_x_assum `~(_ /\ dt = st)` mp_tac >> simp[])) >>
     (conj_tac >- metis_tac[]) >>
     qpat_x_assum `!dty sty dtv stv v dst src sa sb s dw sw. _` kall_tac >>
     qpat_x_assum `!cv sp dp sc ec u sw dw. _` mp_tac >> simp[ADD_COMM])) >>
  strip_tac >> qexistsl [`t`, `g`] >> gvs[] >> first_assum ACCEPT_TAC
QED

Theorem typed_store_array_entry_path_mem:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_rank ce.ce_struct_fields (ArrayT elem bd) = rank /\
  type_widens_to tenv sty (ArrayT elem bd) /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv (ArrayT elem bd) = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  compile_store_memory_typed ce dst (ArrayT elem bd) src sty sa = ((),sb) /\
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
  drule_all typed_array_entry_metadata >>
  disch_then (qx_choose_then `se` (qx_choose_then `sbd`
    (qx_choose_then `sev` (qx_choose_then `dev` strip_assume_tac)))) >>
  qpat_x_assum `sty = _` SUBST_ALL_TAC >>
  qpat_x_assum `stv = _` SUBST_ALL_TAC >>
  qpat_x_assum `dtv = _` SUBST_ALL_TAC >>
  qpat_x_assum `sbd = _` SUBST_ALL_TAC >>
  qpat_x_assum `bd = _` SUBST_ALL_TAC
  >~ [`val_in_memory (ArrayTV _ (Fixed cap)) _ _ _`]
  >- (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
      simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def] >>
      strip_tac >>
      `0 < cap /\ 0 < type_memory_size dev` by
        (qpat_x_assum `evaluate_type _ (ArrayT elem _) = _` mp_tac >>
         simp[evaluate_type_def, type_memory_size_slots, AllCaseEqs()]) >>
      `cap < dimword(:256)` by fs[] >>
      drule_all typed_store_sarray_entry_path_mem >> simp[]) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def] >>
  disch_tac >>
  `?vs. v = ArrayV (DynArrayV vs)` by
    (qpat_x_assum `value_has_type (ArrayTV _ (Dynamic _)) v` mp_tac >>
     Cases_on `v` >> simp[value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >> simp[value_has_type_def]) >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  `m < dimword(:256)` by fs[] >>
  Cases_on `type_memory_bytes ce elem = type_memory_bytes ce se /\ elem = se`
  >- (pop_assum strip_assume_tac >>
      qpat_x_assum `!dty sty dtv stv v dst src sa sb s dw sw. _` kall_tac >>
      qpat_x_assum `elem = _` SUBST_ALL_TAC >>
      `sev = dev` by fs[] >> qpat_x_assum `sev = _` SUBST_ALL_TAC >>
      `LENGTH vs <= n /\ LENGTH vs <= m /\
       val_wf (ArrayTV dev (Dynamic (LENGTH vs))) (ArrayV (DynArrayV vs))` by
        fs[value_has_type_def, typed_copy_dynarray_wf] >>
      `mload (w2n sw) s = n2w (LENGTH vs)` by
        fs[val_in_memory_def, GSYM mem_word_at_eq_mload] >>
      `type_memory_bytes ce se = type_memory_size dev` by
        (irule typed_copy_memory_size >> qexists `tenv` >> simp[] >> metis_tac[]) >>
      `32 + LENGTH vs * type_memory_size dev <= type_memory_size (ArrayTV dev (Dynamic n)) /\
       LENGTH vs * type_memory_size dev < dimword(:256) /\
       w2n sw + 32 < dimword(:256) /\ w2n dw + 32 < dimword(:256)` by
        (fs[type_memory_size_def, Excl "LE_MULT_RCANCEL"] >>
         `LENGTH vs * type_memory_size dev <= n * type_memory_size dev` by simp[] >>
         decide_tac) >>
      `!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
      drule_all typed_store_dynarray_equal_path_mem >> simp[]) >>
  drule_all typed_store_dynarray_slow_entry_path_mem >> simp[]
QED
