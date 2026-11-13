(* Same-endpoint continuation and frame for direct typed place stores. *)
Theory bodyMemPlaceDirectStore
Ancestors
  typedStoreEndpoint typedStoreAllocationFrame context compileEnv venomState
  memContinuation valueEncodingDefs vyperTypeSystem exprLoweringProps
  typedCopyAgreement memoryLocalRhsProps bodyCopyMemory typedBytesArrayMem
  exprSimBufferStore rich_list

Theorem place_direct_typed_store_cont:
  ~is_word_type dty /\
  (is_bytestring_type dty \/ dty <> sty /\ ~tuple_memory_layout_eq dty sty) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  compile_store_memory ce src dst dty sty sa = ((),sb) /\
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
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) /\
  alloca_inv s /\ alloca_room ctx fn s ==>
  ?t. mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_inv t /\ alloca_room ctx fn t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_store_memory_typed ce dst dty src sty sa = ((),sb)` by
    (Cases_on `is_bytestring_type dty`
     >- (`is_bytestring_type sty` by
           (gvs[type_widens_to_def] >> metis_tac[arg_type_fits_bytestring_source]) >>
         gvs[compile_store_memory_def, compile_store_memory_typed_bytes]) >>
     gvs[compile_store_memory_def]) >>
  drule_all typed_store_mem_cont >>
  disch_then (qspec_then `ctx`
    (qx_choose_then `t` (map_every assume_tac o CONJUNCTS))) >>
  drule typed_store_frame_allocations >> strip_tac >>
  `alloca_inv t /\ alloca_room ctx fn t` by
    (irule typed_store_frame_resources >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `t` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!p k. _ ==> mem_bytes_at _ _ _ = _` irule >> decide_tac
QED

Theorem place_direct_bulk_copy_cont:
  compile_copy_memory dst src (type_memory_size tv) sa = ((),sb) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= type_memory_size tv /\
  type_memory_size tv < dimword(:256) /\
  w2n sw + type_memory_size tv <= s.vs_alloca_next /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  alloca_history fn s /\ alloca_inv s /\ alloca_room ctx fn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory tv v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size tv <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_inv t /\ alloca_room ctx fn t /\ alloca_history fn t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all buffer_copy_memory_encoding >> strip_tac >>
  drule buffer_copy_memory_shape >> strip_tac >>
  drule copy_memory_body_code >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all compile_copy_memory_body_mem_ok >> simp[]) >>
  `mem_cont_sim ctx fn s (q with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule typed_bytes_child_seq_cont >> fs[same_blocks_def, IS_PREFIX_APPEND] >>
     qexists_tac `sa` >> simp[IS_PREFIX_APPEND]) >>
  `alloca_history fn (q with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (drule_all copy_memory_body_history >> simp[]) >>
  `(q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s` by
    (gvs[venom_state_component_equality]) >>
  `alloca_inv (q with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   alloca_room ctx fn (q with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule typed_store_frame_resources >> goal_assum (drule_at Any) >>
     simp[] >> qexistsl_tac [`sa.cs_current_bb`, `LENGTH sa.cs_current_insts`,
       `s.vs_prev_bb`] >> gvs[venom_state_component_equality]) >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qpat_x_assum `(q with vs_memory := _) = s` mp_tac >>
  simp[venom_state_component_equality, lookup_var_def, same_blocks_def] >>
  rpt strip_tac >> gvs[same_blocks_def]
QED
