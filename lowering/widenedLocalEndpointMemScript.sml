(* Shared physical endpoint of a widened assignment/declaration copy. *)
Theory widenedLocalEndpointMem
Ancestors
  widenedAssignValueParts stagedLocalRegionCopyMem bodyMemoryDefs
  exprLoweringProps compileEnv venomState words arithmetic stmtLowering context

Theorem widened_local_copy_endpoint_mem:
  compile_assign_value ce dst LocMemory src F (SOME LocMemory)
    dty sty info bytes sa = ((),sb) /\ fn_has_code sa sb fn /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
  stmt_state_rel ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ alloca_history fn s /\ return_buf_frame d ce sa s /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  type_memory_bytes ce sty = type_memory_size stv /\
  type_memory_size stv < dimword(:256) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  ((?aid. FLOOKUP s.vs_allocas aid = SOME (w2n dw,sz) /\ aid < sa.cs_next_id) \/
   (?name. local_region ce es.scopes s name (w2n dw) sz)) /\
  type_memory_size dtv <= sz /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u t g.
    gas_path_mem ctx fn s 0 (OK u) /\ gas_path_mem ctx fn s g (OK t) /\
    stmt_state_rel ctx fn ce cx es u /\ alloca_history fn u /\ alloca_history fn t /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ return_buf_frame d ce sb t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry /\ FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!op w. eval_operand op s = SOME w /\
      (!x. op = Var x ==> not_fresh_at sa x) ==> eval_operand op u = SOME w) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      lookup_var x t = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH t.vs_memory /\
    (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
      vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
      vs_prev_bb := u.vs_prev_bb|>) = u /\
    (!a k. a+k <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k u.vs_memory)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all assign_memory_typed_layout_code >> strip_tac >>
  `compile_store_memory ce buf.buf_operand dst dty sty sn = ((),sb)` by
    simp[compile_store_memory_def] >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (mp_tac (Q.SPECL [`type_memory_bytes ce sty`, `sa`] ci_mono_compile_alloc_buffer) >>
     mp_tac (Q.SPECL [`buf.buf_operand`, `src`, `type_memory_bytes ce sty`, `sm`]
       ci_mono_compile_copy_memory) >>
     mp_tac (Q.SPECL [`ce`, `buf.buf_operand`, `dst`, `dty`, `sty`, `sn`]
       ci_mono_compile_store_memory) >>
     asm_rewrite_tac[ci_mono_def] >> simp[]) >>
  `type_memory_bytes ce sty < dimword(:256) /\
   w2n sw + type_memory_bytes ce sty <= s.vs_alloca_next` by simp[] >>
  drule_all staged_region_typed_copy_path_mem >>
  disch_then (qx_choose_then `r` (qx_choose_then `u` (qx_choose_then `t`
    (qx_choose_then `tw` (qx_choose_then `g`
      (map_every assume_tac o CONJUNCTS)))))) >>
  suspend "frame"
QED

Resume widened_local_copy_endpoint_mem[frame]:
  markerLib.RESUME_TAC >>
  `return_buf_frame d ce sb t` by
    (irule return_buf_frame_frame >> metis_tac[]) >>
  `u.vs_allocas = t.vs_allocas` by
    (qpat_x_assum `(t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
       vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|>) = u` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexistsl_tac [`u`, `t`, `g`] >> asm_rewrite_tac[] >>
  metis_tac[]
QED

Finalise widened_local_copy_endpoint_mem
