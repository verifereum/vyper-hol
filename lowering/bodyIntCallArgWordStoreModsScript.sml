Theory bodyIntCallArgWordStoreMods
Ancestors
  logStoreDataOriginPtr bodyFullIntCallArgs[qualified] allocaHistory
  emitHelperProps venomState typedMemoryCopy exprSimProps
  valueTypingMemoryProps finite_map

(* Only the post-unwrap store runs here. The copy frame keeps memory outside
   the single written word; the path and all postconditions share an endpoint. *)
Theorem intcall_arg_word_store_mods:
  compile_store_memory cenv src_op (Var dst) dty sty sa = ((),sb) /\
  is_word_type dty /\ evaluate_type tenv dty = SOME dtv /\ value_has_type dtv v /\
  eval_operand src_op s = SOME (typed_val_to_w256 dtv v) /\
  op_taint tn src_op = {} /\ lookup_var dst s = SOME dw /\
  w2n dw + 32 < dimword (:256) /\ w2n dw + 32 <= s.vs_alloca_next /\
  ptr_covers G tn dst s 32 /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    type_memory_size dtv = 32 /\ val_wf dtv v /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) 32 s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func t /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + 32) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!p. FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_store_memory_word_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule_all_then assume_tac word_tv_memory_size >>
  drule_then assume_tac value_has_type_memory_wf >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  simp[] >>
  `emit_inst MSTORE [Var dst;src_op] [] sa = ((),sb)` by
    fs[contextTheory.compile_store_memory_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def] >>
  drule_then strip_assume_tac emit_inst_extends >>
  drule_all_then assume_tac bodyFullIntCallArgsTheory.intcall_args_word_store_history >>
  irule alloca_history_frame >>
  goal_assum (drule_at Any) >>
  simp[mstore_def, write_memory_with_expansion_def]
QED
