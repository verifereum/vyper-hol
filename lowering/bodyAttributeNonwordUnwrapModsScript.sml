(* Specialize the reached non-word unwrap endpoint to a linked Attribute.
   The underlying physical endpoint is shared with conditional arms; this
   wrapper exposes the Attribute-shaped precondition and keeps the selected
   non-word buffer and allocation frontier in the result. *)
Theory bodyAttributeNonwordUnwrapMods
Ancestors
  bodyIfExpArmUnwrapMods bodyAttributePreMods

Theorem attribute_nonword_unwrap_endpoint_mods:
  compile_expr ce ty (Attribute ann obj fld) sa = (vv,sm) /\
  unwrap_value ce vv k = (op,sb) /\
  sm.cs_next_var <= k.cs_next_var /\
  sm.cs_next_id <= k.cs_next_id /\
  fn_has_code k sb func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  expr_body_pre_mods mods ce cx env (Attribute ann obj fld) es /\
  ~is_word_type ann /\
  eval_expr cx (Attribute ann obj fld) (es with gas_obs := gs) = (INL tv,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx (Attribute ann obj fld) es sa k s0 ee tv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce (Attribute ann obj fld))
    (lowered_value_type ce (Attribute ann obj fld)) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce (Attribute ann obj fld)) tv vv ee G tn s /\
  (!tag x. vv = StackValue tag x ==> ptr_buf_ok ce (Attribute ann obj fld) x G s) /\
  (!tag p. vv = LocatedValue tag p /\
    p.ptr_location = LocMemory ==> ptr_buf_ok ce (Attribute ann obj fld) p.ptr_operand G s) /\
  (ce.ce_is_ctor /\
    vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx)
               (post_value_type ce (Attribute ann obj fld)) = SOME rt /\
             eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  ~s.vs_halted /\
  s.vs_current_bb = k.cs_current_bb /\
  s.vs_inst_idx = LENGTH k.cs_current_insts /\
  alloca_history func s ==>
  ?v z Gf tf pt rt w.
    read_result cx tv ee = (INL v,ee) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
          (OK z,Gf,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func ce cx (Attribute ann obj fld) es sa sb s0 ee v op z /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z) /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tf /\
    ptr_val_ok cx (post_value_type ce (Attribute ann obj fld)) v op Gf tf z /\
    ptr_buf_ok ce (Attribute ann obj fld) op Gf z /\
    expr_store_bound cx (post_value_type ce (Attribute ann obj fld)) v op z /\
    ~z.vs_halted /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    ~is_word_type (post_value_type ce (Attribute ann obj fld)) /\
    evaluate_type (get_tenv cx) (post_value_type ce (Attribute ann obj fld)) = SOME pt /\
    evaluate_type (get_tenv cx) (lowered_value_type ce (Attribute ann obj fld)) = SOME rt /\
    type_memory_bytes ce (lowered_value_type ce (Attribute ann obj fld)) =
      type_memory_size rt /\
    value_has_type pt v /\
    value_has_type rt v /\
    val_wf rt v /\
    eval_operand op z = SOME w /\
    op_taint tf op = {} /\
    (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n w) mem) /\
    (type_memory_size rt = 0 \/
      w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    w2n w + type_memory_size rt < dimword (:256) /\
    (0 < type_memory_size rt ==>
      ?r. op = Var r /\ not_fresh_at sb r /\
          ptr_covers Gf tf r z (type_memory_size rt)) /\
    (!x. not_fresh_at k x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
      FLOOKUP z.vs_allocas aid = SOME b) /\
    (!x cap. not_fresh_at k x /\
      ptr_covers G tn x s cap ==> ptr_covers Gf tf x z cap) /\
    wb_frame ce ee ee k s z /\
    ghost_kept_at lo ce ee k G tn s Gf tf /\
    ((sb = k /\ z = s /\ Gf = G /\ tf = tn /\ op = vv_operand vv /\
      vv_at ce cx (post_value_type ce (Attribute ann obj fld)) sa k ee tv
        (LocatedValue (post_value_type ce (Attribute ann obj fld))
          (mk_ptr op LocMemory)) s /\
      (!id path. tv = PlaceR (MemoryPlace id path) ==>
        vv_place_ptr ce cx ee s tv
          (LocatedValue (post_value_type ce (Attribute ann obj fld))
            (mk_ptr op LocMemory))) ) \/
     (k.cs_next_id < sb.cs_next_id /\
      post_value_type ce (Attribute ann obj fld) =
        lowered_value_type ce (Attribute ann obj fld) /\
      FLOOKUP z.vs_allocas k.cs_next_id =
        SOME (w2n w,type_memory_size rt) /\
      lo <= w2n w /\
      (!id path. tv <> PlaceR (MemoryPlace id path)) /\
      (!aid b len. aid < k.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) (type_memory_size rt) b len)))
Proof
  strip_tac >>
  `~is_word_type (expr_type (Attribute ann obj fld))` by
    simp[vyperASTTheory.expr_type_def] >>
  drule_all (Q.INST [`e` |-> `Attribute ann obj fld`]
    ifexp_arm_nonword_unwrap_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`v`,`z`,`Gf`,`tf`,`pt`,`rt`,`w`]
      (map_every assume_tac o CONJUNCTS))) >>
  qexistsl [`v`,`z`,`Gf`,`tf`,`pt`,`rt`,`w`] >> asm_rewrite_tac[]
QED
