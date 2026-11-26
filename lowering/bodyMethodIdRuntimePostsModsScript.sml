(* Lift the deterministic MethodId suffix posts to the linked frame. *)
Theory bodyMethodIdRuntimePostsMods
Ancestors
  bodyMemBiMethodIdEndpoint bodyFullPostsMods bodyFieldMemoryProps
  exprSimUnwrapProps exprSimVVFrame
  bodyPtrDefs loweringPosts exprLoweringProps compileEnv context
  venomState vyperAST vyperInterpreter vyperValue list finite_map words arithmetic

Theorem method_id_runtime_endpoint_posts_mods:
  !H ctx func cenv cx e es sa sm sb s0 es' v x s fixed op t r z G tn.
    expr_post H ctx func cenv cx e es sa sm s0 es' v x s /\
    expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
    value_has_type (BaseTV bty) v /\
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    expr_store_bound cx (expr_type e) v x s /\
    run_inst_seq (emitted_insts sm sb) s = OK t /\
    builtin_result cx es'.accounts
      (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)))
      MethodId [expr_type e] [v] = INL r /\
    vv_post H ctx func cenv cx
      (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e])
      es sa sb s0 es' (Value r)
      (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
       LocatedValue (BaseT (BytesT (Dynamic 4))) (mk_ptr op LocMemory)) t /\
    vv_store_bound cx
      (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)))
      (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)))
      es' (Value r)
      (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
       LocatedValue (BaseT (BytesT (Dynamic 4))) (mk_ptr op LocMemory)) t /\
    z = t with vs_inst_idx := LENGTH sb.cs_current_insts /\
    immutable_frame_mods func cenv cx es' z /\
    vv_post H ctx func cenv cx
      (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e])
      es sa sb s0 es' (Value r)
      (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
       LocatedValue (BaseT (BytesT (Dynamic 4))) (mk_ptr op LocMemory)) z /\
    vv_store_bound cx
      (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)))
      (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)))
      es' (Value r)
      (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
       LocatedValue (BaseT (BytesT (Dynamic 4))) (mk_ptr op LocMemory)) z /\
    (if fixed then
       ptr_vv_ok cx (BaseT (BytesT (Fixed 4))) (Value r)
         (StackValue (BaseT (BytesT (Fixed 4))) op) es' G tn z
     else
       ptr_vv_ok cx (BaseT (BytesT (Dynamic 4))) (Value r)
         (LocatedValue (BaseT (BytesT (Dynamic 4))) (mk_ptr op LocMemory)) es' G tn z /\
       ptr_buf_ok cenv
         (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [e]) op G z) ==>
    expr_post_mods H ctx func cenv cx
      (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e])
      es sa sb s0 es' r op z /\
    vv_post_mods H ctx func cenv cx
      (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e])
      es sa sb s0 es' (Value r)
      (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
       LocatedValue (BaseT (BytesT (Dynamic 4))) (mk_ptr op LocMemory)) z /\
    vv_store_bound cx
      (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)))
      (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)))
      es' (Value r)
      (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
       LocatedValue (BaseT (BytesT (Dynamic 4))) (mk_ptr op LocMemory)) z /\
    (if fixed then
       ptr_vv_ok cx (BaseT (BytesT (Fixed 4))) (Value r)
         (StackValue (BaseT (BytesT (Fixed 4))) op) es' G tn z
     else
       ptr_vv_ok cx (BaseT (BytesT (Dynamic 4))) (Value r)
         (LocatedValue (BaseT (BytesT (Dynamic 4))) (mk_ptr op LocMemory)) es' G tn z /\
       ptr_buf_ok cenv
         (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [e]) op G z)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `z = _` SUBST_ALL_TAC >>
  `expr_post H ctx func cenv cx
      (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e])
      es sa sb s0 es' r op
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    ((Cases_on `fixed`
     >- (gvs[] >>
         last_assum (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.expr_post_of_vv_post_stack) >>
         simp[bodyFieldMemoryPropsTheory.body_field_expr_post_inst_idx])
     >> gvs[] >>
         `expr_post H ctx func cenv cx
            (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [e])
            es sa sb s0 es' r (mk_ptr op LocMemory).ptr_operand t` by
           (irule exprSimUnwrapPropsTheory.expr_post_of_vv_post_memory >>
            conj_tac >- simp[mk_ptr_def] >>
            qexists_tac `BaseT (BytesT (Dynamic 4))` >>
            conj_tac >- (simp[is_word_type_def]) >>
            (first_assum (ACCEPT_TAC o REWRITE_RULE [GSYM mk_ptr_def]))) >>
         simp[mk_ptr_def] >> (gvs[bodyFieldMemoryPropsTheory.body_field_expr_post_inst_idx, mk_ptr_def, is_word_type_def, exprSimUnwrapPropsTheory.expr_post_of_vv_post_memory])))
  >> `expr_post_mods H ctx func cenv cx
        (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e])
        es sa sb s0 es' r op (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
       (pure_rewrite_tac[expr_post_mods_def] >>
        conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC) >>
     qhdtm_assum `vv_post`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [vv_post_def]) >>
     qhdtm_assum `vv_post`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [vv_post_def]) >>
     `vv_post_mods H ctx func cenv cx
        (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e])
        es sa sb s0 es' (Value r)
        (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
         LocatedValue (BaseT (BytesT (Dynamic 4))) (mk_ptr op LocMemory))
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
       (Cases_on `fixed` >>
        pure_rewrite_tac[vv_post_mods_def] >>
        gvs[post_value_type_def, expr_type_def, vv_holds_mods_def,
            vv_place_ptr_mods_def, mk_ptr_def] >>
        rpt (conj_tac >- first_assum ACCEPT_TAC) >>
        simp[] >> first_assum ACCEPT_TAC) >>
     metis_tac[]
QED
