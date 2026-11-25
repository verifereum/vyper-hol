(* Cuts of the forced array snapshot. Each machine tuple is (cursor,state,ghost,taint).
   The caller tuple is (trace root,source state,cursor,state,ghost,taint).
   The array tuple is (expression,reached source state,raw result,saved value,element,bound,layout).
   The destination tuple is (operand name,address); its allocation id is the base cursor's next id. *)
Theory bodyCopiedArrayCutDefsMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyMemoryDefs bodyPtrDefs
  loweringPosts loweringStateRelDefs fragExec fragGasOriginPtr gasOutcomeFullMods
  gasShadow gasShadowState gasContext exprSimDefs exprLowering compileEnv
  vyperAST vyperInterpreter vyperState vyperContext vyperTypeSystem vyperStorageFootprint
  context ptrDiscipline venomState venomInst finite_map words

Definition copied_cursor_mods_def:
  copied_cursor_mods ctx fn c s <=>
    ~s.vs_halted /\ s.vs_current_bb = c.cs_current_bb /\
    s.vs_inst_idx = LENGTH c.cs_current_insts /\ alloca_history fn s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s)
End

Definition copied_snapshot_dest_mods_def:
  copied_snapshot_dest_mods fn ce lo mid sm (c,t,G,tn) (q,w) n <=>
    sm.cs_next_id < c.cs_next_id /\ not_fresh_at c q /\
    lookup_var q t = SOME w /\ ptr_covers G tn q t n /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,n) /\
    MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [q]) (fn_insts fn) /\
    lo <= w2n w /\ w2n w + n <= t.vs_alloca_next /\
    w2n w + n < dimword (:256) /\
    (!name b len. local_region ce mid.scopes t name b len ==>
       regions_disjoint (w2n w) n b len)
End

Definition copied_base_frame_mods_def:
  copied_base_frame_mods sm (s,G,tn) (t,Gu,tu) <=>
    s.vs_alloca_next <= t.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
End

Definition copied_array_type_mods_def:
  copied_array_type_mods ce cx (obj,mid,raw,saved,et,bd,atv) <=>
    expr_type obj = ArrayT et bd /\ post_value_type ce obj = ArrayT et bd /\
    lowered_value_type ce obj = ArrayT et bd /\ read_result cx raw mid = (INL saved,mid) /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv /\
    type_memory_bytes ce (ArrayT et bd) = type_memory_size atv /\
    type_memory_size atv < 2 ** 64 /\ value_has_type atv saved /\ val_wf atv saved
End

Definition copied_parent_frame_mods_def:
  copied_parent_frame_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) mid e (c,t,G,tn) <=>
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      stmt_state_rel H ctx fn ce cx es s0 /\
      stmt_state_rel H ctx fn ce cx mid t /\
      immutable_frame_mods fn ce cx mid t /\ storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at_mods (DF H) lo d ce cx mid G tn t) /\
    local_ptrs_reserved ce sa /\ local_ptrs_reserved ce c /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    return_buf_frame d ce c t /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    wb_frame ce es mid sa s0 t /\
    (~expr_has_effect e ==> pure_frame ce fn es sa s0 t)
End

Definition copied_alloc_cut_mods_def:
  copied_alloc_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (k,a,Ga,ta) (l,src,sc,cvv,bvv) (q,w) <=>
    copied_array_type_mods ce cx (obj,mid,raw,saved,et,bd,atv) /\
    vv_type bvv = ArrayT et bd /\
    cvv = LocatedValue (ArrayT et bd) (mk_ptr (Var q) LocMemory) /\
    unwrap_value ce bvv k = (src,l) /\
    compile_store_memory ce src (Var q) (ArrayT et bd) (ArrayT et bd) l = ((),sc) /\
    cs_extends sm k /\ cs_extends k l /\ cs_extends l sc /\
    fn_has_code k l fn /\ fn_has_code l sc fn /\ fn_inst_ids_distinct fn /\
    copied_cursor_mods ctx fn k a /\ allocas_from lo a /\ lo <= a.vs_alloca_next /\
    copied_snapshot_dest_mods fn ce lo mid sm (k,a,Ga,ta) (q,w) (type_memory_size atv) /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) (type_memory_size atv) b len) /\
    copied_base_frame_mods sm (s,G,tn) (a,Ga,ta) /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shctx,ctx,fn,PG)
      (s,G,tn) [] (OK a,Ga,ta)) /\
    copied_parent_frame_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
      (st0,es,sa,s0,G0,tn0) mid obj (k,a,Ga,ta) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       vv_post_mods H ctx fn ce cx obj es sa k s0 mid raw bvv a) /\
    ptr_vv_ok cx (post_value_type ce obj) raw bvv mid Ga ta a /\
    vv_store_bound cx (post_value_type ce obj) (lowered_value_type ce obj) mid raw bvv a /\
    (!x. vv_operand bvv = Var x ==> not_fresh_at k x) /\
    (!tag op. bvv = StackValue tag op ==> ptr_buf_ok ce obj op Ga a) /\
    (!tag p. bvv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
       ptr_buf_ok ce obj p.ptr_operand Ga a) /\
    (ce.ce_is_ctor /\ vv_location bvv = SOME LocCode ==>
       !sw. eval_operand (vv_operand bvv) a = SOME sw ==>
         w2n sw + type_memory_size atv <= lo /\
         (!m. mem_agree_outside ta.t_mem a.vs_memory m ==>
           val_in_memory atv saved (w2n sw) m))
End

Definition copied_store_cut_mods_def:
  copied_store_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (l,t,Gl,tl) (src,sw,sc,cvv) (q,w) <=>
    copied_array_type_mods ce cx (obj,mid,raw,saved,et,bd,atv) /\
    cvv = LocatedValue (ArrayT et bd) (mk_ptr (Var q) LocMemory) /\
    compile_store_memory ce src (Var q) (ArrayT et bd) (ArrayT et bd) l = ((),sc) /\
    cs_extends sm l /\ cs_extends l sc /\ fn_has_code l sc fn /\
    copied_cursor_mods ctx fn l t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    copied_snapshot_dest_mods fn ce lo mid sm (l,t,Gl,tl) (q,w) (type_memory_size atv) /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) (type_memory_size atv) b len) /\
    copied_base_frame_mods sm (s,G,tn) (t,Gl,tl) /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shctx,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gl,tl)) /\
    copied_parent_frame_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
      (st0,es,sa,s0,G0,tn0) mid obj (l,t,Gl,tl) /\
    (!x. src = Var x ==> not_fresh_at l x) /\ eval_operand src t = SOME sw /\
    ptr_mem_ok cx (ArrayT et bd) saved src Gl tl t /\
    (type_memory_size atv <> 0 ==>
       (?x. src = Var x /\ ptr_covers Gl tl x t (type_memory_size atv)) /\
       w2n sw + type_memory_size atv <= t.vs_alloca_next /\
       t.vs_alloca_next < dimword (:256))
End

Definition copied_saved_cut_mods_def:
  copied_saved_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (sc,u,Gc,tc) cvv (q,w) <=>
    copied_array_type_mods ce cx (obj,mid,raw,saved,et,bd,atv) /\
    cvv = LocatedValue (ArrayT et bd) (mk_ptr (Var q) LocMemory) /\
    cs_extends sa sm /\ cs_extends sm sc /\ mid.gas_obs = [] /\
    copied_cursor_mods ctx fn sc u /\ allocas_from lo u /\
    copied_snapshot_dest_mods fn ce lo mid sm (sc,u,Gc,tc) (q,w) (type_memory_size atv) /\
    vv_own ce cx (ArrayT et bd) sm sc mid (Value saved) cvv u /\
    (!m. mem_agree_outside tc.t_mem u.vs_memory m ==> val_in_memory atv saved (w2n w) m) /\
    copied_base_frame_mods sm (s,G,tn) (u,Gc,tc) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,fn,PG)
        (s,G,tn) [] (OK u,Gc,tc)) /\
    copied_parent_frame_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
      (st0,es,sa,s0,G0,tn0) mid obj (sc,u,Gc,tc)
End

Definition copied_select_cut_mods_def:
  copied_select_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (ann,idx,fin,key,iop,dst,vv) (sm,sc,cvv) (si,z,Gi,ti) sb (q,w) <=>
    copied_array_type_mods ce cx (obj,mid,raw,saved,et,bd,atv) /\
    cvv = LocatedValue (ArrayT et bd) (mk_ptr (Var q) LocMemory) /\
    vv = LocatedValue ann (mk_ptr dst LocMemory) /\
    compile_array_subscript (Var q) iop
      (case bd of Fixed _ => F | Dynamic _ => T)
      (case bd of Fixed n => n | Dynamic _ => 0)
      (word_scale LocMemory) (elem_size_in_location ce LocMemory et)
      (is_signed_type (expr_type idx))
      (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocMemory) si = (dst,sb) /\
    cs_extends sa sm /\ cs_extends sm sc /\ cs_extends sc si /\ cs_extends si sb /\
    fn_has_code si sb fn /\ fn_inst_ids_distinct fn /\ local_ptrs_reserved ce sa /\
    copied_cursor_mods ctx fn si z /\ allocas_from lo z /\ fin.gas_obs = [] /\
    copied_snapshot_dest_mods fn ce lo fin sm (si,z,Gi,ti) (q,w) (type_memory_size atv) /\
    vv_own ce cx (ArrayT et bd) sm sc fin (Value saved) cvv z /\
    (!m. mem_agree_outside ti.t_mem z.vs_memory m ==> val_in_memory atv saved (w2n w) m) /\
    ptr_val_ok cx (post_value_type ce idx) key iop Gi ti z /\
    copied_parent_frame_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
      (st0,es,sa,s0,G0,tn0) fin (Subscript ann obj idx) (si,z,Gi,ti)
End

Definition copied_located_post_mods_def:
  copied_located_post_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx (ann,obj,idx)
    (es,sa,s0,G0,tn0) (sb,vv) H res ee G tn t <=>
    ?tv dst. res = INL tv /\ vv = LocatedValue ann (mk_ptr dst LocMemory) /\
      vv_post_mods H ctx fn ce cx (Subscript ann obj idx) es sa sb s0 ee tv vv t /\
      vv_store_bound cx (post_value_type ce (Subscript ann obj idx))
        (lowered_value_type ce (Subscript ann obj idx)) ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history fn t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn t /\
      ptr_vv_ok cx (post_value_type ce (Subscript ann obj idx)) tv vv ee G tn t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type ce (Subscript ann obj idx)) /\
           ~is_bytestring_type (post_value_type ce (Subscript ann obj idx)) ==>
        vv_own ce cx (post_value_type ce (Subscript ann obj idx)) sa sb ee tv vv t) /\
      ptr_buf_ok ce (Subscript ann obj idx) dst G t /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn
End

Definition copied_vv_exit_mods_def:
  copied_vv_exit_mods cx ctx H res ee gt r <=>
    expr_exit res r /\ halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)
End

Definition copied_located_vv_mods_def:
  copied_located_vv_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx ty (ann,obj,idx) es <=>
    !st0 sa sb sha shb vv s0 G0 tn0.
      compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
      compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (Subscript ann obj idx)) sha = (vv,shb) /\
      gas_shadow_state sa sha /\ gas_shadow_state sb shb /\
      gas_shadow_context ctx shctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function fn shfn /\ MEM fn ctx.ctx_functions /\ MEM shfn shctx.ctx_functions /\
      fn_has_code sa sb fn /\ fn_has_code sha shb shfn /\ fn_inst_ids_distinct fn /\
      local_ptrs_reserved ce sa /\ (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
      (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_vv_res_ok es /\
      return_buf_frame d ce sa s0 /\ alloca_history fn s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!f inst s. frag_reachable ctx fn s0 f inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx fn ce cx es s0 /\ immutable_frame_mods fn ce cx es s0 /\
        storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G0 tn0 s0) /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shctx,ctx,fn,PG)
        ce.ce_modules cx st0 (eval_expr cx (Subscript ann obj idx)) (es,s0,G0,tn0)
        (copied_located_post_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
          (ann,obj,idx) (es,sa,s0,G0,tn0) (sb,vv))
        (copied_vv_exit_mods cx ctx)
End

Theorem copied_store_cut_copy_inputs_mods:
  copied_store_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    caller (obj,mid,raw,saved,et,bd,atv) base_run (l,t,Gl,tl) (src,sw,sc,cvv) (q,w) ==>
  compile_store_memory ce src (Var q) (ArrayT et bd) (ArrayT et bd) l = ((),sc) /\
  ~is_word_type (ArrayT et bd) /\ ~is_bytestring_type (ArrayT et bd) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv /\
  val_wf atv saved /\ type_memory_bytes ce (ArrayT et bd) = type_memory_size atv /\
  (!x. src = Var x ==> not_fresh_at l x) /\ not_fresh_at l q /\
  eval_operand src t = SOME sw /\ lookup_var q t = SOME w /\
  ptr_mem_ok cx (ArrayT et bd) saved src Gl tl t /\
  (type_memory_size atv <> 0 ==>
    (?x. src = Var x /\ ptr_covers Gl tl x t (type_memory_size atv)) /\
    ptr_covers Gl tl q t (type_memory_size atv) /\
    w2n sw + type_memory_size atv <= t.vs_alloca_next /\
    w2n w + type_memory_size atv <= t.vs_alloca_next /\
    t.vs_alloca_next < dimword (:256)) /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  fn_has_code l sc fn /\ ~t.vs_halted /\
  t.vs_current_bb = l.cs_current_bb /\ t.vs_inst_idx = LENGTH l.cs_current_insts
Proof
  PairCases_on `caller` >> PairCases_on `base_run` >>
  simp[copied_store_cut_mods_def, copied_array_type_mods_def, copied_cursor_mods_def,
       copied_snapshot_dest_mods_def, is_word_type_def, is_bytestring_type_def]
QED

Theorem copied_saved_cut_index_entry_mods:
  copied_saved_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (sc,u,Gc,tc) cvv (q,w) ==>
  mid.gas_obs = [] /\ local_ptrs_reserved ce sc /\ return_buf_frame d ce sc u /\
  ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  alloca_history fn u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  not_fresh_at sc q /\ lookup_var q u = SOME w /\ ptr_covers Gc tc q u (type_memory_size atv) /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size atv) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx fn ce cx mid u /\ immutable_frame_mods fn ce cx mid u /\
    storage_well_formed_on cx mid (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx mid Gc tc u)
Proof
  simp[copied_saved_cut_mods_def, copied_cursor_mods_def,
       copied_snapshot_dest_mods_def, copied_parent_frame_mods_def] >>
  strip_tac >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED
