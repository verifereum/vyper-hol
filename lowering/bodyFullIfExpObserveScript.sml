(* The observation is about the actual successful materialization endpoint,
   not about an arbitrary tuple satisfying the semantic postconditions. *)
Theory bodyFullIfExpObserve
Ancestors
  exprSimIfExp vyperStorageFootprint
  typedMemoryCopy fragGasOriginPtr
  bodyPtrDefs loweringPosts fragGasSeqPtr

Definition ifexp_observed_unwrap_def:
  ifexp_observed_unwrap own obs DF lo explicit ctx func PG d cenv cx <=>
  !ty e sa vv sm sb op sc es ee s0 s tv rty G tn Gi ti st0.
    compile_expr cenv ty e sa = (vv,sm) /\
    sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
    unwrap_value cenv vv sb = (op,sc) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
      ~is_word_type (post_value_type cenv e) ==>
      type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
      type_memory_size rt < 2**64) /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
    (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
       ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
    vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
    (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op0 G s) /\
    (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand G s) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val,ee) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                  eval_operand (vv_operand vv) s = SOME w ==>
                  w2n w + type_memory_size rt <= lo /\
                  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                         val_in_memory rt val (w2n w) mem)) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
    ?v z G' tn'.
      obs ctx func sb sc s z /\
      read_result cx tv ee = (INL v,ee) /\
      (own ==> !ann p. vv = LocatedValue ann p /\ ~is_word_type ann /\
        (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
         p.ptr_location = LocCode) ==>
        vv_own cenv cx (post_value_type cenv e) sb sc ee (Value v)
          (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
         gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
           (s, G, tn) [] (OK z, G', tn') /\
         expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
         ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
      (~is_word_type (post_value_type cenv e) ==>
       vv_at cenv cx (post_value_type cenv e) sa sc ee tv
         (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
      (~is_word_type (post_value_type cenv e) ==>
       vv_at cenv cx (post_value_type cenv e) sa sm ee tv
         (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z \/
       vv_at cenv cx (post_value_type cenv e) sb sc ee tv
         (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
      expr_store_bound cx (post_value_type cenv e) v op z /\
      z.vs_current_bb = sc.cs_current_bb /\
      z.vs_inst_idx = LENGTH sc.cs_current_insts /\
      alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
      s0.vs_alloca_next <= z.vs_alloca_next /\
      ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' z) /\
      (~is_word_type (post_value_type cenv e) ==>
       !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
              eval_operand op z = SOME w ==>
              type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
      ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
      (!x. not_fresh_at sb x ==>
           lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
           op_taint tn' (Var x) = op_taint tn (Var x)) /\
      wb_frame cenv ee ee sb s z /\
      ghost_kept_at lo cenv ee sb G tn s G' tn'
End

Theorem ifexp_observed_unwrap_drop_own:
  ifexp_observed_unwrap T obs DF lo explicit ctx func PG d cenv cx ==>
  ifexp_observed_unwrap F obs DF lo explicit ctx func PG d cenv cx
Proof
  simp_tac bool_ss [ifexp_observed_unwrap_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> simp[] >>
  disch_then (qx_choosel_then [`v`,`z`,`G'`,`tn'`] strip_assume_tac) >>
  qexistsl [`v`,`z`,`G'`,`tn'`] >> simp[]
QED

Definition ifexp_observed_alloc_def:
  ifexp_observed_alloc obs ctx fn <=>
  !sa sb n buf s out u.
    compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb fn /\
    buf.buf_operand = Var out /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
    obs ctx fn sa sb s (u with vs_inst_idx := SUC s.vs_inst_idx)
End

(* Supply composition only for a compiled widening, not for arbitrary
   adjacent intervals. The layout equations remain available to the client. *)
Definition ifexp_observed_widening_def:
  ifexp_observed_widening obs ctx fn <=>
  !cenv t sty vv n buf src a b c d s u v w.
    compile_alloc_buffer n a = (buf,b) /\ n = type_memory_bytes cenv t /\
    unwrap_value cenv vv b = (src,c) /\
    (compile_store_bytestring src buf.buf_operand c = ((),d) \/
     compile_store_memory_typed cenv buf.buf_operand t src sty c = ((),d)) /\
    fn_has_code a d fn /\ fn_inst_ids_distinct fn /\
    obs ctx fn a b s u /\ obs ctx fn b c u v /\ obs ctx fn c d v w ==>
    obs ctx fn a d s w
End

Definition ifexp_observed_bytes_store_def:
  ifexp_observed_bytes_store obs <=>
  !lo explicit ctx fn PG sa sb src dst G tn s a b len n bb.
      compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
      not_fresh_at sa src /\ not_fresh_at sa dst /\
      lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
      n = 32 + 32 * ((len+31) DIV 32) /\
      len+31 < dimword(:256) /\ n < dimword(:256) /\
      mload (w2n a) s = n2w len /\
      ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
      (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
      allocas_from lo s /\ lo <= s.vs_alloca_next /\
      run_inst_seq_mem_ok (emitted_insts sa sb) s /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
      ?Gf tnf sf.
        (fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
         s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
         obs ctx fn sa sb s (sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
        (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
          (OK (sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),Gf,tnf)) /\
        run_inst_seq (emitted_insts sa sb) s = OK sf /\
        tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
        sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
        sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
        tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
        tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+n}) UNION
          {w2n b+i | i < n /\ w2n a+i IN tn.t_mem} /\
        (!p. not_fresh_at sa p ==>
          lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
          op_taint tnf (Var p) = op_taint tn (Var p))
End

Definition ifexp_observed_typed_store_def:
  ifexp_observed_typed_store obs <=>
  !cenv xd dty xs sty sa sb tenv stv dtv v s sw dw G tn lo ctx func explicit PG.
    compile_store_memory_typed cenv (Var xd) dty (Var xs) sty sa = ((),sb) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
         sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    not_fresh_at sa xs /\ not_fresh_at sa xd /\
    lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory stv v (w2n sw) mem) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
    (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= s.vs_alloca_next) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    ptr_covers G tn xs s (type_memory_size stv) /\
    ptr_covers G tn xd s (type_memory_size dtv) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t Gf tnf.
      obs ctx func sa sb s t /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
           (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
             val_in_memory dtv v (w2n dw) mem) /\
      (!p. not_fresh_at sa p ==>
         FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
End
