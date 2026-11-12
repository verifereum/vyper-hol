(* The arm step of a ternary whose arm is an internal call the lowering
   types at the callee's return type, a widening of the ternary's type,
   with a different layout: allocate a buffer of the ternary's type, unwrap
   the arm's value at its lowered type, copy it in with
   compile_store_memory_typed, as one joint path with no GAS site, and give
   the ternary's posts at the arm's end at one horizon H.  Venom steps
   carry no gas; the widening rules out the dynarray ASSERT and the acyclic
   struct metadata the INVALID.  The shared joint unwrap_value, alloc and
   typed-copy lemmas are premises until they land. *)
Theory bodyFullIfExpWidenCall
Ancestors
  vyperStorageFootprint bodySimFull fragGasOriginPtr exprSimIfExp exprSimDefs exprSimMemDefs
  bodyPtrDefs loweringPosts exprLowering exprLoweringProps fragExec
  emitHelper compileEnv allocaHistory stmtSimDefs vyperAST
  vyperInterpreter vyperState venomState fragGasSeqPtr fragGasEmitCtrl
  instMemFrontier memSafeRun ptrSafeRun ptrDiscipline venomInst
  venomExecSemantics loweringStateRelDefs finite_map typedCopyDomain vyperTypeSystem
  context memoryLayoutSource memoryLayoutDefs typedMemoryCopy

Theorem ifexp_widened_call_store_normalize:
  compile_ifexp_arm cenv t sty vv sm = (op,sb) /\
  ~is_word_type t /\ ~same_memory_layout cenv sty t /\
  type_widens_to tenv sty t ==>
  compile_store_memory cenv src dst t sty =
  compile_store_memory_typed cenv dst t src sty
Proof
  strip_tac >>
  `(!u. punnable cenv u u) /\ (!us. punnable_list cenv us us)` by
    (ho_match_mp_tac (legacyInduction.mutual_ind_from_ops type_induction) >>
     simp[punnable_def]) >>
  `sty <> t` by (strip_tac >> gvs[same_memory_layout_def]) >>
  `(!u v. memory_layout_key v = memory_layout_key u ==> punnable cenv v u) /\
   (!us vs. MAP memory_layout_key vs = MAP memory_layout_key us ==>
      punnable_list cenv vs us)` by
    (`(!b u. punnable cenv u (BaseT b)) /\
      (!n u. punnable cenv u (StructT n)) /\
      (!n u. punnable cenv u (FlagT n)) /\
      (!u. punnable cenv u NoneT)` by
       (rpt strip_tac >> Cases_on `u` >> simp[punnable_def]) >>
     ho_match_mp_tac (legacyInduction.mutual_ind_from_ops type_induction) >>
     rpt strip_tac >>
     gvs[memory_layout_key_tuple, memory_layout_key_array,
       memory_layout_key_tuple_cases, memory_layout_key_array_cases,
       listTheory.MAP_EQ_CONS, punnable_def] >>
     metis_tac[memory_layout_key_bytes]) >>
  `~tuple_memory_layout_eq t sty` by
    (strip_tac >>
     `type_memory_bytes cenv sty = type_memory_bytes cenv t` by
       metis_tac[tuple_memory_layout_eq_bytes] >>
     `punnable cenv sty t` by
       (Cases_on `t` >> Cases_on `sty` >>
        gvs[tuple_memory_layout_eq_def, punnable_def] >> metis_tac[]) >>
     gvs[same_memory_layout_def]) >>
  Cases_on `is_bytestring_type t`
  >- (drule_all typedMemoryCopyTheory.typed_copy_bytestring_source >>
      strip_tac >>
      rewrite_tac[compile_store_memory_def] >>
      simp[] >>
      once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
      simp[]) >>
  simp[compile_store_memory_def]
QED

Theorem ifexp_widened_call_arm_step_full:
  (* The shared joint unwrap_value lemma on H (r8, family form), here a
     premise until it lands. *)
  (!ty e sa vv sm sb op sc es ee s0 s tv rty G tn Gi ti st0.
    compile_expr cenv ty e sa = (vv,sm) /\
    (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
    sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
    unwrap_value cenv vv sb = (op,sc) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
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
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
    (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op0 G s) /\
    (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand G s) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val, ee) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                  eval_operand (vv_operand vv) s = SOME w ==>
                  w2n w + type_memory_size rt <= lo /\
                  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                         val_in_memory rt val (w2n w) mem)) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
    ?v z G' tn'.
      read_result cx tv ee = (INL v, ee) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
         gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
           (s, G, tn) [] (OK z, G', tn') /\
         expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
         ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
      (~is_word_type (post_value_type cenv e) ==>
       vv_at cenv cx (post_value_type cenv e) sa sc ee tv
         (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
      expr_store_bound cx (expr_type e) v op z /\
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
      ghost_kept_at lo cenv ee sb G tn s G' tn') /\
  (* ifexp_alloca_origin_ptr_edge *)
  (!s ctx lo fn bb id n p u D explicit PG G tn.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
    lo <= s.vs_alloca_next /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id ALLOCA [Lit n] [p]) /\
    step_inst_base (mk_inst id ALLOCA [Lit n] [p]) s = OK u ==>
    gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
       step_prov PG G (mk_inst id ALLOCA [Lit n] [p]) u,
       step_taint (mk_inst id ALLOCA [Lit n] [p]) s u tn)) /\
  (* compile_alloc_buffer_ghost_frame_at *)
  (!H D lo ctx fn cenv cx es sa sb n buf sc s out u d PG G tn.
      stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
        ctx fn cenv cx es s /\
      ghost_inv_at D lo d cenv cx es G tn s /\
      local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sb.cs_next_var /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc fn /\
      buf.buf_operand = Var out /\ n < dimword (:256) /\
      step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
      ghost_inv_at D lo d cenv cx es
        (step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
        (step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn) u) /\
  (* compile_alloc_buffer_kept_frame_at *)
  (!H lo ctx fn cenv cx e es sa sb s0 es' tv vv s n buf sc out u PG G0 tn0 G tn.
      vv_post H ctx fn cenv cx e es sa sb s0 es' tv vv s /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      lo <= s.vs_alloca_next /\
      local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
      sa.cs_next_var <= sb.cs_next_var /\
      compile_alloc_buffer n sb = (buf,sc) /\ buf.buf_operand = Var out /\
      n < dimword (:256) /\
      step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
      ghost_kept_at lo cenv es sa G0 tn0 s0
        (step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
        (step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn)) /\
  (* compile_store_memory_typed_origin_ptr_path (r3) *)
  (!cenv xd dty xs sty sa sb tenv stv dtv v s sw dw G tn lo ctx func explicit PG.
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
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t Gf tnf.
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
         FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))) /\
  compile_expr cenv ty e sa = (vv,sm) /\
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  compile_ifexp_arm cenv t (lowered_value_type cenv e) vv sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (e = a \/ e = b) /\ expr_type e = t /\
  ~is_word_type t /\ ~same_memory_layout cenv (lowered_value_type cenv e) t /\
  post_value_type cenv e = lowered_value_type cenv e /\
  type_widens_to (get_tenv cx) (lowered_value_type cenv e) t /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields.
     FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv)
       fields) /\
  (!ty' tvt. evaluate_type (get_tenv cx) ty' = SOME tvt ==>
     type_memory_bytes cenv ty' = type_memory_size tvt) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
     type_memory_size tvt < 2 ** 64) /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  (!v. read_result cx tva ee = (INL v,ee) ==> value_has_type rty v) /\
  (!v ptv. read_result cx tva ee = (INL v,ee) /\
          evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
          value_has_type ptv v) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv /\
  MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es1 sa sm u ee tva vv z /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn z) /\
  vv_store_bound cx t (lowered_value_type cenv e) ee tva vv z /\
  z.vs_current_bb = sm.cs_current_bb /\
  z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
  alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
  ptr_vv_ok cx (post_value_type cenv e) tva vv ee G tn z /\
  (!t' op0. vv = StackValue t' op0 /\ ~is_word_type (post_value_type cenv e) ==>
     ptr_buf_ok cenv e op0 G z) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G z) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tva ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) z = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es1 sa G1 tn1 u G tn ==>
  ?v z' Gz tf.
    read_result cx tva ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (z, G, tn) [] (OK z', Gz, tf) /\
       expr_post H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v op z' /\
       ghost_inv_at (DF H) lo d cenv cx ee Gz tf z') /\
    (~is_word_type t ==>
     vv_at cenv cx t sa sb ee tva (LocatedValue t (mk_ptr op LocMemory)) z') /\
    expr_store_bound cx t v op z' /\
    z'.vs_current_bb = sb.cs_current_bb /\
    z'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z' /\ u.vs_alloca_next <= z'.vs_alloca_next /\
    ptr_val_ok cx t v op Gz tf z' /\
    (~is_word_type t ==>
     !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op Gz z') /\
    (~is_word_type t ==>
     !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
            eval_operand op z' = SOME w ==>
            type_memory_size rt = 0 \/
            w2n w + type_memory_size rt <= z'.vs_alloca_next) /\
    ghost_kept_at lo cenv es1 sa G1 tn1 u Gz tf
Proof
  cheat
QED
