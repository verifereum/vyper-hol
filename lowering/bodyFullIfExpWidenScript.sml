(* The arm step of a ternary whose selected arm is a shorter bytestring
   than the ternary's: allocate a buffer of the ternary's type, unwrap the
   arm's value, copy it in, as one joint path with no GAS site, and give
   the ternary's posts at the arm's end at one horizon H.  The shared
   joint unwrap_value, alloc and bytestring-copy lemmas are premises until
   they land. *)
Theory bodyFullIfExpWiden
Ancestors
  bodySimFull fragGasOriginPtr exprSimIfExp exprSimDefs exprSimMemDefs
  bodyPtrDefs loweringPosts exprLowering exprLoweringProps fragExec
  emitHelper compileEnv allocaHistory stmtSimDefs vyperAST
  vyperInterpreter vyperState venomState fragGasSeqPtr fragGasEmitCtrl
  instMemFrontier memSafeRun ptrSafeRun ptrDiscipline venomInst
  venomExecSemantics loweringStateRelDefs finite_map

Theorem ifexp_widen_arm_step_full:
  (* The shared joint unwrap_value lemma at one horizon (r7 on H), here a
     premise until it lands. *)
  (!e ty sa vv sm sb op sc es ee s0 s tv rty G tn Gi ti.
     compile_expr cenv ty e sa = (vv,sm) /\
     sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
     unwrap_value cenv vv sb = (op,sc) /\
     local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
     MAP FDOM es.scopes = MAP FDOM ee.scopes /\
     sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
     fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
     ~ctx_has_dalloca ctx /\ dead_lo_ok H D lo cenv cx /\
     (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
     (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
           ~is_word_type (post_value_type cenv e) ==>
           type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
           type_memory_size rt < 2**64) /\
     evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
     (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
     vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
     vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
       ee tv vv s /\
     alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
     ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
     s.vs_inst_idx = LENGTH sb.cs_current_insts /\
     ghost_inv_at D lo d cenv cx ee G tn s /\
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
     ?v Gz tf z.
       read_result cx tv ee = (INL v, ee) /\
       gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, Gz, tf) /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       expr_store_bound cx (post_value_type cenv e) v op z /\
       z.vs_current_bb = sc.cs_current_bb /\
       z.vs_inst_idx = LENGTH sc.cs_current_insts /\
       alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
       s0.vs_alloca_next <= z.vs_alloca_next /\
       ghost_inv_at D lo d cenv cx ee Gz tf z /\
       ptr_val_ok cx (post_value_type cenv e) v op Gz tf z /\
       (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op Gz z) /\
       (~is_word_type (post_value_type cenv e) ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
               eval_operand op z = SOME w ==>
               type_memory_size rt = 0 \/
               w2n w + type_memory_size rt <= z.vs_alloca_next) /\
       ghost_kept_at lo cenv es sa Gi ti s0 Gz tf /\
       (!x. not_fresh_at sb x ==>
            lookup_var x z = lookup_var x s /\ FLOOKUP Gz x = FLOOKUP G x /\
            op_taint tf (Var x) = op_taint tn (Var x)) /\
       wb_frame cenv ee ee sb s z /\
       ghost_kept_at lo cenv ee sb G tn s Gz tf) /\
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
      stmt_state_rel H ctx fn cenv cx es s /\
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
  (* compile_store_bytestring_origin_ptr_path *)
  (!D lo explicit ctx fn PG sa sb src dst G tn s a b len n bb.
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
      ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
      ?Gf tnf sf.
        gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
          (OK (sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),Gf,tnf) /\
        run_inst_seq (emitted_insts sa sb) s = OK sf /\
        tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
        sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
        sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
        tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
        tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+n}) UNION
          {w2n b+i | i < n /\ w2n a+i IN tn.t_mem} /\
        (!p. not_fresh_at sa p ==>
          lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
          op_taint tnf (Var p) = op_taint tn (Var p))) /\
  compile_expr cenv ty e sa = (vv,sm) /\
  compile_ifexp_arm cenv t (lowered_value_type cenv e) vv sm = (op,sb) /\
  ~is_word_type t /\ ~same_memory_layout cenv (lowered_value_type cenv e) t /\
  is_bytestring_type t /\ is_bytestring_type (lowered_value_type cenv e) /\
  arg_type_fits (lowered_value_type cenv e) t /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ dead_lo_ok H D lo cenv cx /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (e = a \/ e = b) /\ expr_type e = t /\ post_value_type cenv e = t /\
  (!ty' tvt. evaluate_type (get_tenv cx) ty' = SOME tvt ==>
     type_memory_bytes cenv ty' = type_memory_size tvt) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
     type_memory_size tvt < 2 ** 64) /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  (!v. read_result cx tva ee = (INL v,ee) ==> value_has_type rty v) /\
  MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
  vv_post H ctx func cenv cx e es1 sa sm u ee tva vv z /\
  vv_store_bound cx t (lowered_value_type cenv e) ee tva vv z /\
  z.vs_current_bb = sm.cs_current_bb /\
  z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
  alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
  ghost_inv_at D lo d cenv cx ee G tn z /\
  ptr_vv_ok cx t tva vv ee G tn z /\
  (!t' op0. vv = StackValue t' op0 /\ ~is_word_type t ==>
     ptr_buf_ok cenv e op0 G z) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G z) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tva ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
                eval_operand (vv_operand vv) z = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es1 sa G1 tn1 u G tn ==>
  ?v z' Gz tf.
    read_result cx tva ee = (INL v,ee) /\
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
      (z, G, tn) [] (OK z', Gz, tf) /\
    expr_post H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v op z' /\
    (~is_word_type t ==>
     vv_at cenv cx t sa sb ee tva (LocatedValue t (mk_ptr op LocMemory)) z') /\
    expr_store_bound cx t v op z' /\
    z'.vs_current_bb = sb.cs_current_bb /\
    z'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z' /\ u.vs_alloca_next <= z'.vs_alloca_next /\
    ghost_inv_at D lo d cenv cx ee Gz tf z' /\
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
