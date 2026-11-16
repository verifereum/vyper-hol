(* Successful-head boundary: one physical endpoint for every dead-byte map. *)
Theory bodyFullBuiltinConcatHead
Ancestors exprLowering[qualified,ignore_grammar] vyperAST[qualified,ignore_grammar] arithmetic[qualified,ignore_grammar]
  bodyFullBuiltinConcatScratch bodyFullBuiltinConcatBytes
  bodyFullBuiltinConcatFixed bodyFullPreds bodySimFull
  bodyPtrBytestringBuiltinsConcatOperand exprPtrUnwrapFrames
  exprSimConcatSource exprSimConcatStep exprSimConcatPath exprSimConcatShapeRun
  gasShadowCompile gasShadowCompileHelpers gasShadowState gasShadowUnit
  gasExplicitSites bodyPtrBytestringBuiltinsWindowGhost
  wordArgsPtr bodyMemoryDefs fragGasOriginPtrDead
  exprLoweringProps loweringStateRelDefs compileEnv freshWrites
  vyperStorageFootprint exprOperandVar loweringPosts exprSimMemDefs
  venomMemDefs valueEncodingDefs vyperTyping venomState vyperValue exprSimProps
  words list finite_map pred_set
Libs
  monadsyntax

Theorem concat_head_bytes_uniform:
  (do arg_len <- emit_op MLOAD [Var sp];
      arg_data <- emit_op ADD [Var sp;Lit 32w];
      offset_op <- emit_op MLOAD [Var oq];
      dst <- emit_op ADD [Var dp;offset_op];
      emit_void MCOPY [dst;arg_data;arg_len];
      new_offset <- emit_op ADD [offset_op;arg_len];
      emit_void MSTORE [Var oq;new_offset]
   od) sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  lookup_var sp s = SOME (n2w srcbase) /\
  lookup_var dp s = SOME (n2w (B+32)) /\ lookup_var oq s = SOME (n2w ob) /\
  not_fresh_at sa sp /\ not_fresh_at sa dp /\ not_fresh_at sa oq /\
  ptr_covers G tn sp s (32+LENGTH bs) /\
  ptr_covers G tn dp s (bsz-32) /\ ptr_covers G tn oq s 32 /\
  ~ctx_has_dalloca ctx /\
  (!i. srcbase <= i /\ i < srcbase+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
  (!i. ob <= i /\ i < ob+32 ==> i NOTIN tn.t_mem) /\
  mload srcbase s = n2w (LENGTH bs) /\ mload ob s = n2w k /\
  mem_bytes_at (srcbase+32) (LENGTH bs) s.vs_memory = bs /\
  32+k+LENGTH bs <= bsz /\ B+bsz < dimword (:256) /\
  srcbase+32+LENGTH bs < dimword (:256) /\ ob+64 < dimword (:256) /\
  srcbase+32+LENGTH bs <= s.vs_alloca_next /\
  B+bsz <= s.vs_alloca_next /\ ob+64 <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (B+bsz <= ob \/ ob+64 <= B) /\ lo <= B /\ lo <= ob /\
  local_ptrs_reserved cenv sa /\
  MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas binst.inst_id = SOME (B,bsz) /\
  MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas oinst.inst_id = SOME (ob,64) /\
  (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
    (B+bsz <= lb \/ lb+lsz <= B) /\ (ob+64 <= lb \/ lb+lsz <= ob)) /\
  local_ptrs_rel func cenv es.scopes s /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) ==>
  ?u V G' tn'.
    u = (mstore ob (n2w (k+LENGTH bs))
      (mcopy (B+32+k) (srcbase+32) (LENGTH bs) s) with
      <|vs_vars := V; vs_inst_idx := LENGTH sb.cs_current_insts|>) /\
    (!z. not_fresh_at sa z ==> FLOOKUP V z = FLOOKUP s.vs_vars z) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G',tn')) /\
    alloca_history func u /\ u.vs_current_bb = sb.cs_current_bb /\
    ~u.vs_halted /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    tn'.t_mem SUBSET tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==> FLOOKUP G' z = FLOOKUP G z /\
      op_taint tn' (Var z) = op_taint tn (Var z)) /\
    (!i. B+32+k <= i /\ i < B+32+k+LENGTH bs ==> i NOTIN tn'.t_mem) /\
    (!i. ob <= i /\ i < ob+32 ==> i NOTIN tn'.t_mem) /\
    (!H. stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es u) /\
    (!D. ghost_inv_at D lo d cenv cx es G tn s ==> ghost_inv_at D lo d cenv cx es G' tn' u) /\
    (!sa0 G0 tn0 s0. ghost_kept_at lo cenv es sa0 G0 tn0 s0 G tn /\
      (!z. not_fresh_at sa0 z ==> not_fresh_at sa z) ==>
      ghost_kept_at lo cenv es sa0 G0 tn0 s0 G' tn') /\
    mem_bytes_at (B+32) (k+LENGTH bs) u.vs_memory = mem_bytes_at (B+32) k s.vs_memory ++ bs /\
    mload ob u = n2w (k+LENGTH bs) /\
    (!p n. (p+n <= B \/ B+bsz <= p) /\ (p+n <= ob \/ ob+64 <= p) ==>
      mem_bytes_at p n u.vs_memory = mem_bytes_at p n s.vs_memory)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all concat_bytes_arm_full_run >>
  disch_then (qspecl_then [`explicit`,`PG`,
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
    strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G',tn')` by
    (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
  `!D. ghost_inv_at D lo d cenv cx es G tn s ==> ghost_inv_at D lo d cenv cx es G' tn' u` by
    (gen_tac >> drule_all concat_bytes_arm_full_frame >> simp[]) >>
  drule_all concat_bytes_arm_full_frame >> strip_tac >>
  qexistsl_tac [`u`,`V`,`G'`,`tn'`] >> gvs[] >> metis_tac[]
QED

Theorem concat_head_fixed_uniform:
  (do offset_op <- emit_op MLOAD [Var oq];
      dst <- emit_op ADD [Var dp;offset_op];
      emit_void MSTORE [dst;x];
      new_offset <- emit_op ADD [offset_op;Lit (n2w m)];
      emit_void MSTORE [Var oq;new_offset]
   od) sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  lookup_var dp s = SOME (n2w (B+32)) /\
  lookup_var oq s = SOME (n2w ob) /\
  eval_operand x s = SOME (word_of_bytes_be (PAD_RIGHT 0w 32 bs)) /\
  not_fresh_at sa dp /\ not_fresh_at sa oq /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  ptr_covers G tn dp s (bsz-32) /\ ptr_covers G tn oq s 32 /\
  op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (!i. ob <= i /\ i < ob+32 ==> i NOTIN tn.t_mem) /\
  mload ob s = n2w k /\ LENGTH bs = m /\ m <= 32 /\ 32+k+32 <= bsz /\
  B+bsz < dimword (:256) /\ ob+64 < dimword (:256) /\
  B+bsz <= s.vs_alloca_next /\ ob+64 <= s.vs_alloca_next /\
  (B+bsz <= ob \/ ob+64 <= B) /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lo <= B /\ lo <= ob /\ local_ptrs_reserved cenv sa /\
  MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas binst.inst_id = SOME (B,bsz) /\
  MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas oinst.inst_id = SOME (ob,64) /\
  (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
    (B+bsz <= lb \/ lb+lsz <= B) /\ (ob+64 <= lb \/ lb+lsz <= ob)) /\
  local_ptrs_rel func cenv es.scopes s /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) ==>
  ?u V G' tn'.
    u = (mstore ob (n2w (k+m))
      (mstore (B+32+k) (word_of_bytes_be (PAD_RIGHT 0w 32 bs)) s) with
      <|vs_vars := V; vs_inst_idx := LENGTH sb.cs_current_insts|>) /\
    (!z. not_fresh_at sa z ==> FLOOKUP V z = FLOOKUP s.vs_vars z) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G',tn')) /\
    alloca_history func u /\ u.vs_current_bb = sb.cs_current_bb /\
    ~u.vs_halted /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    tn'.t_mem SUBSET tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==> FLOOKUP G' z = FLOOKUP G z /\
      op_taint tn' (Var z) = op_taint tn (Var z)) /\
    (!i. B+32+k <= i /\ i < B+32+k+32 ==> i NOTIN tn'.t_mem) /\
    (!i. ob <= i /\ i < ob+32 ==> i NOTIN tn'.t_mem) /\
    (!H. stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es u) /\
    (!D. ghost_inv_at D lo d cenv cx es G tn s ==> ghost_inv_at D lo d cenv cx es G' tn' u) /\
    (!sa0 G0 tn0 s0. ghost_kept_at lo cenv es sa0 G0 tn0 s0 G tn /\
      (!z. not_fresh_at sa0 z ==> not_fresh_at sa z) ==>
      ghost_kept_at lo cenv es sa0 G0 tn0 s0 G' tn') /\
    mem_bytes_at (B+32) (k+m) u.vs_memory = mem_bytes_at (B+32) k s.vs_memory ++ bs /\
    mload ob u = n2w (k+m) /\
    (!p n. (p+n <= B \/ B+bsz <= p) /\ (p+n <= ob \/ ob+64 <= p) ==>
      mem_bytes_at p n u.vs_memory = mem_bytes_at p n s.vs_memory)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all concat_fixed_arm_full_run >>
  disch_then (qspecl_then [`explicit`,`PG`,
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
    strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G',tn')` by
    (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
  `!D. ghost_inv_at D lo d cenv cx es G tn s ==> ghost_inv_at D lo d cenv cx es G' tn' u` by
    (gen_tac >> drule_all concat_fixed_arm_full_frame >> simp[]) >>
  drule_all concat_fixed_arm_full_frame >> strip_tac >>
  qexistsl_tac [`u`,`V`,`G'`,`tn'`] >> gvs[] >> metis_tac[]
QED

Theorem concat_head_arm_full:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env st0
   e args es ee sa sc sb shadow_sa shadow_sc shadow_sb s t G tn G1 tn1
   B bsz ow k P binst oinst dv ov v op tv.
    compile_concat compile_expr cenv (e::args) (Var dv)
      (MAP (\e.
         if is_bytestring_type (expr_type e) then (T,0:num)
         else case expr_type e of BaseT (BytesT (Fixed m)) => (F,m)
                       | _ => (F,32:num)) (e::args)) (Var ov) sa = ((),sb) /\
    compile_concat compile_expr cenv (MAP gas_shadow_expr (e::args)) (Var dv)
      (MAP (\e.
         if is_bytestring_type (expr_type e) then (T,0:num)
         else case expr_type e of BaseT (BytesT (Fixed m)) => (F,m)
                       | _ => (F,32:num)) (e::args)) (Var ov) shadow_sa = ((),shadow_sb) /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,sc) /\
    lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa =
      (op,shadow_sc) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sc shadow_sc /\
    gas_shadow_state sb shadow_sb /\ gas_shadow_context ctx shadow_ctx /\
    gas_shadow_function func shadow_func /\ ctx_inst_ids_distinct ctx /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    EVERY (\e. is_bytestring_type (expr_type e) \/
                 ?m. expr_type e = BaseT (BytesT (Fixed m))) (e::args) /\
    expr_sim_inv cenv cx env es /\ expr_sim_inv cenv cx env ee /\
    (!x st. MEM x (e::args) /\ expr_sim_inv cenv cx env st ==>
       expr_body_pre cenv cx env x st) /\
    body_exprs_full_ok cx (e::args) /\ body_inv tops ctx cenv cx /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    storage_trace_domain cx st0 es.storage_trace /\
    storage_trace_domain cx st0 ee.storage_trace /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    return_buf_frame d cenv sa s /\ alloca_history func s /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post H ctx func cenv cx e es sa sc s ee v op t /\
       expr_store_bound cx (expr_type e) v op t /\
       ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t /\
       ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 t /\
       (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G1 t)) /\
    ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    lookup_var dv s = SOME (n2w (B+32)) /\ lookup_var ov s = SOME ow /\
    not_fresh_at sa dv /\ not_fresh_at sa ov /\
    MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
    binst.inst_id < sa.cs_next_id /\
    FLOOKUP s.vs_allocas binst.inst_id = SOME (B,bsz) /\
    MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
    oinst.inst_id < sa.cs_next_id /\
    FLOOKUP s.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
    (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
       (B+bsz <= lb \/ lb+lsz <= B) /\
       (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)) /\
    (B+bsz <= w2n ow \/ w2n ow+64 <= B) /\
    B+bsz < dimword (:256) /\ w2n ow+64 < dimword (:256) /\
    B+bsz <= s.vs_alloca_next /\ w2n ow+64 <= s.vs_alloca_next /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ lo <= B /\ lo <= w2n ow /\
    ptr_covers G tn dv s (bsz-32) /\ ptr_covers G tn ov s 32 /\
    (!i. B+32 <= i /\ i < B+32+k ==> i NOTIN tn.t_mem) /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn.t_mem) /\
    mload (w2n ow) s = n2w k /\ k <= P /\
    32+P+SUM (MAP concat_payload_capacity (MAP expr_type (e::args))) <= bsz /\
    32+concat_data_bound P (MAP expr_type (e::args)) <= bsz ==>
    ?s2 shadow_s2 u V G2 tn2.
      compile_concat compile_expr cenv args (Var dv)
        (MAP (\e.
           if is_bytestring_type (expr_type e) then (T,0:num)
           else case expr_type e of BaseT (BytesT (Fixed m)) => (F,m)
                         | _ => (F,32:num)) args) (Var ov) s2 = ((),sb) /\
      compile_concat compile_expr cenv (MAP gas_shadow_expr args) (Var dv)
        (MAP (\e.
           if is_bytestring_type (expr_type e) then (T,0:num)
           else case expr_type e of BaseT (BytesT (Fixed m)) => (F,m)
                         | _ => (F,32:num)) args) (Var ov) shadow_s2 = ((),shadow_sb) /\
      gas_shadow_state s2 shadow_s2 /\
      ci_mono sa sc /\ ci_mono sc s2 /\ ci_mono s2 sb /\
      fn_has_code s2 sb func /\ fn_has_code shadow_s2 shadow_sb shadow_func /\
      local_ptrs_reserved cenv s2 /\
      (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z) /\
      (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z) /\
      not_fresh_at s2 dv /\ not_fresh_at s2 ov /\
      binst.inst_id < s2.cs_next_id /\ oinst.inst_id < s2.cs_next_id /\
      u.vs_vars = V /\
      (!z. not_fresh_at sc z ==> FLOOKUP V z = FLOOKUP t.vs_vars z) /\
      ~u.vs_halted /\ u.vs_current_bb = s2.cs_current_bb /\
      u.vs_inst_idx = LENGTH s2.cs_current_insts /\
      alloca_history func u /\ u.vs_allocas = t.vs_allocas /\
      u.vs_alloca_next = t.vs_alloca_next /\
      u.vs_call_ctx = t.vs_call_ctx /\ u.vs_accounts = t.vs_accounts /\
      u.vs_transient = t.vs_transient /\
      allocas_from lo u /\ lo <= u.vs_alloca_next /\
      B+bsz <= u.vs_alloca_next /\ w2n ow+64 <= u.vs_alloca_next /\
      return_buf_frame d cenv s2 u /\
      lookup_var dv u = SOME (n2w (B+32)) /\ lookup_var ov u = SOME ow /\
      FLOOKUP u.vs_allocas binst.inst_id = SOME (B,bsz) /\
      FLOOKUP u.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
      (!name lb lsz. local_region cenv ee.scopes u name lb lsz ==>
         (B+bsz <= lb \/ lb+lsz <= B) /\
         (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)) /\
      ptr_covers G2 tn2 dv u (bsz-32) /\ ptr_covers G2 tn2 ov u 32 /\
      (!i. B+32 <= i /\
           i < B+32+k+LENGTH (case v of BytesV bs => bs
                    | StringV str => MAP (n2w o ORD) str | _ => []) ==>
           i NOTIN tn2.t_mem) /\
      (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn2.t_mem) /\
      mload (w2n ow) u = n2w (k+LENGTH (case v of BytesV bs => bs
                    | StringV str => MAP (n2w o ORD) str | _ => [])) /\
      k+LENGTH (case v of BytesV bs => bs
                    | StringV str => MAP (n2w o ORD) str | _ => []) <=
        P+concat_payload_capacity (expr_type e) /\
      32+(P+concat_payload_capacity (expr_type e))+
        SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz /\
      32+concat_data_bound (P+concat_payload_capacity (expr_type e))
        (MAP expr_type args) <= bsz /\
      mem_bytes_at (B+32) (k+LENGTH (case v of BytesV bs => bs
                    | StringV str => MAP (n2w o ORD) str | _ => [])) u.vs_memory =
        mem_bytes_at (B+32) k s.vs_memory ++
          (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) /\
      (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==> lookup_var z u = SOME w) /\
      (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP u.vs_allocas aid = SOME a) /\
      (!aid p n. FLOOKUP s.vs_allocas aid = SOME (p,n) /\ aid < sa.cs_next_id /\
         (p+n <= B \/ B+bsz <= p) /\ (p+n <= w2n ow \/ w2n ow+64 <= p) /\
         (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
                         p+n <= lb \/ lb+lsz <= p) ==>
         mem_bytes_at p n u.vs_memory = mem_bytes_at p n s.vs_memory) /\
      locals_kept cenv es ee s u /\
      (~expr_has_effect e ==>
        (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
           mem_bytes_at lb lsz u.vs_memory = mem_bytes_at lb lsz s.vs_memory) /\
        (!p n. (p+n <= B \/ B+bsz <= p) /\
           (p+n <= w2n ow \/ w2n ow+64 <= p) /\
           (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
              sa.cs_next_id <= inst.inst_id /\ FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
              regions_disjoint p n b sz) ==>
           mem_bytes_at p n u.vs_memory = mem_bytes_at p n s.vs_memory)) /\
      ghost_kept_at lo cenv es sa G tn s G2 tn2 /\
      (!(H:(bool # bytes32 # type_value) list # num list).
           stmt_state_rel H ctx func cenv cx ee t ==>
           stmt_state_rel H ctx func cenv cx ee u) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
           (t,G1,tn1) [] (OK u,G2,tn2) /\
         stmt_state_rel H ctx func cenv cx ee u /\
         storage_well_formed_on cx ee (FST H) /\
         ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 u)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `local_ptrs_rel func cenv es.scopes s` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     qpat_assum `storage_trace_domain cx st0 es.storage_trace` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[storage_trace_domain_def,stmt_state_rel_def,state_rel_def]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sa sc` by
    (qpat_assum `lower_value _ _ _ e sa = _`
       (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[ci_mono_def]) >>
  `not_fresh_at sc dv /\ not_fresh_at sc ov` by
    metis_tac[not_fresh_at_mono,ci_mono_def] >>
  `!z. op = Var z ==> not_fresh_at sc z` by
    metis_tac[compile_lower_value_var] >>
  `FLOOKUP t.vs_allocas binst.inst_id = SOME (B,bsz) /\
   mem_bytes_at B bsz t.vs_memory = mem_bytes_at B bsz s.vs_memory /\
   (!i. B <= i /\ i < B+bsz /\ i IN tn1.t_mem ==> i IN tn.t_mem) /\
   (!z. not_fresh_at sa z ==> FLOOKUP G1 z = FLOOKUP G z /\
      op_taint tn1 (Var z) = op_taint tn (Var z)) /\
   (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==> lookup_var z t = SOME w)` by
    (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       (INST_TYPE [``:'b`` |-> ``:num # num``] concat_scratch_child_frame) >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  `FLOOKUP t.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
   mem_bytes_at (w2n ow) 64 t.vs_memory = mem_bytes_at (w2n ow) 64 s.vs_memory /\
   (!i. w2n ow <= i /\ i < w2n ow+64 /\ i IN tn1.t_mem ==> i IN tn.t_mem) /\
   (!z. not_fresh_at sa z ==> FLOOKUP G1 z = FLOOKUP G z /\
      op_taint tn1 (Var z) = op_taint tn (Var z)) /\
   (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==> lookup_var z t = SOME w)` by
    (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       (INST_TYPE [``:'b`` |-> ``:num # num``] concat_scratch_child_frame) >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee t` by
    fs[expr_post_def] >>
  `alloca_inv t /\ t.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_def,alloca_room_next_lt] >>
  `local_ptrs_rel func cenv ee.scopes t` by
    fs[stmt_state_rel_def,state_rel_def] >>
  `lookup_var dv t = SOME (n2w (B+32)) /\ lookup_var ov t = SOME ow` by
    metis_tac[] >>
  `ptr_covers G1 tn1 dv t (bsz-32) /\ ptr_covers G1 tn1 ov t 32` by
    (conj_tac >> irule (iffRL copy_ptr_covers_transport) >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[] >> metis_tac[]) >>
  `!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn1.t_mem` by
    (rpt strip_tac >> `i < w2n ow+64` by decide_tac >> metis_tac[]) >>
  `mem_bytes_at (w2n ow) 32 t.vs_memory = mem_bytes_at (w2n ow) 32 s.vs_memory` by
    (qpat_assum `mem_bytes_at (w2n ow) 64 _ = _`
       (mp_then Any mp_tac valueEncodingPropsTheory.mem_bytes_at_translated_window) >>
     disch_then (qspecl_then [`0`,`32`] mp_tac) >> simp[]) >>
  `mload (w2n ow) t = n2w k` by
    (qpat_assum `mem_bytes_at (w2n ow) 32 _ = _` mp_tac >>
     qpat_assum `mload (w2n ow) s = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[mload_def,mem_word_at_def,mem_bytes_at_def]) >>
  `B+bsz <= t.vs_alloca_next /\ w2n ow+64 <= t.vs_alloca_next` by decide_tac >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `!name lb lsz. local_region cenv ee.scopes t name lb lsz ==>
     local_region cenv es.scopes s name lb lsz` by
    (rpt strip_tac >> drule_all local_region_frame >> simp[]) >>
  `!name lb lsz. local_region cenv ee.scopes t name lb lsz ==>
     (B+bsz <= lb \/ lb+lsz <= B) /\
     (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)` by metis_tac[] >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> fs[ci_mono_def]) >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sc z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sc z)` by
    (conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >>
     qexists `sa` >> fs[ci_mono_def] >> metis_tac[]) >>
  `!ce ty ex st. ci_mono st (SND (compile_expr ce ty ex st))` by
    (rpt gen_tac >> Cases_on `compile_expr ce ty ex st` >>
     drule (cj 1 compile_expr_grows) >> simp[ci_mono_def]) >>
  `!ce es dp infos off st.
     ci_mono st (SND (compile_concat compile_expr ce es dp infos off st))` by
    (rpt gen_tac >> irule ci_mono_compile_concat_cfn >> simp[]) >>
  qmatch_goalsub_abbrev_tac `LENGTH bs` >>
  `?s2 shadow_s2 u V G2 tn2.
    compile_concat compile_expr cenv args (Var dv)
      (MAP (\e. if is_bytestring_type (expr_type e) then (T,0:num)
        else case expr_type e of BaseT (BytesT (Fixed m)) => (F,m)
             | _ => (F,32:num)) args) (Var ov) s2 = ((),sb) /\
    compile_concat compile_expr cenv (MAP gas_shadow_expr args) (Var dv)
      (MAP (\e. if is_bytestring_type (expr_type e) then (T,0:num)
        else case expr_type e of BaseT (BytesT (Fixed m)) => (F,m)
             | _ => (F,32:num)) args) (Var ov) shadow_s2 = ((),shadow_sb) /\
    gas_shadow_state s2 shadow_s2 /\ ci_mono sc s2 /\
    ci_mono s2 sb /\ fn_has_code s2 sb func /\
    fn_has_code shadow_s2 shadow_sb shadow_func /\
    LENGTH bs <= concat_payload_capacity (expr_type e) /\
    u.vs_vars = V /\ u.vs_inst_idx = LENGTH s2.cs_current_insts /\
    (!z. not_fresh_at sc z ==> FLOOKUP V z = FLOOKUP t.vs_vars z) /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK u,G2,tn2)) /\
    alloca_history func u /\ u.vs_current_bb = s2.cs_current_bb /\
    ~u.vs_halted /\ u.vs_allocas = t.vs_allocas /\
    u.vs_alloca_next = t.vs_alloca_next /\ u.vs_call_ctx = t.vs_call_ctx /\
    u.vs_accounts = t.vs_accounts /\ u.vs_transient = t.vs_transient /\
    tn2.t_mem SUBSET tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
    tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
    (!z. not_fresh_at sc z ==> FLOOKUP G2 z = FLOOKUP G1 z /\
      op_taint tn2 (Var z) = op_taint tn1 (Var z)) /\
    (!i. B+32+k <= i /\ i < B+32+k+LENGTH bs ==> i NOTIN tn2.t_mem) /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn2.t_mem) /\
    (!(H:(bool # bytes32 # type_value) list # num list).
      stmt_state_rel H ctx func cenv cx ee t ==>
      stmt_state_rel H ctx func cenv cx ee u) /\
    (!D. ghost_inv_at D lo d cenv cx ee G1 tn1 t ==>
      ghost_inv_at D lo d cenv cx ee G2 tn2 u) /\
    (!sa0 G0 tn0 s0. ghost_kept_at lo cenv ee sa0 G0 tn0 s0 G1 tn1 /\
      (!z. not_fresh_at sa0 z ==> not_fresh_at sc z) ==>
      ghost_kept_at lo cenv ee sa0 G0 tn0 s0 G2 tn2) /\
    mem_bytes_at (B+32) (k+LENGTH bs) u.vs_memory =
      mem_bytes_at (B+32) k t.vs_memory ++ bs /\
    mload (w2n ow) u = n2w (k+LENGTH bs) /\
    (!p n. (p+n <= B \/ B+bsz <= p) /\
      (p+n <= w2n ow \/ w2n ow+64 <= p) ==>
      mem_bytes_at p n u.vs_memory = mem_bytes_at p n t.vs_memory)` by
    (Cases_on `is_bytestring_type (expr_type e)`
     >- (qpat_x_assum `compile_concat _ _ (e::args) _ _ _ sa = _` mp_tac >>
         simp[] >> disch_then (strip_assume_tac o MATCH_MP compile_concat_bytes_cons) >>
         `mem_ptr = op /\ s1 = sc` by metis_tac[pairTheory.PAIR_EQ] >>
         qpat_x_assum `mem_ptr = op` SUBST_ALL_TAC >>
         qpat_x_assum `s1 = sc` SUBST_ALL_TAC >>
         qpat_x_assum `compile_concat _ _ (MAP gas_shadow_expr (e::args)) _ _ _ shadow_sa = _` mp_tac >>
         simp[] >> disch_then (strip_assume_tac o MATCH_MP compile_concat_bytes_cons) >>
         `mem_ptr = op /\ s1 = shadow_sc` by
           (fs[gasShadowTheory.gas_shadow_expr_type] >> metis_tac[pairTheory.PAIR_EQ]) >>
         qpat_x_assum `mem_ptr = op` SUBST_ALL_TAC >>
         qpat_x_assum `s1 = shadow_sc` SUBST_ALL_TAC >>
         drule_all concat_operand_bytes_read >>
         disch_then (qx_choose_then `sw` (qx_choose_then `sp` strip_assume_tac)) >>
         qpat_x_assum `op = Var sp` SUBST_ALL_TAC >>
         `w2n sw+32+LENGTH bs <= t.vs_alloca_next` by
           (simp[Abbr `bs`] >>
            qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
            qpat_x_assum `evaluate_type _ _ = SOME tv` mp_tac >>
            qpat_x_assum `value_has_type tv v` mp_tac >>
            qpat_x_assum `is_bytestring_type _` mp_tac >>
            qpat_x_assum `lookup_var sp t = SOME sw` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
            `(?n. expr_type e = BaseT (BytesT (Dynamic n))) \/
             (?n. expr_type e = BaseT (StringT n))` by
              (Cases_on `expr_type e` >> fs[is_bytestring_type_def] >>
               rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_bytestring_type_def] >>
               rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_bytestring_type_def]) >>
            fs[expr_store_bound_def,eval_operand_def,evaluate_type_def] >>
            Cases_on `v` >> gvs[value_has_type_def,val_store_size_def,is_word_type_def] >>
            qmatch_asmsub_abbrev_tac `word_size len` >>
            qspec_then `len` mp_tac le_word_size_mul >> decide_tac) >>
         `mload (w2n sw) t = n2w (LENGTH bs)` by
           (simp[Abbr `bs`] >> fs[mload_def,mem_word_at_def]) >>
         `32+k+LENGTH bs <= bsz /\ w2n sw+32+LENGTH bs < dimword (:256)` by
           (fs[Abbr `bs`] >> decide_tac) >>
         qabbrev_tac `arm =
           do arg_len <- emit_op MLOAD [Var sp];
              arg_data <- emit_op ADD [Var sp;Lit 32w];
              offset_op <- emit_op MLOAD [Var ov];
              dst <- emit_op ADD [Var dv;offset_op];
              emit_void MCOPY [dst;arg_data;arg_len];
              new_offset <- emit_op ADD [offset_op;arg_len];
              emit_void MSTORE [Var ov;new_offset]
           od` >>
         `arm sc = ((),s2) /\ arm shadow_sc = ((),s2')` by simp[Abbr `arm`] >>
         `!st. ci_mono st (SND (arm st))` by
           (simp[Abbr `arm`,comp_ignore_bind_def] >> gen_tac >>
            rpt (irule ci_mono_bind >> simp[ci_mono_emit_op,ci_mono_emit_void] >>
                 rpt gen_tac)) >>
         `ci_mono sc s2 /\ ci_mono shadow_sc s2'` by metis_tac[pairTheory.SND] >>
         `ci_mono s2 sb /\ ci_mono s2' shadow_sb` by metis_tac[pairTheory.SND] >>
         `cs_extends sa sc /\ cs_extends sc s2 /\ cs_extends s2 sb /\
          cs_extends shadow_sa shadow_sc /\ cs_extends shadow_sc s2' /\
          cs_extends s2' shadow_sb` by
           (fs[ci_mono_def] >> metis_tac[cj 2 compile_expr_grows]) >>
         `fn_has_code sc s2 func /\ fn_has_code s2 sb func /\
          fn_has_code s2' shadow_sb shadow_func` by
           metis_tac[fragExecTheory.fn_has_code_mid,fragExecTheory.fn_has_code_split,cs_extends_trans] >>
         `gas_shadow_compiles arm arm` by
           (simp[Abbr `arm`,comp_ignore_bind_def] >>
            rpt (irule gas_shadow_compiles_bind >>
              simp[gas_shadow_compiles_emit_op,gas_shadow_compiles_emit_void] >>
              rpt gen_tac)) >>
         `gas_shadow_state s2 s2'` by
           (qpat_assum `gas_shadow_compiles arm arm` mp_tac >>
            rewrite_tac[gas_shadow_compiles_def] >>
            disch_then (qspecl_then [`sc`,`shadow_sc`] mp_tac) >> simp[]) >>
         `lookup_var sp t = SOME (n2w (w2n sw)) /\
          lookup_var ov t = SOME (n2w (w2n ow)) /\ not_fresh_at sc sp` by simp[] >>
         `mem_bytes_at (w2n sw+32) (LENGTH bs) t.vs_memory = bs /\
          ptr_covers G1 tn1 sp t (32+LENGTH bs) /\
          (!i. w2n sw <= i /\ i < w2n sw+32+LENGTH bs ==> i NOTIN tn1.t_mem)` by
           simp[Abbr `bs`] >>
         simp[Abbr `arm`] >>
         drule_all (INST_TYPE [alpha |-> ``:256``] concat_head_bytes_uniform) >>
         disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`d`,`cx`,`PG`] strip_assume_tac) >>
         qexistsl_tac [`s2`,`s2'`,`u`,`G'`,`tn'`] >>
         simp[] >> conj_tac >- simp[Abbr `bs`] >>
         qpat_x_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _` mp_tac >>
         simp[]) >>
     `?m. expr_type e = BaseT (BytesT (Fixed m))` by fs[] >>
     qpat_x_assum `compile_concat _ _ (e::args) _ _ _ sa = _` mp_tac >>
     simp[is_bytestring_type_def] >>
     disch_then (strip_assume_tac o MATCH_MP compile_concat_fixed_cons) >>
     rename1 `lower_value _ _ _ e sa = (fixed_op,s1)` >>
     `fixed_op = op /\ s1 = sc` by metis_tac[pairTheory.PAIR_EQ] >>
     qpat_x_assum `fixed_op = op` SUBST_ALL_TAC >>
     qpat_x_assum `s1 = sc` SUBST_ALL_TAC >>
     qpat_x_assum `compile_concat _ _ (MAP gas_shadow_expr (e::args)) _ _ _ shadow_sa = _` mp_tac >>
     simp[gasShadowTheory.gas_shadow_expr_type,is_bytestring_type_def] >>
     disch_then (strip_assume_tac o MATCH_MP compile_concat_fixed_cons) >>
     rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (fixed_op,s1)` >>
     `fixed_op = op /\ s1 = shadow_sc` by
       (fs[gasShadowTheory.gas_shadow_expr_type] >> metis_tac[pairTheory.PAIR_EQ]) >>
     qpat_x_assum `fixed_op = op` SUBST_ALL_TAC >>
     qpat_x_assum `s1 = shadow_sc` SUBST_ALL_TAC >>
     `m <= 32` by
       (qpat_assum `evaluate_type _ _ = SOME tv` mp_tac >>
        qpat_assum `expr_type e = _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
        rpt strip_tac >> gvs[evaluate_type_def,AllCaseEqs()]) >>
     `is_word_type (expr_type e)` by simp[is_word_type_def] >>
     `post_value_type cenv e = expr_type e` by simp[] >>
     `expr_val_rel cx (BaseT (BytesT (Fixed m))) v op t` by fs[expr_post_def] >>
     `v = BytesV bs /\ LENGTH bs = m /\ m <= 32 /\
       eval_operand op t = SOME (word_of_bytes_be (PAD_RIGHT 0w 32 bs))` by
       (qpat_assum `expr_val_rel _ _ _ _ _` mp_tac >>
        qpat_assum `value_has_type tv v` mp_tac >>
        qpat_assum `evaluate_type _ _ = SOME tv` mp_tac >>
        qpat_assum `expr_type e = _` mp_tac >>
        qpat_assum `Abbrev (bs = _)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        `m <= 32 /\ tv = BaseTV (BytesT (Fixed m))` by
          gvs[evaluate_type_def,AllCaseEqs()] >>
        Cases_on `v` >>
        gvs[value_has_type_def,markerTheory.Abbrev_def,expr_val_rel_def,
          is_word_type_def,valueEncodingTheory.typed_val_to_w256_def,evaluate_type_def]) >>
     `concat_payload_capacity (expr_type e) = m` by
       simp[exprLoweringTheory.concat_payload_capacity_def] >>
     `32+k+32 <= bsz` by
       (qpat_assum `32+concat_data_bound P _ <= bsz` mp_tac >>
        qpat_assum `expr_type e = _` mp_tac >>
        qpat_assum `k <= P` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
        simp[exprLoweringTheory.concat_data_bound_def,LET_THM] >>
        rw[arithmeticTheory.MAX_DEF] >> (gvs[exprLoweringTheory.concat_data_bound_def, exprLoweringTheory.concat_payload_capacity_def, compileEnvTheory.is_bytestring_type_def, vyperASTTheory.expr_type_def, listTheory.MAP_def, arithmeticTheory.NUMERAL_DEF])) >>
     `op_taint tn1 op = {}` by fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
     qabbrev_tac `arm =
       do offset_op <- emit_op MLOAD [Var ov];
          dst <- emit_op ADD [Var dv;offset_op];
          emit_void MSTORE [dst;op];
          new_offset <- emit_op ADD [offset_op;Lit (n2w m)];
          emit_void MSTORE [Var ov;new_offset]
       od` >>
     `arm sc = ((),s2) /\ arm shadow_sc = ((),s2')` by simp[Abbr `arm`] >>
     `!st. ci_mono st (SND (arm st))` by
       (simp[Abbr `arm`,comp_ignore_bind_def] >> gen_tac >>
        rpt (irule ci_mono_bind >> simp[ci_mono_emit_op,ci_mono_emit_void] >> rpt gen_tac)) >>
     `ci_mono sc s2 /\ ci_mono shadow_sc s2'` by metis_tac[pairTheory.SND] >>
     `ci_mono s2 sb /\ ci_mono s2' shadow_sb` by metis_tac[pairTheory.SND] >>
     `cs_extends sa sc /\ cs_extends sc s2 /\ cs_extends s2 sb /\
      cs_extends shadow_sa shadow_sc /\ cs_extends shadow_sc s2' /\
      cs_extends s2' shadow_sb` by
       (fs[ci_mono_def] >> metis_tac[cj 2 compile_expr_grows]) >>
     `fn_has_code sc s2 func /\ fn_has_code s2 sb func /\
      fn_has_code s2' shadow_sb shadow_func` by
       metis_tac[fragExecTheory.fn_has_code_mid,fragExecTheory.fn_has_code_split,cs_extends_trans] >>
     `gas_shadow_compiles arm arm` by
       (simp[Abbr `arm`,comp_ignore_bind_def] >>
        rpt (irule gas_shadow_compiles_bind >>
          simp[gas_shadow_compiles_emit_op,gas_shadow_compiles_emit_void] >> rpt gen_tac)) >>
     `gas_shadow_state s2 s2'` by
       (qpat_assum `gas_shadow_compiles arm arm` mp_tac >>
        rewrite_tac[gas_shadow_compiles_def] >>
        disch_then (qspecl_then [`sc`,`shadow_sc`] mp_tac) >> simp[]) >>
     `lookup_var ov t = SOME (n2w (w2n ow))` by simp[] >>
     simp[Abbr `arm`] >>
     drule_all (INST_TYPE [alpha |-> ``:256``] concat_head_fixed_uniform) >>
     disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`d`,`cx`,`PG`] strip_assume_tac) >>
     qexistsl_tac [`s2`,`s2'`,`u`,`G'`,`tn'`] >>
     simp[] >> conj_tac >- simp[exprLoweringTheory.concat_payload_capacity_def] >>
     qpat_x_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _` mp_tac >> simp[]) >>
  pop_assum strip_assume_tac >>
  `!name lb lsz. local_region cenv ee.scopes t name lb lsz <=>
     local_region cenv es.scopes s name lb lsz` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> first_assum irule >> first_assum ACCEPT_TAC) >>
     strip_tac >> drule_all local_region_frame_fwd >> simp[]) >>
  `ghost_kept_at lo cenv ee sc G1 tn1 t G2 tn2` by
    (first_assum irule >> simp[ghost_kept_at_refl]) >>
  `ghost_kept_at lo cenv es sa G tn s G2 tn2` by
    (irule ghost_kept_at_trans >>
     qexistsl_tac [`G1`,`ee`,`t`,`sc`,`tn1`] >> fs[ci_mono_def] >>
     metis_tac[expr_post_def]) >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at sc z /\ not_fresh_at s2 z` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists `sa` >> fs[ci_mono_def] >> decide_tac) >>
  `!z. not_fresh_at sc z ==> lookup_var z u = lookup_var z t` by
    (simp[lookup_var_def] >> metis_tac[]) >>
  `!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==>
     lookup_var z u = SOME w` by metis_tac[] >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists `sc` >> fs[ci_mono_def]) >>
  `return_buf_frame d cenv s2 u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`sa`] >> fs[ci_mono_def]) >>
  `!name lb lsz. local_region cenv ee.scopes u name lb lsz <=>
     local_region cenv ee.scopes t name lb lsz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     `not_fresh_at sc p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     metis_tac[]) >>
  `ptr_covers G2 tn2 dv u (bsz-32) /\ ptr_covers G2 tn2 ov u 32` by
    (conj_tac >> irule (iffRL copy_ptr_covers_transport) >>
     qexistsl_tac [`G1`,`t`,`tn1`] >> simp[] >> metis_tac[]) >>
  `mem_bytes_at (B+32) k t.vs_memory = mem_bytes_at (B+32) k s.vs_memory` by
    (qpat_assum `mem_bytes_at B bsz t.vs_memory = _`
       (mp_then Any mp_tac valueEncodingPropsTheory.mem_bytes_at_translated_window) >>
     disch_then (qspecl_then [`32`,`k`] mp_tac) >> simp[]) >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z)` by
    metis_tac[not_fresh_at_mono,ci_mono_def] >>
  `binst.inst_id < s2.cs_next_id /\ oinst.inst_id < s2.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (fs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  `k+LENGTH bs <= P+concat_payload_capacity (expr_type e) /\
   32+(P+concat_payload_capacity (expr_type e))+
     SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz` by
    (qpat_assum `k <= P` mp_tac >>
     qpat_assum `LENGTH bs <= concat_payload_capacity (expr_type e)` mp_tac >>
     qpat_assum `32+P+SUM _ <= bsz` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> decide_tac) >>
  `32+concat_data_bound (P+concat_payload_capacity (expr_type e))
     (MAP expr_type args) <= bsz` by
    (qpat_assum `32+concat_data_bound P _ <= bsz` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringTheory.concat_data_bound_def,LET_THM] >>
     rw[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `not_fresh_at s2 dv /\ not_fresh_at s2 ov /\
   lookup_var dv u = SOME (n2w (B+32)) /\ lookup_var ov u = SOME ow` by
    metis_tac[not_fresh_at_mono,ci_mono_def] >>
  `!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
     mem_bytes_at lb lsz u.vs_memory = mem_bytes_at lb lsz t.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!name lb lsz. local_region cenv es.scopes s name lb lsz ==> _`
       drule >> strip_tac >>
     qpat_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _`
       (qspecl_then [`lb`,`lsz`] mp_tac) >> simp[]) >>
  `locals_kept cenv es ee s u` by
    (irule locals_kept_regions_tail >> qexists `t` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!aid p n. FLOOKUP s.vs_allocas aid = SOME (p,n) /\
     aid < sa.cs_next_id /\ (p+n <= B \/ B+bsz <= p) /\
     (p+n <= w2n ow \/ w2n ow+64 <= p) /\
     (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
       p+n <= lb \/ lb+lsz <= p) ==>
     mem_bytes_at p n u.vs_memory = mem_bytes_at p n s.vs_memory` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     irule EQ_TRANS >> qexists `mem_bytes_at p n t.vs_memory` >> conj_tac
     >- (qpat_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _`
           (qspecl_then [`p`,`n`] mp_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
     qpat_assum `!aid off sz. _ ==> mem_bytes_at off sz t.vs_memory = _`
       (qspecl_then [`aid`,`p`,`n`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     simp_tac bool_ss []) >>
  `!i. B+32 <= i /\ i < B+32+k ==> i NOTIN tn1.t_mem` by
    (rpt strip_tac >> `B <= i /\ i < B+bsz` by decide_tac >> metis_tac[]) >>
  `!i. B+32 <= i /\ i < B+32+k+LENGTH bs ==> i NOTIN tn2.t_mem` by
    (rpt strip_tac >> Cases_on `i < B+32+k`
     >- (fs[SUBSET_DEF] >> metis_tac[]) >>
     qpat_assum `!i. B+32+k <= i /\ _ ==> i NOTIN tn2.t_mem`
       (qspec_then `i` mp_tac) >>
     (impl_tac >- decide_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G1,tn1) [] (OK u,G2,tn2) /\
     stmt_state_rel H ctx func cenv cx ee u /\
     storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 u` by
    (qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) [] (OK u,G2,tn2)` mp_tac >>
     qpat_assum `!H. stmt_state_rel H ctx func cenv cx ee t ==> _` mp_tac >>
     qpat_assum `!D. ghost_inv_at D lo d cenv cx ee G1 tn1 t ==> _` mp_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >>
     strip_tac >> fs[expr_post_def] >>
     qpat_x_assum `!H. stmt_state_rel H ctx func cenv cx ee t ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `~expr_has_effect e ==>
    (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
      mem_bytes_at lb lsz u.vs_memory = mem_bytes_at lb lsz s.vs_memory) /\
    (!p n. (p+n <= B \/ B+bsz <= p) /\
      (p+n <= w2n ow \/ w2n ow+64 <= p) /\
      (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        sa.cs_next_id <= inst.inst_id /\
        FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
        regions_disjoint p n b sz) ==>
      mem_bytes_at p n u.vs_memory = mem_bytes_at p n s.vs_memory)` by
    (qpat_assum `~expr_has_effect e ==> pure_frame cenv func es sa s t` mp_tac >>
     qpat_assum `!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
       mem_bytes_at lb lsz u.vs_memory = _` mp_tac >>
     qpat_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _` mp_tac >>
     qpat_assum `u.vs_allocas = t.vs_allocas` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[pure_frame_def,arithmeticTheory.ADD_COMM]) >>
  `B+bsz <= u.vs_alloca_next /\ w2n ow+64 <= u.vs_alloca_next` by
    (qpat_assum `u.vs_alloca_next = t.vs_alloca_next` (fn th => rewrite_tac[th]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `FLOOKUP u.vs_allocas binst.inst_id = SOME (B,bsz) /\
   FLOOKUP u.vs_allocas oinst.inst_id = SOME (w2n ow,64)` by
    (qpat_assum `u.vs_allocas = t.vs_allocas` (fn th => rewrite_tac[th]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!name lb lsz. local_region cenv ee.scopes u name lb lsz ==>
     (B+bsz <= lb \/ lb+lsz <= B) /\
     (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)` by
    (qpat_assum `!name lb lsz. local_region cenv ee.scopes u name lb lsz <=> _` mp_tac >>
     qpat_assum `!name lb lsz. local_region cenv ee.scopes t name lb lsz ==> _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `mem_bytes_at (B+32) (k+LENGTH bs) u.vs_memory =
     mem_bytes_at (B+32) k s.vs_memory ++ bs` by
    (qpat_assum `mem_bytes_at (B+32) (k+LENGTH bs) u.vs_memory = _`
       (fn th => rewrite_tac[th]) >>
     qpat_assum `mem_bytes_at (B+32) k t.vs_memory = _`
       (fn th => rewrite_tac[th])) >>
  `!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP u.vs_allocas aid = SOME a` by
    (qpat_assum `u.vs_allocas = t.vs_allocas` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`s2`,`shadow_s2`,`u`,`V`,`G2`,`tn2`] >>
  qpat_x_assum `Abbrev (bs = _)`
    (fn th => rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED
