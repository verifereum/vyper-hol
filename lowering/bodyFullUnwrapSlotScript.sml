(* unwrap_value's storage and transient aggregates on one joint path: a
   fresh buffer, then one load and store or the word-copy loop. *)
Theory bodyFullUnwrapSlot
Ancestors
  exprPtrUnwrapMarked exprSimMemUnwrap fragGasOriginPtr fragGasSeqPtr
  bodyPtrEnvBuiltinsEdges bodyPtrDefs loweringPosts exprSimMemDefs
  exprLowering compileEnv context
  bodyFullUnwrapSlotSelectedPost bodyFullUnwrapSlotOrigin bodyFullUnwrapSlotPost
  bodyFullUnwrapRun fragGasOriginPtrDead exprLoweringProps localPtrsProps
  exprSimProps loweringStateRelDefs ptrDiscipline finite_map pred_set
  vyperStorageFootprint exprSimFieldLayout valueEncodingProps words
  exprPtrUnwrapStorage exprSimMemorySource freshWrites
  bodyFullUnwrapSlotFrame exprPtrUnwrapAllocSemantic exprSimCopy
  exprSimPtrTopLevelStorageCopy exprSimStorageCopy venomState venomExecSemantics
  exprSimAbiEncodeMemoryLength arithmetic slotCopyExecution emitHelper
  assignTuplePtrAlloc bodyPtrBytestringBuiltinsAllocation bodyPtrMakeArrayExternalCaller
Libs pureFrameLib

(* The low materializer selects the execution and the ghosts together.  A
   caller may ask it to retain an extra property of those physical states. *)
Definition unwrap_slot_origin_side_producer_def:
  unwrap_slot_origin_side_producer ctx func lo explicit PG Side <=>
    !loc src nb n ctor imm sa op sb
     (H : (bool # bytes32 # type_value) list # num list) cenv cx es s tn p.
      (loc = LocStorage \/ loc = LocTransient) /\
      compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
      fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
      nb < dimword (:256) /\ 32*n <= nb /\ n < 2**256 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
      allocas_from lo s /\ lo <= s.vs_alloca_next /\
      alloca_history func s /\ fn_inst_ids_distinct func /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand src s = SOME p /\ op_taint tn src = {} ==>
      !G. ?root d a G0 tn0 Gf tnf t sm buf u.
        fn_has_code sa sm func /\ fn_has_code sm sb func /\
        u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
        step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
        a = u with vs_inst_idx := SUC s.vs_inst_idx /\
        G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
        tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
        op = Var root /\ d = n2w (buffer_allocation_base s sa.cs_next_id) /\
        compile_alloc_buffer nb sa = (buf,sm) /\ buf.buf_operand = Var root /\
        gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,G0,tn0) /\
        gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG) (a,G0,tn0) [] (OK t,Gf,tnf) /\
        gas_origin_ptr_path (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
        (n <> 1 ==> ?cv ds.
          toplevel_copy_inv cv ds root src loc p (w2n d) n a G0 tn0 n Gf tnf t /\
          (!x. not_fresh_at sm x ==> ~MEM x ds) /\ ~t.vs_halted) /\
        (n = 1 ==>
          t = (mstore (w2n d) (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p)
            (update_var (STRING #"%" (toString sm.cs_next_var))
              (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p) a)
                with vs_inst_idx := LENGTH sb.cs_current_insts) /\
          tnf.t_mem = (tn0.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32}) UNION
            {w2n d+k | k IN key_taint (if loc=LocStorage then tn0.t_stor else tn0.t_trans) p} /\
          tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm /\
          (!x. x <> STRING #"%" (toString sm.cs_next_var) ==>
             FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x))) /\
        Side sa sb s t
End

Theorem unwrap_slot_origin_side_producer_true:
  unwrap_slot_origin_side_producer ctx func lo explicit PG (\_ _ _ _. T)
Proof
  pure_rewrite_tac[unwrap_slot_origin_side_producer_def, AND_CLAUSES] >>
  rpt gen_tac >>
  disch_then (fn pre =>
    qx_gen_tac `g` >>
    mp_tac (Q.INST [`G` |-> `g`]
      (MATCH_MP unwrap_ensure_slot_origin_execution pre))) >>
  simp_tac bool_ss []
QED

(* A storage or transient aggregate is copied into a fresh buffer. *)
Theorem unwrap_slot_copy_origin_ptr_no_dead_side:
  unwrap_slot_origin_side_producer ctx func lo explicit PG Side /\
  vv = LocatedValue t p /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
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
    Side sb sc s z /\ pure_frame cenv func ee sb s z /\
    read_result cx tv ee = (INL v, ee) /\
    vv_own cenv cx (post_value_type cenv e) sb sc ee (Value v)
      (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z /\
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,
       lo, explicit, ctx, func, PG) (s,G,tn) [] (OK z,G',tn') /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sb sc ee tv
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
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  match_mp_tac (Q.INST [`exit_ok` |-> `Side sb sc s`] unwrap_slot_copy_post_with_exit) >>
  rpt gen_tac >>
  qpat_x_assum `unwrap_slot_origin_side_producer _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [unwrap_slot_origin_side_producer_def]) >>
  disch_then (fn supplier => disch_then (fn pre =>
    mp_tac (Q.SPEC `G` (MATCH_MP (SPEC_ALL supplier) pre)))) >>
  simp_tac bool_ss []
QED

Theorem unwrap_slot_copy_origin_ptr_no_dead_pure:
  vv = LocatedValue t p /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
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
    pure_frame cenv func ee sb s z /\
    read_result cx tv ee = (INL v, ee) /\
    vv_own cenv cx (post_value_type cenv e) sb sc ee (Value v)
      (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z /\
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,
       lo, explicit, ctx, func, PG) (s,G,tn) [] (OK z,G',tn') /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sb sc ee tv
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
Proof
  MATCH_ACCEPT_TAC (SIMP_RULE bool_ss [unwrap_slot_origin_side_producer_true]
    (Q.INST [`Side` |-> `\_ _ _ _. T`] (SPEC_ALL unwrap_slot_copy_origin_ptr_no_dead_side)))
QED

Theorem unwrap_slot_copy_origin_ptr_no_dead =
  pureFrameLib.drop_frame unwrap_slot_copy_origin_ptr_no_dead_pure


Theorem unwrap_slot_copy_origin_ptr:
  vv = LocatedValue t p /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
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
    vv_own cenv cx (post_value_type cenv e) sb sc ee (Value v)
      (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sb sc ee tv
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
Proof
  disch_then (mp_tac o MATCH_MP unwrap_slot_copy_origin_ptr_no_dead) >>
  disch_then (qx_choose_then `v` (qx_choose_then `z`
    (qx_choose_then `G'` (qx_choose_then `tn'`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac))))) >>
  qexistsl [`v`, `z`, `G'`, `tn'`] >> simp[]
QED
