(* Successful-head boundary: one physical endpoint for every dead-byte map. *)
Theory bodyFullBuiltinConcatHead
Ancestors
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
