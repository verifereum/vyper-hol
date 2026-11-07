(*
 * unwrap_value's copy of an aggregate into memory (#636)
 *
 * unwrap_value lowers an aggregate that sits in storage, transient
 * storage or code by allocating a buffer of type_memory_bytes bytes at
 * instruction id sm.cs_next_id and copying the value's words into it
 * (compile_ensure_in_memory).  These lemmas take vv_post, which says the
 * source location holds the value, to expr_post, which says the buffer
 * does.
 *
 * Each copy needs the buffer to be the value's memory size, and that size
 * to fit below Python's allocation limit, 2 ** 64 bytes.  For storage and
 * transient storage both are premises; in code, immutable_holds already
 * bounds the size, so only the equality is.
 *
 * TOP-LEVEL:
 *   unwrap_storage_copy_sim      — storage and transient storage
 *   unwrap_runtime_code_copy_sim — code, at runtime (DLOAD)
 *   unwrap_ctor_code_copy_sim    — code, in the constructor
 *)

Theory exprSimCopy
Ancestors
  valueEncodingProps
  exprSimProps
  loweringPosts
  exprSimAlloc exprSimOps
  list finite_map
   exprLowering compileEnv context vyperAST vyperInterpreter
  vyperState valueEncoding
  fragExec localPtrsProps loweringSlice exprLoweringProps emitHelperProps
  exprSimStorageCopy immutableCopyExecution storageDecodeMemory
  vyperTypeStatePreservation vyperTypeValues valueEncodingTyping vyperStorageBackend
  venomInst venomExecSemantics venomState

Theorem copy_buffer_mstore_locals_kept:
  !cenv es s0 s a (w:bytes32) b sz.
    locals_kept cenv es s0 s /\ b <= a /\ a + 32 <= b + sz /\
    (!name lb len. local_region cenv es.scopes s0 name lb len ==>
       b + sz <= lb \/ lb + len <= b) ==>
    locals_kept cenv es s0 (mstore a w s)
Proof
  cheat
QED

Theorem copy_buffer_local_region_frame:
  !cenv st s t scopes name b sz.
    local_ptrs_reserved cenv st /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) ==>
    (local_region cenv scopes t name b sz <=>
     local_region cenv scopes s name b sz)
Proof
  cheat
QED

(* Successful old pointer lookups suffice in this direction: vv_post does
   not require the initial machine to contain every live local pointer. *)
Theorem copy_buffer_original_local_separation:
  !ctx func cenv cx e es sa sm s0 es' tv vv s b sz.
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
    (!name lb len. local_region cenv es'.scopes s name lb len ==>
       b + sz <= lb \/ lb + len <= b) ==>
    (!name lb len. local_region cenv es.scopes s0 name lb len ==>
       b + sz <= lb \/ lb + len <= b)
Proof
  cheat
QED

Theorem copy_buffer_locals_kept_frame:
  !cenv es0 s0 s t b sz.
    locals_kept cenv es0 s0 s /\
    (!name lb len. local_region cenv es0.scopes s0 name lb len ==>
       b + sz <= lb \/ lb + len <= b) /\
    (!off len. off + len <= b \/ b + sz <= off ==>
       mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) ==>
    locals_kept cenv es0 s0 t
Proof
  cheat
QED

Theorem copy_buffer_state_rel_frame:
  !ctx func cenv cx es st s t inst b sz.
    stmt_state_rel ctx func cenv cx es s /\
    local_ptrs_reserved cenv st /\ copy_static t = copy_static s /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    (!name lb len. local_region cenv es.scopes s name lb len ==>
       b + sz <= lb \/ lb + len <= b) /\
    (!off len. off + len <= b \/ b + sz <= off ==>
       mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) ==>
    stmt_state_rel ctx func cenv cx es t
Proof
  cheat
QED

(* A copied buffer may be allocated after the expression starts. *)
Theorem copy_buffer_expr_post_physical[local]:
  !ctx func cenv cx e es sa sb s0 es' s v tv op w aid sz.
    ~is_word_type (post_value_type cenv e) /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tv /\
    val_wf tv v /\ val_in_memory tv v (w2n w) s.vs_memory /\
    stmt_state_rel ctx func cenv cx es' s /\
    eval_operand op s = SOME w /\
    FLOOKUP s.vs_allocas aid = SOME (w2n w,sz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    val_footprint tv v <= sz /\
    (!name b len. local_region cenv es'.scopes s name b len ==>
       w2n w + sz <= b \/ b + len <= w2n w) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
       lookup_var x s = SOME w) /\
    (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
       FLOOKUP s.vs_allocas id = SOME entry) /\
    (!id off len. FLOOKUP s0.vs_allocas id = SOME (off,len) /\
       id < sa.cs_next_id /\
       (!name b k. local_region cenv es.scopes s0 name b k ==>
          off + len <= b \/ b + k <= off) ==>
       mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory) /\
    locals_kept cenv es s0 s ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op s
Proof
  cheat
QED

Theorem copy_buffer_expr_post:
  !ctx func cenv cx e es sa sb s0 es' s v tv op w aid sz.
    post_value_type cenv e = expr_type e /\
    ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    val_wf tv v /\ val_in_memory tv v (w2n w) s.vs_memory /\
    stmt_state_rel ctx func cenv cx es' s /\
    eval_operand op s = SOME w /\
    FLOOKUP s.vs_allocas aid = SOME (w2n w,sz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    val_footprint tv v <= sz /\
    (!name b len. local_region cenv es'.scopes s name b len ==>
       w2n w + sz <= b \/ b + len <= w2n w) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
       lookup_var x s = SOME w) /\
    (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
       FLOOKUP s.vs_allocas id = SOME entry) /\
    (!id off len. FLOOKUP s0.vs_allocas id = SOME (off,len) /\
       id < sa.cs_next_id /\
       (!name b k. local_region cenv es.scopes s0 name b k ==>
          off + len <= b \/ b + k <= off) ==>
       mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory) /\
    locals_kept cenv es s0 s ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op s
Proof
  cheat
QED

(* Common semantic boundary for an allocation followed by either copy. *)
Theorem copy_buffer_post_transport_physical[local]:
  !ctx func cenv cx e es sa sm mid sb s0 es' v vv s u z tv op w sz inst.
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sb.cs_next_id /\
    stmt_state_rel ctx func cenv cx es' u /\
    u.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sm.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region cenv es'.scopes u name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sm.cs_next_id /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off + len <= w2n w \/ w2n w + sz <= off ==>
       mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    ~is_word_type (post_value_type cenv e) /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tv /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= sz /\ eval_operand op z = SOME w ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op z
Proof
  cheat
QED
Theorem copy_buffer_post_transport:
  !ctx func cenv cx e es sa sm mid sb s0 es' v vv s u z tv op w sz inst.
    post_value_type cenv e = expr_type e /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sb.cs_next_id /\
    stmt_state_rel ctx func cenv cx es' u /\
    u.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sm.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region cenv es'.scopes u name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sm.cs_next_id /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off + len <= w2n w \/ w2n w + sz <= off ==>
       mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= sz /\ eval_operand op z = SOME w ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op z
Proof
  cheat
QED


(* A copy of the slots a read of tv at w covers holds the decoded value's
   live bytes, wherever the source agrees with the slots on that range. *)
Theorem copied_storage_range_memory[local]:
  !st rt w tv dst mem.
    storage_range_agree st rt w tv /\
    (!i. i < type_slot_size tv ==>
      mem_word_at (dst + 32 * i) mem = lookup_storage (w + n2w i) rt) ==>
    storage_live_memory st (w2n w) tv dst mem
Proof
  cheat
QED

Theorem copy_buffer_storage_contents:
  !ctx func cenv cx es u t v a tr tv b z.
    stmt_state_rel ctx func cenv cx es u /\
    storage_holds cx tr t (Value v) a es u /\
    evaluate_type (get_tenv cx) t = SOME tv /\
    copy_prefix (if tr then LocTransient else LocStorage)
      a b (type_slot_size tv) u (type_slot_size tv) z ==>
    val_wf tv v /\ val_in_memory tv v b z.vs_memory /\
    val_footprint tv v <= type_memory_size tv
Proof
  cheat
QED

(* An aggregate in storage or transient storage: SLOAD or TLOAD and an
   MSTORE for one word, a word-copy loop from slot i to buffer word i
   otherwise. *)
Theorem storage_copy_suffix_value_frag:
  !ctx func cenv cx es u t v a tv loc src dst n mid sb result w R.
    (loc = LocStorage \/ loc = LocTransient) /\
    (if n = 1 then
       do value <- emitHelper$emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
          emitHelper$emit_void MSTORE [dst; value] od
     else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
      mid = (result,sb) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at mid x) /\
    stmt_state_rel ctx func cenv cx es u /\
    storage_holds cx (loc = LocTransient) t (Value v) a es u /\
    evaluate_type (get_tenv cx) t = SOME tv /\ n = type_slot_size tv /\
    eval_operand src u = SOME a /\ eval_operand dst u = SOME w /\
    n < 2**256 /\ w2n w + 32*n < 2**256 ==>
    frag_exec ctx mid sb (\z. z = u)
      (\z. copy_static z = copy_static u /\
         (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
         LENGTH u.vs_memory <= LENGTH z.vs_memory /\
         (!off len. off+len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
           mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
         val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
         val_footprint tv v <= type_memory_size tv /\ eval_operand dst z = SOME w) R
Proof
  cheat
QED

Theorem storage_copy_suffix_ci_mono:
  !loc src dst n sa u sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    (if n = 1 then
       do v <- emitHelper$emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
          emitHelper$emit_void MSTORE [dst; v] od
     else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
      sa = (u,sb) ==>
    ci_mono sa sb
Proof
  cheat
QED

Theorem unwrap_storage_copy_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED


Theorem immutable_holds_data:
  !func cenv cx es s t tv w ctx.
    stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
    immutable_holds cenv cx t tv w es s' ==>
    ?tvt v. evaluate_type (get_tenv cx) t = SOME tvt /\
            read_result cx tv es = (INL v, es) /\
            val_in_memory tvt v (w2n w) s.vs_data_section
Proof
  cheat
QED

Theorem immutable_holds_bounds:
  immutable_holds cenv cx t (Value v) a es s /\
  evaluate_type (get_tenv cx) t = SOME tv ==>
  val_wf tv v /\ w2n a + type_memory_size tv < dimword (:256)
Proof
  cheat
QED

Theorem immutable_holds_memory:
  stmt_state_rel ctx func cenv cx es uu /\ cenv.ce_is_ctor /\
  immutable_holds cenv cx t (Value v) a es uu /\
  evaluate_type (get_tenv cx) t = SOME tv ==>
  val_in_memory tv v (w2n a) uu.vs_memory
Proof
  cheat
QED

Theorem immutable_holds_alloca_disjoint:
  stmt_state_rel ctx func cenv cx es uu /\ cenv.ce_is_ctor /\
  immutable_holds cenv cx t (Value v) a es uu /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP uu.vs_allocas inst.inst_id = SOME (dst,sz) ==>
  regions_disjoint (w2n a) (type_memory_size tv) dst sz
Proof
  cheat
QED

Theorem copy_runtime_contents:
  !ctx func cenv cx es u t v a tv w z s.
    stmt_state_rel ctx func cenv cx es u /\ ~cenv.ce_is_ctor /\
    immutable_holds cenv cx t (Value v) a es s /\
    evaluate_type (get_tenv cx) t = SOME tv /\
    w2n w + type_memory_size tv < dimword (:256) /\
    z.vs_memory = (immutable_transfers F F a w (type_slot_size tv) 0 u).vs_memory ==>
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv
Proof
  cheat
QED

Definition copy_old_operand_def:
  copy_old_operand st op <=> !x. op = Var x ==> not_fresh_at st x
End

Definition copy_runtime_frame_def:
  copy_runtime_frame st s st' s' <=>
    run_inst_seq (emitted_insts st st') s = OK s' /\
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
    same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var /\
    copy_static s' = copy_static s /\
    (!x. not_fresh_at st x ==> lookup_var x s' = lookup_var x s)
End

Theorem copy_old_operand_mono:
  st.cs_next_var <= st'.cs_next_var /\ copy_old_operand st op ==>
  copy_old_operand st' op
Proof
  cheat
QED

Theorem copy_runtime_frame_refl:
  copy_runtime_frame st s st s
Proof
  cheat
QED

Theorem copy_runtime_frame_operand:
  copy_runtime_frame st s st' s' /\ copy_old_operand st op ==>
  eval_operand op s' = eval_operand op s
Proof
  cheat
QED

Theorem copy_runtime_frame_trans:
  copy_runtime_frame st s st1 s1 /\ copy_runtime_frame st1 s1 st2 s2 ==>
  copy_runtime_frame st s st2 s2
Proof
  cheat
QED

Theorem copy_runtime_offset:
  compile_lit_byte_offset op off st = (r,st') /\
  copy_old_operand st op /\ eval_operand op s = SOME a ==>
  ?s'. copy_runtime_frame st s st' s' /\
    eval_operand r s' = SOME (a + n2w off) /\
    copy_old_operand st' r /\ s'.vs_memory = s.vs_memory
Proof
  cheat
QED

Theorem copy_runtime_load:
  compile_imm_load_word F imm op st = (r,st') /\
  copy_old_operand st op /\ eval_operand op s = SOME a ==>
  ?s'. copy_runtime_frame st s st' s' /\ copy_old_operand st' r /\
    eval_operand r s' = SOME (immutable_copy_read F a s) /\
    s'.vs_memory = s.vs_memory
Proof
  cheat
QED

Theorem copy_ctor_load:
  compile_imm_load_word T imm op st = (r,st') /\
  copy_old_operand st op /\ eval_operand op ss = SOME a /\
  (!region. imm = SOME region ==> eval_operand region ss = SOME 0w /\
    copy_old_operand st region) ==>
  ?zz. copy_runtime_frame st ss st' zz /\ copy_old_operand st' r /\
    eval_operand r zz = SOME (immutable_copy_read T a ss) /\
    zz.vs_memory = ss.vs_memory
Proof
  cheat
QED

Theorem copy_ctor_load_shape:
  compile_imm_load_word T imm op st = (r,st') ==>
  st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
  same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var /\
  EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; MSTORE]) (emitted_insts st st')
Proof
  cheat
QED

Theorem copy_runtime_store:
  emitHelper$emit_void MSTORE [dst;value] st = ((),st') /\
  copy_old_operand st dst /\ copy_old_operand st value /\
  eval_operand dst s = SOME b /\ eval_operand value s = SOME w ==>
  copy_runtime_frame st s st' (mstore (w2n b) w s)
Proof
  cheat
QED

Theorem copy_runtime_one:
  immutable_copy_one F imm src dst off st = ((),st') /\
  copy_old_operand st src /\ copy_old_operand st dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b ==>
  ?s'. copy_runtime_frame st s st' s' /\
    s'.vs_memory = (immutable_word_transfer F F a b off s).vs_memory
Proof
  cheat
QED

Theorem copy_ctor_one:
  immutable_copy_one T imm src dst off st = ((),st') /\
  copy_old_operand st src /\ copy_old_operand st dst /\
  eval_operand src ss = SOME a /\ eval_operand dst ss = SOME b /\
  (!region. imm = SOME region ==> eval_operand region ss = SOME 0w /\
    copy_old_operand st region) ==>
  ?zz. copy_runtime_frame st ss st' zz /\
    zz.vs_memory = (immutable_word_transfer F T a b off ss).vs_memory
Proof
  cheat
QED

Theorem copy_ctor_transfers_cong[local]:
  !n off s1 s2.
  s1.vs_memory = s2.vs_memory ==>
  (immutable_transfers F T a b n off s1).vs_memory =
  (immutable_transfers F T a b n off s2).vs_memory
Proof
  cheat
QED

Theorem copy_runtime_transfers_cong:
  !n off s1 s2.
  s1.vs_memory = s2.vs_memory /\ s1.vs_data_section = s2.vs_data_section ==>
  (immutable_transfers F F a b n off s1).vs_memory =
  (immutable_transfers F F a b n off s2).vs_memory
Proof
  cheat
QED

Theorem copy_runtime_run:
  !n off st st' s a b.
  compile_imm_copy_to_memory F imm src dst n off st = ((),st') /\
  copy_old_operand st src /\ copy_old_operand st dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b ==>
  ?s'. copy_runtime_frame st s st' s' /\
    s'.vs_memory = (immutable_transfers F F a b n off s).vs_memory
Proof
  cheat
QED

Theorem code_offset_insts:
  !op off st r st'.
    compile_lit_byte_offset op off st = (r,st') ==>
    EVERY (\i. i.inst_opcode = ADD) (emitted_insts st st')
Proof
  cheat
QED

Theorem code_copy_insts:
  !n imm src dst off sa sb.
    compile_imm_copy_to_memory F imm src dst n off sa = ((),sb) ==>
    same_blocks sa sb /\
    ?is. sb.cs_current_insts = sa.cs_current_insts ++ is /\
         EVERY (\i. MEM i.inst_opcode [ADD; DLOAD; MSTORE]) is
Proof
  cheat
QED

Theorem copy_ctor_run:
  !n off st st' ss a b.
  compile_imm_copy_to_memory T imm src dst n off st = ((),st') /\
  copy_old_operand st src /\ copy_old_operand st dst /\
  eval_operand src ss = SOME a /\ eval_operand dst ss = SOME b /\
  (!region. imm = SOME region ==> eval_operand region ss = SOME 0w /\
    copy_old_operand st region) ==>
  ?zz. copy_runtime_frame st ss st' zz /\
    zz.vs_memory = (immutable_transfers F T a b n off ss).vs_memory
Proof
  cheat
QED

Theorem code_ctor_copy_insts:
  !n imm src dst off sa sb.
    compile_imm_copy_to_memory T imm src dst n off sa = ((),sb) ==>
    same_blocks sa sb /\
    ?is. sb.cs_current_insts = sa.cs_current_insts ++ is /\
         EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; MSTORE]) is
Proof
  cheat
QED

Theorem copy_runtime_frag:
  !ctx imm src dst n off st st' s a b R.
  compile_imm_copy_to_memory F imm src dst n off st = ((),st') /\
  copy_old_operand st src /\ copy_old_operand st dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b ==>
  frag_exec ctx st st' (\z. z = s)
    (\z. z.vs_memory = (immutable_transfers F F a b n off s).vs_memory /\
         copy_static z = copy_static s /\
         (!x. not_fresh_at st x ==> lookup_var x z = lookup_var x s)) R
Proof
  cheat
QED

Theorem copy_runtime_zero_frag:
  !ctx imm src dst mid sb s R.
    compile_imm_copy_to_memory F imm src dst 0 0 mid = ((),sb) ==>
    frag_exec ctx mid sb (\z. z = s) (\z. z = s) R
Proof
  cheat
QED

Theorem copy_runtime_one_run:
  !imm src dst mid sb s a b.
    compile_imm_copy_to_memory F imm src dst (SUC 0) 0 mid = ((),sb) /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    (!x. dst = Var x ==> not_fresh_at mid x) ==>
    ?z. run_inst_seq (emitted_insts mid sb) s = OK z /\
      z.vs_memory = (mstore (w2n b) (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s).vs_memory /\
      copy_static z = copy_static s /\
      (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x s)
Proof
  cheat
QED

Theorem copy_ctor_frag:
  !ctx imm src dst n off st st' ss a b R.
    compile_imm_copy_to_memory T imm src dst n off st = ((),st') /\
    copy_old_operand st src /\ copy_old_operand st dst /\
    eval_operand src ss = SOME a /\ eval_operand dst ss = SOME b /\
    (!region. imm = SOME region ==> eval_operand region ss = SOME 0w /\
      copy_old_operand st region) ==>
    frag_exec ctx st st' (\z. z = ss)
      (\z. z.vs_memory = (immutable_transfers F T a b n off ss).vs_memory /\
        copy_static z = copy_static ss /\
        (!x. not_fresh_at st x ==> lookup_var x z = lookup_var x ss)) R
Proof
  cheat
QED

Theorem copy_ctor_memory_snapshot:
  w2n a + type_memory_size tv < dimword (:256) /\
  w2n w + type_memory_size tv < dimword (:256) /\
  regions_disjoint (w2n a) (type_memory_size tv) (w2n w) (type_memory_size tv) /\
  type_slot_size tv <> 0 ==>
  (immutable_transfers F T a w (type_slot_size tv) 0 uu).vs_memory =
  (write_memory_with_expansion (w2n w)
    (mem_bytes_at (w2n a) (type_memory_size tv) uu.vs_memory) uu).vs_memory
Proof
  cheat
QED

Theorem copy_ctor_contents:
  stmt_state_rel ctx func cenv cx es uu /\ cenv.ce_is_ctor /\
  immutable_holds cenv cx t (Value v) a es uu /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  w2n w + type_memory_size tv < dimword (:256) /\
  regions_disjoint (w2n a) (type_memory_size tv) (w2n w) (type_memory_size tv) /\
  zz.vs_memory = (immutable_transfers F T a w (type_slot_size tv) 0 uu).vs_memory ==>
  val_wf tv v /\ val_in_memory tv v (w2n w) zz.vs_memory /\
  val_footprint tv v <= type_memory_size tv /\
  LENGTH uu.vs_memory <= LENGTH zz.vs_memory /\
  (!off len. off + len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
    mem_bytes_at off len zz.vs_memory = mem_bytes_at off len uu.vs_memory)
Proof
  cheat
QED

(* An aggregate in code, at runtime: a DLOAD and an MSTORE per word of the
   buffer.  immutable_holds puts the value inside the data section, so the
   size bound needs no premise. *)
Theorem unwrap_runtime_code_copy_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED




(* An aggregate in code, in the constructor, given that the immutables
   region base is zero: ALLOCA a buffer, then per word ADD the base and
   ILOAD (an MLOAD) from the staged immutables region in memory, and
   MSTORE into the buffer. stmt_state_rel supplies the zero base and
   local_ptrs_reserved protects it from fresh allocation. *)
Theorem unwrap_ctor_code_copy_base_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s /\ immutable_base_zero cenv s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED




(* An aggregate in code, in the constructor: stmt_state_rel supplies the
   zero base and local_ptrs_reserved the base variable's reservation, the
   two extra premises of unwrap_ctor_code_copy_base_sim. *)
Theorem unwrap_ctor_code_copy_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

Theorem runtime_code_copy_memory_frame:
  w2n a + type_memory_size tv < dimword (:256) /\
  w2n w + type_memory_size tv < dimword (:256) /\
  z.vs_memory = (immutable_transfers F F a w (type_slot_size tv) 0 u).vs_memory ==>
  LENGTH u.vs_memory <= LENGTH z.vs_memory /\
  (!off len. off + len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory)
Proof
  cheat
QED

Theorem runtime_code_copy_alloc_run:
  compile_alloc_buffer sz sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ sz < dimword (:256) /\
  eval_operand src s = SOME a /\
  (!x. src = Var x ==> not_fresh_at sm x) ==>
  ?u w. run_inst_seq (emitted_insts sm mid) s = OK u /\
    eval_operand src u = SOME a /\
    stmt_state_rel ctx func cenv cx es u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ u.vs_memory = s.vs_memory /\
    sm.cs_next_id < mid.cs_next_id /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sm.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region cenv es.scopes u name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at mid p)
Proof
  cheat
QED

Theorem runtime_code_copy_run_post:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s ==>
    ?code z. same_blocks sm sb /\
      sb.cs_current_insts = sm.cs_current_insts ++ code /\
      EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE]) code /\
      run_inst_seq code s = OK z /\
      expr_post ctx func cenv cx e es sa sb s0 es' v op z
Proof
  cheat
QED





