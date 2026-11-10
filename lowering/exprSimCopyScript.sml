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
   exprLowering compileEnv loweringStateRelDefs context vyperAST vyperInterpreter
  vyperState valueEncoding valueEncodingDefs
  fragExec localPtrsProps loweringSlice exprLoweringProps emitHelperProps
  exprSimStorageCopy immutableCopyExecution storageDecodeMemory
  vyperTypeStatePreservation vyperTypeValues valueEncodingTyping vyperStorageBackend
  venomInst venomExecSemantics venomState

Theorem copy_buffer_mstore_locals_kept:
  !cenv es s0 s a (w:bytes32) b sz.
    locals_kept cenv es es s0 s /\ b <= a /\ a + 32 <= b + sz /\
    (!name lb len. local_region cenv es.scopes s0 name lb len ==>
       b + sz <= lb \/ lb + len <= b) ==>
    locals_kept cenv es es s0 (mstore a w s)
Proof
  rpt strip_tac >> irule locals_kept_regions_tail >>
  qexists_tac `s` >> simp[] >> rpt strip_tac >>
  irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
  qpat_x_assum `!name lb len. local_region _ _ _ _ _ _ ==> _` drule >>
  decide_tac
QED

Theorem copy_buffer_local_region_frame:
  !cenv st s t scopes name b sz.
    local_ptrs_reserved cenv st /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) ==>
    (local_region cenv scopes t name b sz <=>
     local_region cenv scopes s name b sz)
Proof
  rpt strip_tac >> simp[local_region_def] >>
  `!p. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       lookup_var p t = lookup_var p s` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  metis_tac[]
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
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!name lb len. local_region _ _ _ _ _ _ ==> _` irule >>
  qexists_tac `name` >> irule local_region_frame_fwd >>
  qexistsl_tac [`s0`, `sa`, `es.scopes`] >>
  gvs[vv_post_def]
QED

Theorem copy_buffer_locals_kept_frame:
  !cenv es0 es' s0 s t b sz.
    locals_kept cenv es0 es' s0 s /\
    (!name lb len. local_region cenv es0.scopes s0 name lb len ==>
       b + sz <= lb \/ lb + len <= b) /\
    (!off len. off + len <= b \/ b + sz <= off ==>
       mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) ==>
    locals_kept cenv es0 es' s0 t
Proof
  rpt strip_tac >> irule locals_kept_regions_tail >>
  qexists_tac `s` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  qpat_x_assum `!name lb len. local_region _ _ _ _ _ _ ==> _` drule >>
  decide_tac
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
  rpt gen_tac >> strip_tac >>
  drule copy_static_fields >> strip_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  rewrite_tac[Once stmt_state_rel_def] >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes t` by
    (irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
     simp[] >> conj_tac
     >- (rpt strip_tac >> sym_tac >>
         qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ _ = _` irule >>
         qpat_x_assum `!name lb len. local_region _ _ _ _ _ _ ==> _` drule >>
         decide_tac) >>
     conj_tac
     >- (rpt strip_tac >> first_x_assum irule >>
         gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
     conj_tac >- (rpt strip_tac >> gvs[]) >>
     gvs[state_rel_def]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >>
     simp[] >> reverse conj_tac >- gvs[state_rel_def] >>
     fs[immutable_alloca_sep_def] >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     `regions_disjoint off (type_memory_size tv) b sz` by metis_tac[] >>
     qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ _ = _` irule >>
     gvs[regions_disjoint_def] >> decide_tac) >>
  rewrite_tac[stmt_state_rel_def] >> conj_tac
  >- (irule state_rel_frame >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`es`, `s`] >> simp[] >>
      gvs[copy_static_def, venom_state_component_equality]) >>
  conj_tac >- (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  conj_tac >- (irule alloca_room_fields >> qexists_tac `s` >> simp[]) >>
  conj_tac
  >- (irule fmp_room_fields >> qexists_tac `s` >>
      simp[] >> gvs[copy_static_def, venom_state_component_equality]) >>
  conj_tac
  >- (irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
      simp[] >> rpt strip_tac >> qexists_tac `id` >> simp[] >>
      metis_tac[copy_buffer_local_region_frame]) >>
  conj_tac
  >- (irule immutable_base_zero_frame >> qexists_tac `s` >> simp[] >>
      rpt strip_tac >>
      `not_fresh_at st x` by metis_tac[local_ptrs_reserved_imm_base] >>
      simp[]) >>
  metis_tac[]
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
    locals_kept cenv es es' s0 s ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op s
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def] >>
  conj_tac
  >- (disj1_tac >> qexistsl [`aid`, `w2n w`, `sz`] >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!name b len. local_region _ es'.scopes _ _ _ _ ==> _` drule >>
      decide_tac) >>
  conj_tac
  >- (strip_tac >> simp[expr_val_own_def] >>
      disj1_tac >> qexistsl [`aid`, `w2n w`, `sz`] >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!name b len. local_region _ es'.scopes _ _ _ _ ==> _` drule >>
      decide_tac) >>
  metis_tac[]
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
    locals_kept cenv es es' s0 s ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op s
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `post_value_type cenv e = expr_type e`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  drule_all copy_buffer_expr_post_physical >> simp[]
QED

(* Common semantic boundary for an allocation followed by either copy. *)
Theorem copy_buffer_post_transport_physical:
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
  rpt gen_tac >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> first_x_assum irule >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x u` by
    (rpt strip_tac >> first_x_assum irule >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >>
  `!name b len. local_region cenv es.scopes s0 name b len ==>
     regions_disjoint (w2n w) sz b len` by
    (rpt strip_tac >>
     qpat_x_assum `!name b len. local_region _ es'.scopes _ _ _ _ ==> _` irule >>
     qexists_tac `name` >> irule local_region_frame_fwd >>
     qexistsl_tac [`s0`, `sa`, `es.scopes`] >>
     gvs[vv_post_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv mid` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `stmt_state_rel ctx func cenv cx es' z` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl_tac [`w2n w`, `inst`, `u`, `mid`, `sz`] >>
     simp[] >> gvs[regions_disjoint_def] >> metis_tac[]) >>
  `locals_kept cenv es es' s0 z` by
    (irule copy_buffer_locals_kept_frame >>
     qexistsl_tac [`w2n w`, `u`, `sz`] >> rpt conj_tac
     >~ [`locals_kept _ _ _ _ u`]
     >- (irule locals_kept_mem_tail >> qexists_tac `s` >>
         gvs[vv_post_def]) >>
     gvs[regions_disjoint_def] >> metis_tac[]) >>
  drule copy_static_fields >> strip_tac >>
  irule copy_buffer_expr_post_physical >>
  simp[] >> conj_tac
  >- (gvs[vv_post_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[vv_post_def] >> rpt strip_tac >>
      `id < sm.cs_next_id` by decide_tac >>
      `FLOOKUP s.vs_allocas id = SOME (off,len)` by metis_tac[] >>
      `regions_disjoint (w2n w) sz off len` by metis_tac[] >>
      `mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory` by
        (qpat_x_assum `!aid off sz. _` irule >>
         conj_tac
         >- (rpt strip_tac >>
             qpat_x_assum `!name b k. _` drule >> decide_tac) >>
         qexists_tac `id` >> simp[]) >>
      `mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by
        (qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ z.vs_memory = _` irule >>
         gvs[regions_disjoint_def] >> decide_tac) >>
      metis_tac[]) >>
  conj_tac >- (gvs[vv_post_def] >> metis_tac[]) >>
  qexistsl_tac [`sm.cs_next_id`, `sz`] >> simp[] >>
  rpt strip_tac >>
  `local_region cenv es'.scopes u name b len` by
    metis_tac[copy_buffer_local_region_frame] >>
  gvs[regions_disjoint_def] >> metis_tac[]
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
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `post_value_type cenv e = expr_type e`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  drule_all copy_buffer_post_transport_physical >> simp[]
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
  rpt gen_tac >> strip_tac >>
  simp[storage_live_memory_def, copy_bytes_def] >> rpt strip_tac >>
  qpat_x_assum `!i. i < _ ==> _` drule >> strip_tac >>
  simp[valueEncodingProofsTheory.mem_bytes_at_word] >>
  qpat_x_assum `storage_range_agree _ _ _ _` mp_tac >>
  simp[accountsRelPropsTheory.storage_range_agree_def] >> strip_tac >>
  `w2n w + i < dimword (:256)` by decide_tac >>
  `w2n (w + n2w i) = w2n w + i /\ (n2w (w2n w + i) : bytes32) = w + n2w i /\
   (n2w (i + w2n w) : bytes32) = w + n2w i` by
    (Cases_on `w` >> fs[wordsTheory.word_add_n2w]) >>
  first_x_assum (qspecl_then [`w + n2w i`, `b`] mp_tac) >>
  simp[vyperStorageTheory.read_slot_def]
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
  rpt gen_tac >> strip_tac >>
  gvs[storage_holds_def, read_result_def, return_def] >>
  gvs[read_storage_slot_def, get_storage_backend_eq,
      bind_def, lift_option_def, AllCaseEqs(), return_def, raise_def] >>
  qpat_x_assum `option_CASE _ _ _ _ = _` mp_tac >> CASE_TAC >>
  simp[raise_def, return_def] >> strip_tac >> gvs[] >>
  `well_formed_type_value tv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  `val_wf tv v` by
    metis_tac[cj 1 decode_value_well_typed, value_has_type_val_wf] >>
  simp[val_footprint_le] >>
  irule decode_value_live_memory >> conj_tac >- simp[] >>
  qexistsl_tac [`w2n a`, `get_storage cx es tr`] >> simp[] >>
  irule copied_storage_range_memory >>
  qexists_tac `if tr then contract_transient u else contract_storage u` >>
  simp[] >>
  rpt strip_tac >> drule_all copy_prefix_word >>
  Cases_on `tr` >> gvs[copy_runtime_word_def, sload_def, tload_def]
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
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `eval_operand dst u = SOME (n2w (w2n w))` by simp[] >>
  drule_all storage_copy_suffix_content_capacity_frag >>
  disch_then (qspecl_then [`ctx`, `R`] mp_tac) >>
  disch_then (mp_then Any mp_tac frag_exec_conseq) >>
  disch_then irule >> simp[] >> gen_tac >> strip_tac >>
  `copy_prefix (if loc = LocTransient then LocTransient else LocStorage)
     a (w2n w) (type_slot_size tv) u (type_slot_size tv) s` by
    (Cases_on `loc = LocTransient` >> gvs[]) >>
  drule_all copy_buffer_storage_contents >> strip_tac >>
  `copy_static s = copy_static u` by gvs[copy_prefix_def] >>
  `eval_operand dst s = SOME w` by
    (drule storage_copy_operand_preserved >>
     disch_then (qspecl_then [`mid`, `dst`] mp_tac) >> simp[]) >>
  gvs[copy_prefix_def, type_memory_size_slots] >> metis_tac[]
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
  rpt gen_tac >> disch_tac >>
  `ci_mono sa (SND ((if n = 1 then
       do v <- emitHelper$emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
          emitHelper$emit_void MSTORE [dst; v] od
     else do compile_word_copy_loop src dst n loc LocMemory F; return () od) sa))` by
    (pop_assum kall_tac >> Cases_on `n = 1` >> simp[]
     >- (irule ci_mono_bind >> simp[ci_mono_emit_op, ci_mono_emit_void]) >>
     irule ci_mono_ignore_bind >>
     simp[ci_mono_compile_word_copy_loop, ci_mono_comp_return]) >>
  gvs[]
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
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  `compile_ensure_in_memory p.ptr_operand p.ptr_location
     (type_memory_bytes cenv t) ((type_memory_bytes cenv t + 31) DIV 32)
     cenv.ce_is_ctor cenv.ce_imm_alloca sm = (op,sb)` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     Cases_on `p.ptr_location` >> gvs[unwrap_value_def]) >>
  qpat_x_assum `unwrap_value _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_ensure_in_memory _ _ _ _ _ _ _ = _` mp_tac >>
  drule ensure_storage_memory_layout >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gnvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  irule frag_exec_pointwise >> qx_gen_tac `s1` >> simp[] >> strip_tac >>
  `t = post_value_type cenv e` by
    gvs[vv_post_def, vv_holds_def] >>
  `?a. eval_operand p.ptr_operand s1 = SOME a /\
       storage_holds cx (p.ptr_location = LocTransient)
         (post_value_type cenv e) (Value v) a es' s1` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     Cases_on `p.ptr_location` >>
     gvs[vv_post_def, vv_holds_def]) >>
  `cs_extends sm mid` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends mid cs''` by
    (irule storage_copy_suffix_extends >>
     qexistsl_tac [`buf.buf_operand`, `p.ptr_location`,
       `(type_memory_bytes cenv t + 31) DIV 32`, `p.ptr_operand`, `()`] >>
     gvs[comp_ignore_bind_def]) >>
  `fn_has_code sm mid func` by metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx es' s1` by gvs[vv_post_def] >>
  `?tv. evaluate_type (get_tenv cx) t = SOME tv` by
    (gvs[storage_holds_def] >> metis_tac[]) >>
  `type_memory_bytes cenv t = type_memory_size tv /\
   type_memory_size tv < 2 ** 64` by (res_tac >> fs[]) >>
  `type_memory_size tv < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  `type_memory_bytes cenv t < dimword (:256)` by metis_tac[] >>
  drule_all alloc_buffer_source_frag >>
  disch_then (qspec_then `R` strip_assume_tac) >>
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_bytes cenv t`, `sm`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid cs''` by
    (irule storage_copy_suffix_ci_mono >>
     qexistsl_tac [`buf.buf_operand`, `p.ptr_location`,
       `(type_memory_bytes cenv t + 31) DIV 32`, `p.ptr_operand`, `()`] >>
     gvs[comp_ignore_bind_def]) >>
  `sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= cs''.cs_next_id` by
    gvs[ci_mono_def] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))]
       [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  `((type_memory_bytes cenv t + 31) DIV 32) = type_slot_size tv` by
    (simp[type_memory_size_slots] >> decide_tac) >>
  `!x. p.ptr_operand = Var x \/ buf.buf_operand = Var x ==>
       not_fresh_at mid x` by
    (rpt strip_tac >> gvs[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `(type_memory_bytes cenv t + 31) DIV 32 < 2 ** 256 /\
   w2n w + 32 * ((type_memory_bytes cenv t + 31) DIV 32) < 2 ** 256` by
    (fs[type_memory_size_slots, wordsTheory.dimword_def] >> decide_tac) >>
  qpat_assum `frag_exec ctx sm mid _ _ R` (mp_then Any mp_tac frag_exec_then) >>
  disch_then irule >> simp[] >>
  `storage_holds cx (p.ptr_location = LocTransient) t (Value v) a es' s1` by metis_tac[] >>
  `storage_holds cx (p.ptr_location = LocTransient) t (Value v) a es' u` by
    (qpat_x_assum `storage_holds _ _ _ _ _ es' s1` mp_tac >>
     simp[storage_holds_def]) >>
  drule_all (REWRITE_RULE[comp_ignore_bind_def] storage_copy_suffix_value_frag) >>
  disch_then (qspec_then `R` mp_tac) >>
  disch_then (mp_then Any mp_tac frag_exec_conseq) >>
  disch_then irule >> simp[] >> gen_tac >> strip_tac >>
  irule copy_buffer_post_transport_physical >>
  qpat_assum `t = post_value_type cenv e` (fn th => rewrite_tac[GSYM th]) >>
  simp[] >>
  goal_assum (drule_at Any) >>
  simp[mk_inst_def, SF SFY_ss] >>
  qexists_tac `mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))]
       [STRING #"%" (toString sm.cs_next_var)]` >>
  qexistsl_tac [`mid`, `s1`, `sm`, `u`, `LocatedValue t p`] >>
  simp[mk_inst_def] >>
  gnvs[] >> metis_tac[]
QED


Theorem immutable_holds_data:
  !func cenv cx es s t tv w ctx.
    stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
    immutable_holds cenv cx t tv w es s' ==>
    ?tvt v. evaluate_type (get_tenv cx) t = SOME tvt /\
            read_result cx tv es = (INL v, es) /\
            val_in_memory tvt v (w2n w) s.vs_data_section
Proof
  rw[immutable_holds_def, stmt_state_rel_def, state_rel_def,
     immutables_rel_def] >>
  gvs[] >> first_x_assum drule_all >> strip_tac >>
  gvs[sub_layout_def] >> first_x_assum drule >> strip_tac >>
  `off + k < dimword (:256)` by DECIDE_TAC >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Theorem immutable_holds_bounds:
  immutable_holds cenv cx t (Value v) a es s /\
  evaluate_type (get_tenv cx) t = SOME tv ==>
  val_wf tv v /\ w2n a + type_memory_size tv < dimword (:256)
Proof
  rw[immutable_holds_def, sub_layout_def, read_result_def, return_def] >>
  `off + k < dimword (:256)` by decide_tac >>
  gvs[] >> metis_tac[value_has_type_val_wf, arithmeticTheory.ADD_ASSOC]
QED

Theorem immutable_holds_memory:
  stmt_state_rel ctx func cenv cx es uu /\ cenv.ce_is_ctor /\
  immutable_holds cenv cx t (Value v) a es uu /\
  evaluate_type (get_tenv cx) t = SOME tv ==>
  val_in_memory tv v (w2n a) uu.vs_memory
Proof
  rw[immutable_holds_def, stmt_state_rel_def, state_rel_def,
     immutables_rel_def, read_result_def, return_def]
  >~ [`sub_layout`]
  >- (gvs[] >> first_x_assum drule_all >> strip_tac >>
      gvs[sub_layout_def] >> first_x_assum drule >> strip_tac >>
      `off + k < dimword (:256)` by decide_tac >>
      gvs[arithmeticTheory.ADD_COMM]) >>
  `off + k < dimword (:256)` by decide_tac >> gvs[]
QED

Theorem immutable_holds_alloca_disjoint:
  stmt_state_rel ctx func cenv cx es uu /\ cenv.ce_is_ctor /\
  immutable_holds cenv cx t (Value v) a es uu /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP uu.vs_allocas inst.inst_id = SOME (dst,sz) ==>
  regions_disjoint (w2n a) (type_memory_size tv) dst sz
Proof
  rw[immutable_holds_def, stmt_state_rel_def, immutable_alloca_sep_def,
     read_result_def, return_def] >>
  gvs[sub_layout_def] >>
  `off + k < dimword (:256)` by decide_tac >>
  gvs[] >> first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >>
  simp[regions_disjoint_def] >> decide_tac
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
  rpt strip_tac >>
  drule_all immutable_holds_bounds >> strip_tac >>
  drule_all immutable_holds_data >> strip_tac >>
  gvs[read_result_def, return_def] >>
  simp[val_footprint_le] >>
  irule valueEncodingPropsTheory.val_in_memory_relocate >> simp[] >>
  qexistsl_tac [`u.vs_data_section`, `type_memory_size tv`, `w2n a`] >> simp[] >>
  Cases_on `type_slot_size tv = 0`
  >- (gvs[type_memory_size_slots, mem_bytes_at_def]) >>
  `immutable_transfers F F a w (type_slot_size tv) 0 u =
    write_memory_with_expansion (w2n w)
      (mem_bytes_at (w2n a) (type_memory_size tv) u.vs_data_section) u` by
    (qspecl_then [`type_slot_size tv`, `w2n a`, `w2n w`, `0`, `u`] mp_tac
      immutable_runtime_transfers_snapshot >>
     simp[mem_bytes_at_def, type_memory_size_slots] >>
     gvs[type_memory_size_slots]) >>
  gvs[] >>
  qspec_then `w2n w` mp_tac valueEncodingPropsTheory.write_memory_mem_bytes_at_same >>
  disch_then (qspecl_then
    [`mem_bytes_at (w2n a) (type_memory_size tv) u.vs_data_section`, `u`] mp_tac) >>
  simp[]
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
  metis_tac[copy_old_operand_def, freshWritesTheory.not_fresh_at_mono]
QED

Theorem copy_runtime_frame_refl:
  copy_runtime_frame st s st s
Proof
  simp[copy_runtime_frame_def, emitted_insts_def, same_blocks_def,
       run_inst_seq_def]
QED

Theorem copy_runtime_frame_operand:
  copy_runtime_frame st s st' s' /\ copy_old_operand st op ==>
  eval_operand op s' = eval_operand op s
Proof
  Cases_on `op` >>
  simp[copy_runtime_frame_def, copy_old_operand_def, eval_operand_def] >>
  rpt strip_tac >> gvs[copy_static_def, venom_state_component_equality]
QED

Theorem copy_runtime_frame_trans:
  copy_runtime_frame st s st1 s1 /\ copy_runtime_frame st1 s1 st2 s2 ==>
  copy_runtime_frame st s st2 s2
Proof
  simp[copy_runtime_frame_def] >> strip_tac >>
  `emitted_insts st st2 = emitted_insts st st1 ++ emitted_insts st1 st2` by
    (irule emitted_insts_append >> simp[]) >>
  conj_tac
  >- (qpat_assum `run_inst_seq (emitted_insts st st1) s = _`
        (mp_then Any mp_tac run_inst_seq_append) >> simp[]) >>
  conj_tac >- simp[listTheory.APPEND_ASSOC] >>
  conj_tac >- gvs[same_blocks_def] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LE_TRANS]
QED

Theorem copy_runtime_offset:
  compile_lit_byte_offset op off st = (r,st') /\
  copy_old_operand st op /\ eval_operand op s = SOME a ==>
  ?s'. copy_runtime_frame st s st' s' /\
    eval_operand r s' = SOME (a + n2w off) /\
    copy_old_operand st' r /\ s'.vs_memory = s.vs_memory
Proof
  Cases_on `off = 0`
  >- (simp[compile_lit_byte_offset_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[copy_runtime_frame_refl, wordsTheory.WORD_ADD_0]) >>
  Cases_on `op` >>
  simp[compile_lit_byte_offset_def, emitHelperTheory.emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >> gvs[]
  >- (qexists_tac `s` >>
      gvs[copy_runtime_frame_refl, copy_old_operand_def, eval_operand_def]) >>
  (qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) (a + n2w off) s` >>
  simp[copy_runtime_frame_def, emitted_insts_def,
       listTheory.DROP_APPEND, same_blocks_def] >>
  conj_tac
  >- (conj_tac
      >- (gvs[eval_operand_def] >>
          simp[run_inst_seq_def, mk_inst_def,
               venomExecSemanticsTheory.step_inst_base_opcode_eqs,
               exec_pure2_def, eval_operand_def]) >>
      simp[copy_static_def, update_var_def, lookup_var_def,
           finite_mapTheory.FLOOKUP_UPDATE] >>
      rpt strip_tac >>
      `x <> STRING #"%" (toString st.cs_next_var)` by
        (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LE_REFL]) >> simp[]) >>
  simp[eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, copy_old_operand_def,
       not_fresh_at_def, fresh_var_distinct])
QED

Theorem copy_runtime_load:
  compile_imm_load_word F imm op st = (r,st') /\
  copy_old_operand st op /\ eval_operand op s = SOME a ==>
  ?s'. copy_runtime_frame st s st' s' /\ copy_old_operand st' r /\
    eval_operand r s' = SOME (immutable_copy_read F a s) /\
    s'.vs_memory = s.vs_memory
Proof
  simp[compile_imm_load_word_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >> gvs[] >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var))
    (immutable_copy_read F a s) s` >>
  simp[copy_runtime_frame_def, emitted_insts_def, listTheory.DROP_APPEND,
       same_blocks_def] >>
  conj_tac
  >- (conj_tac
      >- simp[run_inst_seq_def, mk_inst_def,
              venomExecSemanticsTheory.step_inst_base_opcode_eqs,
              exec_read1_def, immutable_copy_read_def] >>
      simp[copy_static_def, update_var_def, lookup_var_def,
           finite_mapTheory.FLOOKUP_UPDATE] >> rpt strip_tac >>
      `x <> STRING #"%" (toString st.cs_next_var)` by
        (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LE_REFL]) >> simp[]) >>
  simp[copy_old_operand_def, not_fresh_at_def, fresh_var_distinct,
       eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
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
  Cases_on `imm`
  >- (simp[compile_imm_load_word_def, emitHelperTheory.emit_op_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def,
           fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >> gvs[] >>
      qexists_tac `update_var (STRING #"%" (toString st.cs_next_var))
        (immutable_copy_read T a ss) ss` >>
      simp[copy_runtime_frame_def, emitted_insts_def, listTheory.DROP_APPEND,
           same_blocks_def] >>
      conj_tac
      >- (conj_tac
          >- simp[run_inst_seq_def, mk_inst_def, step_inst_base_def,
                  exec_read1_def, immutable_copy_read_def] >>
          simp[copy_static_def, update_var_def, lookup_var_def,
               finite_mapTheory.FLOOKUP_UPDATE] >> rpt strip_tac >>
          `x <> STRING #"%" (toString st.cs_next_var)` by
            (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LE_REFL]) >> simp[]) >>
      simp[copy_old_operand_def, not_fresh_at_def, fresh_var_distinct,
           eval_operand_def, update_var_def, lookup_var_def,
           finite_mapTheory.FLOOKUP_UPDATE]) >>
  rpt strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString (st.cs_next_var + 1)))
    (mload (w2n a) ss) (update_var (STRING #"%" (toString st.cs_next_var)) a ss)` >>
  `run_inst_seq (emitted_insts st st') ss = OK
    (update_var (STRING #"%" (toString (st.cs_next_var + 1)))
      (mload (w2n a) ss) (update_var (STRING #"%" (toString st.cs_next_var)) a ss))` by
    (drule immutableWordExecutionTheory.compile_imm_load_word_ctor_execution >> simp[]) >>
  qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
  simp[compile_imm_load_word_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[copy_runtime_frame_def, emitted_insts_def, same_blocks_def,
       listTheory.DROP_APPEND] >>
  simp[copy_old_operand_def, immutable_copy_read_def, copy_static_def,
       eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def, fresh_var_distinct] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem copy_ctor_load_shape:
  compile_imm_load_word T imm op st = (r,st') ==>
  st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
  same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var /\
  EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; MSTORE]) (emitted_insts st st')
Proof
  Cases_on `imm` >>
  simp[compile_imm_load_word_def, emitHelperTheory.emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def, same_blocks_def, listTheory.DROP_APPEND, mk_inst_def] >>
  `LENGTH st.cs_current_insts - (LENGTH st.cs_current_insts + 1) = 0` by decide_tac >>
  simp[]
QED

Theorem copy_runtime_store:
  emitHelper$emit_void MSTORE [dst;value] st = ((),st') /\
  copy_old_operand st dst /\ copy_old_operand st value /\
  eval_operand dst s = SOME b /\ eval_operand value s = SOME w ==>
  copy_runtime_frame st s st' (mstore (w2n b) w s)
Proof
  simp[emitHelperTheory.emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[copy_runtime_frame_def, emitted_insts_def, listTheory.DROP_APPEND,
       same_blocks_def] >> conj_tac
  >- simp[run_inst_seq_def, mk_inst_def, step_inst_base_def, exec_write2_def] >>
  simp[mstore_def, write_memory_with_expansion_def, copy_static_def, lookup_var_def]
QED

Theorem copy_runtime_one:
  immutable_copy_one F imm src dst off st = ((),st') /\
  copy_old_operand st src /\ copy_old_operand st dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b ==>
  ?s'. copy_runtime_frame st s st' s' /\
    s'.vs_memory = (immutable_word_transfer F F a b off s).vs_memory
Proof
  simp[immutable_copy_one_def, immutable_comp_bind_cases] >> rpt strip_tac >>
  drule_all copy_runtime_offset >> strip_tac >>
  drule_all copy_runtime_load >> strip_tac >>
  `copy_runtime_frame st s st1' s''` by
    metis_tac[copy_runtime_frame_trans] >>
  `copy_old_operand st1' dst` by
    metis_tac[copy_old_operand_mono, copy_runtime_frame_def] >>
  `eval_operand dst s'' = SOME b` by
    metis_tac[copy_runtime_frame_operand] >>
  qpat_x_assum `compile_lit_byte_offset src off st = _` kall_tac >>
  drule_all copy_runtime_offset >> strip_tac >>
  rename1 `copy_runtime_frame st1' s'' st1'' s3` >>
  `copy_old_operand st1'' value` by
    metis_tac[copy_old_operand_mono, copy_runtime_frame_def] >>
  `eval_operand value s3 = SOME (immutable_copy_read F (a + n2w off) s')` by
    metis_tac[copy_runtime_frame_operand] >>
  drule_all copy_runtime_store >> strip_tac >>
  qexists_tac `mstore (w2n (b + n2w off))
    (immutable_copy_read F (a + n2w off) s') s3` >>
  conj_tac >- metis_tac[copy_runtime_frame_trans] >>
  `s'.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `copy_runtime_frame st s st1 s'` mp_tac >>
     simp[copy_runtime_frame_def] >> strip_tac >>
     drule copy_static_fields >> simp[]) >>
  simp[immutable_word_transfer_def, immutable_copy_read_def, mstore_def,
       write_memory_with_expansion_def]
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
  simp[immutable_copy_one_def, immutable_comp_bind_cases] >> rpt strip_tac >>
  rename1 `compile_lit_byte_offset src off st = (sop, cs1)` >>
  rename1 `compile_imm_load_word T imm sop cs1 = (value, cs2)` >>
  rename1 `compile_lit_byte_offset dst off cs2 = (dop, cs3)` >>
  drule_all copy_runtime_offset >> strip_tac >>
  rename1 `copy_runtime_frame st ss cs1 zz1` >>
  `!region. imm = SOME region ==> eval_operand region zz1 = SOME 0w /\
    copy_old_operand cs1 region` by
    metis_tac[copy_runtime_frame_operand, copy_old_operand_mono, copy_runtime_frame_def] >>
  drule_all copy_ctor_load >> strip_tac >>
  rename1 `copy_runtime_frame cs1 zz1 cs2 zz2` >>
  `copy_runtime_frame st ss cs2 zz2` by metis_tac[copy_runtime_frame_trans] >>
  `copy_old_operand cs2 dst` by
    metis_tac[copy_old_operand_mono, copy_runtime_frame_def] >>
  `eval_operand dst zz2 = SOME b` by metis_tac[copy_runtime_frame_operand] >>
  qpat_x_assum `compile_lit_byte_offset src off st = _` kall_tac >>
  drule_all copy_runtime_offset >> strip_tac >>
  rename1 `copy_runtime_frame cs2 zz2 cs3 zz3` >>
  `copy_old_operand cs3 value` by
    metis_tac[copy_old_operand_mono, copy_runtime_frame_def] >>
  `eval_operand value zz3 = SOME (immutable_copy_read T (a + n2w off) zz1)` by
    metis_tac[copy_runtime_frame_operand] >>
  drule_all copy_runtime_store >> strip_tac >>
  qexists_tac `mstore (w2n (b + n2w off))
    (immutable_copy_read T (a + n2w off) zz1) zz3` >>
  conj_tac >- metis_tac[copy_runtime_frame_trans] >>
  simp[immutable_word_transfer_def, immutable_copy_read_def, mload_def,
       mstore_def, write_memory_with_expansion_def]
QED

Theorem copy_ctor_transfers_cong[local]:
  !n off s1 s2.
  s1.vs_memory = s2.vs_memory ==>
  (immutable_transfers F T a b n off s1).vs_memory =
  (immutable_transfers F T a b n off s2).vs_memory
Proof
  Induct >> simp[immutable_transfers_def] >> rpt strip_tac >>
  first_x_assum irule >>
  simp[immutable_word_transfer_def, immutable_copy_read_def, mload_def,
       mstore_def, write_memory_with_expansion_def]
QED

Theorem copy_runtime_transfers_cong:
  !n off s1 s2.
  s1.vs_memory = s2.vs_memory /\ s1.vs_data_section = s2.vs_data_section ==>
  (immutable_transfers F F a b n off s1).vs_memory =
  (immutable_transfers F F a b n off s2).vs_memory
Proof
  Induct >> simp[immutable_transfers_def] >> rpt strip_tac >>
  first_x_assum irule >>
  simp[immutable_word_transfer_def, immutable_copy_read_def,
       mstore_def, write_memory_with_expansion_def]
QED

Theorem copy_runtime_run:
  !n off st st' s a b.
  compile_imm_copy_to_memory F imm src dst n off st = ((),st') /\
  copy_old_operand st src /\ copy_old_operand st dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b ==>
  ?s'. copy_runtime_frame st s st' s' /\
    s'.vs_memory = (immutable_transfers F F a b n off s).vs_memory
Proof
  Induct
  >- (simp[compile_imm_copy_to_memory_def, comp_return_def,
           immutable_transfers_def] >> rpt strip_tac >> gvs[] >>
      qexists_tac `s` >> simp[copy_runtime_frame_refl]) >>
  simp[immutable_copy_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  rpt strip_tac >> drule_all copy_runtime_one >> strip_tac >>
  `copy_old_operand st1 src /\ copy_old_operand st1 dst` by
    metis_tac[copy_old_operand_mono, copy_runtime_frame_def] >>
  `eval_operand src s' = SOME a /\ eval_operand dst s' = SOME b` by
    metis_tac[copy_runtime_frame_operand] >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `s''` >>
  conj_tac >- metis_tac[copy_runtime_frame_trans] >>
  `s'.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `copy_runtime_frame st s st1 s'` mp_tac >>
     simp[copy_runtime_frame_def] >> strip_tac >>
     drule copy_static_fields >> simp[]) >>
  simp[immutable_transfers_def] >>
  irule copy_runtime_transfers_cong >>
  simp[immutable_transfer_data, immutable_word_transfer_def, mstore_def]
QED

Theorem code_offset_insts:
  !op off st r st'.
    compile_lit_byte_offset op off st = (r,st') ==>
    EVERY (\i. i.inst_opcode = ADD) (emitted_insts st st')
Proof
  rpt gen_tac >> Cases_on `off = 0`
  >- simp[compile_lit_byte_offset_def, comp_return_def, emitted_insts_def] >>
  Cases_on `op` >>
  simp[compile_lit_byte_offset_def, comp_return_def, emitted_insts_def] >>
  strip_tac >> imp_res_tac emitted_insts_emit_op >>
  gvs[emitted_insts_def, mk_inst_def]
QED

Theorem code_copy_insts:
  !n imm src dst off sa sb.
    compile_imm_copy_to_memory F imm src dst n off sa = ((),sb) ==>
    same_blocks sa sb /\
    ?is. sb.cs_current_insts = sa.cs_current_insts ++ is /\
         EVERY (\i. MEM i.inst_opcode [ADD; DLOAD; MSTORE]) is
Proof
  Induct
  >- simp[compile_imm_copy_to_memory_def, comp_return_def, same_blocks_def] >>
  rpt gen_tac >>
  simp[compile_imm_copy_to_memory_def, compile_imm_load_word_runtime,
       comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_lit_byte_offset src off sa = (sop, s1)` >>
  rename1 `emitHelper$emit_op DLOAD [sop] s1 = (v, s2)` >>
  rename1 `compile_lit_byte_offset dst off s2 = (dop, s3)` >>
  rename1 `emitHelper$emit_void MSTORE [dop; v] s3 = (u, s4)` >>
  Cases_on `u` >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac immutable_byte_offset_extends >>
  imp_res_tac code_offset_insts >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  imp_res_tac emitted_insts_emit_void >>
  gvs[same_blocks_def] >>
  conj_tac
  >- gvs[emitHelperTheory.emit_void_def, emitHelperTheory.emit_inst_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, emit_def] >>
  fs[EVERY_MEM]
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
  Induct
  >- (simp[compile_imm_copy_to_memory_def, comp_return_def,
           immutable_transfers_def] >> rpt strip_tac >> gvs[] >>
      qexists_tac `ss` >> simp[copy_runtime_frame_refl]) >>
  simp[immutable_copy_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  rpt strip_tac >>
  rename1 `immutable_copy_one T imm src dst off st = ((), cs1)` >>
  drule_all copy_ctor_one >> strip_tac >>
  rename1 `copy_runtime_frame st ss cs1 zz1` >>
  `copy_old_operand cs1 src /\ copy_old_operand cs1 dst` by
    metis_tac[copy_old_operand_mono, copy_runtime_frame_def] >>
  `eval_operand src zz1 = SOME a /\ eval_operand dst zz1 = SOME b` by
    metis_tac[copy_runtime_frame_operand] >>
  `!region. imm = SOME region ==> eval_operand region zz1 = SOME 0w /\
    copy_old_operand cs1 region` by
    metis_tac[copy_runtime_frame_operand, copy_old_operand_mono, copy_runtime_frame_def] >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `copy_runtime_frame cs1 zz1 st' zz2` >>
  qexists_tac `zz2` >>
  conj_tac >- metis_tac[copy_runtime_frame_trans] >>
  simp[immutable_transfers_def] >>
  irule copy_ctor_transfers_cong >> simp[]
QED

Theorem code_ctor_copy_insts:
  !n imm src dst off sa sb.
    compile_imm_copy_to_memory T imm src dst n off sa = ((),sb) ==>
    same_blocks sa sb /\
    ?is. sb.cs_current_insts = sa.cs_current_insts ++ is /\
         EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; MSTORE]) is
Proof
  Induct
  >- simp[compile_imm_copy_to_memory_def, comp_return_def, same_blocks_def] >>
  rpt gen_tac >>
  simp[compile_imm_copy_to_memory_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_lit_byte_offset src off sa = (sop, cs1)` >>
  rename1 `compile_imm_load_word T imm sop cs1 = (value, cs2)` >>
  rename1 `compile_lit_byte_offset dst off cs2 = (dop, cs3)` >>
  rename1 `emitHelper$emit_void MSTORE [dop; value] cs3 = (u, cs4)` >>
  Cases_on `u` >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac immutable_byte_offset_extends >>
  imp_res_tac code_offset_insts >>
  drule copy_ctor_load_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_void >>
  gvs[same_blocks_def] >>
  conj_tac
  >- gvs[emitHelperTheory.emit_void_def, emitHelperTheory.emit_inst_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def, emit_def] >>
  fs[EVERY_MEM]
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
  rpt strip_tac >> drule_all copy_runtime_run >> strip_tac >>
  drule code_copy_insts >> strip_tac >>
  `emitted_insts st st' = is` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND3] >>
  reverse conj_tac
  >- (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[is_terminator_def]) >>
  rpt strip_tac >> gvs[] >> disj1_tac >> qexists_tac `s'` >>
  gvs[copy_runtime_frame_def, copy_static_def, lookup_var_def]
QED

Theorem copy_runtime_zero_frag:
  !ctx imm src dst mid sb s R.
    compile_imm_copy_to_memory F imm src dst 0 0 mid = ((),sb) ==>
    frag_exec ctx mid sb (\z. z = s) (\z. z = s) R
Proof
  simp[compile_imm_copy_to_memory_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >> irule frag_exec_refl >> simp[]
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
  simp[compile_imm_copy_to_memory_def, compile_lit_byte_offset_def,
       compile_imm_load_word_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  `!x. not_fresh_at mid x ==>
       x <> STRING #"%" (toString mid.cs_next_var)` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LE_REFL]) >>
  `eval_operand dst (update_var (STRING #"%" (toString mid.cs_next_var))
     (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s) = SOME b` by
    (Cases_on `dst` >> gvs[eval_operand_def, lookup_var_def,
       update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  simp[emitted_insts_def, listTheory.DROP_APPEND, run_inst_seq_def,
       mk_inst_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       exec_read1_def, exec_write2_def] >>
  `LENGTH mid.cs_current_insts - (LENGTH mid.cs_current_insts + 1) = 0` by decide_tac >>
  simp[run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       exec_write2_def,
       eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[update_var_def] >>
  simp[mstore_def, write_memory_with_expansion_def, copy_static_def,
       lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
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
  rpt strip_tac >> drule_all copy_ctor_run >> strip_tac >>
  drule code_ctor_copy_insts >> strip_tac >>
  `emitted_insts st st' = is` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND3] >>
  reverse conj_tac
  >- (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[is_terminator_def]) >>
  rpt strip_tac >> gvs[] >> disj1_tac >> qexists_tac `zz` >>
  gvs[copy_runtime_frame_def, copy_static_def, lookup_var_def]
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
  strip_tac >>
  qspecl_then [`type_slot_size tv`, `w2n a`, `w2n w`, `0`, `uu`] mp_tac
    (Q.INST [`store` |-> `F`, `ctor` |-> `T`] immutable_memory_transfers_snapshot) >>
  simp[GSYM type_memory_size_slots] >>
  gvs[regions_disjoint_def] >>
  simp[mcopy_def, mem_bytes_at_def]
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
  strip_tac >> drule_all immutable_holds_bounds >> strip_tac >>
  drule_all immutable_holds_memory >> strip_tac >>
  simp[val_footprint_le] >>
  Cases_on `type_slot_size tv = 0`
  >- (gvs[immutable_transfers_def, type_memory_size_slots] >>
      irule valueEncodingPropsTheory.val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`uu.vs_memory`, `0`, `w2n a`] >>
      simp[mem_bytes_at_def, type_memory_size_slots]) >>
  drule_all copy_ctor_memory_snapshot >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule valueEncodingPropsTheory.val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`uu.vs_memory`, `type_memory_size tv`, `w2n a`] >> simp[] >>
      qspec_then `w2n w` mp_tac valueEncodingPropsTheory.write_memory_mem_bytes_at_same >>
      disch_then (qspecl_then
        [`mem_bytes_at (w2n a) (type_memory_size tv) uu.vs_memory`, `uu`] mp_tac) >>
      simp[]) >>
  conj_tac >- simp[immutableMemoryFrameTheory.immutable_write_memory_capacity] >>
  rpt strip_tac >> simp[valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint]
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
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  irule frag_exec_pointwise >> qx_gen_tac `s1` >> simp[] >> strip_tac >>
  `t = post_value_type cenv e` by gvs[vv_post_def, vv_holds_def] >>
  `?a. eval_operand p.ptr_operand s1 = SOME a /\
       immutable_holds cenv cx t (Value v) a es' s1` by
    gvs[vv_post_def, vv_holds_def] >>
  `?tv. evaluate_type (get_tenv cx) t = SOME tv` by
    (gvs[immutable_holds_def] >> metis_tac[]) >>
  `val_wf tv v /\ w2n a + type_memory_size tv < dimword (:256)` by
    (drule_all immutable_holds_bounds >> simp[]) >>
  `type_memory_bytes cenv t = type_memory_size tv` by metis_tac[] >>
  `type_memory_bytes cenv t < dimword (:256)` by decide_tac >>
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_bytes cenv t`, `sm`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid cs''` by
    (qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
  `cs_extends sm mid /\ cs_extends mid cs'' /\
   sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= cs''.cs_next_id` by
    gvs[ci_mono_def] >>
  `fn_has_code sm mid func` by metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx es' s1` by gvs[vv_post_def] >>
  drule_all alloc_buffer_source_frag >>
  disch_then (qspec_then `R` strip_assume_tac) >>
  `copy_old_operand mid p.ptr_operand /\ copy_old_operand mid buf.buf_operand` by
    (rw[copy_old_operand_def] >> gvs[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))]
       [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  `(type_memory_bytes cenv t + 31) DIV 32 = type_slot_size tv` by
    (simp[type_memory_size_slots] >> decide_tac) >>
  qpat_assum `frag_exec ctx sm mid _ _ R` (mp_then Any mp_tac frag_exec_then) >>
  disch_then irule >> simp[] >>
  drule_all copy_runtime_frag >>
  disch_then (qspecl_then [`ctx`, `R`] mp_tac) >>
  disch_then (mp_then Any mp_tac frag_exec_conseq) >>
  disch_then irule >> simp[] >> gen_tac >> strip_tac >>
  `s.vs_memory = (immutable_transfers F F a w (type_slot_size tv) 0 u).vs_memory` by
    metis_tac[] >>
  `w2n w + type_memory_size tv < dimword (:256)` by metis_tac[] >>
  drule_all copy_runtime_contents >> strip_tac >>
  suspend "runtime_post"
QED

Resume unwrap_runtime_code_copy_sim[runtime_post]:
  `LENGTH u.vs_memory <= LENGTH s.vs_memory /\
   (!off len. off + len <= w2n w \/
      w2n w + type_memory_bytes cenv t <= off ==>
      mem_bytes_at off len s.vs_memory = mem_bytes_at off len u.vs_memory)` by
    (Cases_on `type_slot_size tv = 0`
     >- gvs[immutable_transfers_def] >>
     `immutable_transfers F F a w (type_slot_size tv) 0 u =
       write_memory_with_expansion (w2n w)
         (mem_bytes_at (w2n a) (type_memory_size tv) u.vs_data_section) u` by
       (qspecl_then [`type_slot_size tv`, `w2n a`, `w2n w`, `0`, `u`] mp_tac
         immutable_runtime_transfers_snapshot >>
        simp[mem_bytes_at_def, type_memory_size_slots] >>
        gvs[type_memory_size_slots]) >>
     gvs[] >> conj_tac
     >- simp[immutableMemoryFrameTheory.immutable_write_memory_capacity] >>
     rpt strip_tac >>
     simp[valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint]) >>
  `eval_operand (Var p') s = SOME w` by
    (qsuff_tac `eval_operand (Var p') s = eval_operand (Var p') u`
     >- gvs[] >>
     irule storage_copy_operand_preserved >> simp[] >>
     qexists_tac `mid` >> simp[]) >>
  irule copy_buffer_post_transport_physical >>
  qpat_assum `t = post_value_type cenv e` (fn th => rewrite_tac[GSYM th]) >>
  simp[] >>
  goal_assum (drule_at Any) >>
  simp[mk_inst_def, SF SFY_ss] >>
  qexists_tac `mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))]
       [STRING #"%" (toString sm.cs_next_var)]` >>
  qexistsl_tac [`mid`, `s1`, `sm`, `u`, `LocatedValue t p`] >>
  simp[mk_inst_def] >> gnvs[] >> metis_tac[]
QED

Finalise unwrap_runtime_code_copy_sim


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
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  irule frag_exec_pointwise >> qx_gen_tac `s1` >> simp[] >> strip_tac >>
  `t = post_value_type cenv e` by gvs[vv_post_def, vv_holds_def] >>
  `?a. eval_operand p.ptr_operand s1 = SOME a /\
       immutable_holds cenv cx t (Value v) a es' s1` by
    gvs[vv_post_def, vv_holds_def] >>
  `?tv. evaluate_type (get_tenv cx) t = SOME tv` by
    (gvs[immutable_holds_def] >> metis_tac[]) >>
  `val_wf tv v /\ w2n a + type_memory_size tv < dimword (:256)` by
    (drule_all immutable_holds_bounds >> simp[]) >>
  `type_memory_bytes cenv t = type_memory_size tv` by metis_tac[] >>
  `type_memory_bytes cenv t < dimword (:256)` by decide_tac >>
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_bytes cenv t`, `sm`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[]) >>
  rename1 `compile_imm_copy_to_memory _ _ _ _ _ _ mid = (_,sc)` >>
  `ci_mono mid sc` by
    (qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
  `cs_extends sm mid /\ cs_extends mid sc /\
   sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= sc.cs_next_id` by
    gvs[ci_mono_def] >>
  `fn_has_code sm mid func` by metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx es' s1` by gvs[vv_post_def] >>
  drule_all alloc_buffer_source_frag_labels >>
  disch_then (qspec_then `R` strip_assume_tac) >>
  `immutable_holds cenv cx t (Value v) a es' u` by
    metis_tac[immutable_holds_memory_cong] >>
  `copy_old_operand mid p.ptr_operand /\ copy_old_operand mid buf.buf_operand` by
    (rw[copy_old_operand_def] >> gvs[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))]
       [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  `(type_memory_bytes cenv t + 31) DIV 32 = type_slot_size tv` by
    (simp[type_memory_size_slots] >> decide_tac) >>
  suspend "ctor_suffix"
QED

Resume unwrap_ctor_code_copy_base_sim[ctor_suffix]:
  `!region. cenv.ce_imm_alloca = SOME region ==>
      eval_operand region u = SOME 0w /\ copy_old_operand mid region` by
    (rpt strip_tac >>
     `eval_operand region s1 = SOME 0w` by fs[immutable_base_zero_def] >>
     Cases_on `region` >> gvs[eval_operand_def, copy_old_operand_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `regions_disjoint (w2n a) (type_memory_size tv)
      (w2n w) (type_memory_size tv)` by
    (irule immutable_holds_alloca_disjoint >>
     qexistsl_tac [`cenv`, `ctx`, `cx`, `es'`, `func`] >>
     goal_assum (drule_at Any) >> simp[mk_inst_def] >>
     qexistsl_tac [`t`, `u`, `v`] >> simp[]) >>
  qpat_assum `frag_exec ctx sm mid _ _ R` (mp_then Any mp_tac frag_exec_then) >>
  disch_then irule >> simp[] >>
  drule_all copy_ctor_frag >>
  disch_then (qspecl_then [`ctx`, `R`] mp_tac) >>
  disch_then (mp_then Any mp_tac frag_exec_conseq) >>
  disch_then irule >> simp[] >> gen_tac >> strip_tac >>
  `s.vs_memory = (immutable_transfers F T a w (type_slot_size tv) 0 u).vs_memory` by
    metis_tac[] >>
  `w2n w + type_memory_size tv < dimword (:256)` by metis_tac[] >>
  drule_all copy_ctor_contents >> strip_tac >>
  suspend "ctor_post"
QED

Resume unwrap_ctor_code_copy_base_sim[ctor_post]:
  rename1 `buf.buf_operand = Var bp` >>
  `eval_operand (Var bp) s = SOME w` by
    (qsuff_tac `eval_operand (Var bp) s = eval_operand (Var bp) u`
     >- gvs[] >>
     irule storage_copy_operand_preserved >> simp[] >>
     qexists_tac `mid` >> simp[]) >>
  irule copy_buffer_post_transport_physical >>
  qpat_assum `t = post_value_type cenv e` (fn th => rewrite_tac[GSYM th]) >>
  simp[] >>
  goal_assum (drule_at Any) >>
  simp[mk_inst_def, SF SFY_ss] >>
  qexists_tac `mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))]
       [STRING #"%" (toString sm.cs_next_var)]` >>
  qexistsl_tac [`mid`, `s1`, `sm`, `u`, `LocatedValue t p`] >>
  simp[mk_inst_def] >> gnvs[] >> metis_tac[]
QED

Finalise unwrap_ctor_code_copy_base_sim

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
  rpt strip_tac >>
  `!s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
         (LocatedValue t p) s ==> immutable_base_zero cenv s` by
    simp[vv_post_def, stmt_state_rel_def] >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `e`, `es`, `sa`, `sm`, `sb`, `s0`,
               `es'`, `v`, `t`, `p`, `op`, `R`] mp_tac
    unwrap_ctor_code_copy_base_sim >>
  impl_tac >- (simp[] >> metis_tac[local_ptrs_reserved_imm_base]) >>
  strip_tac >> irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
  simp[]
QED

Theorem runtime_code_copy_memory_frame:
  w2n a + type_memory_size tv < dimword (:256) /\
  w2n w + type_memory_size tv < dimword (:256) /\
  z.vs_memory = (immutable_transfers F F a w (type_slot_size tv) 0 u).vs_memory ==>
  LENGTH u.vs_memory <= LENGTH z.vs_memory /\
  (!off len. off + len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory)
Proof
  strip_tac >> Cases_on `type_slot_size tv = 0`
  >- gvs[immutable_transfers_def] >>
  `immutable_transfers F F a w (type_slot_size tv) 0 u =
    write_memory_with_expansion (w2n w)
      (mem_bytes_at (w2n a) (type_memory_size tv) u.vs_data_section) u` by
    (qspecl_then [`type_slot_size tv`, `w2n a`, `w2n w`, `0`, `u`] mp_tac
       immutable_runtime_transfers_snapshot >>
     simp[mem_bytes_at_def, type_memory_size_slots] >>
     gvs[type_memory_size_slots]) >>
  gvs[] >> conj_tac
  >- simp[immutableMemoryFrameTheory.immutable_write_memory_capacity] >>
  rpt strip_tac >>
  simp[valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint]
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
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `t.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `eval_operand src t = SOME a` by
    (Cases_on `src` >> gvs[eval_operand_def]) >>
  qexistsl_tac [`t`, `w`] >> simp[] >> metis_tac[]
QED

Theorem runtime_code_copy_run_post_physical:
  !ctx func cenv cx e es sa sm sb s0 es' v p op s.
    unwrap_value cenv (LocatedValue (post_value_type cenv e) p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type (post_value_type cenv e) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tvt ==>
           type_memory_bytes cenv (post_value_type cenv e) = type_memory_size tvt) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue (post_value_type cenv e) p) s ==>
    ?code z. same_blocks sm sb /\
      sb.cs_current_insts = sm.cs_current_insts ++ code /\
      EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE]) code /\
      run_inst_seq code s = OK z /\
      expr_post ctx func cenv cx e es sa sb s0 es' v op z
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  `?a. eval_operand p.ptr_operand s = SOME a /\
       immutable_holds cenv cx (post_value_type cenv e) (Value v) a es' s` by
    gvs[vv_post_def, vv_holds_def] >>
  `?tv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tv` by
    (gvs[immutable_holds_def] >> metis_tac[]) >>
  `val_wf tv v /\ w2n a + type_memory_size tv < dimword (:256)` by
    (drule_all immutable_holds_bounds >> simp[]) >>
  `type_memory_bytes cenv (post_value_type cenv e) = type_memory_size tv` by metis_tac[] >>
  `type_memory_bytes cenv (post_value_type cenv e) < dimword (:256)` by decide_tac >>
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_bytes cenv (post_value_type cenv e)`, `sm`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid cs''` by
    (qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
  `cs_extends sm mid /\ cs_extends mid cs'' /\
   sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= cs''.cs_next_id` by
    gvs[ci_mono_def] >>
  `fn_has_code sm mid func` by metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx es' s` by gvs[vv_post_def] >>
  drule_all runtime_code_copy_alloc_run >> strip_tac >>
  suspend "copy"
QED

Resume runtime_code_copy_run_post_physical[copy]:
  `copy_old_operand mid p.ptr_operand /\ copy_old_operand mid buf.buf_operand` by
    (rw[copy_old_operand_def] >> gvs[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `(type_memory_bytes cenv (post_value_type cenv e) + 31) DIV 32 = type_slot_size tv` by
    (simp[type_memory_size_slots] >> decide_tac) >>
  drule_all copy_runtime_run >> strip_tac >>
  suspend "finish"
QED

Resume runtime_code_copy_run_post_physical[finish]:
  `expr_post ctx func cenv cx e es sa cs'' s0 es' v buf.buf_operand s'` by
    suspend "post" >>
  suspend "code"
QED

Resume runtime_code_copy_run_post_physical[post]:
  `s'.vs_memory = (immutable_transfers F F a w (type_slot_size tv) 0 u).vs_memory` by
    metis_tac[] >>
  `w2n w + type_memory_size tv < dimword (:256)` by metis_tac[] >>
  drule_all copy_runtime_contents >> strip_tac >>
  drule_all runtime_code_copy_memory_frame >> strip_tac >>
  `eval_operand buf.buf_operand s' = SOME w` by
    metis_tac[copy_runtime_frame_operand] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv (post_value_type cenv e)))]
       [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_id = sm.cs_next_id` by
    simp[Abbr `inst`, mk_inst_def] >>
  `sm.cs_next_id < cs''.cs_next_id` by decide_tac >>
  fs[copy_runtime_frame_def] >>
  gvs[] >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) copy_buffer_post_transport_physical >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `copy_static _ = _`)) >>
  disch_then (drule_at (Pat `!x. not_fresh_at _ x ==> lookup_var x _ = lookup_var x _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  disch_then (qspecl_then [`cs''`, `Var p'`] mp_tac) >>
  simp[] >>
  disch_then irule >> metis_tac[]
QED

Resume runtime_code_copy_run_post_physical[code]:
  `same_blocks sm mid /\
   mid.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm mid /\
   EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE])
     (emitted_insts sm mid)` by
    (qpat_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
          comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >>
     gvs[fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def, emitted_insts_def,
         rich_listTheory.DROP_LENGTH_APPEND, same_blocks_def, mk_inst_def]) >>
  drule code_copy_insts >> strip_tac >>
  fs[copy_runtime_frame_def] >>
  qexists_tac `s'` >> simp[run_inst_seq_append] >>
  conj_tac >- gvs[same_blocks_def] >>
  fs[EVERY_MEM] >>
  conj_tac
  >- (qpat_assum `run_inst_seq (emitted_insts sm mid) s = OK u`
        (mp_then Any mp_tac run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts mid cs''` mp_tac) >> simp[]) >>
  gvs[]
QED

Finalise runtime_code_copy_run_post_physical

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
  rpt gen_tac >> strip_tac >>
  `t = post_value_type cenv e` by gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `post_value_type cenv e = expr_type e` kall_tac >>
  gvs[] >> drule_all runtime_code_copy_run_post_physical >> simp[]
QED
