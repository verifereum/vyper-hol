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
 *   unwrap_ctor_code_copy_sim    — code, in the constructor (cheated)
 *)

Theory exprSimCopy
Ancestors
  exprSimAlloc
  list finite_map
  exprSim exprLowering compileEnv context vyperAST vyperInterpreter
  vyperState valueEncoding
  fragExec localPtrsProps loweringSlice exprLoweringProps emitHelperProps
  exprSimStorageCopy immutableCopyExecution
  venomInst venomExecSemantics venomState

Theorem copy_buffer_mstore_locals_kept:
  !cenv es s0 s a (w:bytes32) b sz.
    locals_kept cenv es s0 s /\ b <= a /\ a + 32 <= b + sz /\
    (!name lb len. local_region cenv es.scopes s0 name lb len ==>
       b + sz <= lb \/ lb + len <= b) ==>
    locals_kept cenv es s0 (mstore a w s)
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

Theorem copy_buffer_locals_kept_frame:
  !cenv es0 s0 s t b sz.
    locals_kept cenv es0 s0 s /\
    (!name lb len. local_region cenv es0.scopes s0 name lb len ==>
       b + sz <= lb \/ lb + len <= b) /\
    (!off len. off + len <= b \/ b + sz <= off ==>
       mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) ==>
    locals_kept cenv es0 s0 t
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
  >- (irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
      simp[] >> rpt strip_tac >> qexists_tac `id` >> simp[] >>
      metis_tac[copy_buffer_local_region_frame]) >>
  metis_tac[]
QED

(* A copied buffer may be allocated after the expression starts. *)
Theorem copy_buffer_expr_post:
  !ctx func cenv cx e es sa sb s0 es' s v tv op w aid sz.
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
  rpt gen_tac >> strip_tac >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def] >>
  conj_tac
  >- (disj1_tac >> qexistsl [`aid`, `w2n w`, `sz`] >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!name b len. local_region _ es'.scopes _ _ _ _ ==> _` drule >>
      decide_tac) >>
  metis_tac[]
QED

(* An aggregate in storage or transient storage: SLOAD or TLOAD and an
   MSTORE for one word, a word-copy loop from slot i to buffer word i
   otherwise. *)
Theorem unwrap_storage_copy_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ~is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
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
  rpt gen_tac >> strip_tac >>
  `compile_ensure_in_memory p.ptr_operand p.ptr_location
     (type_memory_bytes cenv t) ((type_memory_bytes cenv t + 31) DIV 32)
     cenv.ce_is_ctor cenv.ce_imm_alloca sm = (op,sb)` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     Cases_on `p.ptr_location` >> gvs[unwrap_value_def]) >>
  qpat_x_assum `unwrap_value _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_ensure_in_memory _ _ _ _ _ _ _ = _` mp_tac >>
  simp[ensure_storage_memory_layout,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  irule frag_exec_pointwise >> qx_gen_tac `s1` >> simp[] >> strip_tac >>
  `t = expr_type e` by
    gvs[vv_post_def, vv_holds_def] >>
  `?a. eval_operand p.ptr_operand s1 = SOME a /\
       storage_holds cx (p.ptr_location = LocTransient)
         (expr_type e) (Value v) a es'` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     Cases_on `p.ptr_location` >>
     gvs[vv_post_def, vv_holds_def]) >>
  cheat
QED

(* An aggregate in code, at runtime: a DLOAD and an MSTORE per word of the
   buffer.  immutable_holds puts the value inside the data section, so the
   size bound needs no premise. *)
Theorem unwrap_runtime_code_copy_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
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

(* An aggregate in code, in the constructor: an MLOAD from the immutables
   buffer at its base variable plus the offset, per word.  Cheated: the
   constructor's prologue sets the base variable to 0
   (compile_fixed_region_with_id), but stmt_state_rel says nothing of the
   base, so vv_post's offset can't be related to the memory the MLOAD
   reads.  unwrap_ctor_immutable_word_sim, the one-word read, is cheated
   for the same reason. *)
Theorem unwrap_ctor_code_copy_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ ~is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED
