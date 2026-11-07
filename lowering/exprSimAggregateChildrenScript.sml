(*
 * Children of aggregate literals (#636)
 *
 * Each child is evaluated, unwrapped and stored at its offset in the
 * parent's buffer.  This covers the child's vv_post when materialise turns
 * a storage ArrayRef into a Value, framing locals and older allocations
 * across the child's code, the ADD-unwrap-store step, and the buffer's
 * ALLOCA and final vv_post.
 *
 * TOP-LEVEL:
 *   buffer_alloc_frag — the buffer's ALLOCA, disjoint from older
 *     allocations and locals
 *   aggregate_buffer_clearance — carry buffer clearance through aggregate children
 *   buffer_loop_memory_vv_post — a filled buffer is the parent's vv_post
 *   aggregate_child_unwrap_var, aggregate_child_add_then,
 *   aggregate_unwrap_store_slice_sim — the per-child step
 *   vv_post_old_buffer — an older allocation outside the locals keeps its
 *     bytes
 *   vv_post_local_region_backward — local
 *     regions after a child were there before it
 *
 * Helpers: the *_materialise lemmas, vv_*_vars_frame, vv_post_rebase,
 *   the *_rebased_* and aggregate_store_* lemmas, buffer_alloc_provenance.
 *)
Theory exprSimAggregateChildren
Ancestors
  exprSimVVFrame
  exprSimProps
  loweringPosts vyperTypeSystem vyperValue valueEncoding valueEncodingProofs vyperTyping
  exprSimAlloc typedMemoryCopy
   exprSimHyps exprSimHypsDefs exprSimUnwrap exprSimUnwrapProps exprSimBufferStore exprSimBuffer
  vyperInterpreter vyperValueOperation vyperState fragExec
  compileEnv context exprSimLiteralBuffer exprSimOps venomState
  exprSimHash exprOperandVar emitHelperProps ASCIInumbers exprLoweringProps venomInst
  vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes oracleExecProps

Theorem typed_value_wf:
  (!ty v. value_has_type ty v ==> val_wf ty v) /\
  (!tvs vs. values_have_types tvs vs ==> tuple_val_wf vs tvs) /\
  (!tv n kvs. sparse_has_type tv n kvs ==> kvs_val_wf kvs tv n) /\
  (!tv vs. all_have_type tv vs ==> elems_val_wf vs tv) /\
  (!ftvs fields. struct_has_type ftvs fields ==> fields_val_wf fields ftvs)
Proof
  ho_match_mp_tac value_has_type_ind >>
  simp[value_has_type_def, val_wf_def, type_memory_size_def] >>
  rpt strip_tac >>
  qspec_then `max` assume_tac le_word_size_mul >> decide_tac
QED

Theorem nonbytes_val_footprint:
  (!n. tv <> BaseTV (BytesT (Dynamic n))) /\
  (!n. tv <> BaseTV (StringT n)) ==>
  val_footprint tv v = type_memory_size tv
Proof
  Cases_on `v` >> simp[val_footprint_def] >>
  Cases_on `tv` >> simp[] >> rename1 `BaseTV bt` >>
  Cases_on `bt` >> simp[] >> rename1 `BytesT bd` >>
  Cases_on `bd` >> simp[]
QED

Theorem evaluated_nonbytes_footprint:
  ~is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
  val_footprint tv v = type_memory_size tv
Proof
  strip_tac >> irule nonbytes_val_footprint >>
  Cases_on `ty` >>
  gvs[vyperValueTheory.evaluate_type_def, is_bytestring_type_def,
      AllCaseEqs()]
QED
Theorem arg_fits_zero_memory_size:
  (!sty dty. !stv dtv.
    arg_type_fits sty dty /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv dty = SOME dtv ==>
    (type_memory_size stv = 0 <=> type_memory_size dtv = 0)) /\
  (!stys dtys. !stvs dtvs.
    arg_types_fit stys dtys /\
    OPT_MMAP (evaluate_type tenv) stys = SOME stvs /\
    OPT_MMAP (evaluate_type tenv) dtys = SOME dtvs ==>
    (type_memory_size_list stvs = 0 <=> type_memory_size_list dtvs = 0))
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def, vyperValueTheory.evaluate_type_def,
     AllCaseEqs(), type_memory_size_def, evaluate_types_OPT_MMAP] >>
  gvs[vyperValueTheory.evaluate_type_def, evaluate_types_OPT_MMAP,
      type_memory_size_def]
QED

Theorem widening_zero_memory_size:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv dty = SOME dtv ==>
  (type_memory_size stv = 0 <=> type_memory_size dtv = 0)
Proof
  rw[type_widens_to_def] >> gvs[] >>
  metis_tac[cj 1 arg_fits_zero_memory_size]
QED


Theorem vv_holds_materialise:
  read_result cx tv es = (INL v,es) /\
  vv_holds cenv cx t tv vv es s ==>
  vv_holds cenv cx t (Value v) vv es s
Proof
  Cases_on `vv`
  >- (simp[vv_holds_def] >> rpt strip_tac >>
      gvs[read_result_def, return_def]) >>
  rename1 `LocatedValue t' p` >>
  Cases_on `p.ptr_location` >>
  simp[vv_holds_def, storage_holds_def, immutable_holds_def,
       read_result_def, return_def] >>
  rpt strip_tac >> gvs[read_result_def, return_def] >>
  qexistsl [`name`, `off`, `itv`, `iv`, `k`] >> simp[]
QED

Theorem vv_at_materialise:
  read_result cx tv es = (INL v,es) /\
  vv_holds cenv cx t tv vv es s /\
  vv_at cenv cx t sa sb es tv vv s ==>
  vv_at cenv cx t sa sb es (Value v) vv s
Proof
  Cases_on `vv`
  >- (simp[vv_holds_def, vv_at_def] >> rpt strip_tac >>
      gvs[read_result_def, return_def]) >>
  rename1 `LocatedValue t' p` >>
  simp[vv_at_def, read_result_def, return_def] >>
  metis_tac[]
QED

Theorem vv_post_materialise:
  read_result cx tv es' = (INL v,es') /\
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv s ==>
  vv_post ctx func cenv cx e es sa sb s0 es' (Value v) vv s
Proof
  rpt strip_tac >> drule vv_post_read_result >> metis_tac[]
QED

(* Materialization keeps the child's physical post layout, including widened
   internal-call buffers. *)
Theorem unwrap_value_materialise_physical_sim:
  !ctx func cenv cx e es sa sm sb s0 es' tv v vv op R.
    unwrap_value cenv vv sm = (op,sb) /\
    local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    read_result cx tv es' = (INL v,es') /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tvt /\
           ~is_word_type (post_value_type cenv e) ==>
           type_memory_bytes cenv (post_value_type cenv e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' tv vv s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> irule frag_exec_conseq >>
  qexistsl_tac
    [`\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s`,
     `\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s`, `R`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all vv_post_materialise >> simp[]) >>
  irule unwrap_value_physical_sim >> simp[]
QED

Theorem unwrap_value_materialise_sim:
  !ctx func cenv cx e es sa sm sb s0 es' tv v vv op R.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv vv sm = (op,sb) /\
    local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    read_result cx tv es' = (INL v,es') /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' tv vv s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> irule unwrap_value_materialise_physical_sim >> simp[]
QED

Theorem vv_post_old_buffer:
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv s /\
  FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
  (!n b k. local_region cenv es.scopes s0 n b k ==>
    off + sz <= b \/ b + k <= off) ==>
  mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory
Proof
  pure_rewrite_tac[vv_post_def] >> strip_tac >>
  first_x_assum irule >> asm_rewrite_tac[] >>
  qexists_tac `aid` >> asm_rewrite_tac[]
QED

Theorem vv_post_local_region_backward:
  eval_expr cx e es = (res,es1) /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  vv_post ctx func ce cx e es sa sb s0 es1 tv vv s1 /\
  local_region ce es1.scopes s1 name b sz ==>
  local_region ce es.scopes s0 name b sz
Proof
  rpt strip_tac >> irule local_region_frame >>
  conj_tac
  >- (qexists_tac `func` >>
      gvs[stmt_state_rel_def, state_rel_def]) >>
  qexistsl_tac [`sa`, `es1.scopes`, `s1`] >>
  gvs[vv_post_def] >>
  metis_tac[eval_expr_preserves_scopes_dom]
QED









(* The aggregate compiler emits the destination ADD before unwrapping the
   child.  Preserve its value judgment across precisely that update. *)
Theorem buffer_emit_add_vv_post:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  eval_operand buf s = SOME w ==>
  ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
    vv_post ctx func cenv cx e es sa sn s0 es' tv vv q /\
    eval_operand dst q = SOME (w + n2w off) /\
    (q with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s)
Proof
  strip_tac >> drule_all buffer_emit_add_run >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString sm.cs_next_var))
    (w + n2w off) s` >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac
  >- (irule vv_post_update_var >> simp[] >> qexists_tac `sm` >> simp[] >>
      conj_tac
      >- metis_tac[CONJUNCT1 compiler_compile_var] >>
      simp[not_fresh_at_def, toString_11]) >>
  simp[eval_operand_def, lookup_var_update_var, update_var_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def, lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, toString_11]
QED

Theorem buffer_emit_add_vv_sim:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) ==>
  frag_exec ctx sm sn
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
         eval_operand buf s = SOME w)
    (\s. vv_post ctx func cenv cx e es sa sn s0 es' tv vv s /\
         eval_operand dst s = SOME (w + n2w off)) R
Proof
  strip_tac >> irule frag_exec_run_inst_seq >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  gvs[cs_extends_def, same_blocks_def, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >> disj1_tac >>
  drule_all buffer_emit_add_vv_post >> strip_tac >>
  qexists_tac `q` >> gvs[eval_operand_def, lookup_var_def]
QED

(* Provenance follows the actual compile/ADD/unwrap order, not lower_value. *)
Theorem aggregate_child_unwrap_var:
  compile_expr ce ty e sa = (vv,sm) /\ local_ptrs_reserved ce sa /\
  sm.cs_next_var <= sadd.cs_next_var /\
  unwrap_value ce vv sadd = (op,su) ==>
  !x. op = Var x ==> not_fresh_at su x
Proof
  strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sadd x` by
    metis_tac[CONJUNCT1 compiler_compile_var,
              freshWritesTheory.not_fresh_at_mono] >>
  drule_at (Pos hd) compiler_unwrap_value_var >>
  Cases_on `vv` >> simp[vv_operand_def] >> metis_tac[]
QED

(* Placement uses allocation IDs, independently of the variable watermark. *)
Theorem expr_val_at_start_var[simp]:
  expr_val_at ce cx ty (sa with cs_next_var := n) sb es v op s <=>
  expr_val_at ce cx ty sa sb es v op s
Proof
  simp[expr_val_at_def]
QED

Theorem vv_at_start_var[simp]:
  vv_at ce cx ty (sa with cs_next_var := n) sb es tv vv s <=>
  vv_at ce cx ty sa sb es tv vv s
Proof
  Cases_on `vv` >> simp[vv_at_def]
QED

Theorem vv_own_start_var[simp]:
  vv_own ce cx ty (sa with cs_next_var := n) sb es tv vv s <=>
  vv_own ce cx ty sa sb es tv vv s
Proof
  Cases_on `vv` >> simp[vv_own_def, expr_val_own_def]
QED

Theorem vv_post_rebase:
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r ==>
  vv_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    sm r es' tv vv r
Proof
  simp[vv_post_def]
QED

Theorem unwrap_value_rebased_physical_sim:
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
           ~is_word_type (post_value_type ce e) ==>
           type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
  frag_exec ctx sm su (\s. s = r)
    (\s. expr_post ctx func ce cx e es'
      (sa with cs_next_var := sm.cs_next_var) su r es' v op s) R
Proof
  strip_tac >> irule frag_exec_conseq >>
  qexistsl_tac
    [`\s. vv_post ctx func ce cx e es'
        (sa with cs_next_var := sm.cs_next_var) sm r es' tv vv s`,
     `\s. expr_post ctx func ce cx e es'
        (sa with cs_next_var := sm.cs_next_var) su r es' v op s`, `R`] >>
  simp[] >> conj_tac
  >- (drule vv_post_rebase >> simp[]) >>
  `local_ptrs_reserved ce (sa with cs_next_var := sm.cs_next_var)` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sm` >> simp[]) >>
  irule unwrap_value_materialise_physical_sim >> simp[]
QED

Theorem unwrap_value_rebased_sim:
  post_value_type ce e = expr_type e /\
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
  frag_exec ctx sm su (\s. s = r)
    (\s. expr_post ctx func ce cx e es'
      (sa with cs_next_var := sm.cs_next_var) su r es' v op s) R
Proof
  strip_tac >> irule unwrap_value_rebased_physical_sim >> simp[] >>
  qexistsl_tac [`es`, `s0`, `tv`, `vv`] >> simp[]
QED

Theorem expr_post_rebased_lookup:
  expr_post ctx func ce cx e es (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w ==>
  lookup_var x s = SOME w
Proof
  simp[expr_post_def, not_fresh_at_def] >> metis_tac[]
QED

(* Restrict the expression's old-allocation frame before composing a store.
   The allocation identity remains explicit at this boundary. *)
Theorem expr_post_rebased_slice:
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    off + sz <= b \/ b + k <= off) /\
  off <= a /\ a + len <= off + sz ==>
  mem_bytes_at a len s.vs_memory = mem_bytes_at a len r.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def] >> strip_tac >>
  qpat_x_assum `!aid off sz. _` (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
  strip_tac >> metis_tac[]
QED

Theorem expr_post_rebased_store_slice:
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    off + sz <= b \/ b + k <= off) /\
  off <= a /\ a + len <= off + sz /\
  (!a len. a + len <= dst \/ dst + n <= a ==>
    mem_bytes_at a len q.vs_memory = mem_bytes_at a len s.vs_memory) /\
  (a + len <= dst \/ dst + n <= a) ==>
  mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory
Proof
  strip_tac >> drule_all expr_post_rebased_slice >>
  strip_tac >> metis_tac[]
QED

(* Store the just-unwrapped value.  Both reference-state frames are composed
   here, so consumers need not inspect the rebased expr_post. *)
Theorem aggregate_store_rebased_slice_run:
  post_value_type ce e = expr_type e /\
  compile_store_memory ce op (Var x) (expr_type e) (expr_type e) su = ((),sb) /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel ctx func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) ==>
  ?q. run_inst_seq (emitted_insts su sb) s = OK q /\
    val_in_memory tv v (w2n w) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
      FLOOKUP q.vs_allocas aid = SOME b) /\
    (!aid off sz a k.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b len. local_region ce es'.scopes r n b len ==>
        off + sz <= b \/ b + len <= off) /\
      off <= a /\ a + k <= off + sz /\
      (a + k <= w2n w \/ w2n w + type_memory_size tv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    locals_kept ce es' es' r q
Proof
  strip_tac >>
  `lookup_var x s = SOME w` by
    (drule_at (Pos hd) expr_post_rebased_lookup >> simp[]) >>
  `!n b k. local_region ce es'.scopes s n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b` by
    (rpt strip_tac >>
     `local_region ce es'.scopes r n b k` by
       (irule local_region_frame >> conj_tac
        >- (qexists_tac `func` >>
            gvs[expr_post_def, stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sm`, `es'.scopes`, `s`] >>
        gvs[expr_post_def, not_fresh_at_def]) >> metis_tac[]) >>
  `!z. op = Var z \/ Var x = Var z ==> not_fresh_at su z` by
    (rpt strip_tac >> gvs[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `expr_val_rel cx (expr_type e) v op s /\
   stmt_state_rel ctx func ce cx es' s` by gvs[expr_post_def] >>
  `eval_operand (Var x) s = SOME w` by simp[eval_operand_def] >>
  drule_all (SRULE [] buffer_store_memory_encoding) >> strip_tac >>
  `LENGTH s.vs_memory <= LENGTH q.vs_memory` by
    (drule_all (SRULE [] buffer_store_memory_capacity) >> simp[]) >>
  `stmt_state_rel ctx func ce cx es' q` by
    (irule buffer_store_state_frame >>
     qexistsl_tac [`w2n w`, `type_memory_size tv`, `s`, `su`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `locals_kept ce es' es' r q` by
    (irule locals_kept_regions_tail >> qexists_tac `s` >>
     reverse conj_tac >- gvs[expr_post_def] >>
     rpt strip_tac >> metis_tac[]) >>
  qexists_tac `q` >> simp[] >>
  `q.vs_allocas = s.vs_allocas` by
    (qpat_assum `q with <|vs_memory := _; vs_vars := _|> = s`
      (mp_tac o AP_TERM ``\z. z.vs_allocas``) >> simp[]) >>
  gvs[expr_post_def, not_fresh_at_def] >>
  rpt conj_tac >> rpt strip_tac >>
  `mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz r.vs_memory` by
    (qpat_x_assum `!aid off sz. _` irule >>
     conj_tac >- metis_tac[] >> qexists_tac `aid` >> simp[]) >>
  drule valueEncodingProofsTheory.mem_bytes_at_agree_window >> strip_tac >>
  `mem_bytes_at a k r.vs_memory = mem_bytes_at a k s.vs_memory` by
    (first_x_assum irule >> simp[]) >>
  metis_tac[]
QED

Theorem aggregate_store_memory_straight:
  compile_store_memory ce src dst ty ty sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  strip_tac >> Cases_on `is_word_type ty` >>
  Cases_on `is_bytestring_type ty` >>
  gvs[compile_store_memory_def, compile_store_bytestring_def,
      compile_bytestring_copy_len_def, compile_copy_memory_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       mk_inst_def, is_terminator_def] >>
  Cases_on `type_memory_bytes ce ty` >>
  gvs[compile_copy_memory_def, comp_return_def,
      emitHelperTheory.emit_void_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, emit_def, emitted_insts_def,
      rich_listTheory.DROP_APPEND1, mk_inst_def, is_terminator_def]
QED

Theorem aggregate_store_rebased_slice_sim:
  post_value_type ce e = expr_type e /\
  compile_store_memory ce op (Var x) (expr_type e) (expr_type e) su = ((),sb) /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel ctx func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) ==>
  frag_exec ctx su sb
    (\s. expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
      su r es' v op s)
    (\q. val_in_memory tv v (w2n w) q.vs_memory /\
      stmt_state_rel ctx func ce cx es' q /\
      (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
        lookup_var z q = SOME a) /\
      (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
        FLOOKUP q.vs_allocas aid = SOME b) /\
      (!aid off sz a k.
        FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b len. local_region ce es'.scopes r n b len ==>
          off + sz <= b \/ b + len <= off) /\
        off <= a /\ a + k <= off + sz /\
        (a + k <= w2n w \/ w2n w + type_memory_size tv <= a) ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
      locals_kept ce es' es' r q) R
Proof
  strip_tac >> drule buffer_store_memory_shape >> strip_tac >>
  irule hash_run_frag >> simp[] >>
  reverse conj_tac >- (drule aggregate_store_memory_straight >> simp[]) >>
  rpt strip_tac >> drule_all aggregate_store_rebased_slice_run >> strip_tac >>
  qexists_tac `q` >> simp[stmt_state_rel_inst_idx] >>
  conj_tac >- gvs[lookup_var_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  qexistsl_tac [`aid`, `off`, `sz`] >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem aggregate_child_add_then:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
  frag_exec ctx sa sm P
    (\s. ?tv. res = INL tv /\
      vv_post ctx func ce cx e es sa sm s0 es' tv vv s) R /\
  (!tv r. res = INL tv /\
    vv_post ctx func ce cx e es sa sm s0 es' tv vv r ==>
    eval_operand buf r = SOME w) /\
  (!tv r. res = INL tv /\
    vv_post ctx func ce cx e es sa sn s0 es' tv vv r /\
    eval_operand dst r = SOME (w + n2w off) ==>
    frag_exec ctx sn sb (\s. s = r) Q R) ==>
  frag_exec ctx sa sb P Q R
Proof
  strip_tac >> irule frag_exec_seq_pointwise >>
  qexistsl_tac
    [`\s. ?tv. res = INL tv /\
       vv_post ctx func ce cx e es sa sm s0 es' tv vv s`, `sm`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule frag_exec_seq_pointwise >>
      qexistsl_tac
        [`\s. vv_post ctx func ce cx e es sa sn s0 es' tv vv s /\
             eval_operand dst s = SOME (w + n2w off)`, `sn`] >>
      simp[] >> irule frag_exec_conseq >>
      qexistsl_tac
        [`\s. vv_post ctx func ce cx e es sa sm s0 es' tv vv s /\
             eval_operand buf s = SOME w`,
         `\s. vv_post ctx func ce cx e es sa sn s0 es' tv vv s /\
             eval_operand dst s = SOME (w + n2w off)`, `R`] >>
      simp[] >> irule buffer_emit_add_vv_sim >> simp[]) >>
  metis_tac[cs_extends_trans]
QED

Theorem aggregate_unwrap_store_slice_sim:
  post_value_type ce e = expr_type e /\
  unwrap_value ce vv sm = (op,su) /\
  compile_store_memory ce op (Var x) (expr_type e) (expr_type e) su = ((),sb) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  cs_extends sm su /\ cs_extends su sb /\
  read_result cx tvv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  (~is_word_type (expr_type e) ==> type_memory_size tv < 2 ** 64) /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  stmt_state_rel ctx func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  (!q. val_in_memory tv v (w2n w) q.vs_memory /\
      stmt_state_rel ctx func ce cx es' q /\
      (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
        lookup_var z q = SOME a) /\
      (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
        FLOOKUP q.vs_allocas aid = SOME b) /\
      (!aid off sz a k.
        FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b len. local_region ce es'.scopes r n b len ==>
          off + sz <= b \/ b + len <= off) /\
        off <= a /\ a + k <= off + sz /\
        (a + k <= w2n w \/ w2n w + type_memory_size tv <= a) ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
      locals_kept ce es' es' r q ==>
      Q q) ==>
  frag_exec ctx sm sb (\s. s = r) Q R
Proof
  strip_tac >> irule frag_exec_seq >>
  qexistsl_tac
    [`\s. expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
        su r es' v op s`, `su`] >> simp[] >>
  conj_tac
  >- (irule unwrap_value_rebased_sim >> simp[] >>
      conj_tac >- (strip_tac >> fs[]) >>
      qexistsl_tac [`es`, `s0`, `tvv`, `vv`] >> simp[]) >>
  drule_all aggregate_store_rebased_slice_sim >>
  disch_then (qspecl_then [`sa`, `R`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_weaken) >>
  simp[] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  qexistsl_tac [`aid`, `off`, `sz`] >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

(* Allocation's static provenance is independent of the source expression. *)
Theorem buffer_alloc_provenance:
  compile_alloc_buffer sz sa = (buf,sm) /\
  fn_has_code sa sm func /\ local_ptrs_reserved ce sa ==>
  ?inst x. buf.buf_operand = Var x /\ MEM inst (fn_insts func) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [x] /\
    inst.inst_id < sm.cs_next_id /\ not_fresh_at sm x /\
    local_ptrs_reserved ce sm /\
    (!scopes. not_local_ptr ce scopes x) /\
    sm.cs_blocks = sa.cs_blocks /\ sm.cs_current_bb = sa.cs_current_bb /\
    isPREFIX sa.cs_current_insts sm.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sm)
Proof
  rpt strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
    comp_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
    emit_def, comp_ignore_bind_def] >> strip_tac >> gvs[] >>
  qexists `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  simp[venomInstTheory.mk_inst_def, not_fresh_at_def,
    ASCIInumbersTheory.toString_11, emitted_insts_def,
    rich_listTheory.DROP_LENGTH_APPEND, rich_listTheory.IS_PREFIX_APPEND,
    venomInstTheory.is_terminator_def] >>
  conj_tac >- (irule local_ptrs_reserved_next_var >>
    goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[local_ptrs_reserved_fresh, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem buffer_local_region_inst_idx[local]:
  local_region ce scopes (t with vs_inst_idx := k) name p n <=>
  local_region ce scopes t name p n
Proof
  simp[local_region_def, lookup_var_def]
QED

(* Code without GAS leaves the gas readings alone. *)
Theorem buffer_run_gas_readings[local]:
  !code s t. EVERY (\i. i.inst_opcode <> GAS) code /\
    run_inst_seq code s = OK t ==> t.vs_gas_readings = s.vs_gas_readings
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >>
  Cases_on `step_inst_base h s` >> simp[] >> strip_tac >>
  metis_tac[oracleExecPropsTheory.step_inst_base_gas_readings]
QED

Theorem buffer_alloc_frag:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  sz < dimword (:256) ==>
  ?inst x. buf.buf_operand = Var x /\ MEM inst (fn_insts func) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [x] /\
    inst.inst_id < sm.cs_next_id /\ not_fresh_at sm x /\
    local_ptrs_reserved ce sm /\ (!scopes. not_local_ptr ce scopes x) /\
    frag_exec ctx sa sm (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
      (\t. ?b. stmt_state_rel ctx func ce cx es t /\
        lookup_var x t = SOME (n2w b) /\
        FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\
        b + sz < dimword (:256) /\ t.vs_memory = s0.vs_memory /\
        t.vs_gas_readings = s0.vs_gas_readings /\
        (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s0) /\
        (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
          FLOOKUP t.vs_allocas aid = SOME a) /\
        (!aid p n. aid < sa.cs_next_id /\
          FLOOKUP s0.vs_allocas aid = SOME (p,n) ==>
          regions_disjoint b sz p n) /\
        (!name p n. local_region ce es.scopes t name p n ==>
          regions_disjoint b sz p n) /\
        (!name p n. local_region ce es.scopes t name p n <=>
          local_region ce es.scopes s0 name p n)) R
Proof
  rpt strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sm)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def, comp_ignore_bind_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
       venomInstTheory.mk_inst_def]) >>
  drule_all buffer_alloc_provenance >> strip_tac >>
  qexistsl [`inst`,`x`] >> simp[] >>
  irule frag_exec_run_inst_seq >> simp[] >> rpt strip_tac >> gvs[] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `t.vs_gas_readings = s0.vs_gas_readings` by
    metis_tac[buffer_run_gas_readings] >>
  `!name p n. local_region ce es.scopes t name p n <=>
    local_region ce es.scopes s0 name p n` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule local_region_frame >> conj_tac
         >- (qexists_tac `func` >>
             gvs[stmt_state_rel_def, state_rel_def]) >>
         qexistsl [`sa`, `es.scopes`, `t`] >> simp[]) >>
     metis_tac[local_region_frame_fwd]) >>
  disj1_tac >> goal_assum (drule_at Any) >>
  simp[stmt_state_rel_inst_idx, buffer_local_region_inst_idx] >>
  gvs[eval_operand_def, lookup_var_def] >> metis_tac[]
QED

(* Compose the allocation-entry and aggregate-loop frames once for all
   fresh-buffer constructors. *)
Theorem aggregate_buffer_clearance:
  stmt_state_rel ctx func ce cx es t /\
  local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (!z w. not_fresh_at sm z /\ lookup_var z t = SOME w ==>
         lookup_var z r = SOME w) /\
  (!name lb len. local_region ce es.scopes t name lb len <=>
                  local_region ce es.scopes s0 name lb len) /\
  (!name lb len. local_region ce es.scopes s0 name lb len ==>
                  regions_disjoint b sz lb len)
  ==>
  !name lb len. local_region ce es'.scopes r name lb len ==>
                 b + sz <= lb \/ lb + len <= b
Proof
  rpt strip_tac >>
  `local_region ce es.scopes t name lb len` by
    (irule local_region_frame >> conj_tac
     >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl [`sm`, `es'.scopes`, `r`] >> simp[]) >>
  `local_region ce es.scopes s0 name lb len` by metis_tac[] >>
  qpat_x_assum `!name lb len. local_region _ _ s0 _ _ _ ==> _` drule >>
  simp[regions_disjoint_def]
QED

Theorem buffer_loop_memory_vv_post:
  post_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ val_in_memory tv v b r.vs_memory /\
  val_footprint tv v <= sz /\ stmt_state_rel ctx func ce cx es' r /\
  p.ptr_location = LocMemory /\
  eval_operand p.ptr_operand r = SOME (n2w b) /\
  ci_mono sa sm /\ ci_mono sm sb /\ sa.cs_next_id < sm.cs_next_id /\
  b + sz < dimword (:256) /\
  (!name lb len. local_region ce es'.scopes r name lb len ==>
    b + sz <= lb \/ lb + len <= b) /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,sz) /\
  (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s0) /\
  (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
    FLOOKUP t.vs_allocas aid = SOME a) /\
  (!aid a n. aid < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas aid = SOME (a,n) ==> regions_disjoint b sz a n) /\
  (!name a n. local_region ce es.scopes t name a n <=>
    local_region ce es.scopes s0 name a n) /\
  (!z w. not_fresh_at sm z /\ lookup_var z t = SOME w ==>
    lookup_var z r = SOME w) /\
  (!aid a. FLOOKUP t.vs_allocas aid = SOME a ==>
    FLOOKUP r.vs_allocas aid = SOME a) /\
  (!aid a n. FLOOKUP t.vs_allocas aid = SOME (a,n) /\
    aid < sm.cs_next_id /\ (a+n <= b \/ b+sz <= a) /\
    (!name lo k. local_region ce es.scopes t name lo k ==>
      a+n <= lo \/ lo+k <= a) ==>
    mem_bytes_at a n r.vs_memory = mem_bytes_at a n t.vs_memory) /\
  t.vs_memory = s0.vs_memory /\ locals_kept ce es es' t r ==>
  vv_post ctx func ce cx e es sa sb s0 es' (Value v)
    (LocatedValue (expr_type e) p) r
Proof
  strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `locals_kept ce es es' s0 r` by
    (qpat_x_assum `locals_kept ce es es' t r` mp_tac >>
     rewrite_tac[locals_kept_def, popped_kept_def] >>
     qpat_assum `!name a n. local_region _ _ t _ _ _ <=> _`
       (fn th => rewrite_tac[th]) >>
     qpat_assum `t.vs_memory = _` (fn th => rewrite_tac[th])) >>
  irule buffer_memory_vv_post_general >>
  simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (irule freshWritesTheory.not_fresh_at_mono >>
         qexists `sa` >> gvs[ci_mono_def]) >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      qpat_x_assum `!aid a n. FLOOKUP t.vs_allocas _ = _ /\ _ ==> _` irule >>
      simp[] >> conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!n b' k. local_region _ _ _ _ _ _ ==> _`
            (qspecl_then [`name`,`lo`,`k`] mp_tac) >> simp[] >> decide_tac) >>
      conj_tac >- (qexists `aid` >> gvs[ci_mono_def] >> metis_tac[]) >>
      qpat_x_assum `!aid a n. _ /\ _ ==> regions_disjoint _ _ _ _`
        (qspecl_then [`aid`,`off`,`len`] mp_tac) >>
      simp[regions_disjoint_def] >> decide_tac) >>
  conj_tac >- (gvs[ci_mono_def] >> decide_tac) >>
  qexists `sz` >>
  simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> metis_tac[]
QED

(* Interface probe: disjoint allocations give full-layout source safety. *)
Theorem aggregate_allocated_source_bounds:
  stmt_state_rel ctx func ce cx es s /\
  FLOOKUP s.vs_allocas aid = SOME (a,n) /\
  FLOOKUP s.vs_allocas did = SOME (b,k) /\ aid <> did /\
  a <= src /\ src + len <= a+n /\
  b <= dst /\ dst + dlen <= b+k ==>
  src + len < dimword (:256) /\
  (src + len <= dst \/ dst + dlen <= src)
Proof
  strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[exprLoweringPropsTheory.alloca_room_next_lt,
              exprLoweringPropsTheory.stmt_state_rel_def] >>
  `alloca_inv s` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
  `a+n <= s.vs_alloca_next` by
    (fs[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  `a+n <= b \/ b+k <= a` by
    (fs[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.allocas_non_overlapping_def] >> metis_tac[]) >>
  decide_tac
QED

Theorem aggregate_physical_source_bounds:
  expr_val_at ce cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  val_footprint tv v = type_memory_size tv /\ 0 < type_memory_size tv /\
  eval_operand op s = SOME sw /\ stmt_state_rel ctx func ce cx es s /\
  FLOOKUP s.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= dst /\ dst + dlen <= b+k /\
  (!name a n. local_region ce es.scopes s name a n ==>
    a+n <= dst \/ dst+dlen <= a) ==>
  w2n sw + type_memory_size tv < dimword (:256) /\
  (w2n sw + type_memory_size tv <= dst \/ dst+dlen <= w2n sw)
Proof
  strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[exprLoweringPropsTheory.alloca_room_next_lt,
              exprLoweringPropsTheory.stmt_state_rel_def] >>
  `local_ptrs_rel func ce es.scopes s` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[]
  >- (`alloca_inv s` by
        gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
      `b'+sz <= s.vs_alloca_next` by
        (fs[venomMemDefsTheory.alloca_inv_def,
            venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
      `b'+sz <= b \/ b+k <= b'` by
        (fs[venomMemDefsTheory.alloca_inv_def,
            venomMemDefsTheory.allocas_non_overlapping_def] >>
         `aid <> did` by decide_tac >> metis_tac[]) >> decide_tac)
  >- (`b' + sz <= s.vs_alloca_next` by
        (fs[local_ptrs_rel_def, local_region_def] >>
         first_x_assum drule_all >> strip_tac >> gvs[]) >>
      first_x_assum drule >> decide_tac) >>
  simp[wordsTheory.w2n_lt]
QED

Theorem aggregate_physical_source_slot_bounds:
  expr_val_at ce cx sty sa sb es v op s /\
  evaluate_type (get_tenv cx) sty = SOME tv /\ ~is_word_type sty /\
  ~is_bytestring_type sty /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  eval_operand op s = SOME sw /\ stmt_state_rel ctx func ce cx es s /\
  FLOOKUP s.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n dw /\ w2n dw + type_memory_size dtv <= b+k /\
  (!name a n. local_region ce es.scopes s name a n ==>
    a+n <= w2n dw \/ w2n dw + type_memory_size dtv <= a) ==>
  w2n sw + type_memory_size tv < dimword (:256) /\
  (w2n sw + type_memory_size tv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw)
Proof
  strip_tac >> Cases_on `type_memory_size tv = 0`
  >- (drule_all widening_zero_memory_size >> strip_tac >>
      gvs[wordsTheory.w2n_lt] >> decide_tac) >>
  `val_footprint tv v = type_memory_size tv` by
    metis_tac[evaluated_nonbytes_footprint] >>
  `0 < type_memory_size tv` by decide_tac >>
  drule_all aggregate_physical_source_bounds >> simp[]
QED

Theorem aggregate_child_physical_encoding:
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  expr_post ctx func ce cx e ers sa sb r es' v op s /\
  ~is_word_type (post_value_type ce e) ==>
  ?stv sw.
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv /\
    value_has_type stv v /\ val_wf stv v /\
    eval_operand op s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    type_widens_to (get_tenv cx) (post_value_type ce e) (expr_type e)
Proof
  strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule_all memory_rhs_read_post_typed >>
  simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >> strip_tac >>
  `val_wf tv v` by metis_tac[cj 1 typed_value_wf] >>
  `type_widens_to (get_tenv cx) (post_value_type ce e) (expr_type e)` by
    (fs[expr_body_pre_def] >>
     drule_all post_value_type_widens >> simp[]) >>
  gvs[expr_post_def, expr_val_rel_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Typed copies may change the control location, but not the data-state
   invariants used by the aggregate store frame. *)
Theorem aggregate_store_control_frame:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
  (!a k. a+k <= dst \/ dst+n <= a ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    b+sz <= dst \/ dst+n <= b) /\
  LENGTH s.vs_memory <= LENGTH q.vs_memory /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) dst n) ==>
  stmt_state_rel ctx func ce cx es q
Proof
  strip_tac >>
  qabbrev_tac `t = q with <|vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>` >>
  `stmt_state_rel ctx func ce cx es t` by
    (irule buffer_store_state_frame >>
     qexistsl [`dst`, `n`, `s`, `sa`] >>
     simp[Abbr `t`, lookup_var_def] >>
     gvs[venom_state_component_equality, lookup_var_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `stmt_state_rel ctx func ce cx es t` mp_tac >>
  simp[Abbr `t`] >> rpt (pop_assum kall_tac) >>
  simp[stmt_state_rel_def, state_rel_def, accounts_rel_def, local_ptrs_rel_def,
      local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
      transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
      contract_storage_def, contract_transient_def, venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.allocas_non_overlapping_def,
      venomMemDefsTheory.alloca_next_valid_def, alloca_room_def, fmp_room_def,
      pending_alloca_size_def, immutable_alloca_sep_def, immutable_base_zero_alt] >>
  strip_tac >> gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED


Theorem aggregate_store_rebased_control_frame:
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  sm.cs_next_var <= su.cs_next_var /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
    vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!z. not_fresh_at su z ==> lookup_var z q = lookup_var z s) /\
  (!a len. a+len <= dst \/ dst+n <= a ==>
    mem_bytes_at a len q.vs_memory = mem_bytes_at a len s.vs_memory) /\
  (!name b k. local_region ce es'.scopes s name b k ==>
    b+k <= dst \/ dst+n <= b) /\
  LENGTH s.vs_memory <= LENGTH q.vs_memory /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) dst n) ==>
  stmt_state_rel ctx func ce cx es' q /\
  (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
    lookup_var z q = SOME a) /\
  (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
    FLOOKUP q.vs_allocas aid = SOME b) /\
  (!aid off sz a len.
    FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!name b k. local_region ce es'.scopes r name b k ==>
      off+sz <= b \/ b+k <= off) /\
    off <= a /\ a+len <= off+sz /\ (a+len <= dst \/ dst+n <= a) ==>
    mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
  locals_kept ce es' es' r q
Proof
  strip_tac >>
  conj_tac
  >- (irule aggregate_store_control_frame >>
      qexistsl [`dst`, `n`, `s`, `su`] >> simp[] >>
      gvs[expr_post_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >>
      `lookup_var z s = SOME a` by
        (drule_all expr_post_rebased_lookup >> simp[]) >>
      `not_fresh_at su z` by
        metis_tac[freshWritesTheory.not_fresh_at_mono] >> simp[]) >>
  conj_tac
  >- (gvs[expr_post_def, venom_state_component_equality] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ q.vs_memory = _` mp_tac >>
      pop_assum mp_tac >> rpt (pop_assum kall_tac) >>
      metis_tac[expr_post_rebased_store_slice]) >>
  irule locals_kept_regions_tail >> qexists `s` >>
  reverse conj_tac >- gvs[expr_post_def] >>
  rpt strip_tac >>
  `local_region ce es'.scopes s n' b sz` by
    (irule local_region_frame_fwd >>
     qexistsl [`r`, `sm`, `es'.scopes`] >> simp[] >>
     rpt strip_tac >> drule_all expr_post_rebased_lookup >> simp[]) >>
  metis_tac[]
QED

Theorem aggregate_store_body_typed_run:
  compile_store_memory_typed ce (Var x) (expr_type e) op
    (post_value_type ce e) su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  ~is_word_type (post_value_type ce e) /\
  ~is_bytestring_type (post_value_type ce e) /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!name a len. local_region ce es'.scopes r name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  fn_has_code su sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = su.cs_current_bb /\ s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?q. val_in_memory tv v (w2n w) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
    (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
    (!aid off sz a len.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!name b k. local_region ce es'.scopes r name b k ==>
        off+sz <= b \/ b+k <= off) /\
      off <= a /\ a+len <= off+sz /\
      (a+len <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
    locals_kept ce es' es' r q /\
    (!fuel rr. run_from fuel ctx fn q = rr /\ (!err. rr <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn s = rr)
Proof
  strip_tac >>
  `lookup_var x s = SOME w` by
    (drule_all expr_post_rebased_lookup >> simp[]) >>
  `!name a len. local_region ce es'.scopes s name a len ==>
    a+len <= w2n w \/ w2n w+type_memory_size tv <= a` by
    (rpt strip_tac >>
     `local_region ce es'.scopes r name a len` by
       (irule local_region_frame >> conj_tac
        >- (qexists `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
        qexistsl [`sm`, `es'.scopes`, `s`] >>
        gvs[expr_post_def, not_fresh_at_def]) >> metis_tac[]) >>
  drule_all aggregate_child_physical_encoding >> strip_tac >>
  `stmt_state_rel ctx func ce cx es' s /\
   expr_val_at ce cx (post_value_type ce e)
     (sa with cs_next_var := sm.cs_next_var) su es' v op s /\
   FLOOKUP s.vs_allocas did = SOME (b,k)` by
    (gvs[expr_post_def] >> metis_tac[]) >>
  `did < (sa with cs_next_var := sm.cs_next_var).cs_next_id` by simp[] >>
  drule_all aggregate_physical_source_slot_bounds >>
  disch_then (CONJUNCTS_THEN assume_tac) >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields)` by
    (fs[expr_body_pre_def, expr_sim_inv_def] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!z. Var x = Var z ==> not_fresh_at su z` by
    (rpt strip_tac >> gvs[] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `eval_operand (Var x) s = SOME w` by simp[eval_operand_def] >>
  drule_all compile_store_memory_typed_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all aggregate_store_rebased_control_frame >> strip_tac >>
  qexists `t` >> fs[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem aggregate_store_body_typed_sim:
  compile_store_memory_typed ce (Var x) (expr_type e) op
    (post_value_type ce e) su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  ~is_word_type (post_value_type ce e) /\
  ~is_bytestring_type (post_value_type ce e) /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!name a len. local_region ce es'.scopes r name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) ==>
  frag_exec ctx su sb
    (\s. expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
      su r es' v op s)
    (\q. val_in_memory tv v (w2n w) q.vs_memory /\
      stmt_state_rel ctx func ce cx es' q /\
      (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
      (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
      (!aid off sz a len.
        FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!name b k. local_region ce es'.scopes r name b k ==>
          off+sz <= b \/ b+k <= off) /\
        off <= a /\ a+len <= off+sz /\
        (a+len <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
        mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
      locals_kept ce es' es' r q) R
Proof
  strip_tac >> simp[frag_exec_def] >> rpt strip_tac >>
  drule_all aggregate_store_body_typed_run >> strip_tac >>
  disj1_tac >> qexists `q` >> fs[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem compile_store_memory_post_type:
  !ce e env src dst.
    well_typed_expr env e ==>
    compile_store_memory ce src dst (expr_type e) (lowered_value_type ce e) =
    compile_store_memory ce src dst (expr_type e) (post_value_type ce e)
Proof
  ho_match_mp_tac exprLoweringTheory.lowered_value_type_ind >>
  simp[exprLoweringTheory.lowered_value_type_def, post_value_type_def,
       vyperASTTheory.expr_type_def, is_bytestring_type_def,
       vyperTypeSystemTheory.well_typed_expr_def,
       vyperTypeSystemTheory.type_builtin_result_ok_def] >>
  rpt strip_tac >> gvs[is_bytestring_type_def, compile_store_memory_def] >>
  gvs[vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  rpt (qpat_x_assum `(_ = BaseT _ /\ _) \/ _` strip_assume_tac) >>
  gvs[is_bytestring_type_def]
QED

Theorem aggregate_store_body_rebased_slice_sim:
  compile_store_memory ce op (Var x) (expr_type e) (lowered_value_type ce e)
    su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  (int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields) /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!name a len. local_region ce es'.scopes r name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) ==>
  frag_exec ctx su sb
    (\s. expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
      su r es' v op s)
    (\q. val_in_memory tv v (w2n w) q.vs_memory /\
      stmt_state_rel ctx func ce cx es' q /\
      (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
      (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
      (!aid off sz a len.
        FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!name b k. local_region ce es'.scopes r name b k ==>
          off+sz <= b \/ b+k <= off) /\
        off <= a /\ a+len <= off+sz /\
        (a+len <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
        mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
      locals_kept ce es' es' r q) R
Proof
  strip_tac >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  drule compile_store_memory_post_type >>
  disch_then (qspecl_then [`ce`, `op`, `Var x`] mp_tac) >>
  disch_then SUBST_ALL_TAC >>
  Cases_on `post_value_type ce e = expr_type e`
  >- (irule aggregate_store_rebased_slice_sim >> fs[] >>
      rpt strip_tac >> metis_tac[]) >>
  `acyclic_struct_metadata ce.ce_struct_fields` by
    metis_tac[post_value_type_no_calls, post_value_type_lowered] >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[post_value_type_word, post_value_type_bytestring] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `type_widens_to (get_tenv cx) (post_value_type ce e) (expr_type e)` by
    (fs[expr_body_pre_def] >> drule_all post_value_type_widens >> simp[]) >>
  `~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e)` by
    metis_tac[return_source_word_widens_eq, type_widens_from_bytestring] >>
  `compile_store_memory_typed ce (Var x) (expr_type e) op
    (post_value_type ce e) su = ((),sb)` by fs[compile_store_memory_def] >>
  drule_all aggregate_store_body_typed_sim >> fs[] >>
  disch_then irule >> simp[]
QED

(* Body-aware child continuation: unwrap at the physical post type, then
   re-layout into the destination slot. *)
Theorem aggregate_body_unwrap_store_slice_sim:
  unwrap_value ce vv sm = (op,su) /\
  compile_store_memory ce op (Var x) (expr_type e) (lowered_value_type ce e)
    su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  (int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  cs_extends sm su /\ cs_extends su sb /\
  read_result cx tvv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
    ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64) /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  (!q. val_in_memory tv v (w2n w) q.vs_memory /\
      stmt_state_rel ctx func ce cx es' q /\
      (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
        lookup_var z q = SOME a) /\
      (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
        FLOOKUP q.vs_allocas aid = SOME b) /\
      (!aid off sz a k.
        FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b len. local_region ce es'.scopes r n b len ==>
          off + sz <= b \/ b + len <= off) /\
        off <= a /\ a + k <= off + sz /\
        (a + k <= w2n w \/ w2n w + type_memory_size tv <= a) ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
      locals_kept ce es' es' r q ==>
      Q q) ==>
  frag_exec ctx sm sb (\s. s = r) Q R
Proof
  strip_tac >> irule frag_exec_seq >>
  qexistsl_tac
    [`\s. expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
        su r es' v op s`, `su`] >> simp[] >>
  conj_tac
  >- (irule unwrap_value_rebased_physical_sim >> simp[] >>
      qexistsl_tac [`es`, `s0`, `tvv`, `vv`] >> simp[]) >>
  drule_all aggregate_store_body_rebased_slice_sim >>
  disch_then (qspec_then `R` mp_tac) >>
  disch_then (mp_then Any irule frag_exec_weaken) >>
  simp[] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  qexistsl_tac [`aid`, `off`, `sz`] >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem aggregate_intcall_result_location:
  compile_call cfn ce rt ty (IntCall fid) args drv sa = (vv,sb) ==>
  !t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory
Proof
  simp[exprLoweringTheory.compile_call_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  Cases_on `returns_count > 0` >> Cases_on `return_buf_size > 0` >>
  gvs[] >> rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[contextTheory.base_ptr_def]
QED

Theorem aggregate_unequal_post_result_location:
  post_value_type ce e <> expr_type e /\
  compile_expr ce ty e si = (vv,sj) ==>
  !t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory
Proof
  strip_tac >>
  `?et fid args drv. e = Call et (IntCall fid) args drv` by
    metis_tac[post_value_type_not_int_call] >>
  qpat_x_assum `e = _` SUBST_ALL_TAC >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once exprLoweringTheory.compile_expr_def] >>
  strip_tac >> drule aggregate_intcall_result_location >> simp[]
QED

Theorem unwrap_value_body_rebased_sim:
  compile_expr ce ty e si = (vv,sj) /\
  expr_body_pre ce cx env e es /\
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) ==>
  frag_exec ctx sm su (\s. s = r)
    (\s. expr_post ctx func ce cx e es'
      (sa with cs_next_var := sm.cs_next_var) su r es' v op s) R
Proof
  strip_tac >> Cases_on `post_value_type ce e = expr_type e`
  >- (irule unwrap_value_rebased_sim >> simp[] >> conj_tac
      >- (rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
      qexistsl_tac [`es`, `s0`, `tv`, `vv`] >> simp[]) >>
  `vv_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    sm r es' (Value v) vv r` by
    (drule_all vv_post_materialise >> disch_then (mp_tac o MATCH_MP vv_post_rebase) >> simp[]) >>
  irule frag_exec_conseq >>
  qexistsl_tac
    [`\s. vv_post ctx func ce cx e es'
        (sa with cs_next_var := sm.cs_next_var) sm r es' (Value v) vv s`,
     `\s. expr_post ctx func ce cx e es'
        (sa with cs_next_var := sm.cs_next_var) su r es' v op s`, `R`] >>
  simp[] >> Cases_on `vv`
  >- (gvs[exprLoweringTheory.unwrap_value_def, comp_return_def] >> irule frag_exec_refl >>
      simp[] >> metis_tac[expr_post_of_vv_post_stack]) >>
  irule unwrap_memory_sim >> simp[] >>
  metis_tac[aggregate_unequal_post_result_location]
QED

Theorem aggregate_body_child_store_slice_sim:
  compile_expr ce ty e si = (vv,sj) /\
  unwrap_value ce vv sm = (op,su) /\
  compile_store_memory ce op (Var x) (expr_type e) (lowered_value_type ce e)
    su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  (int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  cs_extends sm su /\ cs_extends su sb /\
  read_result cx tvv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  (!q. val_in_memory tv v (w2n w) q.vs_memory /\
      stmt_state_rel ctx func ce cx es' q /\
      (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
        lookup_var z q = SOME a) /\
      (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
        FLOOKUP q.vs_allocas aid = SOME b) /\
      (!aid off sz a k.
        FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b len. local_region ce es'.scopes r n b len ==>
          off + sz <= b \/ b + len <= off) /\
        off <= a /\ a + k <= off + sz /\
        (a + k <= w2n w \/ w2n w + type_memory_size tv <= a) ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
      locals_kept ce es' es' r q ==> Q q) ==>
  frag_exec ctx sm sb (\s. s = r) Q R
Proof
  strip_tac >> irule frag_exec_seq >>
  qexistsl_tac
    [`\s. expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
        su r es' v op s`, `su`] >> simp[] >>
  conj_tac
  >- (irule unwrap_value_body_rebased_sim >> simp[] >>
      qexistsl_tac [`env`, `es`, `s0`, `si`, `sj`, `tvv`, `ty`, `vv`] >> simp[]) >>
  drule_all aggregate_store_body_rebased_slice_sim >>
  disch_then (qspec_then `R` mp_tac) >>
  disch_then (mp_then Any irule frag_exec_weaken) >>
  simp[] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  qexistsl_tac [`aid`, `off`, `sz`] >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED
