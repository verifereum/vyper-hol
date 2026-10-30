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
 *   buffer_loop_memory_vv_post — a filled buffer is the parent's vv_post
 *   aggregate_child_unwrap_var, aggregate_child_add_then,
 *   aggregate_unwrap_store_slice_sim — the per-child step
 *   vv_post_old_buffer — an older allocation outside the locals keeps its
 *     bytes
 *   local_region_vars_backward, vv_post_local_region_backward — local
 *     regions after a child were there before it
 *
 * Helpers: the *_materialise lemmas, vv_*_vars_frame, vv_post_rebase,
 *   the *_rebased_* and aggregate_store_* lemmas, buffer_alloc_provenance.
 *)
Theory exprSimAggregateChildren
Ancestors
  exprSim exprSimHyps exprSimUnwrap exprSimBufferStore exprSimBuffer
  vyperInterpreter vyperValueOperation vyperState fragExec
  compileEnv context exprSimLiteralBuffer exprSimOps venomState
  exprSimHash exprOperandVar emitHelperProps ASCIInumbers exprLoweringProps venomInst
  vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes

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
  metis_tac[arithmeticTheory.LESS_MOD]
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
  vv_post func cenv cx e es sa sb s0 es' tv vv s ==>
  vv_post func cenv cx e es sa sb s0 es' (Value v) vv s
Proof
  pure_rewrite_tac[vv_post_def] >> strip_tac >>
  `vv_holds cenv cx (expr_type e) (Value v) vv es' s` by
    (drule_all vv_holds_materialise >> simp[]) >>
  `vv_at cenv cx (expr_type e) sa sb es' (Value v) vv s` by
    (drule_all vv_at_materialise >> simp[]) >>
  asm_rewrite_tac[]
QED

Theorem unwrap_value_materialise_sim:
  !ctx func cenv cx e es sa sm sb s0 es' tv v vv op R.
    unwrap_value cenv vv sm = (op,sb) /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    read_result cx tv es' = (INL v,es') ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' tv vv s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> irule frag_exec_conseq >>
  qexistsl_tac
    [`\s. vv_post func cenv cx e es sa sm s0 es' (Value v) vv s`,
     `\s. expr_post func cenv cx e es sa sb s0 es' v op s`, `R`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all vv_post_materialise >> simp[]) >>
  irule unwrap_value_sim >> simp[]
QED

Theorem vv_post_old_buffer:
  vv_post func cenv cx e es sa sb s0 es' tv vv s /\
  FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
  (!n b k. local_region cenv es.scopes s0 n b k ==>
    off + sz <= b \/ b + k <= off) ==>
  mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory
Proof
  pure_rewrite_tac[vv_post_def] >> strip_tac >>
  first_x_assum irule >> asm_rewrite_tac[] >>
  qexists_tac `aid` >> asm_rewrite_tac[]
QED

Theorem local_region_vars_forward:
  local_ptrs_reserved cenv sa /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w) /\
  local_region cenv scopes s n b sz ==>
  local_region cenv scopes t n b sz
Proof
  rw[local_region_def] >>
  `not_fresh_at sa p` by
    (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem local_region_vars_backward:
  MAP FDOM scopes0 = MAP FDOM scopes1 /\
  local_ptrs_reserved ce sa /\ local_ptrs_rel func ce scopes0 s0 /\
  (!p w. not_fresh_at sa p /\ lookup_var p s0 = SOME w ==>
    lookup_var p s1 = SOME w) /\
  local_region ce scopes1 s1 name b sz ==>
  local_region ce scopes0 s0 name b sz
Proof
  rw[local_region_def] >>
  `?entry0. lookup_scopes name scopes0 = SOME entry0` by
    (Cases_on `lookup_scopes name scopes0` >> simp[] >>
     drule_all lookup_scopes_none_map_fdom >> simp[]) >>
  `?w0. lookup_var p s0 = SOME w0` by
    (gvs[local_ptrs_rel_def] >> metis_tac[]) >>
  `not_fresh_at sa p` by
    (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `lookup_var p s1 = SOME w0` by metis_tac[] >>
  gvs[] >> metis_tac[]
QED

Theorem vv_post_local_region_backward:
  eval_expr cx e es = (res,es1) /\
  stmt_state_rel func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  vv_post func ce cx e es sa sb s0 es1 tv vv s1 /\
  local_region ce es1.scopes s1 name b sz ==>
  local_region ce es.scopes s0 name b sz
Proof
  rpt strip_tac >> irule local_region_vars_backward >>
  conj_tac
  >- (qexists_tac `func` >>
      gvs[stmt_state_rel_def, state_rel_def]) >>
  qexistsl_tac [`s1`, `sa`, `es1.scopes`] >>
  gvs[vv_post_def] >>
  metis_tac[eval_expr_preserves_scopes_dom]
QED

Theorem vv_holds_vars_frame:
  vv_holds cenv cx ty tv vv es s /\ t.vs_memory = s.vs_memory /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s ==>
  vv_holds cenv cx ty tv vv es t
Proof
  Cases_on `vv` >>
  simp[vv_holds_def, vv_operand_def, expr_val_rel_def] >>
  metis_tac[]
QED

Theorem vv_at_vars_frame:
  vv_at cenv cx ty sa sm es tv vv s /\
  t.vs_allocas = s.vs_allocas /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!n b sz. local_region cenv es.scopes s n b sz ==>
    local_region cenv es.scopes t n b sz) /\
  sm.cs_next_id <= sn.cs_next_id ==>
  vv_at cenv cx ty sa sn es tv vv t
Proof
  Cases_on `vv` >>
  simp[vv_at_def, vv_operand_def, expr_val_at_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem vv_post_vars_frame:
  vv_post func cenv cx e es sa sm s0 es' tv vv s /\
  (t with vs_vars := s.vs_vars) = s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w) /\
  local_ptrs_reserved cenv sa /\ sm.cs_next_id <= sn.cs_next_id /\
  stmt_state_rel func cenv cx es' t ==>
  vv_post func cenv cx e es sa sn s0 es' tv vv t
Proof
  strip_tac >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `t with vs_vars := _ = s`
      (mp_tac o AP_TERM ``\z. (z.vs_memory,z.vs_allocas)``) >> simp[]) >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  `vv_holds cenv cx (expr_type e) tv vv es' t` by
    (drule_all vv_holds_vars_frame >> simp[]) >>
  `vv_at cenv cx (expr_type e) sa sn es' tv vv t` by
    (irule vv_at_vars_frame >> qexistsl_tac [`s`, `sm`] >>
     simp[] >> rpt strip_tac >> irule local_region_vars_forward >>
     qexistsl_tac [`s`, `sa`] >> asm_rewrite_tac[]) >>
  pure_rewrite_tac[vv_post_def] >> asm_rewrite_tac[] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem vv_post_update_var:
  vv_post func cenv cx e es sa sm s0 es' tv vv s /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sm.cs_next_id <= sn.cs_next_id /\ ~not_fresh_at sm x /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) ==>
  vv_post func cenv cx e es sa sn s0 es' tv vv (update_var x w s)
Proof
  strip_tac >>
  `!z. not_fresh_at sm z ==> z <> x` by metis_tac[] >>
  `!z. not_fresh_at sa z ==> z <> x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand (vv_operand vv) (update_var x w s) =
   eval_operand (vv_operand vv) s` by
    (irule literal_operand_frame >>
     reverse conj_tac >- simp[update_var_def] >>
     qexists_tac `sm` >>
     simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `stmt_state_rel func cenv cx es' (update_var x w s)` by
    (irule exprLoweringPropsTheory.stmt_state_rel_update_var >>
     gvs[vv_post_def, not_local_ptr_def, local_ptrs_reserved_def] >>
     metis_tac[]) >>
  irule vv_post_vars_frame >> asm_rewrite_tac[] >>
  qexistsl_tac [`s`, `sm`] >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* The aggregate compiler emits the destination ADD before unwrapping the
   child.  Preserve its value judgment across precisely that update. *)
Theorem buffer_emit_add_vv_post:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  vv_post func cenv cx e es sa sm s0 es' tv vv s /\
  eval_operand buf s = SOME w ==>
  ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
    vv_post func cenv cx e es sa sn s0 es' tv vv q /\
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
    (\s. vv_post func cenv cx e es sa sm s0 es' tv vv s /\
         eval_operand buf s = SOME w)
    (\s. vv_post func cenv cx e es sa sn s0 es' tv vv s /\
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

Theorem vv_post_rebase:
  vv_post func ce cx e es sa sm s0 es' tv vv r ==>
  vv_post func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    sm r es' tv vv r
Proof
  simp[vv_post_def]
QED

Theorem unwrap_value_rebased_sim:
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tv es' = (INL v,es') /\
  vv_post func ce cx e es sa sm s0 es' tv vv r ==>
  frag_exec ctx sm su (\s. s = r)
    (\s. expr_post func ce cx e es'
      (sa with cs_next_var := sm.cs_next_var) su r es' v op s) R
Proof
  strip_tac >> irule frag_exec_conseq >>
  qexistsl_tac
    [`\s. vv_post func ce cx e es'
        (sa with cs_next_var := sm.cs_next_var) sm r es' tv vv s`,
     `\s. expr_post func ce cx e es'
        (sa with cs_next_var := sm.cs_next_var) su r es' v op s`, `R`] >>
  simp[] >> conj_tac
  >- (drule vv_post_rebase >> simp[]) >>
  irule unwrap_value_materialise_sim >> simp[]
QED

Theorem expr_post_rebased_lookup:
  expr_post func ce cx e es (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w ==>
  lookup_var x s = SOME w
Proof
  simp[expr_post_def, not_fresh_at_def] >> metis_tac[]
QED

(* Store the just-unwrapped value.  Both reference-state frames are composed
   here, so consumers need not inspect the rebased expr_post. *)
Theorem aggregate_store_rebased_slice_run:
  compile_store_memory ce op (Var x) (expr_type e) (expr_type e) su = ((),sb) /\
  expr_post func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_vars (module_var_key (ce.ce_module,name)) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) ==>
  ?q. run_inst_seq (emitted_insts su sb) s = OK q /\
    val_in_memory tv v (w2n w) q.vs_memory /\
    stmt_state_rel func ce cx es' q /\
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
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory)
Proof
  strip_tac >>
  `lookup_var x s = SOME w` by
    (drule_at (Pos hd) expr_post_rebased_lookup >> simp[]) >>
  `!n b k. local_region ce es'.scopes s n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b` by
    (rpt strip_tac >>
     `local_region ce es'.scopes r n b k` by
       (irule local_region_frame >> conj_tac
        >- metis_tac[] >>
        qexistsl_tac [`sm`, `es'.scopes`, `s`] >>
        gvs[expr_post_def, not_fresh_at_def]) >> metis_tac[]) >>
  `!z. op = Var z \/ Var x = Var z ==> not_fresh_at su z` by
    (rpt strip_tac >> gvs[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `expr_val_rel cx (expr_type e) v op s /\
   stmt_state_rel func ce cx es' s` by gvs[expr_post_def] >>
  `eval_operand (Var x) s = SOME w` by simp[eval_operand_def] >>
  drule_all (SRULE [] buffer_store_memory_encoding) >> strip_tac >>
  `LENGTH s.vs_memory <= LENGTH q.vs_memory` by
    (drule_all (SRULE [] buffer_store_memory_capacity) >> simp[]) >>
  `stmt_state_rel func ce cx es' q` by
    (irule buffer_store_state_frame >>
     qexistsl_tac [`w2n w`, `type_memory_size tv`, `s`, `su`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
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
  compile_store_memory ce op (Var x) (expr_type e) (expr_type e) su = ((),sb) /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_vars (module_var_key (ce.ce_module,name)) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) ==>
  frag_exec ctx su sb
    (\s. expr_post func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
      su r es' v op s)
    (\q. val_in_memory tv v (w2n w) q.vs_memory /\
      stmt_state_rel func ce cx es' q /\
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
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory)) R
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
      vv_post func ce cx e es sa sm s0 es' tv vv s) R /\
  (!tv r. res = INL tv /\
    vv_post func ce cx e es sa sm s0 es' tv vv r ==>
    eval_operand buf r = SOME w) /\
  (!tv r. res = INL tv /\
    vv_post func ce cx e es sa sn s0 es' tv vv r /\
    eval_operand dst r = SOME (w + n2w off) ==>
    frag_exec ctx sn sb (\s. s = r) Q R) ==>
  frag_exec ctx sa sb P Q R
Proof
  strip_tac >> irule frag_exec_seq_pointwise >>
  qexistsl_tac
    [`\s. ?tv. res = INL tv /\
       vv_post func ce cx e es sa sm s0 es' tv vv s`, `sm`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule frag_exec_seq_pointwise >>
      qexistsl_tac
        [`\s. vv_post func ce cx e es sa sn s0 es' tv vv s /\
             eval_operand dst s = SOME (w + n2w off)`, `sn`] >>
      simp[] >> irule frag_exec_conseq >>
      qexistsl_tac
        [`\s. vv_post func ce cx e es sa sm s0 es' tv vv s /\
             eval_operand buf s = SOME w`,
         `\s. vv_post func ce cx e es sa sn s0 es' tv vv s /\
             eval_operand dst s = SOME (w + n2w off)`, `R`] >>
      simp[] >> irule buffer_emit_add_vv_sim >> simp[]) >>
  metis_tac[cs_extends_trans]
QED

Theorem aggregate_unwrap_store_slice_sim:
  unwrap_value ce vv sm = (op,su) /\
  compile_store_memory ce op (Var x) (expr_type e) (expr_type e) su = ((),sb) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  cs_extends sm su /\ cs_extends su sb /\
  read_result cx tvv es' = (INL v,es') /\
  vv_post func ce cx e es sa sm s0 es' tvv vv r /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_vars (module_var_key (ce.ce_module,name)) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  (!q. val_in_memory tv v (w2n w) q.vs_memory /\
      stmt_state_rel func ce cx es' q /\
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
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) ==>
      Q q) ==>
  frag_exec ctx sm sb (\s. s = r) Q R
Proof
  strip_tac >> irule frag_exec_seq >>
  qexistsl_tac
    [`\s. expr_post func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
        su r es' v op s`, `su`] >> simp[] >>
  conj_tac
  >- (irule unwrap_value_rebased_sim >> simp[] >>
      qexistsl_tac [`es`, `s0`, `tvv`, `vv`] >> simp[]) >>
  drule_all aggregate_store_rebased_slice_sim >>
  disch_then (qspecl_then [`sa`, `ctx`, `R`] mp_tac) >>
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

Theorem buffer_alloc_frag:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  sz < dimword (:256) ==>
  ?inst x. buf.buf_operand = Var x /\ MEM inst (fn_insts func) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [x] /\
    inst.inst_id < sm.cs_next_id /\ not_fresh_at sm x /\
    local_ptrs_reserved ce sm /\ (!scopes. not_local_ptr ce scopes x) /\
    frag_exec ctx sa sm (\s. s = s0 /\ stmt_state_rel func ce cx es s)
      (\t. ?b. stmt_state_rel func ce cx es t /\
        lookup_var x t = SOME (n2w b) /\
        FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\
        b + sz < dimword (:256) /\ t.vs_memory = s0.vs_memory /\
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
  rpt strip_tac >> drule_all buffer_alloc_provenance >> strip_tac >>
  qexistsl [`inst`,`x`] >> simp[] >>
  irule frag_exec_run_inst_seq >> simp[] >> rpt strip_tac >> gvs[] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `!name p n. local_region ce es.scopes t name p n <=>
    local_region ce es.scopes s0 name p n` by
    (rpt gen_tac >> eq_tac
     >- metis_tac[local_region_frame] >>
     metis_tac[local_region_vars_forward]) >>
  disj1_tac >> goal_assum (drule_at Any) >>
  simp[stmt_state_rel_inst_idx, buffer_local_region_inst_idx] >>
  gvs[eval_operand_def, lookup_var_def] >> metis_tac[]
QED

(* Compose the allocation-entry and aggregate-loop frames once for all
   fresh-buffer constructors. *)
Theorem buffer_loop_memory_vv_post:
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ val_in_memory tv v b r.vs_memory /\
  val_footprint tv v <= sz /\ stmt_state_rel func ce cx es' r /\
  p.ptr_location = LocMemory /\
  eval_operand p.ptr_operand r = SOME (n2w b) /\
  ci_mono sa sm /\ ci_mono sm sb /\ sa.cs_next_id < sm.cs_next_id /\
  b + sz < dimword (:256) /\
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
  t.vs_memory = s0.vs_memory ==>
  vv_post func ce cx e es sa sb s0 es' (Value v)
    (LocatedValue (expr_type e) p) r
Proof
  strip_tac >>
  `b < dimword (:256)` by decide_tac >>
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
