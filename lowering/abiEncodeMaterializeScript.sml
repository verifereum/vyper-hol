Theory abiEncodeMaterialize
Ancestors
  abiEncodeMaterializeExec exprSimAggregateChildren exprSimUnwrap
  valueCopyBytes exprSimHyps exprSimLayoutTransport
  exprSimDefs exprSimProps loweringPosts context finite_map exprSimCopy freshWrites fragExec exprSimStorageCopy
  exprSimWordArgs venomMemDefs exprSimAlloc exprLowering compileEnv

Theorem materialize_post_lowered_classify:
  !ce e. ~is_word_type (expr_type e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) ==>
    post_value_type ce e = lowered_value_type ce e \/
    is_bytestring_type (post_value_type ce e) /\
    is_bytestring_type (lowered_value_type ce e)
Proof
  ho_match_mp_tac lowered_value_type_ind >>
  simp[lowered_value_type_def, post_value_type_def, vyperASTTheory.expr_type_def,
       is_bytestring_type_def, is_word_type_def, concat_buffer_type_def] >>
  rpt strip_tac >> gvs[vyperTypeSystemTheory.arg_type_fits_def]
  >~ [`MAP (concat_payload_capacity o expr_type) args`]
  >- (Cases_on `ty` >>
      gvs[vyperTypeSystemTheory.arg_type_fits_def, is_bytestring_type_def] >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[vyperTypeSystemTheory.arg_type_fits_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[vyperTypeSystemTheory.arg_type_fits_def, is_bytestring_type_def])
  >~ [`abi_size_bound _ _`]
  >- (rename1 `arg_type_fits (BaseT (BytesT (Dynamic _))) ty` >>
      Cases_on `ty` >> gvs[vyperTypeSystemTheory.arg_type_fits_def,
                          is_bytestring_type_def] >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[vyperTypeSystemTheory.arg_type_fits_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[vyperTypeSystemTheory.arg_type_fits_def, is_bytestring_type_def]) >>
  IF_CASES_TAC >> gvs[] >>
  metis_tac[compileEnvTheory.arg_type_fits_bytestring_source]
QED

(* A physical expression post can be read at the layout chosen for capture.
   Only bytestring capacities can differ; the copy reads the actual payload. *)
Theorem materialize_expr_post_lowered_source:
  expr_body_pre ce cx env e es /\
  expr_post ctx func ce cx e es0 sa sb s0 es' v src s /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v ==>
  ?w. eval_operand src s = SOME w /\
      val_in_memory tv v (w2n w) s.vs_memory
Proof
  strip_tac >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `~is_word_type (lowered_value_type ce e)` by
    metis_tac[exprSimLayoutTransportTheory.compatible_word_type] >>
  drule_all materialize_post_lowered_classify >> strip_tac
  >- (gvs[expr_post_def, expr_val_rel_def]) >>
  `post_value_type ce e = expr_type e \/
   post_value_type ce e = lowered_value_type ce e` by
    (Cases_on `e` >> simp[post_value_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     simp[post_value_type_def, vyperASTTheory.expr_type_def] >>
     IF_CASES_TAC >> simp[]) >>
  `?ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv` by
    metis_tac[expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS] >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  gvs[expr_post_def, expr_val_rel_def] >>
  irule valueCopyBytesTheory.bytestring_val_in_memory_transfer >>
  simp[] >> qexistsl [`expr_type e`, `lowered_value_type ce e`,
                     `get_tenv cx`, `ptv`] >> simp[]
QED

(* Allocating a new buffer extends the allocation map, rather than leaving
   it equal.  Existing value ownership only needs preservation of entries. *)
Theorem materialize_vv_at_alloc_frame:
  vv_at cenv cx ty sa sm es tv vv s /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP t.vs_allocas aid = SOME entry) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!n b sz. local_region cenv es.scopes s n b sz <=>
     local_region cenv es.scopes t n b sz) /\
  sm.cs_next_id <= sn.cs_next_id ==>
  vv_at cenv cx ty sa sn es tv vv t
Proof
  Cases_on `vv` >>
  simp[vv_at_def, vv_operand_def, expr_val_at_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
        metis_tac[])
  >>~- ([`local_region cenv es.scopes s n b sz`],
        disj2_tac >> disj1_tac >> qexistsl [`n`, `b`, `sz`] >> simp[])
  >> metis_tac[]
QED

(* Transport the incoming captured value over allocation, before unwrap.
   The allocation may extend the map; it does not change existing bytes. *)
Theorem materialize_vv_post_alloc_storage_frame:
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  stmt_state_rel ctx func cenv cx es' t /\
  t.vs_memory = s.vs_memory /\
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= sn.cs_next_id ==>
  vv_post ctx func cenv cx e es sa sn s0 es' tv vv t
Proof
  strip_tac >>
  `!n b sz. local_region cenv es'.scopes s n b sz <=>
             local_region cenv es'.scopes t n b sz` by
    (rpt gen_tac >> sym_tac >> irule copy_buffer_local_region_frame >>
     qexists_tac `sm` >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >> first_x_assum irule >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[vv_post_def] >> strip_tac >>
  `vv_holds cenv cx (post_value_type cenv e) tv vv es' t` by
    (irule exprSimVVFrameTheory.vv_holds_vars_frame >> qexists_tac `s` >> simp[]) >>
  `vv_at cenv cx (post_value_type cenv e) sa sn es' tv vv t` by
    (irule materialize_vv_at_alloc_frame >> qexistsl [`s`, `sm`] >> simp[]) >>
  `locals_kept cenv es es' s0 t` by
    (irule locals_kept_mem_tail >> qexists_tac `s` >> simp[]) >>
  `post_value_type cenv e <> expr_type e ==>
   vv_own cenv cx (post_value_type cenv e) sa sn es' tv vv t` by
    (strip_tac >>
     qpat_x_assum `_ ==> vv_own _ _ _ _ _ _ _ _ _` drule >>
     Cases_on `vv` >>
     simp[vv_own_def, expr_val_own_def, vv_operand_def] >>
     rpt strip_tac >> gvs[vv_operand_def] >>
     disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
     metis_tac[]) >>
  `~expr_has_effect e ==> vv_storage_live cx vv es' t` by
    (Cases_on `vv` >>
     gvs[vv_storage_live_def, vv_operand_def]) >>
  simp[vv_post_def] >> gvs[]
QED

(* Rebase the variable watermark, not the allocation watermark: the
   unwrapped value may still live in an earlier expression allocation. *)
Theorem materialize_unwrap_owned_sim:
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tvv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
         ~is_word_type (post_value_type ce e) ==>
         type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64) /\
  not_fresh_at sm p /\ lookup_var p r = SOME w /\
  FLOOKUP r.vs_allocas aid = SOME (w2n w,sz) ==>
  frag_exec ctx sm su (\s. s = r)
    (\s. expr_post ctx func ce cx e es'
           (sa with cs_next_var := sm.cs_next_var) su r es' v op s /\
         lookup_var p s = SOME w /\
         FLOOKUP s.vs_allocas aid = SOME (w2n w,sz)) R
Proof
  strip_tac >> irule frag_exec_conseq >>
  qexistsl
    [`\s. s = r`,
     `\s. expr_post ctx func ce cx e es'
        (sa with cs_next_var := sm.cs_next_var) su r es' v op s`, `R`] >>
  simp[] >> conj_tac
  >- (gen_tac >> strip_tac >> conj_tac
      >- (drule_all expr_post_rebased_lookup >> simp[]) >>
      gvs[expr_post_def] >> metis_tac[]) >>
  irule unwrap_value_rebased_physical_sim >> simp[] >> metis_tac[]
QED

(* The final store preserves the expression-state invariant because its
   destination is an actual ALLOCA, disjoint from live source locals. *)
Theorem materialize_store_state_run:
  compile_store_memory ce src (Var p) ty ty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
  eval_operand src s = SOME sw /\ lookup_var p s = SOME dw /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,type_memory_size tv) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  (if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory) /\
  type_memory_size tv + 64 < dimword (:256) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  (!name b len. local_region ce es.scopes s name b len ==>
     w2n dw + type_memory_size tv <= b \/ b + len <= w2n dw) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel ctx func ce cx es t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      lookup_var p t = SOME dw /\ t.vs_allocas = s.vs_allocas /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!off len. off + len <= w2n dw \/ w2n dw + type_memory_size tv <= off ==>
        mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
      locals_kept ce es es s t
Proof
  strip_tac >> drule_all materialize_store_owned_run >> strip_tac >>
  `copy_static t = copy_static s` by
    (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = s`
       (mp_tac o Q.AP_TERM `copy_static`) >> simp[copy_static_def]) >>
  `stmt_state_rel ctx func ce cx es t` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl [`w2n dw`, `inst`, `s`, `sa`, `type_memory_size tv`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `locals_kept ce es es s t` by
    (irule copy_buffer_locals_kept_frame >>
     qexistsl [`w2n dw`, `s`, `type_memory_size tv`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexists_tac `t` >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

(* Writing a newly owned allocation cannot damage the original expression
   frame.  The allocation map invariant supplies separation, not a presumed
   full-capacity representation of the input value. *)
Theorem materialize_fresh_store_frame:
  wb_frame ce es es' sa s0 s /\
  allocas_non_overlapping s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  t.vs_allocas = s.vs_allocas /\
  (!off len. off + len <= b \/ b + sz <= off ==>
     mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!name lb len. local_region ce es.scopes s0 name lb len ==>
     b + sz <= lb \/ lb + len <= b) ==>
  wb_frame ce es es' sa s0 t
Proof
  strip_tac >>
  `locals_kept ce es es' s0 t` by
    (irule copy_buffer_locals_kept_frame >>
     qexistsl [`b`, `s`, `sz`] >>
     simp[] >> gvs[wb_frame_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  rewrite_tac[wb_frame_def] >> conj_tac
  >- (rpt strip_tac >> gvs[wb_frame_def] >> metis_tac[]) >>
  conj_tac >- (gvs[wb_frame_def] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  `FLOOKUP s.vs_allocas aid' = SOME (off,sz')` by
    (gvs[wb_frame_def] >> metis_tac[]) >>
  `off + sz' <= b \/ b + sz <= off` by
    (gvs[allocas_non_overlapping_def] >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` irule >>
     qexistsl [`aid'`, `aid`] >> simp[] >> decide_tac) >>
  `mem_bytes_at off sz' t.vs_memory = mem_bytes_at off sz' s.vs_memory` by
    metis_tac[] >>
  gvs[wb_frame_def] >> metis_tac[]
QED

Theorem materialize_vv_post_operand:
  vv_post ctx func ce cx e es sa sm s0 es' tv vv s ==>
  ?w. eval_operand (vv_operand vv) s = SOME w
Proof
  Cases_on `vv` >>
  simp[vv_post_def, vv_holds_def, vv_operand_def, expr_val_rel_def] >>
  metis_tac[]
QED

Theorem materialize_alloc_vv_sim:
  compile_alloc_buffer n sm = (buf,mid) /\
  fn_has_code sm mid func /\ fn_inst_ids_distinct func /\
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r /\
  local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= mid.cs_next_id /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  n < dimword (:256) ==>
  ?u w. frag_exec ctx sm mid (\z. z = r) (\z. z = u) R /\
    vv_post ctx func ce cx e es sa mid s0 es' tv vv u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,n) /\
    w2n w + n < dimword (:256) /\
    u.vs_memory = r.vs_memory /\ sm.cs_next_id < mid.cs_next_id /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x r) /\
    (!aid entry. FLOOKUP r.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!name b len. local_region ce es'.scopes u name b len ==>
       regions_disjoint (w2n w) n b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at mid p)
Proof
  strip_tac >> drule materialize_vv_post_operand >> strip_tac >>
  `stmt_state_rel ctx func ce cx es' r` by gvs[vv_post_def] >>
  drule_all alloc_buffer_source_frag >>
  disch_then (qspec_then `R` strip_assume_tac) >>
  `vv_post ctx func ce cx e es sa mid s0 es' tv vv u` by
    (irule materialize_vv_post_alloc_storage_frame >> simp[] >>
     qexistsl [`r`, `sm`] >> simp[]) >>
  qexistsl [`u`, `w'`] >> simp[] >> metis_tac[]
QED

Theorem materialize_compile_trace:
  compile_materialize_vv ce ty vv sm = (dst,sb) ==>
  ?buf mid src su.
    compile_alloc_buffer (type_memory_bytes ce ty) sm = (buf,mid) /\
    unwrap_value ce vv mid = (src,su) /\
    compile_store_memory ce src buf.buf_operand ty ty su = ((),sb) /\
    dst = buf.buf_operand
Proof
  simp[compile_materialize_vv_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> metis_tac[]
QED

Theorem materialize_expr_post_inst_idx[local]:
  expr_post ctx func ce cx e es sa sb s0 es' v op (s with vs_inst_idx := n) <=>
  expr_post ctx func ce cx e es sa sb s0 es' v op s
Proof
  simp[expr_post_def, exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       expr_val_rel_def, expr_val_at_def, expr_val_own_def,
       venomStateTheory.lookup_var_def,
       local_region_def, locals_kept_def, popped_kept_def]
QED

Theorem materialize_store_owned_post_sim:
  compile_store_memory ce src (Var p) (expr_type e) (expr_type e) su = ((),sb) /\
  expr_post ctx func ce cx e es sa su s0 es' v src z /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at su x) /\ not_fresh_at su p /\
  local_ptrs_reserved ce su /\ sa.cs_next_var <= su.cs_next_var /\
  lookup_var p z = SOME w /\
  FLOOKUP z.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
  (!name b len. local_region ce es'.scopes z name b len ==>
     w2n w + type_memory_size tv <= b \/ b + len <= w2n w) /\
  (!name b len. local_region ce es.scopes s0 name b len ==>
     w2n w + type_memory_size tv <= b \/ b + len <= w2n w) ==>
  frag_exec ctx su sb (\s. s = z)
    (\s. expr_post ctx func ce cx e es sa sb s0 es' v (Var p) s /\
      FLOOKUP s.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      eval_operand (Var p) s = SOME w /\
      val_in_memory tv v (w2n w) s.vs_memory /\
      (!name b len. local_region ce es'.scopes s name b len ==>
         w2n w + type_memory_size tv <= b \/ b + len <= w2n w)) R
Proof
  cheat
QED

Theorem materialize_store_post_sim:
  compile_store_memory ce src (Var p) (expr_type e) (expr_type e) su = ((),sb) /\
  expr_post ctx func ce cx e es sa su s0 es' v src z /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at su x) /\ not_fresh_at su p /\
  local_ptrs_reserved ce su /\ sa.cs_next_var <= su.cs_next_var /\
  lookup_var p z = SOME w /\
  FLOOKUP z.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
  (!name b len. local_region ce es'.scopes z name b len ==>
     w2n w + type_memory_size tv <= b \/ b + len <= w2n w) /\
  (!name b len. local_region ce es.scopes s0 name b len ==>
     w2n w + type_memory_size tv <= b \/ b + len <= w2n w) ==>
  frag_exec ctx su sb (\s. s = z)
    (\s. expr_post ctx func ce cx e es sa sb s0 es' v (Var p) s /\
      FLOOKUP s.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      eval_operand (Var p) s = SOME w /\
      val_in_memory tv v (w2n w) s.vs_memory) R
Proof
  cheat
QED

Theorem materialize_rebase_post:
  vv_post ctx func ce cx e es sa mid s0 es' tvv vv u /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := mid.cs_next_var)
    su u es' v src z /\
  stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= mid.cs_next_var ==>
  expr_post ctx func ce cx e es sa su s0 es' v src z
Proof
  cheat
QED

Theorem compile_materialize_vv_owned_sim:
  compile_materialize_vv ce (expr_type e) vv sm = (dst,sb) /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  read_result cx tvv es' = (INL v,es') /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\
  type_memory_size tv + 64 < dimword (:256) ==>
  frag_exec ctx sm sb (\s. s = r)
    (\s. expr_post ctx func ce cx e es sa sb s0 es' v dst s /\
      sm.cs_next_id < sb.cs_next_id /\
      ?w. eval_operand dst s = SOME w /\
        FLOOKUP s.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
        val_in_memory tv v (w2n w) s.vs_memory /\
        (!name b len. local_region ce es'.scopes s name b len ==>
           w2n w + type_memory_size tv <= b \/ b + len <= w2n w)) R
Proof
  cheat
QED


Theorem compile_materialize_vv_sim:
  compile_materialize_vv ce (expr_type e) vv sm = (dst,sb) /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  read_result cx tvv es' = (INL v,es') /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\
  type_memory_size tv + 64 < dimword (:256) ==>
  frag_exec ctx sm sb (\s. s = r)
    (\s. expr_post ctx func ce cx e es sa sb s0 es' v dst s /\
      ?w. eval_operand dst s = SOME w /\
        FLOOKUP s.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
        val_in_memory tv v (w2n w) s.vs_memory) R
Proof
  cheat
QED
