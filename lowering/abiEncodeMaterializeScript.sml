Theory abiEncodeMaterialize
Ancestors
  abiEncodeMaterializeExec exprSimAggregateChildren exprSimUnwrap
  exprSim context finite_map exprSimCopy freshWrites fragExec exprSimStorageCopy
  exprSimWordArgs venomMemDefs exprSimAlloc exprLowering compileEnv

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
Theorem materialize_vv_post_alloc_frame:
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  stmt_state_rel ctx func cenv cx es' t /\
  t.vs_memory = s.vs_memory /\
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
  `vv_holds cenv cx (expr_type e) tv vv es' t` by
    (irule vv_holds_vars_frame >> qexists_tac `s` >> simp[]) >>
  `vv_at cenv cx (expr_type e) sa sn es' tv vv t` by
    (irule materialize_vv_at_alloc_frame >> qexistsl [`s`, `sm`] >> simp[]) >>
  `locals_kept cenv es s0 t` by
    (irule locals_kept_mem_tail >> qexists_tac `s` >> simp[]) >>
  simp[vv_post_def] >> metis_tac[]
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
  (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
         ~is_word_type (expr_type e) ==>
         type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
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
  irule unwrap_value_rebased_sim >> simp[] >> metis_tac[]
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
      locals_kept ce es s t
Proof
  strip_tac >> drule_all materialize_store_owned_run >> strip_tac >>
  `copy_static t = copy_static s` by
    (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = s`
       (mp_tac o Q.AP_TERM `copy_static`) >> simp[copy_static_def]) >>
  `stmt_state_rel ctx func ce cx es t` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl [`w2n dw`, `inst`, `s`, `sa`, `type_memory_size tv`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `locals_kept ce es s t` by
    (irule copy_buffer_locals_kept_frame >>
     qexistsl [`w2n dw`, `s`, `type_memory_size tv`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexists_tac `t` >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

(* Writing a newly owned allocation cannot damage the original expression
   frame.  The allocation map invariant supplies separation, not a presumed
   full-capacity representation of the input value. *)
Theorem materialize_fresh_store_frame:
  wb_frame ce es sa s0 s /\
  allocas_non_overlapping s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  t.vs_allocas = s.vs_allocas /\
  (!off len. off + len <= b \/ b + sz <= off ==>
     mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!name lb len. local_region ce es.scopes s0 name lb len ==>
     b + sz <= lb \/ lb + len <= b) ==>
  wb_frame ce es sa s0 t
Proof
  strip_tac >>
  `locals_kept ce es s0 t` by
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
  compile_alloc_buffer (type_memory_bytes ce (expr_type e)) sm = (buf,mid) /\
  fn_has_code sm mid func /\ fn_inst_ids_distinct func /\
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r /\
  local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= mid.cs_next_id /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  type_memory_bytes ce (expr_type e) < dimword (:256) ==>
  ?u w. frag_exec ctx sm mid (\z. z = r) (\z. z = u) R /\
    vv_post ctx func ce cx e es sa mid s0 es' tv vv u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sm.cs_next_id =
      SOME (w2n w,type_memory_bytes ce (expr_type e)) /\
    w2n w + type_memory_bytes ce (expr_type e) < dimword (:256) /\
    u.vs_memory = r.vs_memory /\ sm.cs_next_id < mid.cs_next_id /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x r) /\
    (!aid entry. FLOOKUP r.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!name b len. local_region ce es'.scopes u name b len ==>
       regions_disjoint (w2n w) (type_memory_bytes ce (expr_type e)) b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at mid p)
Proof
  strip_tac >> drule materialize_vv_post_operand >> strip_tac >>
  `stmt_state_rel ctx func ce cx es' r` by gvs[vv_post_def] >>
  drule_all alloc_buffer_source_frag >>
  disch_then (qspec_then `R` strip_assume_tac) >>
  `vv_post ctx func ce cx e es sa mid s0 es' tv vv u` by
    (irule materialize_vv_post_alloc_frame >> simp[] >>
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
       expr_val_rel_def, expr_val_at_def, venomStateTheory.lookup_var_def,
       local_region_def, locals_kept_def]
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
  strip_tac >> drule exprSimBufferStoreTheory.buffer_store_memory_shape >> strip_tac >>
  irule exprSimHashTheory.hash_run_frag >> simp[] >>
  reverse conj_tac >- (drule aggregate_store_memory_straight >> simp[]) >>
  rpt strip_tac >>
  drule expr_post_state >> strip_tac >>
  `?sw. eval_operand src z = SOME sw /\
     val_in_memory tv v (w2n sw) z.vs_memory` by
    (gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n w,type_memory_size tv)` by simp[] >>
  `(if is_word_type (expr_type e) then sw = typed_val_to_w256 tv v
    else val_in_memory tv v (w2n sw) z.vs_memory)` by simp[] >>
  drule_all materialize_store_state_run >> strip_tac >>
  `allocas_non_overlapping z` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def, alloca_inv_def] >>
  `wb_frame ce es sa s0 z` by metis_tac[expr_post_frame] >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x z` by
    metis_tac[not_fresh_at_mono] >>
  `wb_frame ce es sa s0 t` by
    (irule materialize_fresh_store_frame >>
     qexistsl [`aid`, `w2n w`, `z`, `type_memory_size tv`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `!name b len. local_region ce es'.scopes t name b len ==>
     w2n w + type_memory_size tv <= b \/ b + len <= w2n w` by
    (rpt strip_tac >> qpat_x_assum `!name b len. local_region _ es'.scopes z _ _ _ ==> _` irule >>
     qexists_tac `name` >>
     `!name b len. local_region ce es'.scopes t name b len <=>
                    local_region ce es'.scopes z name b len` by
       (rpt gen_tac >> irule copy_buffer_local_region_frame >>
        qexists_tac `su` >> simp[]) >> metis_tac[]) >>
  `expr_post ctx func ce cx e es sa sb s0 es' v (Var p) t` by
    (irule copy_buffer_expr_post >>
     fs[wb_frame_def] >> conj_tac
     >- metis_tac[arithmeticTheory.ADD_COMM] >>
     qexistsl [`aid`, `type_memory_size tv`, `w`] >>
     simp[venomStateTheory.eval_operand_def, val_footprint_le] >>
     metis_tac[]) >>
  qexists_tac `t` >>
  simp[materialize_expr_post_inst_idx, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def]
QED
