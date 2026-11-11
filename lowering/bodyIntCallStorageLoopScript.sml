(* Counted storage-copy loop and typed ownership at one endpoint. *)
Theory bodyIntCallStorageLoop
Ancestors
  storageCopyGasPath exprSimCopy exprSimStorageCopy exprLoweringProps
Libs
  monadsyntax

Theorem storage_copy_loop_owned_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src dst (type_slot_size tv) loc LocMemory F sa = (r,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME (n2w b) /\
  type_slot_size tv < 2**256 /\ b + 32 * type_slot_size tv < 2**256 /\
  ~u.vs_halted /\ u.vs_current_bb = sa.cs_current_bb /\
  u.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func ce cx es u /\
  storage_holds cx (loc = LocTransient) ty (Value v) a es u /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  FLOOKUP u.vs_allocas aid = SOME (b,sz) /\ type_memory_size tv <= sz ==>
  ?z. gas_marked_path F ctx func u 0 (OK z) /\
      copy_prefix loc a b (type_slot_size tv) u (type_slot_size tv) z /\
      LENGTH u.vs_memory <= LENGTH z.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x u) /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      copy_static z = copy_static u /\
      FLOOKUP z.vs_allocas aid = SOME (b,sz) /\
      val_wf tv v /\ val_in_memory tv v b z.vs_memory /\
      val_footprint tv v <= type_memory_size tv /\
      eval_operand dst z = SOME (n2w b)
Proof
  strip_tac >>
  drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)
    (PairRules.PSPEC_ALL (Q.SPEC `F` compile_storage_copy_content_capacity_path)) >>
  disch_then (qspec_then `u` mp_tac) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`ctx`, `b`, `a`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  rename1 `gas_marked_path F ctx func u 0 (OK z)` >>
  `copy_static z = copy_static u` by gvs[copy_prefix_def] >>
  `z.vs_allocas = u.vs_allocas` by metis_tac[copy_static_fields] >>
  `eval_operand dst z = eval_operand dst u` by
    (irule storage_copy_operand_preserved >> metis_tac[]) >>
  `copy_prefix (if loc = LocTransient then LocTransient else LocStorage)
      a b (type_slot_size tv) u (type_slot_size tv) z` by gvs[] >>
  drule_all copy_buffer_storage_contents >> strip_tac >>
  qexists_tac `z` >> simp[]
QED
