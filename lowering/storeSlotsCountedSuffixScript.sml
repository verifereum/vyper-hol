(* Counted sparse stores with their source-language storage postcondition. *)
Theory storeSlotsCountedSuffix
Ancestors
  storeSlotsCountedRun storeSlotsMemoryTransfer placeStoreSlots
  exprSimHypsDefs exprSimDefs stmtSimDefs vyperStorage vyperTyping words

Theorem place_store_slots_suffix_run_mem:
  !cenv src dst dty tr sa sb tv func s sw start ctx cx env ee mid name subs
   rootk root path delta writes v.
  compile_store_slots cenv src dst dty tr sa = ((),sb) /\
  evaluate_type (get_tenv cx) dty = SOME tv /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME (n2w start) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n sw + type_memory_size tv <= s.vs_alloca_next /\
  local_ptrs_reserved cenv sa /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\
  val_in_memory tv v (w2n sw) s.vs_memory ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    t.vs_alloca_next = s.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `start < dimword (:256)` by decide_tac >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==>
        sz = type_memory_size tv) fields)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  drule_at (Pat `evaluate_type _ _ = SOME _`) store_slots_rank_run_mem >>
  simp_tac bool_ss [] >>
  disch_then (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
  simp_tac std_ss [wordsTheory.w2n_n2w] >>
  pure_rewrite_tac [GSYM AND_IMP_INTRO] >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  asm_simp_tac std_ss [wordsTheory.w2n_n2w, IgnAsm `start = _`] >>
  pure_rewrite_tac [GSYM AND_IMP_INTRO] >>
  disch_then drule_all >>
  disch_then (qspec_then `ctx` (qx_choosel_then [`t`, `ks`] strip_assume_tac)) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  drule_all store_slots_semantic_endpoint >> simp[]
QED
