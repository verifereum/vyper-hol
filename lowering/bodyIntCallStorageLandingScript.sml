(* Joint counted storage/transient copy at its actual protected landing. *)
Theory bodyIntCallStorageLanding
Ancestors
  bodyIntCallMaterializeLanding storageCopyGasPath exprSimStorageCopy exprSimCopy
  intCallFrame compileEnv finite_map list words

Theorem protected_storage_loop_landing:
  compile_word_copy_loop src dst n loc LocMemory F sa = (result,sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\ fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  n = type_slot_size tv /\ n < 2**256 /\ b+32*n < 2**256 /\
  stmt_state_rel ctx func ce cx es s /\
  storage_holds cx (loc = LocTransient) ty (Value v) a es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ 32*n <= sz /\ allocas_above lo s /\
  (!p k. P p k ==> regions_disjoint p k b (32*n)) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    val_wf tv v /\ val_in_memory tv v b u.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\
    FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    allocas_above lo u /\ copy_static u = copy_static s /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  mp_tac (Q.INST [`sbase` |-> `s`, `u` |-> `result`]
    (SPEC_ALL (SRULE [] (compile_storage_copy_content_capacity_path
      |> Q.SPEC `F`
      |> CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX)))
      |> Q.SPEC `(ctx,func)`)))) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  `copy_static t = copy_static s` by fs[copy_prefix_def] >>
  drule copy_static_fields >> strip_tac >>
  `copy_prefix (if loc = LocTransient then LocTransient else LocStorage)
     a b (type_slot_size tv) s (type_slot_size tv) t` by
    (Cases_on `loc = LocTransient` >> gvs[]) >>
  drule_all copy_buffer_storage_contents >> strip_tac >>
  `!p k. P p k ==> mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory` by
    (rpt strip_tac >> irule copy_prefix_bytes >>
     fs[regions_disjoint_def] >> metis_tac[]) >>
  `!q. reserved q ==> eval_operand q t = eval_operand q s` by
    (rpt strip_tac >> irule storage_copy_operand_preserved >> metis_tac[]) >>
  qexists_tac `t` >> fs[allocas_above_def] >> gvs[]
QED
