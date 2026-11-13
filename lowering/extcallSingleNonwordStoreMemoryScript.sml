(* Actual singleton tuple stores, without changing the zero-MCOPY case. *)
Theory extcallSingleNonwordStoreMemory
Ancestors
  extcallStoreStagesMemory extcallStoreMemory exprLoweringProps
  exprLowering compileEnv context fragExec

Theorem extcall_single_nonword_store_mem:
  compile_extcall_store_values ce [(vv,lt)] buf off sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (is_bytestring_type lt \/ type_memory_bytes ce lt <> 0) /\
  stmt_state_rel ctx func ce cx es s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand buf s = SOME (n2w b) /\
  b + off + type_memory_size tv < dimword (:256) /\
  b + off + type_memory_size tv <= s.vs_alloca_next /\
  ~is_word_type lt /\ evaluate_type (get_tenv cx) lt = SOME tv /\
  type_memory_bytes ce lt = type_memory_size tv /\
  value_has_type tv v /\ val_wf tv v /\
  vv_holds ce cx lt (Value v) vv es s /\
  vv_store_bound cx lt lt es (Value v) vv s /\ vv_storage_live cx vv es s /\
  (!x. vv_operand vv = Var x \/ buf = Var x ==> not_fresh_at sa x) /\
  (!tag p. vv = LocatedValue tag p ==>
    (p.ptr_location <> LocMemory \/ is_word_type tag ==> tag = lt) /\
    (p.ptr_location = LocCode /\ ce.ce_is_ctor ==>
      !region. ce.ce_imm_alloca = SOME region ==>
        eval_operand region s = SOME 0w /\
        (!x. region = Var x ==> not_fresh_at sa x))) /\
  (!name a n. local_region ce es.scopes s name a n ==>
    a + n <= b + off \/ b + off + type_memory_size tv <= a) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size tv)) ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\
    stmt_state_rel ctx func ce cx es z /\ alloca_history func z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory tv v (b+off) z.vs_memory /\
    contract_storage z = contract_storage s /\
    contract_transient z = contract_transient s /\
    z.vs_data_section = s.vs_data_section /\ z.vs_labels = s.vs_labels /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP z.vs_allocas aid = SOME entry) /\
    (!aid a n x k. FLOOKUP s.vs_allocas aid = SOME (a,n) /\
      aid < sa.cs_next_id /\ a <= x /\ x+k <= a+n /\
      (x+k <= b+off \/ b+off+type_memory_size tv <= x) ==>
      mem_bytes_at x k z.vs_memory = mem_bytes_at x k s.vs_memory) /\
    (!name a n x k. local_region ce es.scopes s name a n /\
      a <= x /\ x+k <= a+n ==>
      mem_bytes_at x k z.vs_memory = mem_bytes_at x k s.vs_memory) /\
    (!name io itv iv x k. ce.ce_is_ctor /\
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) /\
      io <= x /\ x+k <= io+type_memory_size itv ==>
      mem_bytes_at x k z.vs_memory = mem_bytes_at x k s.vs_memory)
Proof
  strip_tac >> drule_all extcall_single_store_stages >> strip_tac >>
  `compile_store_memory ce src dst lt lt su = ((),sb)` by
    (Cases_on `is_bytestring_type lt` >>
     gvs[compile_store_memory_def] >>
     Cases_on `type_memory_size tv` >>
     gvs[compile_copy_memory_def]) >>
  drule_all extcall_stored_nonword_capture_mem >> simp[]
QED
