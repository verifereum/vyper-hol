(* Forcing a value keeps the bytes of every window inside an allocation
   made before the forcing's own (an earlier site's), every variable not
   fresh at sa, and the locals' bytes, on top of what protected_value_forcing
   gives; and it carries where the value sits (vv_at/vv_own from a value
   lowered from sv) to the forced operand. *)
Theory bodyIntCallWindowForcing
Ancestors
  bodyIntCallForcing

Theorem protected_value_window_forcing:
  unwrap_value ce vv sa = (op,sb) /\ vv_holds ce cx ty r vv es s /\
  read_result cx r es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  allocas_above lo s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. P p k ==> p+k <= lo) /\
  (!p k. Win p k ==> ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) /\
  (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
    (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
    ?w a k. eval_operand (vv_operand vv) s = SOME w /\
      a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
      (lo <= a \/ ?b z. staged b z /\ b <= a /\ a+k <= b+z)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_val_rel cx ty v op u /\ stmt_state_rel ctx func ce cx es u /\
    allocas_above lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!p k. Win p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
           lookup_var x u = SOME w) /\
    locals_kept ce es s u /\
    (!sv. sv.cs_next_id <= sa.cs_next_id /\ vv_at ce cx ty sv sa es r vv s ==>
          expr_val_at ce cx ty sv sb es v op u) /\
    (!sv. sv.cs_next_id <= sa.cs_next_id /\ vv_own ce cx ty sv sa es r vv s ==>
          expr_val_own ce cx ty sv sb es v op u) /\
    (!name b sz. local_region ce scopes u name b sz <=> local_region ce scopes s name b sz) /\
    (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty ==>
      ?w a k. eval_operand op u = SOME w /\ a <= w2n w /\
        w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
        (lo <= a \/ ?b z. staged b z /\ b <= a /\ a+k <= b+z)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED
