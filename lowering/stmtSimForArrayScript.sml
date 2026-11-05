(* Array iteration boundaries shared by loop simulation and body adapters. *)
Theory stmtSimForArray
Ancestors
  supportedStmts vyperTypeSystem vyperTypeValues vyperValue
  arithmetic words vyperAST vyperInterpreter vyperState vyperValueOperation
  vyperArray vyperTypeEnv vyperTypeInvariants vyperTyping exprSimHyps
  compileEnv valueEncodingProps valueEncodingProofs valueCopy stmtLowering
  emitHelperProps exprLoweringProps venomState emitHelper rich_list
  immutableMemoryFrame stmtSimDeclStore loweringSlice localPtrsProps
  stmtSimForArrayFrame valueEncodingTyping list alist pair

Theorem array_for_hypotheses:
  !tops bindings id ty e n body env ret_ty env'.
  supported_stmt tops bindings (For id ty (Array e) n body) /\
  type_stmt env ret_ty (For id ty (Array e) n body) = SOME env' ==>
  ?name env_b.
    e = Name (ArrayT ty (Fixed n)) name /\ env' = env /\
    well_typed_expr env (Name (ArrayT ty (Fixed n)) name) /\
    assignable_type env.type_defs ty /\ id NOTIN FDOM env.var_types /\
    iterator_unmodified (Array (Name (ArrayT ty (Fixed n)) name)) body /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_b /\
    supported_stmts tops bindings body /\
    ~supported_stmts_expr_exists expr_internal_call_root body
Proof
  cheat
QED

Theorem evaluated_fixed_array_bound:
  evaluate_type tenv (ArrayT ty (Fixed n)) = SOME tv ==>
    0 < n /\ n < dimword (:256)
Proof
  cheat
QED

Theorem eval_iterator_fixed_name:
  !cx ty n name es entry elem_tv av.
    lookup_scopes name es.scopes = SOME entry /\
    entry.value = ArrayV av /\
    evaluate_type (get_tenv cx) (ArrayT ty (Fixed n)) =
      SOME (ArrayTV elem_tv (Fixed n)) ==>
    eval_iterator cx (Array (Name (ArrayT ty (Fixed n)) name)) es =
      (INL (array_elements (ArrayTV elem_tv (Fixed n)) av), es)
Proof
  cheat
QED

Theorem fixed_array_elements_length:
  LENGTH (array_elements (ArrayTV elem_tv (Fixed n)) (SArrayV al)) = n
Proof
  cheat
QED

Theorem array_name_local_binding:
  !cenv cx env es ty n name.
    expr_sim_inv cenv cx env es /\
    well_typed_expr env (Name (ArrayT ty (Fixed n)) name) ==>
    ?entry elem_tv ptr sz.
      lookup_scopes name es.scopes = SOME entry /\
      evaluate_type (get_tenv cx) ty = SOME elem_tv /\
      entry.type = ArrayTV elem_tv (Fixed n) /\
      value_has_type entry.type entry.value /\
      well_formed_type_value entry.type /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ptr) sz) /\
      cenv.ce_var_type name = SOME (ArrayT ty (Fixed n)) /\
      0 < n /\ n < dimword (:256)
Proof
  cheat
QED

(* Project the source snapshot at the address used by an array iteration. *)
Theorem fixed_array_element_in_memory:
  !tv n kvs base mem k.
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) base mem /\
    k < n ==>
    val_in_memory tv
      (EL k (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs)))
      (base + k * type_memory_size tv) mem
Proof
  cheat
QED

Theorem fixed_array_element_extent:
  !base n sz k limit.
    base + n * sz <= limit /\ k < n ==>
    base + k * sz + sz <= limit
Proof
  cheat
QED

Theorem fixed_array_element_address:
  !base n sz k.
    base + n * sz < dimword (:256) /\ k < n ==>
    w2n ((n2w base : bytes32) + n2w k * n2w sz) = base + k * sz
Proof
  cheat
QED

Theorem array_iter_composite_copy_run:
  !cenv src dst ty bytes sa sb s tenv tv v sw dw.
    ~is_word_type ty /\
    compile_iter_elem_copy cenv src dst bytes LocMemory F ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    val_in_memory tv v (w2n sw) s.vs_memory /\
    type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  cheat
QED

(* Unlike fresh_vars_wrt, not_fresh_at is stable when this code is run
   again on a later iteration, after its temporary output has a value. *)
Theorem array_iter_word_copy_run:
  !cenv src dst ty bytes sa sb s sw dw.
    is_word_type ty /\
    compile_iter_elem_copy cenv src dst bytes LocMemory F ty ty sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      t.vs_memory = (mstore (w2n dw) (mload (w2n sw) s) s).vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem array_iter_mload_mstore_value:
  !tv v src dst s.
    val_in_memory tv v src s.vs_memory /\ val_wf tv v /\
    type_memory_size tv <= 32 ==>
    val_in_memory tv v dst (mstore dst (mload src s) s).vs_memory
Proof
  cheat
QED

Theorem array_iter_copy_run:
  !cenv src dst ty bytes sa sb s tenv tv v sw dw.
    compile_iter_elem_copy cenv src dst bytes LocMemory F ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    val_in_memory tv v (w2n sw) s.vs_memory /\
    type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  cheat
QED

(* An allocation-local copy preserves the constructor's immutable snapshot. *)
Theorem array_iter_copy_immutables:
  !func cenv cx es s t inst b sz bytes.
    stmt_state_rel ctx func cenv cx es s /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\ bytes <= sz /\
    t.vs_data_section = s.vs_data_section /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!a len. a + len <= b \/ b + bytes <= a ==>
      mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) ==>
    immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t
Proof
  cheat
QED

Theorem array_iter_copy_declare_rel:
  !ctx func cenv cx es s t id p sz w inst v tv sc rest a sa.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!q. q = p \/ ~not_local_ptr cenv es.scopes q ==> not_fresh_at sa q) /\
    (!b len. b + len <= w2n w \/ w2n w + type_memory_size tv <= b ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    type_memory_size tv <= sz /\ val_wf tv v /\
    val_in_memory tv v (w2n w) t.vs_memory ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        (sc |+ (id, <|assignable := a; type := tv; value := v; popped := []|>)) :: rest) t
Proof
  cheat
QED

Theorem fixed_array_elements_typed:
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV al)) /\
  well_formed_type_value (ArrayTV tv (Fixed n)) /\ k < n ==>
  value_has_type tv (EL k (array_elements (ArrayTV tv (Fixed n)) (SArrayV al))) /\
  val_wf tv (EL k (array_elements (ArrayTV tv (Fixed n)) (SArrayV al)))
Proof
  cheat
QED

Theorem array_snapshot_memory:
  !name ei entry tv n al cenv ptr sz ctx func cx s.
  lookup_scopes name ei.scopes = SOME entry /\
  entry.type = ArrayTV tv (Fixed n) /\
  entry.value = ArrayV (SArrayV al) /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ptr) sz) /\
  stmt_state_rel ctx func cenv cx ei s ==>
  ?base. eval_operand (Var ptr) s = SOME base /\
    (!k. k < n ==>
      val_in_memory tv
        (EL k (array_elements (ArrayTV tv (Fixed n)) (SArrayV al)))
        (w2n base + k * type_memory_size tv) s.vs_memory /\
      w2n base + k * type_memory_size tv < dimword (:256))
Proof
  cheat
QED
