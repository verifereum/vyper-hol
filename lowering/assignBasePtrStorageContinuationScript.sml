(* Unified direct storage execution, followed by the actual typed RHS adapter. *)
Theory assignBasePtrStorageContinuation
Ancestors assignBasePtrStorageSingle assignBasePtrStorageDirect
  assignBasePtrStorageTypes assignBasePtrStorageExtent assignBasePtrStorageLayout
  assignBasePtrStorageLoop stmtLowering context compileEnv bodyPtrDefs
  exprSimHyps exprSimHypsDefs valueEncodingProps venomState stateFrame
  words arithmetic finite_map

Theorem assign_base_storage_direct_code:
  ~is_bytestring_type ty ==>
  compile_assign_value cenv (Lit k) (if tr then LocTransient else LocStorage)
    (Var root) F loc ty ty NONE capacity =
  (if capacity <= 32 then
     do loaded <- emit_op MLOAD [Var root];
        emit_void (if tr then TSTORE else SSTORE) [Lit k;loaded]
     od
   else do compile_word_copy_loop (Var root) (Lit k) (capacity DIV 32) LocMemory
          (if tr then LocTransient else LocStorage) F; return () od)
Proof
  strip_tac >> Cases_on `tr` >>
  simp[FUN_EQ_THM, compile_assign_value_def, comp_bind_def,
    comp_return_def, comp_ignore_bind_def, compile_memory_to_storage_def,
    compile_memory_to_transient_def] >>
  gen_tac >> pairarg_tac >> simp[]
QED

Theorem assign_base_storage_direct_counted:
  !tr root k n cenv ty loc sa z sb fn s G tn ctx D PG a.
    compile_assign_value cenv (Lit k) (if tr then LocTransient else LocStorage)
      (Var root) F loc ty ty NONE (32*n) sa = (z,sb) /\
    ~is_bytestring_type ty /\ fn_has_code sa sb fn /\ not_fresh_at sa root /\
    ptr_covers G tn root s (32*n) /\ lookup_var root s = SOME a /\
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    0<n /\ n < dimword (:256) /\ w2n a+32*(n-1) < dimword (:256) ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      execution_frame u = execution_frame
        (store_copy_prefix (if tr then LocTransient else LocStorage) a k s n) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage) a k s tn n u tf /\
      ptr_covers Gf tf root u (32*n) /\ lookup_var root u = SOME a /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule assign_base_storage_direct_code >> strip_tac >>
  Cases_on `32*n <= 32`
  >- (`n=1` by decide_tac >> gvs[] >>
      drule_all assign_base_storage_single_compiled_counted >>
      disch_then (qspecl_then [`D`, `PG`] mp_tac) >> simp[]) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  `n < dimword (:256) /\ 32*n <= 32*n` by decide_tac >>
  drule_all assign_base_storage_compiled_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `gf` (qx_choose_then `tf` (qx_choose_then `u` strip_assume_tac))) >>
  qexistsl_tac [`gf`, `tf`, `u`] >> asm_rewrite_tac[] >>
  gvs[execution_frame_def]
QED

Theorem assign_base_storage_typed_counted:
  !cenv e tops bctx cx env pre ret target env' tv v ctx func es s sx sy sa z sb
    root a k tr loc fn G tn D PG.
    body_inv tops bctx cenv cx /\ expr_sim_inv cenv cx env pre /\
    expr_body_pre cenv cx env e pre /\ supported_expr tops e /\
    type_stmt env ret (Assign target e) = SOME env' /\
    supported_storage_type tops (expr_type e) /\ ~is_word_type (expr_type e) /\
    (!elem n. expr_type e <> ArrayT elem (Dynamic n)) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx (expr_type e) sx sy es v (Var root) s /\
    lookup_var root s = SOME a /\
    ptr_covers G tn root s (type_memory_bytes cenv (lowered_value_type cenv e)) /\
    compile_assign_value cenv (Lit k) (if tr then LocTransient else LocStorage)
      (Var root) F loc (expr_type e) (lowered_value_type cenv e) NONE
      (type_memory_bytes cenv (expr_type e)) sa = (z,sb) /\
    fn_has_code sa sb fn /\ not_fresh_at sa root /\
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      execution_frame u = execution_frame (store_copy_prefix
        (if tr then LocTransient else LocStorage) a k s (type_slot_size tv)) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage)
        a k s tn (type_slot_size tv) u tf /\
      ptr_covers Gf tf root u (type_memory_bytes cenv (expr_type e)) /\
      lookup_var root u = SOME a /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_storage_rhs_lowered_type >> strip_tac >>
  drule_all assign_base_typed_assignment_capacity_positive >> strip_tac >>
  drule_all expr_body_pre_copy_ok >> strip_tac >>
  `type_memory_bytes cenv (expr_type e) = 32 * type_slot_size tv` by
    metis_tac[type_memory_size_slots] >>
  `eval_operand (Var root) s = SOME a` by simp[eval_operand_def] >>
  drule_all assign_base_storage_rhs_bound >> strip_tac >>
  drule assign_base_storage_not_bytestring >> strip_tac >>
  `0 < type_slot_size tv /\ type_slot_size tv < dimword (:256) /\
   w2n a+32*(type_slot_size tv-1) < dimword (:256)` by
    (gvs[] >> decide_tac) >>
  `ptr_covers G tn root s (32 * type_slot_size tv)` by metis_tac[] >>
  `compile_assign_value cenv (Lit k) (if tr then LocTransient else LocStorage)
     (Var root) F loc (expr_type e) (expr_type e) NONE
     (32 * type_slot_size tv) sa = (z,sb)` by metis_tac[] >>
  drule_all assign_base_storage_direct_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  asm_rewrite_tac[]
QED
