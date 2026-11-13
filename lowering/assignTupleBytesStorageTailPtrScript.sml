Theory assignTupleBytesStorageTailPtr
Ancestors assignBytesStoragePtr assignBytesStorageLandingPtr bodyPtrDefs

Theorem bytes_storage_place_tail_ptr:
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
    compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
      (Var src) F loc dty sty NONE capacity sa = ((),sb) /\
    is_bytestring_type dty /\ is_bytestring_type sty /\
    type_memory_bytes cenv sty = 32*n /\
    fn_has_code sa sb fn /\ not_fresh_at sa src /\
    eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    ptr_covers G tn src s (32*n) /\ lookup_var src s = SOME a /\
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    0<n /\ n<dimword (:256) /\ w2n a+32*(n-1) < dimword (:256) /\
  declared_storage_region cx mid id subs = SOME (tr,root_slot,rtv) /\
  storage_subregion rtv path delta tv /\ w2n k = w2n root_slot+delta /\
  w2n root_slot+type_slot_size rtv <= dimword (:256) /\
  (!mid' id' subs' root_slot' rtv'.
    declared_storage_region cx mid' id' subs' = SOME (tr,root_slot',rtv') /\
    (root_slot',rtv') <> (root_slot,rtv) ==>
    ranges_disjoint (w2n root_slot) (type_slot_size rtv)
                    (w2n root_slot') (type_slot_size rtv')) /\
  0 < type_slot_size tv /\ n <= type_slot_size tv /\
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) /\
  (tv = BaseTV (BytesT (Dynamic cap)) \/ tv = BaseTV (StringT cap)) /\
  mload (w2n a) s = n2w len /\ len < dimword (:256) /\
  len <= 32*(n-1) /\
  write_place cx (StoragePlace tr k tv) v es = (INL (),es') /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?Gf tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
    stmt_state_rel ctx fn cenv cx es' u /\ ghost_inv d cenv cx es' Gf tf u /\
    ghost_kept cenv es sa G tn s Gf tf /\
    assign_base_store_frame (if tr then LocTransient else LocStorage)
      a k s tn n u tf /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    execution_frame u = execution_frame
      (store_copy_prefix (if tr then LocTransient else LocStorage) a k s n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`root` |-> `src`,`z` |-> `()`]
    (SPEC_ALL bytes_storage_copy_counted_ptr)) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`Gf`,`tf`,`u`] strip_assume_tac) >>
  mp_tac (Q.INST [`func` |-> `fn`,`s0` |-> `s`,
    `G0` |-> `G`,`tn0` |-> `tn`,`b` |-> `a`,`copied` |-> `n`,
    `s` |-> `u`,`tn` |-> `tf`,`G` |-> `Gf`,`root` |-> `root_slot`]
    (SPEC_ALL bytes_storage_counted_landing_ptr)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    asm_rewrite_tac[] >> metis_tac[])) >> strip_tac >>
  qexistsl_tac [`Gf`,`tf`,`u`] >> asm_rewrite_tac[]
QED
