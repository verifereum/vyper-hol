(* The actual equal-layout full storage copy and its semantic landing. *)
Theory assignStaticStorageLandingPtr
Ancestors
  assignTupleStorageAddressPtr assignStorageLandingPtr assignBasePtrStorageLoop
  exprLoweringProps exprSimDefs bodyPtrDefs loweringPosts compileEnv
  valueEncoding valueEncodingDefs venomState ptrDiscipline stateFrame
  words arithmetic finite_map

Theorem static_storage_copy_landing_ptr:
  compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
    (Var root) F loc ty ty NONE (32*n) sa = (z,sb) /\
  ~is_bytestring_type ty /\ fn_has_code sa sb func /\ not_fresh_at sa root /\
  eval_operand dst s0 = SOME k /\ op_taint tn0 dst = {} /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  ptr_covers G0 tn0 root s0 (32*n) /\ lookup_var root s0 = SOME b /\
  ~s0.vs_halted /\ ~s0.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  0<n /\ w2n b+32*n < dimword (:256) /\ n=type_slot_size tv /\
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  declared_storage_region cx mid id subs = SOME (tr,root_slot,rtv) /\
  storage_subregion rtv path delta tv /\ w2n k = w2n root_slot+delta /\
  w2n root_slot+type_slot_size rtv <= dimword (:256) /\
  (!mid' id' subs' root_slot' rtv'.
    declared_storage_region cx mid' id' subs' = SOME (tr,root_slot',rtv') /\
    (root_slot',rtv') <> (root_slot,rtv) ==>
    ranges_disjoint (w2n root_slot) (type_slot_size rtv)
                    (w2n root_slot') (type_slot_size rtv')) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\
  (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==>
    val_in_memory tv v (w2n b) m) /\
  write_place cx (StoragePlace tr k tv) v es = (INL (),es') /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?s G tn.
    gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0 G tn (OK s) /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~s.vs_halted /\
    stmt_state_rel ctx func cenv cx es' s /\ ghost_inv d cenv cx es' G tn s /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    assign_base_store_frame (if tr then LocTransient else LocStorage)
      b k s0 tn0 n s tn /\
    (!x. not_fresh_at sa x ==>
      lookup_var x s = lookup_var x s0 /\ FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >>
  `n < dimword (:256) /\ w2n b+32*(n-1) < dimword (:256)` by decide_tac >>
  mp_tac (Q.SPECL [`tr`,`root`,`dst`,`k`,`n`,`cenv`,`ty`,`loc`,`sa`,`z`,`sb`,
    `func`,`s0`,`G0`,`tn0`,`ctx`,`cx_dead cx`,`PG`,`b`]
    tuple_storage_address_direct_counted) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`G`,`tn`,`s`] strip_assume_tac) >>
  `!st i c. w2n k <= i /\ i < w2n k+type_slot_size tv /\ c<32 /\
    ~dead_bytes (apply_writes k writes st) (w2n k) tv i c ==>
    i < w2n k+n` by (rpt strip_tac >> decide_tac) >>
  `!q c. (q,c) IN (if tr then tn0.t_trans else tn0.t_stor) /\
    w2n k+n <= w2n q /\ w2n q < w2n k+type_slot_size tv ==>
    dead_bytes (if tr then contract_transient s else contract_storage s)
      (w2n k) tv (w2n q) c` by (rpt strip_tac >> gvs[] >> decide_tac) >>
  `0 < type_slot_size tv` by decide_tac >>
  `!x. not_fresh_at sa x ==>
    FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x) /\
    lookup_var x s = lookup_var x s0` by metis_tac[] >>
  `stmt_state_rel ctx func cenv cx es' s /\ ghost_inv d cenv cx es' G tn s /\
   ghost_kept cenv es sa G0 tn0 s0 G tn` by
    (mp_tac (Q.INST [`copied` |-> `n`,`root` |-> `root_slot`]
      (SPEC_ALL storage_prefix_counted_landing_ptr)) >>
     (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
     asm_rewrite_tac[]) >>
  qexistsl_tac [`s`,`G`,`tn`] >> asm_rewrite_tac[]
QED
