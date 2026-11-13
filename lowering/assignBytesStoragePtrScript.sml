(* Bytestring storage copies the source capacity, even at a wider destination. *)
Theory assignBytesStoragePtr
Ancestors
  assignTupleStorageAddressPtr assignBasePtrStorageLoop fragGasPathPtr
  stmtLowering context compileEnv emitHelper bodyPtrDefs ptrDiscipline
  venomState venomExecSemantics stateFrame words arithmetic
Libs monadsyntax

Theorem bytes_storage_copy_code:
  is_bytestring_type dty /\ is_bytestring_type sty ==>
  compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
    (Var root) F loc dty sty NONE capacity =
  (if type_memory_bytes cenv sty <= 32 then
     do loaded <- emit_op MLOAD [Var root];
        emit_void (if tr then TSTORE else SSTORE) [dst;loaded]
     od
   else do compile_word_copy_loop (Var root) dst
          (type_memory_bytes cenv sty DIV 32) LocMemory
          (if tr then LocTransient else LocStorage) F; return () od)
Proof
  strip_tac >> Cases_on `tr` >>
  simp[FUN_EQ_THM,compile_assign_value_def,comp_bind_def,
    comp_return_def,comp_ignore_bind_def,compile_memory_to_storage_def,
    compile_memory_to_transient_def] >>
  gen_tac >> pairarg_tac >> simp[]
QED

Theorem bytes_storage_copy_counted_ptr:
  !tr root dst k n cenv dty sty loc capacity sa z sb fn s G tn ctx D PG a.
    compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
      (Var root) F loc dty sty NONE capacity sa = (z,sb) /\
    is_bytestring_type dty /\ is_bytestring_type sty /\
    type_memory_bytes cenv sty = 32*n /\
    fn_has_code sa sb fn /\ not_fresh_at sa root /\
    eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    ptr_covers G tn root s (32*n) /\ lookup_var root s = SOME a /\
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    0<n /\ n<dimword (:256) /\ w2n a+32*(n-1) < dimword (:256) ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      execution_frame u = execution_frame
        (store_copy_prefix (if tr then LocTransient else LocStorage) a k s n) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage)
        a k s tn n u tf /\
      ptr_covers Gf tf root u (32*n) /\ lookup_var root u = SOME a /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
    (Var root) F loc dty sty NONE capacity =
    (if type_memory_bytes cenv sty <= 32 then
       do loaded <- emit_op MLOAD [Var root];
          emit_void (if tr then TSTORE else SSTORE) [dst;loaded] od
     else do compile_word_copy_loop (Var root) dst
          (type_memory_bytes cenv sty DIV 32) LocMemory
          (if tr then LocTransient else LocStorage) F; return () od)` by
    (irule bytes_storage_copy_code >> asm_rewrite_tac[]) >>
  Cases_on `32*n<=32`
  >- (`n=1` by decide_tac >> gvs[] >>
      drule_all tuple_storage_address_single_compiled_counted >>
      disch_then (qspecl_then [`D`,`PG`] mp_tac) >> simp[]) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> simp[comp_ignore_bind_def,comp_bind_def,comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  `n < dimword (:256) /\ 32*n<=32*n` by decide_tac >>
  drule_all tuple_storage_address_compiled_counted >>
  disch_then (qspecl_then [`D`,`PG`] mp_tac) >>
  disch_then (qx_choose_then `gf` (qx_choose_then `tf`
    (qx_choose_then `u` strip_assume_tac))) >>
  qexistsl_tac [`gf`,`tf`,`u`] >> asm_rewrite_tac[] >> gvs[execution_frame_def]
QED
