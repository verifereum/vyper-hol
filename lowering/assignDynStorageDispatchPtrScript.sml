(* Word and multiword dynamic stores yield one complete active-prefix frame. *)
Theory assignDynStorageDispatchPtr
Ancestors
  assignDynStorageCompiledPtr assignTupleDynamicStoragePtr assignStorageHeaderFramePtr
  assignBasePtrStorageLoop bodyPtrDefs ptrDiscipline compileEnv venomState
  words arithmetic finite_map stateFrame

Theorem dyn_storage_compiled_prefix_ptr:
  !tr root dst sa z sb fn s G tn ctx D PG a k n capacity ew ems.
    compile_dynarray_to_storage (Var root) dst ew ems tr sa = (z,sb) /\
    fn_has_code sa sb fn /\ not_fresh_at sa root /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
    eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
    mload (w2n a) s = n2w n /\ mem_word_taint tn.t_mem (w2n a) = {} /\
    n < dimword (:256) /\ 0 < ew /\ ew < dimword (:256) /\
    ems = 32*ew /\ 32+n*ems <= capacity /\
    w2n a+32+n*ems < dimword (:256) /\
    w2n k+1+n*ew <= dimword (:256) /\
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage)
        a k s tn (1+n*ew) u tf /\
      execution_frame u = execution_frame
        (store_copy_prefix (if tr then LocTransient else LocStorage) a k s (1+n*ew)) /\
      ptr_covers Gf tf root u capacity /\ lookup_var root u = SOME a /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `?Gf tf u v tv.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
    assign_base_store_frame (if tr then LocTransient else LocStorage)
      (a+32w) (k+1w) s tn (n*ew) v tv /\
    u = ((if tr then tstore k (n2w n) v else sstore k (n2w n) v)
      with vs_inst_idx := 1) /\
    tf = (if tr then tv with t_trans := key_update tv.t_trans k {}
          else tv with t_stor := key_update tv.t_stor k {}) /\
    execution_frame u = execution_frame
      (store_copy_prefix (if tr then LocTransient else LocStorage) a k s (1+n*ew)) /\
    ptr_covers Gf tf root u capacity /\ lookup_var root u = SOME a /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))` by
    (Cases_on `ew=1`
     >- (gvs[] >>
         `n < dimword (:256) /\ 32+32*n <= capacity /\
          w2n a+32+32*n < dimword (:256)` by decide_tac >>
         mp_tac (Q.SPECL [`tr`,`root`,`dst`,`sa`,`()`,`sb`,`fn`,`s`,`G`,`tn`,
           `ctx`,`D`,`PG`,`a`,`k`,`n`,`capacity`] tuple_dynamic_storage_compiled_counted) >>
         (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
     mp_tac (Q.SPECL [`tr`,`root`,`dst`,`sa`,`z`,`sb`,`fn`,`s`,`G`,`tn`,
       `ctx`,`D`,`PG`,`a`,`k`,`n`,`capacity`,`ew`,`ems`]
       dyn_storage_multi_compiled_counted) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `!h. h<n*ew ==> k <> (k+1w)+n2w h` by
    (rpt strip_tac >>
     `w2n k+1+h < dimword (:256) /\
      w2n k+1 < dimword (:256) /\ h < dimword (:256)` by decide_tac >>
     `w2n ((k+1w)+n2w h) = w2n k+1+h` by
       simp[word_add_def,w2n_n2w,LESS_MOD] >>
     `w2n k = w2n k+1+h` by metis_tac[] >> decide_tac) >>
  `assign_base_store_frame (if tr then LocTransient else LocStorage)
     a k s tn (1+n*ew) u tf` by
    (mp_tac (Q.INST [`b` |-> `a`,`k` |-> `k`,`s0` |-> `s`,`tn0` |-> `tn`,
       `n` |-> `n*ew`,`v` |-> `v`,`tv` |-> `tv`,`tr` |-> `tr`,
       `value` |-> `n2w n:bytes32`,`index` |-> `1`]
       (SPEC_ALL assign_base_store_frame_header)) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     Cases_on `tr` >> gvs[ADD1]) >>
  qexistsl_tac [`Gf`,`tf`,`u`] >> gvs[execution_frame_def]
QED
