(* Exact successful traces and memory safety for static entry arguments. *)
Theory entryStaticDecodeMem
Ancestors
  entryArgPtrs entryHaltMem

Theorem entry_decode_arg_safe_run:
  !cenv cenv0 tenv fname args vals env i off hi st st' ctx loc dst s0 p tv.
    dec_cenv_agrees cenv0 tenv /\
    off = 4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
                       (TAKE i args)) /\
    compile_decode_args cenv [build_positional_arg cenv0 (EL i args)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars (FST (EL i args)) = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    bind_arguments tenv args vals = SOME env /\ i < LENGTH args /\
    calldata_encodes tenv fname (MAP SND args) vals s0.vs_call_ctx.cc_calldata /\
    (is_word_type (SND (EL i args)) \/
      (assignable_type tenv (SND (EL i args)) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND (EL i args))))) /\
    evaluate_type tenv (SND (EL i args)) = SOME tv /\ int_byte_widths tv /\
    off + type_memory_size tv < dimword (:256) /\
    w2n p + type_memory_size tv < dimword (:256) /\
    ~s0.vs_halted /\ s0.vs_current_bb = st.cs_current_bb /\
    s0.vs_inst_idx = LENGTH st.cs_current_insts /\
    w2n p + type_memory_size tv <= s0.vs_alloca_next ==>
    (?u. dec_straight st st' /\
      run_inst_seq (emitted_insts st st') s0 = OK u /\
      let t = u with vs_inst_idx := LENGTH st'.cs_current_insts in
        dec_frame st (w2n p) (type_memory_size tv) s0 t /\
        fresh_vars_wrt st' t /\
        val_in_memory tv (EL i vals) (w2n p) t.vs_memory /\
        ~t.vs_halted /\ t.vs_current_bb = s0.vs_current_bb /\
        t.vs_prev_bb = s0.vs_prev_bb) /\
    run_inst_seq_mem_ok (emitted_insts st st') s0
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (drule_all entry_decode_arg_run >>
      disch_then (qspec_then `ctx` ACCEPT_TAC)) >>
  drule_all entry_decode_arg_mem_ok >> simp[]
QED
