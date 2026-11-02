(*
 * Memory footprints of the external entry and return sequences (S3)
 *
 * The frag_exec_mem versions of loweringHalt's return fragments, and the
 * footprint of one static argument's decode at the external entry.  Each
 * buffer the sequences write is an ALLOCA they emit themselves, or the
 * argument's own buffer, so they need only that it lies below the
 * allocation frontier.
 *
 * TOP-LEVEL:
 *   compile_return_none_external_frag_mem,
 *   compile_guarded_body_stop_frag_mem
 *                             — a return without a value, and falling off
 *                               the end: a STOP
 *   compile_external_return_word_frag_mem
 *                             — returning a primitive word: ALLOCA 32,
 *                               MSTORE, RETURN
 *   compile_external_return_copy_frag_mem
 *                             — returning a static complex value: ALLOCA,
 *                               MCOPY from the value, RETURN
 *   entry_decode_arg_mem_ok   — decoding a static argument into a buffer
 *                               below the frontier
 *)
Theory entryHaltMem
Ancestors
  list fragExec fragExecMem memSafeRun allocaFootprint loweringHalt
  entryArgPtrs entryDecodePlanProps abiDecodeStaticProps
  compileEnv stmtLowering moduleLowering emitHelper abiBuiltinAllocation
  unitTransformDefs venomState venomInst venomExecSemantics venomMemDefs
  words

(* ===== STOP ===== *)

Theorem compile_return_none_external_frag_mem:
  !ctx cenv lctx ty st x st' nr nkey ut iv P Q R.
    compile_stmt cenv lctx ty (Return NONE) st = (x, st') /\
    cenv.ce_return_pc = NONE /\
    cenv.ce_nonreentrant = (nr, nkey, ut, iv) /\ (nr ==> iv) /\
    (!s. P s ==> R (Halt (halt_state (s with vs_returndata := [])))) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rpt strip_tac >>
  `st'.cs_current_bb = st.cs_current_bb /\
   st'.cs_current_insts =
     st.cs_current_insts ++ [mk_inst st.cs_next_id STOP [] []]` by
    (qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
     simp[compile_stmt_def, optional_unlock_view, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, emit_inst_def,
          fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  qspecl_then [`ctx`, `st`, `st'`, `st.cs_next_id`, `P`, `Q`, `R`] mp_tac
    stop_frag_mem >>
  simp[]
QED

Theorem compile_guarded_body_stop_frag_mem:
  !ctx cenv nr nkey ut iv stmts st x st' sa sb P Q R.
    compile_guarded_body cenv nr nkey ut iv stmts NONE st = (x, st') /\
    (nr ==> iv) /\
    (if nr then compile_nonreentrant_lock nkey ut iv else comp_return ()) st =
      ((), sa) /\
    compile_stmts cenv NoLoop (BaseT BoolT) stmts sa = ((), sb) /\
    ~block_is_terminated sb /\
    (!s. P s ==> R (Halt (halt_state (s with vs_returndata := [])))) ==>
    frag_exec_mem ctx sb st' P Q R
Proof
  rpt strip_tac >>
  `st'.cs_current_bb = sb.cs_current_bb /\
   st'.cs_current_insts =
     sb.cs_current_insts ++ [mk_inst sb.cs_next_id STOP [] []]` by
    (qpat_x_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_guarded_body_def, optional_unlock_view, comp_bind_def,
          comp_ignore_bind_def, comp_get_def] >>
     strip_tac >>
     gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
         emit_inst_def, fresh_id_def, emit_def]) >>
  qspecl_then [`ctx`, `sb`, `st'`, `sb.cs_next_id`, `P`, `Q`, `R`] mp_tac
    stop_frag_mem >>
  simp[]
QED

(* ===== Returned buffers ===== *)

(* The return buffer's ALLOCA site, if it already ran (a loop), holds a
   32-byte allocation, as the site's own literal size gives; the existing
   scratch-buffer leaves (compile_keccak256_word_mem_ok) take the same
   premise. *)
Theorem compile_external_return_word_frag_mem:
  !ctx op ei msz nr nkey ut iv st x st' w P Q R.
    compile_external_return (SOME op) T F ei msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    (!s. P s ==>
         eval_operand op s = SOME w /\ alloca_next_valid s /\
         ?b. FLOOKUP (abi_builtin_allocate_state st.cs_next_id 32 s).vs_allocas
               st.cs_next_id = SOME (b, 32)) /\
    (!s ss. P s /\ ss.vs_returndata = word_to_bytes w T /\
            ss.vs_accounts = s.vs_accounts /\
            ss.vs_transient = s.vs_transient /\
            ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
            R (Halt ss)) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  cheat
QED

(* The MCOPY reads the value's m bytes at its address p, which the caller
   puts below the frontier (a local's region, local_ptrs_rel), and writes
   them into the buffer, msz >= m bytes. *)
Theorem compile_external_return_copy_frag_mem:
  !ctx op m msz nr nkey ut iv st x st' P Q R.
    compile_external_return (SOME op) F F (AbiCopy m) msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    m <= msz /\ msz < dimword(:256) /\
    (!s. P s ==>
         alloca_next_valid s /\
         (?b. FLOOKUP (abi_builtin_allocate_state st.cs_next_id msz s).vs_allocas
                st.cs_next_id = SOME (b, msz)) /\
         ?p. eval_operand op s = SOME p /\
             (m = 0 \/ w2n p + m <= s.vs_alloca_next) /\
             !ss. ss.vs_returndata = mem_bytes_at (w2n p) m s.vs_memory /\
                  ss.vs_accounts = s.vs_accounts /\
                  ss.vs_transient = s.vs_transient /\
                  ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests ==>
                  R (Halt ss)) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  cheat
QED

(* ===== The entry's static argument decode ===== *)

(* entry_decode_arg_run's premises, with the argument's buffer [p, p + its
   memory size) below the frontier: every instruction the decode runs is
   below the frontier where it runs. *)
Theorem entry_decode_arg_mem_ok:
  !cenv cenv0 tenv fname args vals env i off hi st st' loc dst s0 p tv.
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
    w2n p + type_memory_size tv <= s0.vs_alloca_next ==>
    run_inst_seq_mem_ok (emitted_insts st st') s0
Proof
  cheat
QED
