Theory bodyPtrTypeBuiltinsEmptyPost
Ancestors
  wordLoadStorePtr
  bodyPtrDefs exprSimAggregateLayout venomMemProofs valueEncoding valueEncodingDefs
  valueEncodingProofs list

(* A clean window is stable even when bytes outside it are arbitrary. *)
Theorem clean_window_agreement:
  !m mem mem' a n.
    mem_agree_outside m mem mem' /\
    (!i. a <= i /\ i < a+n ==> i NOTIN m) ==>
    mem_bytes_at a n mem' = mem_bytes_at a n mem
Proof
  rpt strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `j < n` >>
  `a+j NOTIN m` by (first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (a+j) 1 mem = mem_bytes_at (a+j) 1 mem'` by
    metis_tac[mem_agree_outside_def] >>
  qpat_x_assum `mem_bytes_at _ 1 _ = _` mp_tac >>
  simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem empty_robust_default_memory:
  !cenv cx env es ty tv off mem m.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    (if is_bytestring_type ty \/
        (case ty of ArrayT _ (Dynamic _) => T | _ => F)
     then mem_word_at off mem = 0w /\
          (!i. off <= i /\ i < off+32 ==> i NOTIN m)
     else mem_bytes_at off (type_memory_bytes cenv ty) mem =
            REPLICATE (type_memory_bytes cenv ty) 0w /\
          (!i. off <= i /\ i < off+type_memory_bytes cenv ty ==> i NOTIN m)) ==>
    !mem'. mem_agree_outside m mem mem' ==>
      val_in_memory tv (default_value tv) off mem'
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  irule empty_type_default_memory >>
  qexistsl_tac [`cenv`, `cx`, `env`, `es`, `ty`] >> simp[] >>
  Cases_on `is_bytestring_type ty \/
    (case ty of ArrayT _ (Dynamic _) => T | _ => F)` >> gvs[]
  >>~- ([`mem_word_at off mem' = 0w`],
      `mem_bytes_at off 32 mem' = mem_bytes_at off 32 mem` by
        (irule clean_window_agreement >> metis_tac[]) >>
      gvs[mem_word_at_def, mem_bytes_at_def])
  >> metis_tac[clean_window_agreement]
QED

(* C1.4.1 interface audit (not an admitted execution theorem).
   Compiler-facing candidate: under compile_builtin_empty_complex sz header
   sa = (buf,sb), fn_has_code sa sb func, fn_inst_ids_distinct func,
   local_ptrs_reserved cenv sa, stmt_state_rel ctx func cenv cx es s,
   ghost_inv d cenv cx es G tn s, return-variable freshness at sa,
   ~ctx_has_dalloca ctx, ~s.vs_halted, and the entry PC/index equations,
   sz < dimword (:256), and (if header then 32 <= sz else sz MOD 32 = 0),
   obtain ONE t,w,G',tn' with:
   - gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 G' tn'
       (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts));
   - every semantic/frame clause of compile_builtin_empty_complex_run
       (exprSimBufferEmptyExec lines 149-165), at that same t,w;
   - ptr_covers G' tn' p t sz and buf.buf_operand = Var p;
   - if header then [w2n w,w2n w+32) is clean in tn'.t_mem,
       else [w2n w,w2n w+sz) is clean;
   - ghost_inv d cenv cx es G' tn' t and
       ghost_kept cenv es sa G tn s G' tn'.

   Exact missing bridge: inst_seq_ptr along emitted_insts sa sb, with
   final ghost G',tn', plus the clean-window and ghost-frame clauses.
   run_inst_seq_gas_path_ptr (fragGasSeqPtr 111ff) then uses the SAME
   run_inst_seq witness from compile_builtin_empty_complex_run; shape
   (181ff) supplies straight-line/no-INVOKE information. This is not an
   upgrade of an arbitrary erased path.

   ALLOCA: ptr_inst_ok_alloca needs only ~ctx_has_dalloca; the checked
   alloca_step_ptr_covers (allocationPtr 317ff) needs stmt_state_rel,
   membership of the exact ALLOCA in fn_insts, size bound, and the actual
   successful step. It covers both fresh and reused allocation sites.
   Header MSTORE: ptr_inst_ok_mstore needs 32-byte ptr_covers and clean
   literal; mstore_word_clean kills taint only in its written 32 bytes.
   Full zeroing: compile_zero_words emits ADD base (Lit (n*32)), then
   MSTORE through that result. A counted induction must preserve the
   base provenance and prove offset+32 <= sz for each store; the
   fixed-run mstore_frag_ptr is NOT itself the missing counted boundary.
   Zero size: no zero-word iterations; clean window is vacuous, but
   ALLOCA and its provenance/ghost frame still need their checked step.
   Header-only: unused payload need not be clean, as the theorem above
   quantifies over arbitrary changes there. Nested defaults in static
   aggregates take the whole-buffer branch of empty_type_default_memory.
*)
