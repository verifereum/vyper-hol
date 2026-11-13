(*
 * A bytes or string literal's own buffer (compile_bytelike_literal) on the
 * finite-horizon joint judgment: the ALLOCA, the length word and the
 * 32-byte chunks run once, to an endpoint fixed before the horizon, and
 * at every valid horizon H the run is a pointer-safe instruction
 * sequence at (DF H, lo), constructor frames included.
 *
 * TOP-LEVEL:
 *   literal_bytelike_full_run -- shared by the Literal leaf and the
 *     builtins that lower to a literal buffer (method_id)
 *)
Theory bodyFullLiteralBuffer
Ancestors
  exprSimPtrLiteralBuffer fragGasSeqPtr instSeqPtrLo bodyPtrDefs vyperStorageFootprint
  exprLowering compileEnv loweringStateRelDefs venomState finite_map words

(* The pointer twin is exprSimPtrLiteralBuffer's literal_bytelike_ptr_run at
   lo = 0.  What changes at lo > 0 (a constructor frame): the ALLOCA's base
   is at or above lo (ghost_inv_at's allocas_from lo / lo <= vs_alloca_next),
   so the stores stay off the immutable section below lo.  Everything but
   the pointer-safety of the run and the state relation of the post-ALLOCA
   state is horizon-free (allocation, stores, provenance and taint are
   deterministic), so those are fixed before H; storage_trace_domain gives
   one valid horizon to read the run's facts at. *)
Theorem literal_bytelike_full_run:
  !bs sa buf sb DF lo d PG ctx func cenv cx st0 es s G tn.
    compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
    32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
    storage_trace_domain cx st0 es.storage_trace /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s /\
       ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
    ?u t b p sh G' tn'.
      buf.buf_operand = Var p /\ not_fresh_at sh p /\
      (!x. not_fresh_at sa x ==> not_fresh_at sh x) /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      u.vs_memory = s.vs_memory /\
      FLOOKUP u.vs_allocas sa.cs_next_id =
        SOME (b, 32 + 32 * word_size (LENGTH bs)) /\
      lo <= b /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!aid a len. aid < sa.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
         regions_disjoint b (32 + 32 * word_size (LENGTH bs)) a len) /\
      (!name a len. local_region cenv es.scopes u name a len ==>
         regions_disjoint b (32 + 32 * word_size (LENGTH bs)) a len) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      u.vs_labels = s.vs_labels /\ wb_frame cenv es es sa s u /\
      (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>) = u /\
      LENGTH u.vs_memory <= LENGTH t.vs_memory /\
      (!x. not_fresh_at sh x ==> lookup_var x t = lookup_var x u) /\
      (!a len. a + len <= b \/ b + 32 + 32 * word_size (LENGTH bs) <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
      FLOOKUP G' p = SOME (b, 32 + 32 * word_size (LENGTH bs)) /\
      lookup_var p t = SOME (n2w b) /\ op_taint tn' (Var p) = {} /\
      b + 32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
      mem_word_at b t.vs_memory = n2w (LENGTH bs) /\
      mem_bytes_at (b + 32) (LENGTH bs) t.vs_memory = bs /\
      tn'.t_mem =
        tn.t_mem DIFF {i | b <= i /\ i < b + 32 + 32 * word_size (LENGTH bs)} /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
      tn'.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
         FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x) /\
      !H. valid_horizon cx st0 H es.storage_trace ==>
        inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
        stmt_state_rel H ctx func cenv cx es u
Proof
  cheat
QED
