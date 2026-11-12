(* Assembly boundaries for dynamic aggregate normalization. *)
Theory annAssignTypedCopyDynamicPtr
Ancestors
  annAssignTypedCopyDynamicHeaderPtr annAssignTypedCopyDynamicBulkPtr
  annAssignTypedCopyDynamicTestPtr annAssignTypedCopyDynamicLoopPtr
  typedNormalizeDynarray typedMemoryCopy normalizationPrefixPtr
  annAssignTypedCopyFixedMetadataPtr exprLoweringProps fragExec
  bodyPtrDefs context compileEnv emitHelper venomState venomInst
  venomExecSemantics words arithmetic list rich_list freshWrites ASCIInumbers loweringStateRelDefs

Theorem annassign_dynamic_compiler_header[local]:
  !ce dst dt cap src st sa sb fn s a b ss ds n tn G ctx D PG
    len long ok sp dp.
    compile_copy_dynarray_typed ce (Var dst) dt cap (Var src) st sa = ((),sb) /\
    fn_has_code sa sb fn /\
    len = "%" ++ toString sa.cs_next_var /\
    long = "%" ++ toString (sa.cs_next_var+1) /\
    ok = "%" ++ toString (sa.cs_next_var+2) /\
    sp = "%" ++ toString (sa.cs_next_var+3) /\
    dp = "%" ++ toString (sa.cs_next_var+4) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    ptr_covers G tn src s (32+ss) /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s (32+ds) /\ lookup_var dst s = SOME b /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      mem_word_at (w2n a) mem = n2w n) /\
    n <= cap /\ cap < dimword (:256) /\
    w2n a+32 < dimword (:256) /\ w2n b+32 < dimword (:256) ==>
    ?H tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
      u.vs_current_bb = sa.cs_current_bb /\
      u.vs_inst_idx = LENGTH sa.cs_current_insts+7 /\
      ~u.vs_halted /\ typed_copy_state_frame sa (w2n b) 32 s u /\
      lookup_var len u = SOME (n2w n) /\ FLOOKUP H len = NONE /\
      op_taint tf (Var len) = {} /\
      lookup_var sp u = SOME (a+32w) /\ lookup_var dp u = SOME (b+32w) /\
      ptr_covers H tf sp u ss /\ ptr_covers H tf dp u ds /\
      tf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!mem. mem_agree_outside tf.t_mem u.vs_memory mem ==>
        mem_word_at (w2n b) mem = n2w n) /\
      (!x. ~MEM x [len;long;ok;sp;dp] ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x)) /\
      (!i. ~(w2n b <= i /\ i < w2n b+32) ==>
        mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_dynarray_compiler_prefix >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_assum `fn_has_code sa sm fn` mp_tac >>
  pure_rewrite_tac[fn_has_code_def] >> strip_tac >>
  qpat_x_assum `isPREFIX sm.cs_current_insts _` mp_tac >>
  asm_rewrite_tac[] >> rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
  `ALL_DISTINCT [len;long;ok;sp;dp] /\
   ~MEM src [len;long;ok] /\ ~MEM dst [len;long;ok;sp] /\
   (!x. not_fresh_at sa x ==> ~MEM x [len;long;ok;sp;dp])` by
    (gvs[not_fresh_at_def, toString_inj] >> rpt strip_tac >>
     gvs[not_fresh_at_def] >> decide_tac) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id MLOAD [Var src] [len]) /\
   isPREFIX [mk_inst (sa.cs_next_id+1) GT [Var len;Lit (n2w cap)] [long];
     mk_inst (sa.cs_next_id+2) ISZERO [Var long] [ok];
     mk_inst (sa.cs_next_id+3) ASSERT [Var ok] []]
     (DROP (SUC s.vs_inst_idx) bb.bb_instructions) /\
   get_instruction bb (s.vs_inst_idx+4) =
     SOME (mk_inst (sa.cs_next_id+4) MSTORE [Var dst;Var len] []) /\
   get_instruction bb (s.vs_inst_idx+5) =
     SOME (mk_inst (sa.cs_next_id+5) ADD [Var src;Lit 32w] [sp]) /\
   get_instruction bb (s.vs_inst_idx+6) =
     SOME (mk_inst (sa.cs_next_id+6) ADD [Var dst;Lit 32w] [dp])` by
    (simp[get_instruction_def, EL_APPEND_EQN, DROP_APPEND, ADD1,
          DROP_LENGTH_TOO_LONG] >> metis_tac[]) >>
  drule_all (Q.INST [`sa` |-> `sa`] annassign_dynamic_header_counted) >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`H`,`tf`,`u`] >> gvs[] >> gvs[]
QED
