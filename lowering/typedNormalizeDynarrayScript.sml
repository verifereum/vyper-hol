Theory typedNormalizeDynarray
Ancestors
  typedNormalizeFrame typedNormalizeLoop typedBytesArrayMem memContinuation allocaFootprint instMemFrontier
  fragExec fragExecMem emitHelperProps exprLoweringProps venomExecSemantics venomExecProofs venomState venomInst
  context compileEnv emitHelper valueEncoding valueEncodingProps words arithmetic list rich_list

(* Runtime length, not capacity, determines the data copy.  Register names
   are explicit here so the same boundary serves both compiler branches. *)
Theorem typed_dynarray_prologue_run[local]:
  code =
    [mk_inst id MLOAD [src] [len];
     mk_inst (id+1) GT [Var len; Lit (n2w cap)] [long];
     mk_inst (id+2) ISZERO [Var long] [ok];
     mk_inst (id+3) ASSERT [Var ok] [];
     mk_inst (id+4) MSTORE [dst; Var len] [];
     mk_inst (id+5) ADD [src; Lit 32w] [sp];
     mk_inst (id+6) ADD [dst; Lit 32w] [dp]] /\
  ALL_DISTINCT [len;long;ok;sp;dp] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [len;long;ok;sp;dp]) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  mload (w2n p) s = n2w l /\ l <= cap /\ cap < dimword(:256) ==>
  ?q. run_inst_seq code s = OK q /\
    eval_operand (Var len) q = SOME (n2w l) /\
    eval_operand (Var sp) q = SOME (p + 32w) /\
    eval_operand (Var dp) q = SOME (d + 32w) /\
    q.vs_memory = (mstore (w2n d) (n2w l) s).vs_memory /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. ~MEM x [len;long;ok;sp;dp] ==> lookup_var x q = lookup_var x s)
Proof
  strip_tac >> `l < dimword(:256)` by decide_tac >>
  Cases_on `src` >> Cases_on `dst` >>
  gvs[eval_operand_def, lookup_var_def] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure1_def, exec_pure2_def, exec_read1_def, exec_write2_def,
       eval_operand_def, lookup_var_update_var, w2n_n2w, bool_to_word_def,
       mstore_def, write_memory_with_expansion_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE,
                       venom_state_component_equality]
QED

Theorem typed_dynarray_prologue_mem_ok[local]:
  code =
    [mk_inst id MLOAD [src] [len];
     mk_inst (id+1) GT [Var len; Lit (n2w cap)] [long];
     mk_inst (id+2) ISZERO [Var long] [ok];
     mk_inst (id+3) ASSERT [Var ok] [];
     mk_inst (id+4) MSTORE [dst; Var len] [];
     mk_inst (id+5) ADD [src; Lit 32w] [sp];
     mk_inst (id+6) ADD [dst; Lit 32w] [dp]] /\
  ALL_DISTINCT [len;long;ok;sp;dp] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [len;long;ok;sp;dp]) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  mload (w2n p) s = n2w l /\ l <= cap /\ cap < dimword(:256) /\
  w2n p + 32 <= s.vs_alloca_next /\
  w2n d + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok code s
Proof
  strip_tac >> `l < dimword(:256)` by decide_tac >>
  Cases_on `src` >> Cases_on `dst` >>
  gvs[eval_operand_def, lookup_var_def] >>
  simp[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
       below_frontier_MLOAD, below_frontier_MSTORE, below_frontier_no_ranges,
       step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure1_def, exec_pure2_def, exec_read1_def, exec_write2_def,
       eval_operand_def, lookup_var_update_var, w2n_n2w, bool_to_word_def,
       mstore_def, write_memory_with_expansion_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem typed_dynarray_prologue_window_run:
  code =
    [mk_inst id MLOAD [src] [len];
     mk_inst (id+1) GT [Var len; Lit (n2w cap)] [long];
     mk_inst (id+2) ISZERO [Var long] [ok];
     mk_inst (id+3) ASSERT [Var ok] [];
     mk_inst (id+4) MSTORE [dst; Var len] [];
     mk_inst (id+5) ADD [src; Lit 32w] [sp];
     mk_inst (id+6) ADD [dst; Lit 32w] [dp]] /\
  ALL_DISTINCT [len;long;ok;sp;dp] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [len;long;ok;sp;dp]) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  mload (w2n p) s = n2w l /\ l <= cap /\ cap < dimword(:256) /\
  32 <= src_size /\ 32 <= dst_size /\
  w2n p + src_size <= s.vs_alloca_next /\
  w2n d + dst_size <= s.vs_alloca_next /\
  (w2n p + src_size <= w2n d \/ w2n d + dst_size <= w2n p) ==>
  run_inst_seq_mem_ok code s /\
  ?q. run_inst_seq code s = OK q /\
    eval_operand (Var len) q = SOME (n2w l) /\
    eval_operand (Var sp) q = SOME (n2w (w2n p + 32)) /\
    eval_operand (Var dp) q = SOME (n2w (w2n d + 32)) /\
    q.vs_memory = (mstore (w2n d) (n2w l) s).vs_memory /\
    mem_bytes_at (w2n p) src_size q.vs_memory =
      mem_bytes_at (w2n p) src_size s.vs_memory /\
    (!a k. a+k <= w2n d \/ w2n d+32 <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. ~MEM x [len;long;ok;sp;dp] ==> lookup_var x q = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `w2n p + 32 <= s.vs_alloca_next /\
   w2n d + 32 <= s.vs_alloca_next` by decide_tac >>
  conj_tac >- (irule typed_dynarray_prologue_mem_ok >> metis_tac[]) >>
  drule_all typed_dynarray_prologue_run >> strip_tac >>
  qexists_tac `q` >>
  simp[GSYM word_add_n2w] >>
  conj_tac
  >- (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]
QED

(* This suffix is also valid at length zero; MCOPY then accesses no bytes. *)
Theorem typed_dynarray_equal_suffix_run[local]:
  code = [mk_inst id MUL [length_op; Lit (n2w stride)] [sz];
          mk_inst (id+1) MCOPY [dst;src;Var sz] []] /\
  (!x. dst = Var x \/ src = Var x ==> x <> sz) /\
  eval_operand length_op s = SOME (n2w l) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  l * stride < dimword(:256) /\
  w2n p + l * stride <= s.vs_alloca_next /\
  w2n d + l * stride <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok code s /\
  run_inst_seq code s =
    OK (mcopy (w2n d) (w2n p) (l * stride)
          (update_var sz (n2w (l * stride)) s))
Proof
  strip_tac >> Cases_on `length_op` >> Cases_on `src` >> Cases_on `dst` >>
  gvs[eval_operand_def, lookup_var_def] >>
  simp[run_inst_seq_def, run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
       below_frontier_no_ranges, below_frontier_MCOPY,
       step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, word_mul_n2w, w2n_n2w]
QED

Theorem typed_dynarray_equal_shape[local]:
  compile_copy_dynarray_typed ce dst ty cap src ty sa = ((),sb) ==>
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_next_var = sa.cs_next_var + 6 /\
  sb.cs_next_id = sa.cs_next_id + 9 /\
  sb.cs_next_label = sa.cs_next_label /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id MLOAD [src] ["%" ++ toString sa.cs_next_var];
     mk_inst (sa.cs_next_id+1) GT
       [Var ("%" ++ toString sa.cs_next_var);Lit (n2w cap)]
       ["%" ++ toString (sa.cs_next_var+1)];
     mk_inst (sa.cs_next_id+2) ISZERO
       [Var ("%" ++ toString (sa.cs_next_var+1))]
       ["%" ++ toString (sa.cs_next_var+2)];
     mk_inst (sa.cs_next_id+3) ASSERT
       [Var ("%" ++ toString (sa.cs_next_var+2))] [];
     mk_inst (sa.cs_next_id+4) MSTORE
       [dst;Var ("%" ++ toString sa.cs_next_var)] [];
     mk_inst (sa.cs_next_id+5) ADD [src;Lit 32w]
       ["%" ++ toString (sa.cs_next_var+3)];
     mk_inst (sa.cs_next_id+6) ADD [dst;Lit 32w]
       ["%" ++ toString (sa.cs_next_var+4)];
     mk_inst (sa.cs_next_id+7) MUL
       [Var ("%" ++ toString sa.cs_next_var);Lit (n2w (type_memory_bytes ce ty))]
       ["%" ++ toString (sa.cs_next_var+5)];
     mk_inst (sa.cs_next_id+8) MCOPY
       [Var ("%" ++ toString (sa.cs_next_var+4));
        Var ("%" ++ toString (sa.cs_next_var+3));
        Var ("%" ++ toString (sa.cs_next_var+5))] []]
Proof
  simp[Once compile_store_memory_typed_def, LET_THM,
       compile_copy_memory_dynamic_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >>
  gvs[emitted_insts_def, DROP_APPEND1, listTheory.APPEND_ASSOC]
QED


(* Compose at the semantic boundary; do not expand nine opcodes together. *)
Theorem typed_dynarray_equal_sequence_run[local]:
  prefix =
    [mk_inst id MLOAD [src] [len];
     mk_inst (id+1) GT [Var len; Lit (n2w cap)] [long];
     mk_inst (id+2) ISZERO [Var long] [ok];
     mk_inst (id+3) ASSERT [Var ok] [];
     mk_inst (id+4) MSTORE [dst; Var len] [];
     mk_inst (id+5) ADD [src; Lit 32w] [sp];
     mk_inst (id+6) ADD [dst; Lit 32w] [dp]] /\
  suffix = [mk_inst (id+7) MUL [Var len; Lit (n2w stride)] [sz];
            mk_inst (id+8) MCOPY [Var dp;Var sp;Var sz] []] /\
  ALL_DISTINCT [len;long;ok;sp;dp;sz] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [len;long;ok;sp;dp;sz]) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  mload (w2n p) s = n2w l /\ l <= cap /\ cap < dimword(:256) /\
  l * stride < dimword(:256) /\
  w2n p + 32 <= s.vs_alloca_next /\ w2n d + 32 <= s.vs_alloca_next /\
  w2n (p+32w) + l * stride <= s.vs_alloca_next /\
  w2n (d+32w) + l * stride <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (prefix ++ suffix) s /\
  ?q. run_inst_seq prefix s = OK q /\
      run_inst_seq (prefix ++ suffix) s =
        OK (mcopy (w2n (d+32w)) (w2n (p+32w)) (l*stride)
              (update_var sz (n2w (l*stride)) q)) /\
      q.vs_memory = (mstore (w2n d) (n2w l) s).vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. ~MEM x [len;long;ok;sp;dp] ==> lookup_var x q = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ALL_DISTINCT [len;long;ok;sp;dp] /\
   (!x. src = Var x \/ dst = Var x ==> ~MEM x [len;long;ok;sp;dp])` by
    (gvs[] >> metis_tac[]) >>
  drule_all typed_dynarray_prologue_run >> strip_tac >>
  `q.vs_alloca_next = s.vs_alloca_next` by
    gvs[venom_state_component_equality] >>
  `run_inst_seq_mem_ok prefix s` by
    (irule typed_dynarray_prologue_mem_ok >> metis_tac[]) >>
  `run_inst_seq_mem_ok suffix q /\
   run_inst_seq suffix q =
     OK (mcopy (w2n (d+32w)) (w2n (p+32w)) (l*stride)
           (update_var sz (n2w (l*stride)) q))` by
    (irule typed_dynarray_equal_suffix_run >> simp[] >>
     qexistsl_tac [`Var dp`, `id+7`, `Var len`, `Var sp`] >>
     gvs[] >> simp[ADD_ASSOC]) >>
  conj_tac >- (irule run_inst_seq_mem_ok_append >> simp[] >> metis_tac[]) >>
  qexists_tac `q` >>
  `run_inst_seq (prefix ++ suffix) s =
     OK (mcopy (w2n (d+32w)) (w2n (p+32w)) (l*stride)
           (update_var sz (n2w (l*stride)) q))` by
    (qpat_assum `run_inst_seq prefix s = OK q` (mp_tac o MATCH_MP run_inst_seq_append) >>
     disch_then (qspec_then `suffix` mp_tac) >> simp[]) >>
  simp[]
QED

Theorem typed_dynarray_equal_compiler_run:
  compile_copy_dynarray_typed ce dst ty cap src ty sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  mload (w2n p) s = n2w l /\ l <= cap /\ cap < dimword(:256) /\
  l * type_memory_bytes ce ty < dimword(:256) /\
  w2n p + 32 <= s.vs_alloca_next /\ w2n d + 32 <= s.vs_alloca_next /\
  w2n (p+32w) + l * type_memory_bytes ce ty <= s.vs_alloca_next /\
  w2n (d+32w) + l * type_memory_bytes ce ty <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    u.vs_memory =
      (mcopy (w2n (d+32w)) (w2n (p+32w)) (l * type_memory_bytes ce ty)
        (mstore (w2n d) (n2w l) s)).vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> drule typed_dynarray_equal_shape >> strip_tac >>
  qabbrev_tac `len = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `long = "%" ++ toString (sa.cs_next_var+1)` >>
  qabbrev_tac `ok = "%" ++ toString (sa.cs_next_var+2)` >>
  qabbrev_tac `sp = "%" ++ toString (sa.cs_next_var+3)` >>
  qabbrev_tac `dp = "%" ++ toString (sa.cs_next_var+4)` >>
  qabbrev_tac `sz = "%" ++ toString (sa.cs_next_var+5)` >>
  `ALL_DISTINCT [len;long;ok;sp;dp;sz] /\
   (!x. src = Var x \/ dst = Var x ==> ~MEM x [len;long;ok;sp;dp;sz])` by
    (simp[Abbr `len`, Abbr `long`, Abbr `ok`, Abbr `sp`, Abbr `dp`, Abbr `sz`,
          ASCIInumbersTheory.toString_inj] >>
     rpt strip_tac >>
     qpat_x_assum `!x. src = Var x \/ dst = Var x ==> _` (qspec_then `x` mp_tac) >>
     gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
  `TAKE 7 (emitted_insts sa sb) =
    [mk_inst sa.cs_next_id MLOAD [src] [len];
     mk_inst (sa.cs_next_id+1) GT [Var len;Lit (n2w cap)] [long];
     mk_inst (sa.cs_next_id+2) ISZERO [Var long] [ok];
     mk_inst (sa.cs_next_id+3) ASSERT [Var ok] [];
     mk_inst (sa.cs_next_id+4) MSTORE [dst;Var len] [];
     mk_inst (sa.cs_next_id+5) ADD [src;Lit 32w] [sp];
     mk_inst (sa.cs_next_id+6) ADD [dst;Lit 32w] [dp]]` by simp[] >>
  `DROP 7 (emitted_insts sa sb) =
    [mk_inst (sa.cs_next_id+7) MUL [Var len;Lit (n2w (type_memory_bytes ce ty))] [sz];
     mk_inst (sa.cs_next_id+8) MCOPY [Var dp;Var sp;Var sz] []]` by simp[] >>
  drule_all typed_dynarray_equal_sequence_run >>
  pure_rewrite_tac[TAKE_DROP] >> strip_tac >> simp[] >>
  simp[mcopy_def, update_var_def, lookup_var_def, write_memory_with_expansion_def] >>
  gvs[venom_state_component_equality] >> rpt strip_tac >>
  `~MEM x [len;long;ok;sp;dp;sz]` by
    gvs[Abbr `len`, Abbr `long`, Abbr `ok`, Abbr `sp`, Abbr `dp`, Abbr `sz`,
        not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
  qpat_x_assum `!x. _ ==> lookup_var x q = lookup_var x s`
    (qspec_then `x` mp_tac) >> simp[lookup_var_def]
QED

Theorem typed_dynarray_equal_cont:
  compile_copy_dynarray_typed ce dst ty cap src ty sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  mload (w2n p) s = n2w l /\ l <= cap /\ cap < dimword(:256) /\
  l * type_memory_bytes ce ty < dimword(:256) /\
  w2n p + 32 <= s.vs_alloca_next /\ w2n d + 32 <= s.vs_alloca_next /\
  w2n (p+32w) + l * type_memory_bytes ce ty <= s.vs_alloca_next /\
  w2n (d+32w) + l * type_memory_bytes ce ty <= s.vs_alloca_next /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. mem_cont_sim ctx fn s (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    u.vs_memory =
      (mcopy (w2n (d+32w)) (w2n (p+32w)) (l * type_memory_bytes ce ty)
        (mstore (w2n d) (n2w l) s)).vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> drule_all typed_dynarray_equal_compiler_run >> strip_tac >>
  drule typed_dynarray_equal_shape >> strip_tac >>
  qexists_tac `u` >> reverse conj_tac >- simp[] >>
  irule typed_bytes_child_seq_cont >> simp[] >>
  qexists_tac `sa` >> simp[IS_PREFIX_APPEND, mk_inst_def, is_terminator_def]
QED
