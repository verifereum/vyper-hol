(* Semantic copy steps.  Source slot arithmetic is modular. *)
Theory bodyIntCallCopyContent
Ancestors
  bodyIntCallCopyProbe exprSimStorageCopy valueEncodingProps exprLoweringProps
  emitHelperProps venomExecSemantics venomState venomInst

Theorem copy_load_exact:
  !opc src a id out s.
    (opc = SLOAD \/ opc = TLOAD) /\ eval_operand src s = SOME a ==>
    step_inst_base (mk_inst id opc [src] [out]) s =
      OK (update_var out (if opc = SLOAD then sload a s else tload a s) s)
Proof
  rpt strip_tac >> gvs[]
  >- (irule step_SLOAD >> simp[]) >>
  rw[step_inst_base_def, exec_read1_def]
QED

Theorem copy_slot_exact:
  !opc src dst a b id out s.
    (opc = SLOAD \/ opc = TLOAD) /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    (!x. dst = Var x ==> x <> out) ==>
    run_inst_seq
      [mk_inst id opc [src] [out];
       mk_inst (id+1) MSTORE [dst; Var out] []] s =
    OK (mstore (w2n b) (if opc = SLOAD then sload a s else tload a s)
          (update_var out (if opc = SLOAD then sload a s else tload a s) s))
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id opc [src] [out]) s =
    OK (update_var out (if opc = SLOAD then sload a s else tload a s) s)` by
    (irule copy_load_exact >> simp[]) >>
  qmatch_goalsub_abbrev_tac `mstore (w2n b) loaded t` >>
  `eval_operand dst t = SOME b` by
    (Cases_on `dst` >> gvs[Abbr `t`, eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst (id+1) MSTORE [dst; Var out] []) t =
    OK (mstore (w2n b) loaded t)` by
    (irule step_MSTORE >> simp[Abbr `t`, eval_operand_def, lookup_var_update_var]) >>
  gvs[run_inst_seq_def, Abbr `t`, Abbr `loaded`]
QED

Theorem copy_slot_content_frame:
  !opc src dst a b id out s.
    (opc = SLOAD \/ opc = TLOAD) /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    (!x. dst = Var x ==> x <> out) ==>
    ?t. run_inst_seq
          [mk_inst id opc [src] [out];
           mk_inst (id+1) MSTORE [dst; Var out] []] s = OK t /\
        mem_word_at (w2n b) t.vs_memory =
          (if opc = SLOAD then sload a s else tload a s) /\
        (!off len. off + len <= w2n b \/ w2n b + 32 <= off ==>
          mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
        (!x. x <> out ==> lookup_var x t = lookup_var x s) /\
        t with <|vs_memory := s.vs_memory; vs_vars := s.vs_vars|> = s
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qexists_tac `mstore (w2n b)
    (if opc = SLOAD then sload a s else tload a s)
    (update_var out (if opc = SLOAD then sload a s else tload a s) s)` >>
  conj_tac >- (irule copy_slot_exact >> metis_tac[]) >>
  simp[mstore_mem_word_at_same] >>
  conj_tac
  >- (rpt strip_tac >> irule EQ_TRANS >>
      irule_at Any mstore_mem_bytes_at_disjoint >> simp[] >>
      simp[update_var_def]) >>
  simp[mstore_def, write_memory_with_expansion_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem copy_source_exact:
  !opc src a cv sv vv id s k.
    (opc = SLOAD \/ opc = TLOAD) /\
    eval_operand src s = SOME a /\ eval_operand (Var cv) s = SOME k ==>
    run_inst_seq
      [mk_inst id ADD [src; Var cv] [sv];
       mk_inst (id+1) opc [Var sv] [vv]] s =
    OK (update_var vv (if opc = SLOAD then sload (a+k) s else tload (a+k) s)
          (update_var sv (a+k) s))
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `step_inst_base (mk_inst id ADD [src; Var cv] [sv]) s =
     OK (update_var sv (a+k) s)` by (irule step_ADD >> simp[]) >>
  qmatch_goalsub_abbrev_tac `update_var vv loaded s1` >>
  `step_inst_base (mk_inst (id+1) opc [Var sv] [vv]) s1 =
     OK (update_var vv (if opc = SLOAD then sload (a+k) s1 else tload (a+k) s1) s1)` by
    (irule copy_load_exact >> simp[Abbr `s1`, eval_operand_def,
       lookup_var_update_var]) >>
  gvs[run_inst_seq_def, Abbr `loaded`, Abbr `s1`, sload_def, tload_def,
      update_var_def, contract_storage_def, contract_transient_def]
QED

Theorem copy_destination_exact:
  !dst b cv vv mv dv id s k v.
    eval_operand dst s = SOME b /\ eval_operand (Var cv) s = SOME k /\
    eval_operand (Var vv) s = SOME v /\
    ALL_DISTINCT [vv; mv; dv] /\
    (!x. dst = Var x ==> x <> mv) ==>
    run_inst_seq
      [mk_inst id MUL [Var cv; Lit 32w] [mv];
       mk_inst (id+1) ADD [dst; Var mv] [dv];
       mk_inst (id+2) MSTORE [Var dv; Var vv] []] s =
    OK (mstore (w2n (b+k*32w)) v
         (update_var dv (b+k*32w) (update_var mv (k*32w) s)))
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id MUL [Var cv; Lit 32w] [mv]) s =
     OK (update_var mv (k*32w) s)` by
    (irule step_MUL >> simp[eval_operand_def]) >>
  qmatch_goalsub_abbrev_tac `update_var dv addr s1` >>
  `eval_operand dst s1 = SOME b` by
    (Cases_on `dst` >> gvs[Abbr `s1`, eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst (id+1) ADD [dst; Var mv] [dv]) s1 =
     OK (update_var dv addr s1)` by
    (simp[Abbr `addr`] >> irule step_ADD >>
     simp[Abbr `s1`, eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst (id+2) MSTORE [Var dv; Var vv] [])
     (update_var dv addr s1) = OK (mstore (w2n addr) v (update_var dv addr s1))` by
    (irule step_MSTORE >> gvs[Abbr `s1`, eval_operand_def,
       lookup_var_update_var, listTheory.ALL_DISTINCT]) >>
  simp[run_inst_seq_def, Abbr `s1`]
QED

Theorem copy_increment_exact:
  !cv nv id s k.
    eval_operand (Var cv) s = SOME k ==>
    run_inst_seq
      [mk_inst id ADD [Var cv; Lit 1w] [nv];
       mk_inst (id+1) ASSIGN [Var nv] [cv]] s =
    OK (update_var cv (k+1w) (update_var nv (k+1w) s))
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id ADD [Var cv; Lit 1w] [nv]) s =
     OK (update_var nv (k+1w) s)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  simp[run_inst_seq_def] >>
  simp[step_inst_base_def, eval_operand_def, lookup_var_update_var]
QED

Theorem copy_body_exact:
  !opc src dst a b cv sv vv mv dv nv id s k.
    (opc = SLOAD \/ opc = TLOAD) /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    eval_operand (Var cv) s = SOME k /\
    ALL_DISTINCT [cv; sv; vv; mv; dv; nv] /\
    (!x. src = Var x \/ dst = Var x ==>
         ~MEM x [cv; sv; vv; mv; dv; nv]) ==>
    run_inst_seq
      [mk_inst id ADD [src; Var cv] [sv];
       mk_inst (id+1) opc [Var sv] [vv];
       mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
       mk_inst (id+3) ADD [dst; Var mv] [dv];
       mk_inst (id+4) MSTORE [Var dv; Var vv] [];
       mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
       mk_inst (id+6) ASSIGN [Var nv] [cv]] s =
    OK (update_var cv (k+1w) (update_var nv (k+1w)
      (mstore (w2n (b+k*32w))
        (if opc = SLOAD then sload (a+k) s else tload (a+k) s)
        (update_var dv (b+k*32w) (update_var mv (k*32w)
          (update_var vv (if opc = SLOAD then sload (a+k) s else tload (a+k) s)
            (update_var sv (a+k) s)))))))
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac `update_var vv loaded s0` >>
  qabbrev_tac `s1 = update_var vv loaded s0` >>
  `run_inst_seq [mk_inst id ADD [src; Var cv] [sv];
      mk_inst (id+1) opc [Var sv] [vv]] s = OK s1` by
    (simp[Abbr `s1`, Abbr `s0`, Abbr `loaded`] >>
     irule copy_source_exact >> simp[]) >>
  qmatch_goalsub_abbrev_tac `mstore off loaded s2` >>
  `run_inst_seq [mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
      mk_inst ((id+2)+1) ADD [dst; Var mv] [dv];
      mk_inst ((id+2)+2) MSTORE [Var dv; Var vv] []] s1 =
    OK (mstore off loaded s2)` by
    (simp[Abbr `off`, Abbr `s2`, SimpRHS] >> irule copy_destination_exact >>
     gvs[Abbr `s1`, Abbr `s0`, eval_operand_def, lookup_var_update_var,
         listTheory.ALL_DISTINCT] >> Cases_on `dst` >>
     gvs[eval_operand_def, lookup_var_update_var] >> metis_tac[]) >>
  `run_inst_seq [mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
      mk_inst ((id+5)+1) ASSIGN [Var nv] [cv]] (mstore off loaded s2) =
    OK (update_var cv (k+1w) (update_var nv (k+1w) (mstore off loaded s2)))` by
    (irule copy_increment_exact >>
     gvs[Abbr `s2`, Abbr `s1`, Abbr `s0`, eval_operand_def,
       lookup_var_update_var, mstore_def, write_memory_with_expansion_def,
       lookup_var_def, update_var_def, listTheory.ALL_DISTINCT]) >>
  qpat_x_assum `run_inst_seq _ s = OK s1`
    (assume_tac o SRULE [] o MATCH_MP run_inst_seq_append) >>
  qpat_x_assum `run_inst_seq _ s1 = OK (mstore _ _ _)`
    (assume_tac o SRULE [arithmeticTheory.ADD_ASSOC] o MATCH_MP run_inst_seq_append) >>
  gvs[arithmeticTheory.ADD_ASSOC]
QED

Theorem copy_body_content_frame:
  !opc src dst a b cv sv vv mv dv nv id s k.
    (opc = SLOAD \/ opc = TLOAD) /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    eval_operand (Var cv) s = SOME k /\
    ALL_DISTINCT [cv; sv; vv; mv; dv; nv] /\
    (!x. src = Var x \/ dst = Var x ==>
         ~MEM x [cv; sv; vv; mv; dv; nv]) ==>
    ?t. run_inst_seq
      [mk_inst id ADD [src; Var cv] [sv];
       mk_inst (id+1) opc [Var sv] [vv];
       mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
       mk_inst (id+3) ADD [dst; Var mv] [dv];
       mk_inst (id+4) MSTORE [Var dv; Var vv] [];
       mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
       mk_inst (id+6) ASSIGN [Var nv] [cv]] s = OK t /\
      eval_operand (Var cv) t = SOME (k+1w) /\
      mem_word_at (w2n (b+k*32w)) t.vs_memory =
        (if opc = SLOAD then sload (a+k) s else tload (a+k) s) /\
      (!off len. off + len <= w2n (b+k*32w) \/
           w2n (b+k*32w) + 32 <= off ==>
        mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
      (!x. ~MEM x [cv; sv; vv; mv; dv; nv] ==>
        lookup_var x t = lookup_var x s) /\
      t with <|vs_memory := s.vs_memory; vs_vars := s.vs_vars|> = s
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qexists_tac `update_var cv (k+1w) (update_var nv (k+1w)
    (mstore (w2n (b+k*32w))
      (if opc = SLOAD then sload (a+k) s else tload (a+k) s)
      (update_var dv (b+k*32w) (update_var mv (k*32w)
        (update_var vv (if opc = SLOAD then sload (a+k) s else tload (a+k) s)
          (update_var sv (a+k) s))))))` >>
  conj_tac >- (irule copy_body_exact >> metis_tac[]) >>
  simp[eval_operand_def, lookup_var_update_var] >>
  simp[update_var_def, mstore_mem_word_at_same] >>
  conj_tac
  >- (rpt strip_tac >> irule EQ_TRANS >>
      irule_at Any mstore_mem_bytes_at_disjoint >> simp[] >>
      simp[update_var_def]) >>
  simp[mstore_def, write_memory_with_expansion_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem copy_prefix_store:
  !start k n f s sbase.
    k < n /\
    (!j. j < k ==> mem_word_at (start+32*j) s.vs_memory = f j) /\
    (!off len. off+len <= start \/ start+32*n <= off ==>
      mem_bytes_at off len s.vs_memory = mem_bytes_at off len sbase.vs_memory) ==>
    (!j. j < k+1 ==>
      mem_word_at (start+32*j) (mstore (start+32*k) (f k) s).vs_memory = f j) /\
    (!off len. off+len <= start \/ start+32*n <= off ==>
      mem_bytes_at off len (mstore (start+32*k) (f k) s).vs_memory =
        mem_bytes_at off len sbase.vs_memory)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt strip_tac >> Cases_on `j = k`
      >- gvs[mstore_mem_word_at_same] >>
      `j < k` by decide_tac >>
      `start+32*j+32 <= start+32*k` by decide_tac >>
      simp[mstore_mem_word_at_disjoint]) >>
  rpt strip_tac >>
  `off+len <= start+32*k \/ start+32*k+32 <= off` by decide_tac >>
  simp[mstore_mem_bytes_at_disjoint]
QED

Theorem copy_destination_address:
  !b k n.
    k < n /\ w2n (b:bytes32) + 32*n < dimword (:256) ==>
    w2n (b + n2w k * 32w) = w2n b + 32*k
Proof
  rpt strip_tac >>
  `w2n b + 32*k < dimword (:256)` by decide_tac >>
  `b = n2w (w2n b)` by simp[] >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[wordsTheory.word_mul_n2w, wordsTheory.word_add_n2w] >>
  asm_simp_tac bool_ss [wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
       arithmeticTheory.MULT_COMM, wordsTheory.w2n_lt] >>
  irule arithmeticTheory.LESS_MOD >>
  once_rewrite_tac[arithmeticTheory.MULT_COMM] >> first_assum ACCEPT_TAC
QED
