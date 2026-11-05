(* Semantic copy steps.  Source slot arithmetic is modular. *)
Theory bodyIntCallCopyContent
Ancestors
  bodyIntCallCopyProbe exprSimStorageCopy valueEncodingProps exprLoweringProps
  emitHelperProps fragExec venomExecSemantics venomState venomInst

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

(* Header transport is polymorphic in the semantic invariant. *)
Theorem copy_counter_header_frag:
  !ctx sa sb cv tv limit k P R.
    same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id EQ [Var cv; Lit limit] [tv]] /\
    cv <> tv /\
    (!s w. P s ==> P (update_var tv w s)) /\
    (!s i. P s ==> P (s with vs_inst_idx := i)) ==>
    frag_exec ctx sa sb
      (\s. eval_operand (Var cv) s = SOME k /\ P s)
      (\s. eval_operand (Var cv) s = SOME k /\ P s /\
        eval_operand (Var tv) s = SOME (bool_to_word (k = limit))) R
Proof
  rpt gen_tac >> strip_tac >> irule frag_exec_run_inst_seq >>
  fs[same_blocks_def] >> simp[mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id EQ [Var cv; Lit limit] [tv]) s =
    OK (update_var tv (bool_to_word (k = limit)) s)` by
    (irule step_EQ >> simp[eval_operand_def]) >>
  disj1_tac >> qexists_tac `update_var tv (bool_to_word (k = limit)) s` >>
  gvs[GSYM mk_inst_def, run_inst_seq_def] >>
  conj_tac
  >- gvs[eval_operand_def, lookup_var_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem copy_counter_test:
  !k n. k <= n /\ n < dimword (:256) ==>
    ((n2w k:bytes32) = n2w n <=> k = n)
Proof
  rpt strip_tac >> `k < dimword (:256)` by decide_tac >>
  asm_simp_tac bool_ss [wordsTheory.n2w_11, arithmeticTheory.LESS_MOD]
QED

val _ = Parse.hide "I";

Theorem copy_counted_loop:
  !ctx st0 st1 sth stj st2 stb ste st3 stx hdr body exit cv tv n
    x0 x1 x2 x3 x4 x5 P R.
    emit_inst JMP [Label hdr] [] st0 = (x0,st1) /\
    new_block hdr st1 = (x1,sth) /\
    emit_inst JNZ [Var tv; Label exit; Label body] [] stj = (x2,st2) /\
    new_block body st2 = (x3,stb) /\
    emit_inst JMP [Label hdr] [] ste = (x4,st3) /\
    new_block exit st3 = (x5,stx) /\
    cs_extends sth stj /\ cs_extends stb ste /\
    same_blocks sth stj /\ isPREFIX sth.cs_current_insts stj.cs_current_insts /\
    emitted_insts sth stj =
      [mk_inst sth.cs_next_id EQ [Var cv; Lit (n2w n)] [tv]] /\
    cv <> tv /\ n < dimword (:256) /\
    (!k s w. P k s ==> P k (update_var tv w s)) /\
    (!k s i. P k s ==> P k (s with vs_inst_idx := i)) /\
    (!k s l. P k s ==> P k (jump_to l s)) /\
    (!k. k < n ==> frag_exec ctx stb ste
      (\s. eval_operand (Var cv) s = SOME (n2w k) /\ P k s)
      (\s. eval_operand (Var cv) s = SOME (n2w (k+1)) /\ P (k+1) s) R) ==>
    frag_exec ctx st0 stx
      (\s. eval_operand (Var cv) s = SOME 0w /\ P 0 s)
      (\s. eval_operand (Var cv) s = SOME (n2w n) /\ P n s /\
        eval_operand (Var tv) s = SOME 1w) R
Proof
  rpt gen_tac >> strip_tac >>
  irule (SRULE [bool_to_word_def] (Q.INST
    [`I` |-> `\k s. eval_operand (Var cv) s = SOME (n2w k) /\ P k s`,
     `J` |-> `\k s. eval_operand (Var cv) s = SOME (n2w k) /\ P k s /\
         eval_operand (Var tv) s = SOME (bool_to_word (k = n))`,
     `N` |-> `n`] (SPEC_ALL frag_exec_loop))) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  Cases_on `x0` >> Cases_on `x2` >> Cases_on `x4` >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >>
  rpt (goal_assum (drule_at (Pat `new_block _ _ = _`))) >>
  rpt (goal_assum (drule_at Any)) >>
  conj_tac
  >- (rpt strip_tac >> qexists_tac `bool_to_word (k = n)` >>
      simp[bool_to_word_def] >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> irule frag_exec_conseq >>
      first_x_assum (qspec_then `k` mp_tac) >> simp[arithmeticTheory.ADD1] >>
      disch_then (irule_at Any) >> simp[]) >>
  rpt strip_tac >>
  `((n2w k:bytes32) = n2w n) = (k = n)` by
    (irule copy_counter_test >> simp[]) >>
  irule frag_exec_conseq >> irule_at Any copy_counter_header_frag >>
  goal_assum (drule_at (Pat `emitted_insts _ _ = _`)) >>
  qexistsl_tac [`n2w k:bytes32`, `R`, `P k`] >> simp[]
QED

val _ = Parse.reveal "I";

(* The loop invariant records immutable source reads and the full destination
   exterior, independently of the loop's control position. *)
Definition copy_content_inv_def:
  copy_content_inv ds a b n opc sbase k s <=>
    (!j. j < k ==> mem_word_at (w2n b+32*j) s.vs_memory =
      (if opc = SLOAD then sload (a+n2w j) sbase else tload (a+n2w j) sbase)) /\
    (!off len. off+len <= w2n b \/ w2n b+32*n <= off ==>
      mem_bytes_at off len s.vs_memory = mem_bytes_at off len sbase.vs_memory) /\
    (!x. ~MEM x ds ==> lookup_var x s = lookup_var x sbase) /\
    s with <|vs_memory := sbase.vs_memory; vs_vars := sbase.vs_vars;
      vs_prev_bb := sbase.vs_prev_bb; vs_current_bb := sbase.vs_current_bb;
      vs_inst_idx := sbase.vs_inst_idx|> = sbase
End

Theorem copy_content_inv_control:
  (!ds a b n opc sbase k s i.
    copy_content_inv ds a b n opc sbase k (s with vs_inst_idx := i) =
    copy_content_inv ds a b n opc sbase k s) /\
  (!ds a b n opc sbase k s l.
    copy_content_inv ds a b n opc sbase k (jump_to l s) =
    copy_content_inv ds a b n opc sbase k s)
Proof
  simp[copy_content_inv_def, jump_to_def, lookup_var_def]
QED

Theorem copy_content_inv_register:
  !ds a b n opc sbase k s tv w.
    MEM tv ds /\ copy_content_inv ds a b n opc sbase k s ==>
    copy_content_inv ds a b n opc sbase k (update_var tv w s)
Proof
  rw[copy_content_inv_def, update_var_def, lookup_var_def,
     finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem copy_content_inv_initial:
  !ds a b n opc sbase. copy_content_inv ds a b n opc sbase 0 sbase
Proof
  simp[copy_content_inv_def]
QED

Theorem copy_content_inv_source:
  !ds a b n opc sbase k s addr.
    copy_content_inv ds a b n opc sbase k s ==>
    sload addr s = sload addr sbase /\ tload addr s = tload addr sbase /\
    s.vs_labels = sbase.vs_labels
Proof
  rpt strip_tac >> fs[copy_content_inv_def] >>
  qpat_x_assum `_ with <|vs_memory := _; vs_vars := _;
    vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = _` mp_tac >>
  simp[venom_state_component_equality, sload_def, tload_def,
    contract_storage_def, contract_transient_def] >> metis_tac[]
QED

Theorem copy_content_inv_store:
  !ds a b n opc sbase k s.
    k < n /\ copy_content_inv ds a b n opc sbase k s ==>
    copy_content_inv ds a b n opc sbase (k+1)
      (mstore (w2n b+32*k)
        (if opc = SLOAD then sload (a+n2w k) sbase
         else tload (a+n2w k) sbase) s)
Proof
  rpt gen_tac >> strip_tac >>
  `(!j. j < k+1 ==> mem_word_at (w2n b+32*j)
      (mstore (w2n b+32*k)
        (if opc = SLOAD then sload (a+n2w k) sbase
         else tload (a+n2w k) sbase) s).vs_memory =
        (if opc = SLOAD then sload (a+n2w j) sbase
         else tload (a+n2w j) sbase)) /\
    (!off len. off+len <= w2n b \/ w2n b+32*n <= off ==>
      mem_bytes_at off len (mstore (w2n b+32*k)
        (if opc = SLOAD then sload (a+n2w k) sbase
         else tload (a+n2w k) sbase) s).vs_memory =
      mem_bytes_at off len sbase.vs_memory)` by
    (ho_match_mp_tac copy_prefix_store >> fs[copy_content_inv_def] >> metis_tac[]) >>
  rewrite_tac[copy_content_inv_def] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  fs[copy_content_inv_def] >>
  simp[mstore_def, write_memory_with_expansion_def, lookup_var_def]
QED

Theorem copy_content_body_run:
  !opc src dst a b cv sv vv mv dv nv id s k n ds sbase.
    (opc = SLOAD \/ opc = TLOAD) /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    eval_operand (Var cv) s = SOME (n2w k) /\
    ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
    (!x. src = Var x \/ dst = Var x ==>
      ~MEM x [cv;sv;vv;mv;dv;nv]) /\
    EVERY (\x. MEM x ds) [cv;sv;vv;mv;dv;nv] /\
    k < n /\ w2n b+32*n < dimword (:256) /\
    copy_content_inv ds a b n opc sbase k s ==>
    ?t. run_inst_seq
      [mk_inst id ADD [src; Var cv] [sv];
       mk_inst (id+1) opc [Var sv] [vv];
       mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
       mk_inst (id+3) ADD [dst; Var mv] [dv];
       mk_inst (id+4) MSTORE [Var dv; Var vv] [];
       mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
       mk_inst (id+6) ASSIGN [Var nv] [cv]] s = OK t /\
      eval_operand (Var cv) t = SOME (n2w (k+1)) /\
      copy_content_inv ds a b n opc sbase (k+1) t
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `w2n (b+n2w k*32w) = w2n b+32*k` by
    (irule copy_destination_address >> metis_tac[]) >>
  `sload (a+n2w k) s = sload (a+n2w k) sbase /\
   tload (a+n2w k) s = tload (a+n2w k) sbase` by
    metis_tac[copy_content_inv_source] >>
  qexists_tac `update_var cv (n2w k+1w) (update_var nv (n2w k+1w)
    (mstore (w2n (b+n2w k*32w))
      (if opc = SLOAD then sload (a+n2w k) s else tload (a+n2w k) s)
      (update_var dv (b+n2w k*32w) (update_var mv (n2w k*32w)
        (update_var vv (if opc = SLOAD then sload (a+n2w k) s
          else tload (a+n2w k) s) (update_var sv (a+n2w k) s))))))` >>
  conj_tac >- (irule copy_body_exact >> metis_tac[]) >>
  conj_tac >- simp[eval_operand_def, lookup_var_update_var, wordsTheory.word_add_n2w] >>
  asm_rewrite_tac[] >>
  irule copy_content_inv_register >> conj_tac >- fs[] >>
  irule copy_content_inv_register >> conj_tac >- fs[] >>
  irule copy_content_inv_store >> simp[] >>
  ntac 4 (irule copy_content_inv_register >> conj_tac >- fs[]) >>
  first_assum ACCEPT_TAC
QED

Theorem copy_content_operand:
  !ds a b n opc sbase k s op w.
    copy_content_inv ds a b n opc sbase k s /\
    (!x. op = Var x ==> ~MEM x ds) /\ eval_operand op sbase = SOME w ==>
    eval_operand op s = SOME w
Proof
  rpt strip_tac >>
  `s.vs_labels = sbase.vs_labels` by metis_tac[copy_content_inv_source] >>
  Cases_on `op` >> fs[eval_operand_def, copy_content_inv_def] >> metis_tac[]
QED

Theorem copy_content_body_frag:
  !ctx opc src dst a b cv sv vv mv dv nv sa sb k n ds sbase R.
    (opc = SLOAD \/ opc = TLOAD) /\
    same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ADD [src; Var cv] [sv];
       mk_inst (sa.cs_next_id+1) opc [Var sv] [vv];
       mk_inst (sa.cs_next_id+2) MUL [Var cv; Lit 32w] [mv];
       mk_inst (sa.cs_next_id+3) ADD [dst; Var mv] [dv];
       mk_inst (sa.cs_next_id+4) MSTORE [Var dv; Var vv] [];
       mk_inst (sa.cs_next_id+5) ADD [Var cv; Lit 1w] [nv];
       mk_inst (sa.cs_next_id+6) ASSIGN [Var nv] [cv]] /\
    ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
    EVERY (\x. MEM x ds) [cv;sv;vv;mv;dv;nv] /\
    (!x. src = Var x \/ dst = Var x ==> ~MEM x ds) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b /\
    k < n /\ w2n b+32*n < dimword (:256) ==>
    frag_exec ctx sa sb
      (\s. eval_operand (Var cv) s = SOME (n2w k) /\
        copy_content_inv ds a b n opc sbase k s)
      (\s. eval_operand (Var cv) s = SOME (n2w (k+1)) /\
        copy_content_inv ds a b n opc sbase (k+1) s) R
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `opc <> INVOKE /\ ~is_terminator opc` by gvs[is_terminator_def] >>
  irule frag_exec_run_inst_seq >>
  qpat_x_assum `same_blocks sa sb` mp_tac >>
  rewrite_tac[same_blocks_def] >> strip_tac >>
  simp[mk_inst_def, is_terminator_def] >> rpt strip_tac >>
  `eval_operand src s = SOME a /\ eval_operand dst s = SOME b` by
    metis_tac[copy_content_operand] >>
  `!x. src = Var x \/ dst = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]` by
    (fs[] >> metis_tac[]) >>
  drule_all copy_content_body_run >>
  disch_then (qspec_then `sa.cs_next_id` strip_assume_tac) >>
  disj1_tac >> qexists_tac `t` >>
  gvs[GSYM mk_inst_def, copy_content_inv_control, eval_operand_def, lookup_var_def]
QED

Theorem copy_content_init_frag:
  !ctx sa sb cv ds a b n opc sbase R.
    same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    emitted_insts sa sb = [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]] /\
    MEM cv ds ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. eval_operand (Var cv) s = SOME 0w /\
        copy_content_inv ds a b n opc sbase 0 s) R
Proof
  rpt strip_tac >> irule frag_exec_run_inst_seq >>
  fs[same_blocks_def] >> simp[mk_inst_def, is_terminator_def] >>
  rpt strip_tac >> gvs[] >> disj1_tac >>
  qexists_tac `update_var cv 0w sbase` >>
  simp[run_inst_seq_def, step_inst_base_def, eval_operand_def,
       lookup_var_update_var, copy_content_inv_control] >>
  conj_tac >- simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  irule copy_content_inv_register >> simp[copy_content_inv_initial]
QED

Theorem compile_storage_copy_content_frag:
  !ctx loc src dst n sa u sb sbase a b R.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b /\
    n < dimword (:256) /\ w2n b+32*n < dimword (:256) ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (!j. j < n ==> mem_word_at (w2n b+32*j) s.vs_memory =
         (if loc = LocStorage then sload (a+n2w j) sbase
          else tload (a+n2w j) sbase)) /\
        (!off len. off+len <= w2n b \/ w2n b+32*n <= off ==>
          mem_bytes_at off len s.vs_memory = mem_bytes_at off len sbase.vs_memory) /\
        (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
        s with <|vs_memory := sbase.vs_memory; vs_vars := sbase.vs_vars;
          vs_prev_bb := sbase.vs_prev_bb; vs_current_bb := sbase.vs_current_bb;
          vs_inst_idx := sbase.vs_inst_idx|> = sbase) R
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all compile_storage_copy_certificate >> strip_tac >>
  rename1 `emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj)` >>
  rename1 `emitted_insts sa s0 = [mk_inst _ ASSIGN _ _]` >>
  rename1 `emitted_insts stb ste = [mk_inst _ ADD _ [sv]; _; _; _; _; _; _]` >>
  qmatch_asmsub_abbrev_tac `ALL_DISTINCT ds` >>
  irule frag_exec_seq >>
  qexistsl_tac [`\s. eval_operand (Var cv) s = SOME 0w /\
    copy_content_inv ds a b n (if loc = LocStorage then SLOAD else TLOAD) sbase 0 s`,
    `s0`] >> simp[] >>
  conj_tac >- (irule copy_content_init_frag >> simp[Abbr `ds`]) >>
  irule frag_exec_conseq >>
  irule_at Any copy_counted_loop >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >>
  rpt (goal_assum (drule_at (Pat `new_block _ _ = _`))) >>
  rpt (goal_assum (drule_at Any)) >>
  qexistsl_tac [`R`, `copy_content_inv ds a b n
    (if loc = LocStorage then SLOAD else TLOAD) sbase`] >>
  simp[copy_content_inv_control] >>
  conj_tac >- gvs[Abbr `ds`, listTheory.ALL_DISTINCT] >>
  conj_tac
  >- (rpt strip_tac >> irule copy_content_inv_register >>
      simp[Abbr `ds`]) >>
  conj_tac
  >- (rpt strip_tac >> irule copy_content_body_frag >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac
      >- (goal_assum (drule_at (Pat `emitted_insts _ _ = [_;_;_;_;_;_;_]`)) >>
          simp[Abbr `ds`] >> gvs[listTheory.ALL_DISTINCT] >> metis_tac[]) >>
      simp[] >> Cases_on `loc = LocStorage` >> simp[]) >>
  rw[copy_content_inv_def] >> metis_tac[]
QED
