(* Runtime data-section copies: padded DLOAD, never constructor ILOAD. *)
Theory bodyIntCallCodeCopy
Ancestors
  bodyIntCallCopyContent exprSimUnwrap valueEncoding valueEncodingProps exprSimAttributeFields
  storageDecodeMemory
  venomState venomExecSemantics venomMemProps venomInst emitHelperProps fragExec exprLoweringProps
  exprSimStorageCopy exprLowering context emitHelper list rich_list loweringSlice compileEnv exprSim valueEncodingTyping
Libs
  monadsyntax

Theorem code_copy_load_exact:
  !src a id out s.
    eval_operand src s = SOME a ==>
    step_inst_base (mk_inst id DLOAD [src] [out]) s =
      OK (update_var out (mem_word_at (w2n a) s.vs_data_section) s)
Proof
  rpt strip_tac >> drule step_DLOAD >> simp[mem_word_at_def]
QED

Theorem code_copy_slot_exact:
  !src dst a b id out s.
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    (!x. dst = Var x ==> x <> out) ==>
    run_inst_seq
      [mk_inst id DLOAD [src] [out];
       mk_inst (id+1) MSTORE [dst; Var out] []] s =
    OK (mstore (w2n b) (mem_word_at (w2n a) s.vs_data_section)
          (update_var out (mem_word_at (w2n a) s.vs_data_section) s))
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id DLOAD [src] [out]) s =
    OK (update_var out (mem_word_at (w2n a) s.vs_data_section) s)` by
    (irule code_copy_load_exact >> simp[]) >>
  qmatch_goalsub_abbrev_tac `mstore (w2n b) loaded t` >>
  `eval_operand dst t = SOME b` by
    (Cases_on `dst` >> gvs[Abbr `t`, eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst (id+1) MSTORE [dst; Var out] []) t =
    OK (mstore (w2n b) loaded t)` by
    (irule step_MSTORE >> simp[Abbr `t`, eval_operand_def, lookup_var_update_var]) >>
  gvs[run_inst_seq_def, Abbr `t`, Abbr `loaded`]
QED

Theorem code_copy_slot_content_frame:
  !src dst a b id out s.
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    (!x. dst = Var x ==> x <> out) ==>
    ?t. run_inst_seq
          [mk_inst id DLOAD [src] [out];
           mk_inst (id+1) MSTORE [dst; Var out] []] s = OK t /\
        mem_word_at (w2n b) t.vs_memory = mem_word_at (w2n a) s.vs_data_section /\
        (!off len. off + len <= w2n b \/ w2n b + 32 <= off ==>
          mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
        (!x. x <> out ==> lookup_var x t = lookup_var x s) /\
        t with <|vs_memory := s.vs_memory; vs_vars := s.vs_vars|> = s
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `mstore (w2n b) (mem_word_at (w2n a) s.vs_data_section)
    (update_var out (mem_word_at (w2n a) s.vs_data_section) s)` >>
  conj_tac >- (irule code_copy_slot_exact >> metis_tac[]) >>
  simp[mstore_mem_word_at_same] >> conj_tac
  >- (rpt strip_tac >> irule EQ_TRANS >>
      irule_at Any mstore_mem_bytes_at_disjoint >> simp[] >> simp[update_var_def]) >>
  simp[mstore_def, write_memory_with_expansion_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Unlike the ordinary split boundary, this also covers data past EOF. *)
Theorem mem_bytes_at_split_padded:
  !off m n mem.
    mem_bytes_at off (m+n) mem =
      mem_bytes_at off m mem ++ mem_bytes_at (off+m) n mem
Proof
  rw[mem_bytes_at_def, listTheory.LIST_EQ_REWRITE,
     listTheory.LENGTH_APPEND, listTheory.LENGTH_TAKE,
     listTheory.LENGTH_DROP, rich_listTheory.LENGTH_REPLICATE] >>
  rw[listTheory.EL_APPEND_EQN, listTheory.EL_TAKE, listTheory.EL_DROP,
     rich_listTheory.EL_REPLICATE, listTheory.LENGTH_APPEND, listTheory.LENGTH_TAKE,
     listTheory.LENGTH_DROP, rich_listTheory.LENGTH_REPLICATE] >> fs[]
QED

Theorem mem_word_at_bytes_eq:
  !a b m m'. mem_word_at a m = mem_word_at b m' ==>
    mem_bytes_at a 32 m = mem_bytes_at b 32 m'
Proof
  rpt strip_tac >>
  `word_to_bytes (mem_word_at a m) T = mem_bytes_at a 32 m` by
    (simp[NoAsms, mem_word_at_def, GSYM mem_bytes_at_def] >>
     irule venomMemProofsTheory.word_bytes_roundtrip_proof >>
     simp[dividesTheory.divides_def]) >>
  `word_to_bytes (mem_word_at b m') T = mem_bytes_at b 32 m'` by
    (simp[NoAsms, mem_word_at_def, GSYM mem_bytes_at_def] >>
     irule venomMemProofsTheory.word_bytes_roundtrip_proof >>
     simp[dividesTheory.divides_def]) >>
  metis_tac[]
QED

Theorem copied_code_words_bytes:
  !n src dst mem mem'.
    (!j. j < n ==> mem_word_at (dst+32*j) mem' = mem_word_at (src+32*j) mem) ==>
    mem_bytes_at dst (32*n) mem' = mem_bytes_at src (32*n) mem
Proof
  Induct >- simp[mem_bytes_at_def] >> rpt gen_tac >> strip_tac >>
  `32*SUC n = 32*n+32` by decide_tac >>
  simp[mem_bytes_at_split_padded] >> BINOP_TAC
  >- (first_x_assum irule >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  irule mem_word_at_bytes_eq >>
  first_x_assum (qspec_then `n` mp_tac) >>
  qpat_x_assum `32*SUC n = _` kall_tac >>
  qpat_x_assum `!src dst mem mem'. _` kall_tac >>
  `32*n+src = src+32*n` by decide_tac >>
  pop_assum SUBST1_TAC >> simp[]
QED

Theorem code_copy_source_exact:
  !src a cv smv sv vv id s k.
    eval_operand src s = SOME a /\ eval_operand (Var cv) s = SOME k /\
    cv <> smv /\ (!x. src = Var x ==> x <> smv) ==>
    run_inst_seq
      [mk_inst id MUL [Var cv; Lit 32w] [smv];
       mk_inst (id+1) ADD [src; Var smv] [sv];
       mk_inst (id+2) DLOAD [Var sv] [vv]] s =
    OK (update_var vv (mem_word_at (w2n (a+k*32w)) s.vs_data_section)
          (update_var sv (a+k*32w) (update_var smv (k*32w) s)))
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id MUL [Var cv; Lit 32w] [smv]) s =
    OK (update_var smv (k*32w) s)` by
    (irule step_MUL >> simp[eval_operand_def]) >>
  qmatch_goalsub_abbrev_tac `update_var sv addr s1` >>
  `eval_operand src s1 = SOME a` by
    (Cases_on `src` >> gvs[Abbr `s1`, eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst (id+1) ADD [src; Var smv] [sv]) s1 =
    OK (update_var sv addr s1)` by
    (simp[Abbr `addr`] >> irule step_ADD >>
     simp[Abbr `s1`, eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst (id+2) DLOAD [Var sv] [vv]) (update_var sv addr s1) =
    OK (update_var vv (mem_word_at (w2n addr) (update_var sv addr s1).vs_data_section)
      (update_var sv addr s1))` by
    (irule code_copy_load_exact >> simp[eval_operand_def, lookup_var_update_var]) >>
  gvs[Abbr `s1`] >> simp[run_inst_seq_def] >> simp[update_var_def]
QED

Theorem code_copy_body_exact:
  !src dst a b cv smv sv vv mv dv nv id s k.
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    eval_operand (Var cv) s = SOME k /\
    ALL_DISTINCT [cv;smv;sv;vv;mv;dv;nv] /\
    (!x. src = Var x \/ dst = Var x ==>
         ~MEM x [cv;smv;sv;vv;mv;dv;nv]) ==>
    run_inst_seq
      [mk_inst id MUL [Var cv; Lit 32w] [smv];
       mk_inst (id+1) ADD [src; Var smv] [sv];
       mk_inst (id+2) DLOAD [Var sv] [vv];
       mk_inst (id+3) MUL [Var cv; Lit 32w] [mv];
       mk_inst (id+4) ADD [dst; Var mv] [dv];
       mk_inst (id+5) MSTORE [Var dv; Var vv] [];
       mk_inst (id+6) ADD [Var cv; Lit 1w] [nv];
       mk_inst (id+7) ASSIGN [Var nv] [cv]] s =
    OK (update_var cv (k+1w) (update_var nv (k+1w)
      (mstore (w2n (b+k*32w))
        (mem_word_at (w2n (a+k*32w)) s.vs_data_section)
        (update_var dv (b+k*32w) (update_var mv (k*32w)
          (update_var vv (mem_word_at (w2n (a+k*32w)) s.vs_data_section)
            (update_var sv (a+k*32w) (update_var smv (k*32w) s))))))))
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `update_var vv loaded s0` >>
  qabbrev_tac `s1 = update_var vv loaded s0` >>
  `run_inst_seq [mk_inst id MUL [Var cv; Lit 32w] [smv];
      mk_inst (id+1) ADD [src; Var smv] [sv];
      mk_inst (id+2) DLOAD [Var sv] [vv]] s = OK s1` by
    (simp[Abbr `s1`, Abbr `s0`, Abbr `loaded`] >>
     irule code_copy_source_exact >> fs[listTheory.ALL_DISTINCT] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `mstore off loaded s2` >>
  `run_inst_seq [mk_inst (id+3) MUL [Var cv; Lit 32w] [mv];
      mk_inst ((id+3)+1) ADD [dst; Var mv] [dv];
      mk_inst ((id+3)+2) MSTORE [Var dv; Var vv] []] s1 =
    OK (mstore off loaded s2)` by
    (simp[Abbr `off`, Abbr `s2`, SimpRHS] >> irule copy_destination_exact >>
     gvs[Abbr `s1`, Abbr `s0`, eval_operand_def, lookup_var_update_var,
         listTheory.ALL_DISTINCT] >> Cases_on `dst` >>
     gvs[eval_operand_def, lookup_var_update_var] >> metis_tac[]) >>
  `run_inst_seq [mk_inst (id+6) ADD [Var cv; Lit 1w] [nv];
      mk_inst ((id+6)+1) ASSIGN [Var nv] [cv]] (mstore off loaded s2) =
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

(* A copied-prefix footprint packages the repeated content, exterior-memory,
   old-register and control-independent state conjunction for the loop. *)
Definition code_copy_inv_def:
  code_copy_inv ds a b n sbase k s <=>
    (!j. j < k ==> mem_word_at (w2n b+32*j) s.vs_memory =
      mem_word_at (w2n a+32*j) sbase.vs_data_section) /\
    (!off len. off+len <= w2n b \/ w2n b+32*n <= off ==>
      mem_bytes_at off len s.vs_memory = mem_bytes_at off len sbase.vs_memory) /\
    (!x. ~MEM x ds ==> lookup_var x s = lookup_var x sbase) /\
    s with <|vs_memory := sbase.vs_memory; vs_vars := sbase.vs_vars;
      vs_prev_bb := sbase.vs_prev_bb; vs_current_bb := sbase.vs_current_bb;
      vs_inst_idx := sbase.vs_inst_idx|> = sbase
End

Theorem code_copy_inv_control:
  (!ds a b n sbase k s i.
    code_copy_inv ds a b n sbase k (s with vs_inst_idx := i) =
    code_copy_inv ds a b n sbase k s) /\
  (!ds a b n sbase k s l.
    code_copy_inv ds a b n sbase k (jump_to l s) =
    code_copy_inv ds a b n sbase k s)
Proof
  simp[code_copy_inv_def, jump_to_def, lookup_var_def]
QED

Theorem code_copy_inv_register:
  !ds a b n sbase k s tv w.
    MEM tv ds /\ code_copy_inv ds a b n sbase k s ==>
    code_copy_inv ds a b n sbase k (update_var tv w s)
Proof
  rw[code_copy_inv_def, update_var_def, lookup_var_def,
     finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem code_copy_inv_initial:
  !ds a b n sbase. code_copy_inv ds a b n sbase 0 sbase
Proof
  simp[code_copy_inv_def]
QED

Theorem code_copy_inv_source:
  !ds a b n sbase k s.
    code_copy_inv ds a b n sbase k s ==>
    s.vs_data_section = sbase.vs_data_section /\ s.vs_labels = sbase.vs_labels
Proof
  rpt strip_tac >> fs[code_copy_inv_def] >>
  qpat_x_assum `_ with <|vs_memory := _; vs_vars := _;
    vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = _` mp_tac >>
  simp[venom_state_component_equality] >> metis_tac[]
QED

Theorem code_copy_inv_store:
  !ds a b n sbase k s.
    k < n /\ code_copy_inv ds a b n sbase k s ==>
    code_copy_inv ds a b n sbase (k+1)
      (mstore (w2n b+32*k) (mem_word_at (w2n a+32*k) sbase.vs_data_section) s)
Proof
  rpt gen_tac >> strip_tac >>
  `(!j. j < k+1 ==> mem_word_at (w2n b+32*j)
      (mstore (w2n b+32*k) (mem_word_at (w2n a+32*k) sbase.vs_data_section) s).vs_memory =
        mem_word_at (w2n a+32*j) sbase.vs_data_section) /\
    (!off len. off+len <= w2n b \/ w2n b+32*n <= off ==>
      mem_bytes_at off len (mstore (w2n b+32*k)
        (mem_word_at (w2n a+32*k) sbase.vs_data_section) s).vs_memory =
      mem_bytes_at off len sbase.vs_memory)` by
    (ho_match_mp_tac copy_prefix_store >> fs[code_copy_inv_def] >> metis_tac[]) >>
  rewrite_tac[code_copy_inv_def] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  fs[code_copy_inv_def] >>
  simp[mstore_def, write_memory_with_expansion_def, lookup_var_def]
QED

Theorem code_copy_content_body_run:
  !src dst a b cv smv sv vv mv dv nv id s k n ds sbase.
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    eval_operand (Var cv) s = SOME (n2w k) /\
    ALL_DISTINCT [cv;smv;sv;vv;mv;dv;nv] /\
    (!x. src = Var x \/ dst = Var x ==>
      ~MEM x [cv;smv;sv;vv;mv;dv;nv]) /\
    EVERY (\x. MEM x ds) [cv;smv;sv;vv;mv;dv;nv] /\
    k < n /\ w2n b+32*n < dimword (:256) /\
    w2n a+32*n < dimword (:256) /\
    code_copy_inv ds a b n sbase k s ==>
    ?t. run_inst_seq
      [mk_inst id MUL [Var cv; Lit 32w] [smv];
       mk_inst (id+1) ADD [src; Var smv] [sv];
       mk_inst (id+2) DLOAD [Var sv] [vv];
       mk_inst (id+3) MUL [Var cv; Lit 32w] [mv];
       mk_inst (id+4) ADD [dst; Var mv] [dv];
       mk_inst (id+5) MSTORE [Var dv; Var vv] [];
       mk_inst (id+6) ADD [Var cv; Lit 1w] [nv];
       mk_inst (id+7) ASSIGN [Var nv] [cv]] s = OK t /\
      eval_operand (Var cv) t = SOME (n2w (k+1)) /\
      code_copy_inv ds a b n sbase (k+1) t
Proof
  rpt gen_tac >> strip_tac >>
  `w2n (b+n2w k*32w) = w2n b+32*k` by
    (irule copy_destination_address >> metis_tac[]) >>
  `w2n (a+n2w k*32w) = w2n a+32*k` by
    (irule copy_destination_address >> metis_tac[]) >>
  `s.vs_data_section = sbase.vs_data_section` by metis_tac[code_copy_inv_source] >>
  qexists_tac `update_var cv (n2w k+1w) (update_var nv (n2w k+1w)
    (mstore (w2n (b+n2w k*32w))
      (mem_word_at (w2n (a+n2w k*32w)) s.vs_data_section)
      (update_var dv (b+n2w k*32w) (update_var mv (n2w k*32w)
        (update_var vv (mem_word_at (w2n (a+n2w k*32w)) s.vs_data_section)
          (update_var sv (a+n2w k*32w) (update_var smv (n2w k*32w) s)))))))` >>
  conj_tac >- (irule code_copy_body_exact >> metis_tac[]) >>
  conj_tac >- simp[eval_operand_def, lookup_var_update_var, wordsTheory.word_add_n2w] >>
  asm_rewrite_tac[] >>
  irule code_copy_inv_register >> conj_tac >- fs[] >>
  irule code_copy_inv_register >> conj_tac >- fs[] >>
  irule code_copy_inv_store >> simp[] >>
  ntac 5 (irule code_copy_inv_register >> conj_tac >- fs[]) >>
  first_assum ACCEPT_TAC
QED

Theorem code_copy_content_operand:
  !ds a b n sbase k s op w.
    code_copy_inv ds a b n sbase k s /\
    (!x. op = Var x ==> ~MEM x ds) /\ eval_operand op sbase = SOME w ==>
    eval_operand op s = SOME w
Proof
  rpt strip_tac >>
  `s.vs_labels = sbase.vs_labels` by metis_tac[code_copy_inv_source] >>
  Cases_on `op` >> fs[eval_operand_def, code_copy_inv_def] >> metis_tac[]
QED

Theorem code_copy_content_body_frag:
  !ctx src dst a b cv smv sv vv mv dv nv sa sb k n ds sbase R.
    same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id MUL [Var cv; Lit 32w] [smv];
       mk_inst (sa.cs_next_id+1) ADD [src; Var smv] [sv];
       mk_inst (sa.cs_next_id+2) DLOAD [Var sv] [vv];
       mk_inst (sa.cs_next_id+3) MUL [Var cv; Lit 32w] [mv];
       mk_inst (sa.cs_next_id+4) ADD [dst; Var mv] [dv];
       mk_inst (sa.cs_next_id+5) MSTORE [Var dv; Var vv] [];
       mk_inst (sa.cs_next_id+6) ADD [Var cv; Lit 1w] [nv];
       mk_inst (sa.cs_next_id+7) ASSIGN [Var nv] [cv]] /\
    ALL_DISTINCT [cv;smv;sv;vv;mv;dv;nv] /\
    EVERY (\x. MEM x ds) [cv;smv;sv;vv;mv;dv;nv] /\
    (!x. src = Var x \/ dst = Var x ==> ~MEM x ds) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b /\
    k < n /\ w2n b+32*n < dimword (:256) /\
    w2n a+32*n < dimword (:256) ==>
    frag_exec ctx sa sb
      (\s. eval_operand (Var cv) s = SOME (n2w k) /\
        code_copy_inv ds a b n sbase k s)
      (\s. eval_operand (Var cv) s = SOME (n2w (k+1)) /\
        code_copy_inv ds a b n sbase (k+1) s) R
Proof
  rpt gen_tac >> strip_tac >> irule frag_exec_run_inst_seq >>
  qpat_x_assum `same_blocks sa sb` mp_tac >>
  rewrite_tac[same_blocks_def] >> strip_tac >>
  simp[mk_inst_def, is_terminator_def] >> rpt strip_tac >>
  `eval_operand src s = SOME a /\ eval_operand dst s = SOME b` by
    metis_tac[code_copy_content_operand] >>
  `!x. src = Var x \/ dst = Var x ==> ~MEM x [cv;smv;sv;vv;mv;dv;nv]` by
    (fs[] >> metis_tac[]) >>
  drule_all code_copy_content_body_run >>
  disch_then (qspec_then `sa.cs_next_id` strip_assume_tac) >>
  disj1_tac >> qexists_tac `t` >>
  gvs[GSYM mk_inst_def, code_copy_inv_control, eval_operand_def, lookup_var_def]
QED

Theorem code_copy_content_init_frag:
  !ctx sa sb cv ds a b n sbase R.
    same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    emitted_insts sa sb = [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]] /\
    MEM cv ds ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. eval_operand (Var cv) s = SOME 0w /\
        code_copy_inv ds a b n sbase 0 s) R
Proof
  rpt strip_tac >> irule frag_exec_run_inst_seq >>
  fs[same_blocks_def] >> simp[mk_inst_def, is_terminator_def] >>
  rpt strip_tac >> gvs[] >> disj1_tac >>
  qexists_tac `update_var cv 0w sbase` >>
  simp[run_inst_seq_def, step_inst_base_def, eval_operand_def,
       lookup_var_update_var, code_copy_inv_control] >>
  conj_tac >- simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  irule code_copy_inv_register >> simp[code_copy_inv_initial]
QED

Theorem compile_code_copy_boundaries[local]:
  !src dst n sa u sb.
    compile_word_copy_loop src dst n LocCode LocMemory F sa = (u,sb) ==>
    ?hdr body exit cv test sm so value scaled dest next old0 oldh
     s1 s2 s3 s4 s0 sj sth stj st2 stb ss s5 s6 s7 s8 s9 s10 ste st3.
      fresh_label "wcopy_cond" sa = (hdr,s1) /\
      fresh_label "wcopy_body" s1 = (body,s2) /\
      fresh_label "wcopy_exit" s2 = (exit,s3) /\
      fresh_var s3 = (cv,s4) /\
      emit_inst ASSIGN [Lit 0w] [cv] s4 = ((),s0) /\
      emit_inst JMP [Label hdr] [] s0 = ((),sj) /\
      new_block hdr sj = (old0,sth) /\
      emit_op EQ [Var cv; Lit (n2w n)] sth = (test,stj) /\
      emit_inst JNZ [test; Label exit; Label body] [] stj = ((),st2) /\
      new_block body st2 = (oldh,stb) /\
      emit_op MUL [Var cv; Lit 32w] stb = (sm,ss) /\
      emit_op ADD [src; sm] ss = (so,s5) /\
      compile_ptr_load F NONE LocCode so s5 = (value,s6) /\
      emit_op MUL [Var cv; Lit 32w] s6 = (scaled,s7) /\
      emit_op ADD [dst; scaled] s7 = (dest,s8) /\
      emit_void MSTORE [dest; value] s8 = ((),s9) /\
      emit_op ADD [Var cv; Lit 1w] s9 = (next,s10) /\
      emit_inst ASSIGN [next] [cv] s10 = ((),ste) /\
      emit_inst JMP [Label hdr] [] ste = ((),st3) /\
      new_block exit st3 = (u,sb)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_word_copy_loop_def, compileEnvTheory.word_scale_def,
      compile_ptr_store_def, comp_ignore_bind_def,
      comp_bind_assoc, storage_copy_bind_eq]
QED

Theorem code_copy_body_layout[local]:
  !src dst cv sm so value scaled dest next stb ss s1 s2 s3 s4 s5 s6 ste.
    emit_op MUL [Var cv; Lit 32w] stb = (sm,ss) /\
    emit_op ADD [src; sm] ss = (so,s1) /\
    compile_ptr_load F NONE LocCode so s1 = (value,s2) /\
    emit_op MUL [Var cv; Lit 32w] s2 = (scaled,s3) /\
    emit_op ADD [dst; scaled] s3 = (dest,s4) /\
    emit_void MSTORE [dest; value] s4 = ((),s5) /\
    emit_op ADD [Var cv; Lit 1w] s5 = (next,s6) /\
    emit_inst ASSIGN [next] [cv] s6 = ((),ste) ==>
    ?smv sv vv mv dv nv.
      sm = Var smv /\ so = Var sv /\ value = Var vv /\ scaled = Var mv /\
      dest = Var dv /\ next = Var nv /\
      ALL_DISTINCT [smv;sv;vv;mv;dv;nv] /\
      (!x. not_fresh_at stb x ==> ~MEM x [smv;sv;vv;mv;dv;nv]) /\
      same_blocks stb ste /\
      isPREFIX stb.cs_current_insts ste.cs_current_insts /\
      ste.cs_next_var = stb.cs_next_var + 6 /\
      emitted_insts stb ste =
       [mk_inst stb.cs_next_id MUL [Var cv; Lit 32w] [smv];
        mk_inst (stb.cs_next_id+1) ADD [src; Var smv] [sv];
        mk_inst (stb.cs_next_id+2) DLOAD [Var sv] [vv];
        mk_inst (stb.cs_next_id+3) MUL [Var cv; Lit 32w] [mv];
        mk_inst (stb.cs_next_id+4) ADD [dst; Var mv] [dv];
        mk_inst (stb.cs_next_id+5) MSTORE [Var dv; Var vv] [];
        mk_inst (stb.cs_next_id+6) ADD [Var cv; Lit 1w] [nv];
        mk_inst (stb.cs_next_id+7) ASSIGN [Var nv] [cv]]
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_ptr_load_def, compile_imm_load_word_def,
      emit_op_def, emit_void_def, emit_inst_def,
      comp_ignore_bind_def, comp_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  simp[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND,
       DROP_LENGTH_APPEND, GSYM APPEND_ASSOC, fresh_var_distinct] >>
  rw[not_fresh_at_def] >> first_x_assum irule >> simp[]
QED

Theorem compile_code_copy_certificate:
  !src dst n sa u sb.
    compile_word_copy_loop src dst n LocCode LocMemory F sa = (u,sb) ==>
    ?s0 sj sth stj st2 stb ste st3 hdr loop_body exit cv tv smv sv vv mv dv nv old0 oldh.
      emit_inst JMP [Label hdr] [] s0 = ((),sj) /\
      new_block hdr sj = (old0,sth) /\
      emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj) /\
      emit_inst JNZ [Var tv; Label exit; Label loop_body] [] stj = ((),st2) /\
      new_block loop_body st2 = (oldh,stb) /\
      emit_inst JMP [Label hdr] [] ste = ((),st3) /\
      new_block exit st3 = (u,sb) /\
      same_blocks sa s0 /\ isPREFIX sa.cs_current_insts s0.cs_current_insts /\
      emitted_insts sa s0 = [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]] /\
      same_blocks sth stj /\ isPREFIX sth.cs_current_insts stj.cs_current_insts /\
      emitted_insts sth stj = [mk_inst sth.cs_next_id EQ [Var cv; Lit (n2w n)] [tv]] /\
      same_blocks stb ste /\ isPREFIX stb.cs_current_insts ste.cs_current_insts /\
      emitted_insts stb ste =
       [mk_inst stb.cs_next_id MUL [Var cv; Lit 32w] [smv];
        mk_inst (stb.cs_next_id+1) ADD [src; Var smv] [sv];
        mk_inst (stb.cs_next_id+2) DLOAD [Var sv] [vv];
        mk_inst (stb.cs_next_id+3) MUL [Var cv; Lit 32w] [mv];
        mk_inst (stb.cs_next_id+4) ADD [dst; Var mv] [dv];
        mk_inst (stb.cs_next_id+5) MSTORE [Var dv; Var vv] [];
        mk_inst (stb.cs_next_id+6) ADD [Var cv; Lit 1w] [nv];
        mk_inst (stb.cs_next_id+7) ASSIGN [Var nv] [cv]] /\
      cs_extends sa s0 /\ cs_extends s0 sb /\
      cs_extends sth stj /\ cs_extends stb ste /\
      ALL_DISTINCT [cv;tv;smv;sv;vv;mv;dv;nv] /\
      (!x. not_fresh_at sa x ==> ~MEM x [cv;tv;smv;sv;vv;mv;dv;nv])
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_code_copy_boundaries >> strip_tac >>
  drule storage_copy_header_layout >> strip_tac >> gnvs[] >>
  drule_all storage_copy_init_layout >> strip_tac >>
  drule_all storage_copy_prefix_freshness >> strip_tac >>
  rename1 `emit_inst ASSIGN [Lit 0w] [cv] s4 = ((),s0)` >>
  rename1 `emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj)` >>
  rename1 `emit_inst JNZ [Var tv; Label exit; Label loop_body] [] stj = ((),st2)` >>
  rename1 `new_block loop_body st2 = (oldh,stb)` >>
  drule_all code_copy_body_layout >> strip_tac >> gnvs[] >>
  rename1 `emit_inst ASSIGN [Var nv] [cv] s10 = ((),ste)` >>
  rename1 `emit_inst JMP [Label hdr] [] ste = ((),st3)` >>
  `cs_extends sa s0 /\ cs_extends sth stj /\ cs_extends stb ste` by
    (rpt conj_tac >> irule cs_extends_same_block >> gvs[same_blocks_def]) >>
  `cs_extends s0 sb` by
    (imp_res_tac cs_extends_emit_inst >> imp_res_tac cs_extends_new_block >>
     metis_tac[cs_extends_trans]) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`compile_word_copy_loop _ _ _ _ _ _ _ = _`, `fresh_var _ = _`,
     `emit_inst ASSIGN [Lit _] _ _ = _`, `compile_ptr_load _ _ _ _ _ = _`,
     `emit_void _ _ _ = _`, `emit_inst ASSIGN _ _ _ = _`] >>
  rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op ADD _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op MUL _ _ = _` kall_tac) >>
  goal_assum (drule_at (Pat `emitted_insts _ _ = [mk_inst _ ASSIGN _ _]`)) >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >>
  rpt (goal_assum (drule_at (Pat `new_block _ _ = _`))) >>
  goal_assum (drule_at (Pat `emitted_insts _ _ = [_;_;_;_;_;_;_;_]`)) >>
  simp[ALL_DISTINCT] >> metis_tac[]
QED

Theorem compile_code_copy_content_frag:
  !ctx src dst n sa u sb sbase a b R.
    compile_word_copy_loop src dst n LocCode LocMemory F sa = (u,sb) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b /\
    n < dimword (:256) /\ w2n b+32*n < dimword (:256) /\
    w2n a+32*n < dimword (:256) ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. mem_bytes_at (w2n b) (32*n) s.vs_memory =
             mem_bytes_at (w2n a) (32*n) sbase.vs_data_section /\
        (!off len. off+len <= w2n b \/ w2n b+32*n <= off ==>
          mem_bytes_at off len s.vs_memory = mem_bytes_at off len sbase.vs_memory) /\
        (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
        s with <|vs_memory := sbase.vs_memory; vs_vars := sbase.vs_vars;
          vs_prev_bb := sbase.vs_prev_bb; vs_current_bb := sbase.vs_current_bb;
          vs_inst_idx := sbase.vs_inst_idx|> = sbase) R
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_code_copy_certificate >> strip_tac >>
  rename1 `emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj)` >>
  rename1 `emitted_insts sa s0 = [mk_inst _ ASSIGN _ _]` >>
  rename1 `emitted_insts stb ste = [mk_inst _ MUL _ [smv]; _; _; _; _; _; _; _]` >>
  qmatch_asmsub_abbrev_tac `ALL_DISTINCT ds` >>
  irule frag_exec_seq >>
  qexistsl_tac [`\s. eval_operand (Var cv) s = SOME 0w /\
    code_copy_inv ds a b n sbase 0 s`, `s0`] >> simp[] >>
  conj_tac >- (irule code_copy_content_init_frag >> simp[Abbr `ds`]) >>
  irule frag_exec_conseq >> irule_at Any copy_counted_loop >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >>
  rpt (goal_assum (drule_at (Pat `new_block _ _ = _`))) >>
  rpt (goal_assum (drule_at Any)) >>
  qexistsl_tac [`R`, `code_copy_inv ds a b n sbase`] >>
  simp[code_copy_inv_control] >>
  conj_tac >- gvs[Abbr `ds`, listTheory.ALL_DISTINCT] >>
  conj_tac
  >- (rpt strip_tac >> irule code_copy_inv_register >> simp[Abbr `ds`]) >>
  conj_tac
  >- (rpt strip_tac >> irule code_copy_content_body_frag >>
      ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >- (goal_assum (drule_at (Pat `emitted_insts _ _ = [_;_;_;_;_;_;_;_]`)) >>
      simp[Abbr `ds`] >> gvs[listTheory.ALL_DISTINCT] >> metis_tac[]) >> simp[]) >>
  rw[code_copy_inv_def]
  >- (irule copied_code_words_bytes >> fs[]) >> metis_tac[]
QED

Theorem compile_code_to_memory_content_frag:
  !ctx src dst n sa u sb sbase a b R.
    compile_code_to_memory src dst n sa = (u,sb) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b /\
    n < dimword (:256) /\ w2n a+32*n < dimword (:256) /\
    w2n b+32*n < dimword (:256) ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. mem_bytes_at (w2n b) (32*n) s.vs_memory =
             mem_bytes_at (w2n a) (32*n) sbase.vs_data_section /\
        (!off len. off+len <= w2n b \/ w2n b+32*n <= off ==>
          mem_bytes_at off len s.vs_memory = mem_bytes_at off len sbase.vs_memory) /\
        (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
        s with <|vs_memory := sbase.vs_memory; vs_vars := sbase.vs_vars;
          vs_prev_bb := sbase.vs_prev_bb; vs_current_bb := sbase.vs_current_bb;
          vs_inst_idx := sbase.vs_inst_idx|> = sbase) R
Proof
  rpt gen_tac >> strip_tac >> Cases_on `n = 0`
  >- (gvs[compile_code_to_memory_def, comp_return_def] >>
      irule frag_exec_refl >> simp[mem_bytes_at_def]) >>
  gvs[compile_code_to_memory_def, comp_ignore_bind_def, storage_copy_bind_eq,
      comp_return_def] >>
  `n < dimword (:256)` by decide_tac >>
  drule compile_code_copy_content_frag >>
  disch_then (qspecl_then [`ctx`, `sbase`, `a`, `b`, `R`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem compile_code_to_memory_subvalue_frag:
  !ctx src dst tv v itv iv off k sa u sb sbase b R.
    compile_code_to_memory src dst ((type_memory_size tv+31) DIV 32) sa = (u,sb) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME (n2w (off+k)) /\
    eval_operand dst sbase = SOME b /\
    val_in_memory itv iv off sbase.vs_data_section /\
    sub_layout itv iv k tv v /\ value_has_type tv v /\
    off+type_memory_size itv < dimword (:256) /\
    w2n b+type_memory_size tv < dimword (:256) ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. val_in_memory tv v (w2n b) s.vs_memory /\
        (!off' len. off'+len <= w2n b \/ w2n b+type_memory_size tv <= off' ==>
          mem_bytes_at off' len s.vs_memory = mem_bytes_at off' len sbase.vs_memory) /\
        (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
        s with <|vs_memory := sbase.vs_memory; vs_vars := sbase.vs_vars;
          vs_prev_bb := sbase.vs_prev_bb; vs_current_bb := sbase.vs_current_bb;
          vs_inst_idx := sbase.vs_inst_idx|> = sbase) R
Proof
  rpt gen_tac >> strip_tac >>
  `k+type_memory_size tv <= type_memory_size itv /\
    val_in_memory tv v (off+k) sbase.vs_data_section` by
    (fs[sub_layout_def] >> metis_tac[]) >>
  `off+k < dimword (:256) /\ off+k+type_memory_size tv < dimword (:256)` by
    decide_tac >>
  `w2n (n2w (off+k):bytes32) = off+k` by simp[wordsTheory.w2n_n2w] >>
  `32*((type_memory_size tv+31) DIV 32) = type_memory_size tv` by
    simp[slot_count_of_memory_size, storageDecodeMemoryTheory.type_memory_size_slots] >>
  `((type_memory_size tv+31) DIV 32) < dimword (:256)` by decide_tac >>
  `val_wf tv v` by metis_tac[value_has_type_val_wf] >>
  `w2n (n2w (off+k):bytes32) + 32*((type_memory_size tv+31) DIV 32) < dimword (:256) /\
    w2n b + 32*((type_memory_size tv+31) DIV 32) < dimword (:256)` by simp[] >>
  drule_all compile_code_to_memory_content_frag >>
  disch_then (qspecl_then [`ctx`, `R`] mp_tac) >>
  disch_then (fn th => irule frag_exec_conseq >> irule_at Any th) >>
  simp[] >> rpt strip_tac >> simp[] >>
  irule valueEncodingPropsTheory.val_in_memory_relocate >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  qexists_tac `type_memory_size tv` >> simp[]
QED

(* The literal-offset helper used by the unrolled immutable copy.  This
   boundary does not require fresh_vars_wrt: replay may overwrite temporaries. *)
Theorem compile_lit_byte_offset_run:
  !src off sa op sb s a.
    compile_lit_byte_offset src off sa = (op,sb) /\
    eval_operand src s = SOME a ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (a+n2w off) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t with vs_vars := s.vs_vars = s
Proof
  rpt gen_tac >> strip_tac >> Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def,
          emitted_insts_def, run_inst_seq_def, wordsTheory.WORD_ADD_0]) >>
  Cases_on `src` >>
  gvs[compile_lit_byte_offset_def, comp_return_def, eval_operand_def]
  >- (qexists_tac `s` >> simp[emitted_insts_def, run_inst_seq_def]) >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qexists_tac `update_var (STRING #"%" (toString sa.cs_next_var)) (a+n2w off) s` >>
  qmatch_asmsub_abbrev_tac `emit_op ADD operands` >>
  `step_inst_base (mk_inst sa.cs_next_id ADD operands
      [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) (a+n2w off) s)` by
    (simp[Abbr `operands`] >> irule step_ADD >> simp[eval_operand_def]) >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var] >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       not_fresh_at_def] >> metis_tac[]
QED

Theorem compile_lit_byte_offset_layout:
  !src off sa op sb.
    compile_lit_byte_offset src off sa = (op,sb) ==>
    same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    sa.cs_next_var <= sb.cs_next_var /\
    ((!x. src = Var x ==> not_fresh_at sa x) ==>
     (!x. op = Var x ==> not_fresh_at sb x))
Proof
  rpt gen_tac >> Cases_on `off = 0`
  >- simp[compile_lit_byte_offset_def, comp_return_def, same_blocks_def] >>
  Cases_on `src` >>
  simp[compile_lit_byte_offset_def, comp_return_def, same_blocks_def] >>
  rw[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
     fresh_var_def, fresh_id_def, emit_def, same_blocks_def,
     not_fresh_at_def, fresh_var_distinct] >> gvs[]
QED

Theorem compile_lit_byte_offset_frag:
  !ctx src off sa op sb sbase a R.
    compile_lit_byte_offset src off sa = (op,sb) /\
    eval_operand src sbase = SOME a ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. eval_operand op s = SOME (a+n2w off) /\
        (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
        s with <|vs_vars := sbase.vs_vars;
          vs_prev_bb := sbase.vs_prev_bb; vs_current_bb := sbase.vs_current_bb;
          vs_inst_idx := sbase.vs_inst_idx|> = sbase) R
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_lit_byte_offset_run >> strip_tac >>
  Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def] >>
      irule frag_exec_refl >> simp[wordsTheory.WORD_ADD_0]) >>
  Cases_on `src` >> gvs[compile_lit_byte_offset_def, comp_return_def]
  >- (irule frag_exec_refl >> gvs[eval_operand_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  gvs[same_blocks_def] >> simp[mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  gvs[GSYM mk_inst_def, eval_operand_def, lookup_var_def,
      venom_state_component_equality]
QED

Theorem compile_runtime_imm_load_run:
  !imm src sa op sb s a.
    compile_imm_load_word F imm src sa = (op,sb) /\
    eval_operand src s = SOME a ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (mem_word_at (w2n a) s.vs_data_section) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t with vs_vars := s.vs_vars = s
Proof
  rpt gen_tac >> simp[compile_imm_load_word_def] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qexists_tac `update_var (STRING #"%" (toString sa.cs_next_var))
    (mem_word_at (w2n a) s.vs_data_section) s` >>
  drule code_copy_load_exact >>
  disch_then (qspecl_then [`sa.cs_next_id`,
    `STRING #"%" (toString sa.cs_next_var)`] assume_tac) >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var] >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       not_fresh_at_def] >> metis_tac[]
QED

Theorem compile_runtime_imm_load_frag:
  !ctx imm src sa op sb sbase a R.
    compile_imm_load_word F imm src sa = (op,sb) /\
    eval_operand src sbase = SOME a ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. eval_operand op s = SOME (mem_word_at (w2n a) sbase.vs_data_section) /\
        (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
        s with <|vs_vars := sbase.vs_vars;
          vs_prev_bb := sbase.vs_prev_bb; vs_current_bb := sbase.vs_current_bb;
          vs_inst_idx := sbase.vs_inst_idx|> = sbase) R
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_runtime_imm_load_run >> strip_tac >>
  gvs[compile_imm_load_word_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  gvs[same_blocks_def] >> simp[mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  gvs[GSYM mk_inst_def, eval_operand_def, lookup_var_def,
      venom_state_component_equality]
QED

Theorem compile_storage_singleton_content_frag:
  !ctx opc src dst sa u sb sbase a b R.
    (opc = SLOAD \/ opc = TLOAD) /\
    do value <- emit_op opc [src]; emit_void MSTORE [dst; value] od sa = (u,sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. mem_bytes_at (w2n b) 32 s.vs_memory =
          word_to_bytes (if opc = SLOAD then sload a sbase else tload a sbase) T /\
        (!off len. off+len <= w2n b \/ w2n b+32 <= off ==>
          mem_bytes_at off len s.vs_memory = mem_bytes_at off len sbase.vs_memory) /\
        (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
        s with <|vs_memory := sbase.vs_memory; vs_vars := sbase.vs_vars;
          vs_prev_bb := sbase.vs_prev_bb; vs_current_bb := sbase.vs_current_bb;
          vs_inst_idx := sbase.vs_inst_idx|> = sbase) R
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule storage_copy_word_layout >> strip_tac >>
  `!x. dst = Var x ==> x <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[] >>
  qspecl_then [`opc`, `src`, `dst`] mp_tac copy_slot_content_frame >>
  disch_then drule_all >>
  disch_then (qspec_then `sa.cs_next_id` strip_assume_tac) >>
  `mem_bytes_at (w2n b) 32 t.vs_memory =
    word_to_bytes (if opc = SLOAD then sload a sbase else tload a sbase) T` by
    (qpat_x_assum `mem_word_at _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[mem_word_at_def, GSYM mem_bytes_at_def] >> sym_tac >>
     irule venomMemProofsTheory.word_bytes_roundtrip_proof >>
     simp[dividesTheory.divides_def]) >>
  irule frag_exec_run_inst_seq >>
  gvs[same_blocks_def] >> simp[mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  gvs[GSYM mk_inst_def, eval_operand_def, lookup_var_def,
      venom_state_component_equality] >> metis_tac[]
QED
