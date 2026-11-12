(* Shared counted indexed-copy execution. *)
Theory typedCopyIndexedLoopPathPtr
Ancestors typedCopyLoopControlFramePathPtr typedCopyLoopIterationPathPtr
  typedCopyTuplePathPtr

(* The common child/control record frame composes without opening either
   endpoint's execution witness. *)
Theorem typed_copy_ambient_frame_trans:
 !s t u.
 (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
   vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
   vs_inst_idx := s.vs_inst_idx|>) = s /\
 (u with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
   vs_prev_bb := t.vs_prev_bb; vs_current_bb := t.vs_current_bb;
   vs_inst_idx := t.vs_inst_idx|>) = t ==>
 (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
   vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
   vs_inst_idx := s.vs_inst_idx|>) = s
Proof
 simp[venomStateTheory.venom_state_component_equality]
QED

Theorem typed_copy_indexed_loop_path_ptr_conditional:
 !D ctx fn PG ce tenv dty sty.
 (!N i S B stv dtv V tn tn' mem mem'.
   i < N /\
   (S + N * type_memory_size stv <= B \/ B + N * type_memory_size dtv <= S) /\
   (!j. j < N ==> val_wf stv (V j) /\ val_wf dtv (V j)) /\
   (!x. ~(B + i * type_memory_size dtv <= x /\
           x < B + (i+1) * type_memory_size dtv) ==>
     mem_bytes_at x 1 mem' = mem_bytes_at x 1 mem /\ (x IN tn' <=> x IN tn)) /\
   (!j. j < N ==> !m. mem_agree_outside tn mem m ==>
     val_in_memory stv (V j) (S + j * type_memory_size stv) m) /\
   (!j. j < i ==> !m. mem_agree_outside tn mem m ==>
     val_in_memory dtv (V j) (B + j * type_memory_size dtv) m) /\
   (!m. mem_agree_outside tn' mem' m ==>
     val_in_memory dtv (V i) (B + i * type_memory_size dtv) m) ==>
   (!j. j < N ==> !m. mem_agree_outside tn' mem' m ==>
     val_in_memory stv (V j) (S + j * type_memory_size stv) m) /\
   (!j. j < i+1 ==> !m. mem_agree_outside tn' mem' m ==>
     val_in_memory dtv (V j) (B + j * type_memory_size dtv) m)) ==>
 (!cd cs sa sb Gh th sh aw bw dtv stv v.
   acyclic_struct_metadata ce.ce_struct_fields /\
   sfields_tenv_consistent ce.ce_struct_fields tenv /\
   (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
   type_widens_to tenv sty dty /\ evaluate_type tenv sty = SOME stv /\
   evaluate_type tenv dty = SOME dtv /\
   value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
   compile_store_memory_typed ce (Var cd) dty (Var cs) sty sa = ((),sb) /\
   not_fresh_at sa cd /\ not_fresh_at sa cs /\
   lookup_var cs sh = SOME aw /\ lookup_var cd sh = SOME bw /\
   ptr_covers Gh th cs sh (type_memory_bytes ce sty) /\
   ptr_covers Gh th cd sh (type_memory_bytes ce dty) /\
   w2n aw + type_memory_bytes ce sty < dimword(:256) /\
   w2n bw + type_memory_bytes ce dty < dimword(:256) /\
   (w2n aw + type_memory_bytes ce sty <= w2n bw \/
    w2n bw + type_memory_bytes ce dty <= w2n aw) /\
   fn_has_code sa sb fn /\ sh.vs_current_bb = sa.cs_current_bb /\
   sh.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~sh.vs_halted /\
   ~ctx_has_dalloca ctx /\
   (!m. mem_agree_outside th.t_mem sh.vs_memory m ==>
     val_in_memory stv v (w2n aw) m) ==>
   ?Gf tnf sf.
   gas_path_ptr D 0 ctx fn PG Gh th sh 0 Gf tnf (OK sf) /\
   sf.vs_current_bb = sb.cs_current_bb /\
   sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
   (sf with <|vs_vars := sh.vs_vars; vs_memory := sh.vs_memory;
    vs_prev_bb := sh.vs_prev_bb; vs_current_bb := sh.vs_current_bb;
    vs_inst_idx := sh.vs_inst_idx|>) = sh /\
   tnf.t_stor = th.t_stor /\ tnf.t_trans = th.t_trans /\ tnf.t_imm = th.t_imm /\
   (!p. not_fresh_at sa p ==>
    lookup_var p sf = lookup_var p sh /\ FLOOKUP Gf p = FLOOKUP Gh p /\
    op_taint tnf (Var p) = op_taint th (Var p)) /\
   (!i. ~(w2n bw <= i /\ i < w2n bw + type_memory_bytes ce dty) ==>
    mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 sh.vs_memory /\
    (i IN tnf.t_mem <=> i IN th.t_mem)) /\
   (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
    val_in_memory dtv v (w2n bw) m)) ==>
 !sa si se G tn s src dst a b N sc dc ss ds stv dtv V len
  ctr lt done so doff sp dp tmp cond body exit
  init_bb head_bb addr_bb back_bb init_pre addr_post
  init_id head_id addr_id back_id.
 acyclic_struct_metadata ce.ce_struct_fields /\
 sfields_tenv_consistent ce.ce_struct_fields tenv /\
 (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
   ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
     sz = type_memory_size tv) fields) /\
 type_widens_to tenv sty dty /\ evaluate_type tenv sty = SOME stv /\
 evaluate_type tenv dty = SOME dtv /\
 ss = type_memory_bytes ce sty /\ ds = type_memory_bytes ce dty /\
 ss = type_memory_size stv /\ ds = type_memory_size dtv /\
 (!j. j < N ==> value_has_type stv (V j) /\ value_has_type dtv (V j) /\
   val_wf stv (V j) /\ val_wf dtv (V j)) /\
 compile_store_memory_typed ce (Var dp) dty (Var sp) sty si = ((),se) /\
 fn_has_code si se fn /\
 si.cs_current_bb = body /\ LENGTH si.cs_current_insts = 4 /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME init_bb /\
 init_bb.bb_instructions = init_pre ++
   [mk_inst init_id ASSIGN [Lit 0w] [ctr];
    mk_inst (init_id+1) JMP [Label cond] []] /\
 lookup_block cond fn.fn_blocks = SOME head_bb /\
 head_bb.bb_instructions =
   [mk_inst head_id LT [Var ctr;len] [lt];
    mk_inst (head_id+1) ISZERO [Var lt] [done];
    mk_inst (head_id+2) JNZ [Var done;Label exit;Label body] []] /\
 lookup_block body fn.fn_blocks = SOME addr_bb /\
 addr_bb.bb_instructions =
   [mk_inst addr_id MUL [Var ctr;Lit (n2w ss)] [so];
    mk_inst (addr_id+1) MUL [Var ctr;Lit (n2w ds)] [doff];
    mk_inst (addr_id+2) ADD [Var src;Var so] [sp];
    mk_inst (addr_id+3) ADD [Var dst;Var doff] [dp]] ++ addr_post /\
 lookup_block se.cs_current_bb fn.fn_blocks = SOME back_bb /\
 back_bb.bb_instructions = se.cs_current_insts ++
   [mk_inst back_id ADD [Var ctr;Lit 1w] [tmp];
    mk_inst (back_id+1) ASSIGN [Var tmp] [ctr];
    mk_inst (back_id+2) JMP [Label cond] []] /\
 ALL_DISTINCT [ctr;lt;done;so;doff;sp;dp;tmp] /\
 (!p. not_fresh_at sa p ==>
   ~MEM p [ctr;lt;done;so;doff;sp;dp;tmp] /\ not_fresh_at si p) /\
 not_fresh_at sa src /\ not_fresh_at sa dst /\
 not_fresh_at si ctr /\ not_fresh_at si sp /\ not_fresh_at si dp /\
 (!p. len = Var p ==> not_fresh_at sa p) /\
 eval_operand len s = SOME (n2w N) /\ op_taint tn len = {} /\ op_prov G len = NONE /\
 N < dimword(:256) /\ N <= sc /\ N <= dc /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 ptr_covers G tn src s (sc*ss) /\ ptr_covers G tn dst s (dc*ds) /\
 w2n a + sc*ss < dimword(:256) /\ w2n b + dc*ds < dimword(:256) /\
 (w2n a + sc*ss <= w2n b \/ w2n b + dc*ds <= w2n a) /\
 s.vs_inst_idx = LENGTH init_pre /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 (!j. j < N ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
   val_in_memory stv (V j) (w2n a+j*ss) m) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = exit /\ sf.vs_inst_idx = 0 /\ ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
   vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
   vs_inst_idx := s.vs_inst_idx|>) = s /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==>
   lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
   op_taint tnf (Var p) = op_taint tn (Var p)) /\
 (!x. ~(w2n b <= x /\ x < w2n b+dc*ds) ==>
   mem_bytes_at x 1 sf.vs_memory = mem_bytes_at x 1 s.vs_memory /\
   (x IN tnf.t_mem <=> x IN tn.t_mem)) /\
 (!j. j < N ==> !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
   val_in_memory dtv (V j) (w2n b+j*ds) m)
Proof
 ntac 8 gen_tac >> disch_then (mk_asm "indexed") >>
 disch_then (mk_asm "child") >> rpt gen_tac >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all typed_copy_loop_init_path_ptr_framed >>
 disch_then (qspecl_then [`D`, `PG`, `G`, `tn`] strip_assume_tac) >>
 qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 G0 tn0 (OK s0)` >>
 qabbrev_tac `Post = \gf tf u.
   u.vs_current_bb = exit /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
   (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
     vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
     vs_inst_idx := s.vs_inst_idx|>) = s /\
   tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
   (!p. not_fresh_at sa p ==>
     lookup_var p u = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
     op_taint tf (Var p) = op_taint tn (Var p)) /\
   (!x. ~(w2n b <= x /\ x < w2n b+dc*ds) ==>
     mem_bytes_at x 1 u.vs_memory = mem_bytes_at x 1 s.vs_memory /\
     (x IN tf.t_mem <=> x IN tn.t_mem)) /\
   (!j. j < N ==> !m. mem_agree_outside tf.t_mem u.vs_memory m ==>
     val_in_memory dtv (V j) (w2n b+j*ds) m)` >>
 qsuff_tac `?Gf tnf sf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\ Post Gf tnf sf`
 >- simp[Abbr `Post`] >>
 qabbrev_tac `Inv = \i Gi ti u.
   i <= N /\ u.vs_current_bb = cond /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
   lookup_var ctr u = SOME (n2w i) /\ FLOOKUP Gi ctr = NONE /\
   op_taint ti (Var ctr) = {} /\
   eval_operand len u = SOME (n2w N) /\ op_taint ti len = {} /\ op_prov Gi len = NONE /\
   lookup_var src u = SOME a /\ lookup_var dst u = SOME b /\
   ptr_covers Gi ti src u (sc*ss) /\ ptr_covers Gi ti dst u (dc*ds) /\
   (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
     vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
     vs_inst_idx := s.vs_inst_idx|>) = s /\
   ti.t_stor = tn.t_stor /\ ti.t_trans = tn.t_trans /\ ti.t_imm = tn.t_imm /\
   (!p. not_fresh_at sa p ==>
     lookup_var p u = lookup_var p s /\ FLOOKUP Gi p = FLOOKUP G p /\
     op_taint ti (Var p) = op_taint tn (Var p)) /\
   (!x. ~(w2n b <= x /\ x < w2n b+dc*ds) ==>
     mem_bytes_at x 1 u.vs_memory = mem_bytes_at x 1 s.vs_memory /\
     (x IN ti.t_mem <=> x IN tn.t_mem)) /\
   (!j. j < N ==> !m. mem_agree_outside ti.t_mem u.vs_memory m ==>
     val_in_memory stv (V j) (w2n a+j*ss) m) /\
   (!j. j < i ==> !m. mem_agree_outside ti.t_mem u.vs_memory m ==>
     val_in_memory dtv (V j) (w2n b+j*ds) m)` >>
 `!i Gi ti u. i <= N /\ Inv i Gi ti u ==>
   ?Gf tnf sf. gas_path_ptr D 0 ctx fn PG Gi ti u 0 Gf tnf (OK sf) /\ Post Gf tnf sf`
   by suspend "iteration" >>
 `Inv 0 G0 tn0 s0` by suspend "initial" >>
 first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
 disch_then drule >> strip_tac >>
 qexistsl_tac [`Gf`, `tnf`, `sf`] >> conj_tac
 >- (irule (fragGasPathPtrTheory.gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`G0`, `s0`, `tn0`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
 first_assum ACCEPT_TAC
QED

Resume typed_copy_indexed_loop_path_ptr_conditional[iteration]:
 ho_match_mp_tac gas_path_ptr_bounded_iteration >>
 conj_tac >- suspend "step" >>
 suspend "exit"
QED

Resume typed_copy_indexed_loop_path_ptr_conditional[initial]:
 asm_x "indexed" kall_tac >> asm_x "child" kall_tac >>
 qpat_x_assum `!i Gi ti u. _` kall_tac >>
 qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
 qpat_x_assum `_ with <|vs_vars := _; vs_memory := _; vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = _` kall_tac >>
 qpat_x_assum `Abbrev (Post = _)` kall_tac >>
 `!p. not_fresh_at sa p ==> p <> ctr` by metis_tac[listTheory.MEM] >>
 `src <> ctr /\ dst <> ctr` by metis_tac[] >>
 `!p. len = Var p ==> p <> ctr` by metis_tac[] >>
 Cases_on `len` >>
 simp[Abbr `Inv`, Abbr `G0`, Abbr `tn0`, Abbr `s0`,
   venomStateTheory.jump_to_def, venomStateTheory.update_var_def,
   venomStateTheory.lookup_var_def, ptrDisciplineTheory.op_taint_def,
   ptrDisciplineTheory.op_prov_def, finite_mapTheory.FLOOKUP_DRESTRICT,
   finite_mapTheory.FLOOKUP_UPDATE, venomStateTheory.eval_operand_def,
   bodyPtrDefsTheory.ptr_covers_def, venomStateTheory.venom_state_component_equality] >>
 gvs[venomStateTheory.lookup_var_def, venomStateTheory.eval_operand_def,
   bodyPtrDefsTheory.ptr_covers_def, ptrDisciplineTheory.op_taint_def,
   ptrDisciplineTheory.op_prov_def]
QED

Resume typed_copy_indexed_loop_path_ptr_conditional[exit]:
 rpt gen_tac >> strip_tac >>
 asm_x "indexed" kall_tac >> asm_x "child" kall_tac >>
 qpat_x_assum `Inv _ _ _ _` mp_tac >>
 simp[Abbr `Inv`] >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 `op_prov Gi (Var ctr) = NONE` by simp[ptrDisciplineTheory.op_prov_def] >>
 `lookup_block u.vs_current_bb fn.fn_blocks = SOME head_bb` by simp[] >>
 `ctr <> lt /\ ctr <> done /\ N <= N` by fs[listTheory.ALL_DISTINCT] >>
 drule_all typed_copy_header_path_ptr_framed >>
 disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
 qexistsl_tac [`Gf`, `tnf`, `sf`] >>
 conj_tac >- first_assum ACCEPT_TAC >>
 qpat_x_assum `sf = _` kall_tac >>
 qpat_x_assum `Gf = _` kall_tac >>
 qpat_x_assum `tnf = _` kall_tac >>
 simp[Abbr `Post`] >>
 conj_tac >- (fs[venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
 conj_tac >- gvs[listTheory.MEM] >>
 first_assum ACCEPT_TAC
QED

Resume typed_copy_indexed_loop_path_ptr_conditional[step]:
 rpt gen_tac >> strip_tac >>
 qpat_x_assum `Inv _ _ _ _` mp_tac >>
 simp[Abbr `Inv`] >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 `op_prov Gi (Var ctr) = NONE` by simp[ptrDisciplineTheory.op_prov_def] >>
 `lookup_block u.vs_current_bb fn.fn_blocks = SOME head_bb` by simp[] >>
 `ctr <> lt /\ ctr <> done /\ i <= N` by fs[listTheory.ALL_DISTINCT] >>
 drule_all typed_copy_header_path_ptr_framed >>
 disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
 rename1 `gas_path_ptr D 0 ctx fn PG Gi ti u 0 Gh th (OK sh)` >>
 qpat_x_assum `sh = _` kall_tac >>
 qpat_x_assum `Gh = _` kall_tac >>
 qpat_x_assum `th = _` kall_tac >>
 `!p. not_fresh_at sa p ==> p <> lt /\ p <> done /\ ~MEM p [so;doff;sp;dp]` by metis_tac[listTheory.MEM] >>
 `lookup_var src sh = SOME a /\ lookup_var dst sh = SOME b` by metis_tac[] >>
 `ptr_covers Gh th src sh (sc*ss) /\ ptr_covers Gh th dst sh (dc*ds)` by
   metis_tac[annAssignPtrBytestringTheory.annassign_ptr_covers_frame_ptr] >>
 `sh.vs_current_bb = body'` by simp[] >>
 `lookup_block sh.vs_current_bb fn.fn_blocks = SOME addr_bb` by simp[] >>
 `ALL_DISTINCT [so;doff;sp;dp]` by fs[listTheory.ALL_DISTINCT] >>
 `!v. MEM v [so;doff;sp;dp] ==> ctr <> v /\ src <> v /\ dst <> v` by
   (asm_x "indexed" kall_tac >> asm_x "child" kall_tac >>
    `~MEM src [so;doff;sp;dp] /\ ~MEM dst [so;doff;sp;dp]` by metis_tac[] >>
    fs[listTheory.ALL_DISTINCT, listTheory.MEM] >> metis_tac[]) >>
 `i*ss+ss <= sc*ss /\ i*ds+ds <= dc*ds` by
   (qsuff_tac `(i+1)*ss <= sc*ss /\ (i+1)*ds <= dc*ds`
    >- (simp_tac bool_ss [arithmeticTheory.RIGHT_ADD_DISTRIB, arithmeticTheory.MULT_CLAUSES] >> simp[]) >>
    conj_tac >> irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
 `w2n a+i*ss < dimword(:256) /\ w2n b+i*ds < dimword(:256)` by decide_tac >>
 `op_taint th (Var ctr) = {}` by metis_tac[] >>
 `ss+i*ss <= sc*ss /\ ds+i*ds <= dc*ds` by decide_tac >>
 qpat_assum `ptr_covers Gh th src sh _`
   (mp_then Any mp_tac (typed_copy_loop_address_path_ptr_framed |> SPEC_ALL |>
     Q.INST [`pre` |-> `[]`] |> REWRITE_RULE [listTheory.APPEND, listTheory.LENGTH])) >>
 disch_then (fn thm => qpat_assum `ptr_covers Gh th dst sh _`
   (mp_then Any mp_tac thm)) >>
 qpat_x_assum `addr_bb.bb_instructions = _`
   (assume_tac o REWRITE_RULE [listTheory.APPEND]) >>
 disch_then drule_all >>
 disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
 rename1 `gas_path_ptr D 0 ctx fn PG Gh th sh 0 Ga ta (OK xa)` >>
 `w2n (n2w (w2n a+i*ss):256 word) = w2n a+i*ss /\
  w2n (n2w (w2n b+i*ds):256 word) = w2n b+i*ds` by simp[wordsTheory.w2n_n2w] >>
 `w2n a+i*ss+ss < dimword(:256) /\
  w2n b+i*ds+ds < dimword(:256)` by decide_tac >>
 Q.SUBGOAL_THEN `w2n a+i*ss+ss <= w2n b+i*ds \/ w2n b+i*ds+ds <= w2n a+i*ss` assume_tac
 >- decide_tac >>
 `value_has_type stv (V i) /\ value_has_type dtv (V i) /\
  val_wf stv (V i) /\ val_wf dtv (V i)` by simp[] >>
 `!m. mem_agree_outside ta.t_mem xa.vs_memory m ==>
  val_in_memory stv (V i) (w2n a+i*ss) m` by metis_tac[] >>
 `xa.vs_current_bb = si.cs_current_bb /\ xa.vs_inst_idx = LENGTH si.cs_current_insts` by simp[] >>
 asm "child" (fn thm => qpat_assum `compile_store_memory_typed _ _ _ _ _ si = _`
   (mp_then Any mp_tac thm)) >>
 disch_then (fn thm => qpat_assum `ss = type_memory_bytes ce sty` (fn eq =>
   qpat_assum `ptr_covers Ga ta sp xa _`
     (mp_then Any mp_tac (REWRITE_RULE [GSYM eq] thm)))) >>
 disch_then (fn thm => qpat_assum `value_has_type stv (V i)`
   (mp_then Any mp_tac thm)) >>
 disch_then (fn thm => qpat_assum `lookup_var sp xa = _` (mp_then Any mp_tac thm)) >>
 disch_then (fn thm => qpat_assum `lookup_var dp xa = _` (mp_then Any mp_tac thm)) >>
 disch_then (fn thm => qpat_assum `evaluate_type tenv dty = SOME dtv` (mp_then Any mp_tac thm)) >>
 impl_tac >- (
   asm_x "indexed" kall_tac >> asm_x "child" kall_tac >>
   qpat_assum `ds = type_memory_bytes ce dty` (fn eq => rewrite_tac [GSYM eq]) >>
   simp[] >>
   conj_tac >- first_assum ACCEPT_TAC >>
   qpat_assum `ss = type_memory_size stv` (fn eq => rewrite_tac [GSYM eq]) >>
   qpat_assum `ds = type_memory_size dtv` (fn eq => rewrite_tac [GSYM eq]) >>
   decide_tac) >>
 strip_tac >>
 rename1 `gas_path_ptr D 0 ctx fn PG Ga ta xa 0 Gc tc (OK xc)` >>
 qpat_assum `w2n (n2w (w2n b+i*ds):256 word) = _` (fn eq =>
   qpat_x_assum `!m. mem_agree_outside tc.t_mem xc.vs_memory m ==> _`
     (assume_tac o REWRITE_RULE [eq])) >>
 qpat_assum `ds = type_memory_size dtv` (fn eq =>
   qpat_x_assum `!m. mem_agree_outside tc.t_mem xc.vs_memory m ==> _`
     (assume_tac o REWRITE_RULE [eq])) >>
 asm "indexed" (qspecl_then [`N`, `i`, `w2n a`, `w2n b`] (fn thm =>
   qpat_assum `!m. mem_agree_outside tc.t_mem xc.vs_memory m ==> _`
     (mp_then Any mp_tac thm))) >>
 disch_then (fn thm => qpat_assum `!j. j < N ==> !m. mem_agree_outside ti.t_mem u.vs_memory m ==> val_in_memory stv (V j) _ m`
   (mp_then Any mp_tac thm)) >>
 impl_tac >- (
   asm_x "indexed" kall_tac >> asm_x "child" kall_tac >>
   conj_tac >- simp[] >>
   conj_tac >- (
     `N*ss <= sc*ss /\ N*ds <= dc*ds` by
       (conj_tac >> irule arithmeticTheory.LESS_MONO_MULT >> simp[]) >>
     qpat_assum `ss = type_memory_size stv` (fn eq => rewrite_tac [GSYM eq]) >>
     qpat_assum `ds = type_memory_size dtv` (fn eq => rewrite_tac [GSYM eq]) >>
     decide_tac) >>
   rpt strip_tac >>
   qpat_x_assum `!x. ~(_ /\ _) ==> mem_bytes_at _ _ xc.vs_memory = _ /\ _`
     (qspec_then `x` mp_tac) >>
   simp[wordsTheory.w2n_n2w]) >>
 strip_tac >>
 asm_x "indexed" kall_tac >> asm_x "child" kall_tac >>
 `ctr <> tmp /\ ~MEM ctr [so;doff;sp;dp] /\ ctr <> lt /\ ctr <> done` by fs[listTheory.ALL_DISTINCT, listTheory.MEM] >>
 `lookup_var ctr xc = SOME (n2w i) /\ FLOOKUP Gc ctr = NONE /\ op_taint tc (Var ctr) = {}` by
   (qpat_assum `!p. not_fresh_at si p ==> _` (qspec_then `ctr` mp_tac) >>
    qpat_assum `!p. ~MEM p [so;doff;sp;dp] ==> _` (qspec_then `ctr` mp_tac) >>
    qpat_assum `!p. p <> lt /\ p <> done ==> _` (qspec_then `ctr` mp_tac) >>
    simp[]) >>
 `i+1 < dimword(:256)` by decide_tac >>
 `lookup_block xc.vs_current_bb fn.fn_blocks = SOME back_bb` by simp[] >>
 drule_all typed_copy_loop_backedge_path_ptr_framed >>
 disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
 qpat_x_assum `sf = _` kall_tac >>
 qpat_x_assum `Gf = _` kall_tac >>
 qpat_x_assum `tnf = _` kall_tac >>
 `gas_path_ptr D 0 ctx fn PG Gi ti u 0 Ga ta (OK xa)` by
   (irule (fragGasPathPtrTheory.gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
    qexistsl_tac [`Gh`, `sh`, `th`] >> conj_tac >> first_assum ACCEPT_TAC) >>
 `gas_path_ptr D 0 ctx fn PG Gi ti u 0 Gc tc (OK xc)` by
   (irule (fragGasPathPtrTheory.gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
    qexistsl_tac [`Ga`, `xa`, `ta`] >> conj_tac >> first_assum ACCEPT_TAC) >>
 qexistsl_tac [`Gf`, `tnf`, `sf`] >> conj_tac
 >- (irule (fragGasPathPtrTheory.gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gc`, `xc`, `tc`] >> conj_tac >> first_assum ACCEPT_TAC) >>
 `!p. not_fresh_at sa p ==>
   lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
   op_taint tnf (Var p) = op_taint tn (Var p)` by
   (rpt strip_tac >>
    `~MEM p [ctr;lt;done;so;doff;sp;dp;tmp] /\ not_fresh_at si p` by metis_tac[] >>
    fs[listTheory.MEM] >> metis_tac[]) >>
 `lookup_var src sf = SOME a /\ lookup_var dst sf = SOME b` by metis_tac[] >>
 `sf.vs_labels = s.vs_labels` by
   (fs[venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
 `eval_operand len sf = SOME (n2w N) /\ op_taint tnf len = {} /\ op_prov Gf len = NONE` by
   (Cases_on `len` >> simp[venomStateTheory.eval_operand_def,
     ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >>
    fs[venomStateTheory.eval_operand_def,
     ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >> metis_tac[]) >>
 `ptr_covers Gf tnf src sf (sc*ss) /\ ptr_covers Gf tnf dst sf (dc*ds)` by
   (metis_tac[annAssignPtrBytestringTheory.annassign_ptr_covers_frame_ptr]) >>
 simp[] >>
 conj_tac >- metis_tac[] >>
 conj_tac >- metis_tac[] >>
 conj_tac >- (fs[venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
 qx_gen_tac `x` >> disch_tac >>
 `~(w2n b+i*ds <= x /\ x < w2n b+i*ds+ds)` by
   (qpat_assum `ds = type_memory_size dtv` (fn eq =>
      qpat_x_assum `~(_ <= x) \/ ~(_ < _)` (mp_tac o REWRITE_RULE [GSYM eq])) >> decide_tac) >>
 qpat_x_assum `!i'. ~(_ /\ _) ==> mem_bytes_at _ _ xc.vs_memory = _ /\ _`
   (qspec_then `x` mp_tac) >>
 simp[wordsTheory.w2n_n2w] >>
 impl_tac >- metis_tac[arithmeticTheory.ADD_ASSOC] >>
 strip_tac >> metis_tac[]
QED

Finalise typed_copy_indexed_loop_path_ptr_conditional
