(*
 * Fuel bound for the dynamic-array-to-storage copy loop.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_dynarray_to_storage
 *)

Theory fragFuelLoopDynStorage
Ancestors
  fragFuel fragFuelContextBase fragFuelContext compileEnv emitHelper context
  venomInst venomExecSemantics venomState finite_map words arithmetic fragExec
Libs
  fragFuelLib

(* Cutting every jump gives the compiler-state structural projections without
   assuming that the generated loop terminates. *)
Theorem dynstorage_cut_fuel[local]:
  !src dst ew em tr.
    fuel_ok UNIV {} UNIV (compile_dynarray_to_storage src dst ew em tr)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_dynarray_to_storage_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void,
             fuel_ok_emit_inst_jmp, fuel_ok_emit_inst_jnz,
             fuel_ok_emit_inst, CONJUNCT2 fuel_ok_compile_word_copy_loop] >>
  simp[is_terminator_def]
QED

Theorem dynstorage_structure[local]:
  !src dst ew em tr st u st'.
    compile_dynarray_to_storage src dst ew em tr st = (u, st') ==>
    cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
    (cs_no_phi st ==> cs_no_phi st')
Proof
  rpt gen_tac >> Cases_on `u` >> strip_tac >>
  mp_tac (SPEC_ALL dynstorage_cut_fuel) >>
  rewrite_tac[fuel_ok_def] >> disch_then drule >> simp[]
QED

(* Keep the nested copy opaque when splitting the generated code into phases. *)
Theorem dynstorage_parts[local]:
  let copy = \counter.
    if ew = 1 then
      do mul <- emit_op MUL [Var counter; Lit 32w];
         off <- emit_op ADD [Lit 32w; mul];
         ptr <- emit_op ADD [src; off];
         value <- emit_op MLOAD [ptr];
         slot <- emit_op ADD [Var counter; Lit 1w];
         dest <- emit_op ADD [dst; slot];
         emit_void (if tr then TSTORE else SSTORE) [dest; value]
      od
    else
      do mul <- emit_op MUL [Var counter; Lit (n2w em)];
         off <- emit_op ADD [Lit 32w; mul];
         ptr <- emit_op ADD [src; off];
         scale <- emit_op MUL [Var counter; Lit (n2w ew)];
         slot <- emit_op ADD [Lit 1w; scale];
         dest <- emit_op ADD [dst; slot];
         compile_word_copy_loop ptr dest ew LocMemory
           (if tr then LocTransient else LocStorage) F;
         return ()
      od
  in
  compile_dynarray_to_storage src dst ew em tr s0 = ((), sf) <=>
  ?len cond body exit counter lt done inc old1 old2 old3
    s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17.
    emit_op MLOAD [src] s0 = (len,s1) /\
    fresh_label "dyn_cond" s1 = (cond,s2) /\
    fresh_label "dyn_body" s2 = (body,s3) /\
    fresh_label "dyn_exit" s3 = (exit,s4) /\
    fresh_var s4 = (counter,s5) /\
    emit_inst ASSIGN [Lit 0w] [counter] s5 = ((),s6) /\
    emit_inst JMP [Label cond] [] s6 = ((),s7) /\
    new_block cond s7 = (old1,s8) /\
    emit_op LT [Var counter; len] s8 = (lt,s9) /\
    emit_op ISZERO [lt] s9 = (done,s10) /\
    emit_inst JNZ [done; Label exit; Label body] [] s10 = ((),s11) /\
    new_block body s11 = (old2,s12) /\
    copy counter s12 = ((),s13) /\
    emit_op ADD [Var counter; Lit 1w] s13 = (inc,s14) /\
    emit_inst ASSIGN [inc] [counter] s14 = ((),s15) /\
    emit_inst JMP [Label cond] [] s15 = ((),s16) /\
    new_block exit s16 = (old3,s17) /\
    emit_void (if tr then TSTORE else SSTORE) [dst; len] s17 = ((),sf)
Proof
  simp_tac std_ss [LET_THM] >>
  Cases_on `ew = 1` >> Cases_on `tr` >> simp[] >>
  (eq_tac
   >- (simp[compile_dynarray_to_storage_def, comp_ignore_bind_def, comp_bind_def,
            comp_return_def] >>
       rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
       metis_tac[pairTheory.PAIR, pairTheory.pair_CASES, oneTheory.one]) >>
   strip_tac >>
   gvs[compile_dynarray_to_storage_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def] >>
   rpt (pairarg_tac >> gvs[]))
QED

Theorem dynstorage_entry_layout[local]:
  !src s0 len s1 cond s2 body s3 exit s4 counter s5 s6 s7 old s8.
  emit_op MLOAD [src] s0 = (len,s1) /\
  fresh_label "dyn_cond" s1 = (cond,s2) /\
  fresh_label "dyn_body" s2 = (body,s3) /\
  fresh_label "dyn_exit" s3 = (exit,s4) /\
  fresh_var s4 = (counter,s5) /\
  emit_inst ASSIGN [Lit 0w] [counter] s5 = ((),s6) /\
  emit_inst JMP [Label cond] [] s6 = ((),s7) /\
  new_block cond s7 = (old,s8) ==>
  ?lv.
    len = Var lv /\
    lv = STRING #"%" (toString s0.cs_next_var) /\
    counter = STRING #"%" (toString (s0.cs_next_var + 1)) /\
    lv <> counter /\
    ~var_below s0.cs_next_var lv /\
    ~var_below s0.cs_next_var counter /\
    var_below s8.cs_next_var lv /\
    var_below s8.cs_next_var counter /\
    s8.cs_next_var = s0.cs_next_var + 2 /\
    s8.cs_next_id = s0.cs_next_id + 3 /\
    s8.cs_current_bb = cond /\ s8.cs_current_insts = [] /\
    s7.cs_current_insts = s0.cs_current_insts ++
      [mk_inst s0.cs_next_id MLOAD [src] [lv];
       mk_inst (s0.cs_next_id + 1) ASSIGN [Lit 0w] [counter];
       mk_inst (s0.cs_next_id + 2) JMP [Label cond] []]
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, fresh_label_def,
      emit_def, new_block_def] >>
  simp[listTheory.APPEND_ASSOC, var_below_fresh, var_below_def,
       ASCIInumbersTheory.toString_inj] >>
  rpt strip_tac >> gvs[ASCIInumbersTheory.toString_inj]
QED

Theorem dynstorage_condition_layout[local]:
  !counter lv s8 lt s9 done s10 exit body s11 old s12.
  var_below s8.cs_next_var lv /\ var_below s8.cs_next_var counter /\
  s8.cs_current_insts = [] /\
  emit_op LT [Var counter; Var lv] s8 = (lt,s9) /\
  emit_op ISZERO [lt] s9 = (done,s10) /\
  emit_inst JNZ [done; Label exit; Label body] [] s10 = ((),s11) /\
  new_block body s11 = (old,s12) ==>
  ?vl vd.
    lt = Var vl /\ done = Var vd /\
    vl = STRING #"%" (toString s8.cs_next_var) /\
    vd = STRING #"%" (toString (s8.cs_next_var + 1)) /\
    vl <> vd /\ vl <> lv /\ vl <> counter /\ vd <> lv /\ vd <> counter /\
    var_below s12.cs_next_var lv /\ var_below s12.cs_next_var counter /\
    s12.cs_next_var = s8.cs_next_var + 2 /\
    s12.cs_current_bb = body /\ s12.cs_current_insts = [] /\
    s11.cs_current_bb = s8.cs_current_bb /\
    s11.cs_current_insts =
      [mk_inst s8.cs_next_id LT [Var counter; Var lv] [vl];
       mk_inst (s8.cs_next_id + 1) ISZERO [Var vl] [vd];
       mk_inst (s8.cs_next_id + 2) JNZ [Var vd; Label exit; Label body] []]
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def, new_block_def] >>
  gvs[var_below_def, ASCIInumbersTheory.toString_inj] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem dynstorage_increment_layout[local]:
  !counter s13 inc s14 s15 cond s16 exit old s17.
  emit_op ADD [Var counter; Lit 1w] s13 = (inc,s14) /\
  emit_inst ASSIGN [inc] [counter] s14 = ((),s15) /\
  emit_inst JMP [Label cond] [] s15 = ((),s16) /\
  new_block exit s16 = (old,s17) ==>
  ?vi.
    inc = Var vi /\ vi = STRING #"%" (toString s13.cs_next_var) /\
    s17.cs_next_var = s13.cs_next_var + 1 /\
    s17.cs_current_bb = exit /\ s17.cs_current_insts = [] /\
    s16.cs_current_bb = s13.cs_current_bb /\
    s16.cs_current_insts = s13.cs_current_insts ++
      [mk_inst s13.cs_next_id ADD [Var counter; Lit 1w] [vi];
       mk_inst (s13.cs_next_id + 1) ASSIGN [Var vi] [counter];
       mk_inst (s13.cs_next_id + 2) JMP [Label cond] []]
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def, new_block_def] >>
  simp[listTheory.APPEND_ASSOC]
QED

(* Semantic boundary for the condition: the temporary values are concrete,
   and neither loop-carried variable is overwritten. *)
Theorem dynstorage_condition_steps[local]:
  !s len ctr lt done l c id1 id2 id3 body exit.
    lookup_var len s = SOME l /\ lookup_var ctr s = SOME c /\
    len <> lt /\ len <> done /\ ctr <> lt /\ ctr <> done ==>
    let s1 = update_var lt (bool_to_word (w2n c < w2n l)) s in
    let s2 = update_var done (bool_to_word (~(w2n c < w2n l))) s1 in
      step_inst_base (mk_inst id1 LT [Var ctr; Var len] [lt]) s = OK s1 /\
      step_inst_base (mk_inst id2 ISZERO [Var lt] [done]) s1 = OK s2 /\
      step_inst_base (mk_inst id3 JNZ
        [Var done; Label exit; Label body] []) s2 =
        OK (jump_to (if w2n c < w2n l then body else exit) s2) /\
      lookup_var len s2 = SOME l /\ lookup_var ctr s2 = SOME c
Proof
  rpt strip_tac >>
  Cases_on `w2n c < w2n l` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       exec_pure1_def, eval_operand_def, bool_to_word_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gvs[lookup_var_def]
QED

Theorem dynstorage_increment_steps[local]:
  !s len ctr tmp l c id1 id2.
    lookup_var len s = SOME l /\ lookup_var ctr s = SOME c /\
    len <> ctr /\ len <> tmp ==>
    let s1 = update_var tmp (c + 1w) s in
    let s2 = update_var ctr (c + 1w) s1 in
      step_inst_base (mk_inst id1 ADD [Var ctr; Lit 1w] [tmp]) s = OK s1 /\
      step_inst_base (mk_inst id2 ASSIGN [Var tmp] [ctr]) s1 = OK s2 /\
      lookup_var len s2 = SOME l /\ lookup_var ctr s2 = SOME (c + 1w)
Proof
  rpt strip_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, eval_operands_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >>
  gvs[lookup_var_def]
QED

Theorem dynstorage_remaining_decreases[local]:
  !(c:bytes32) (l:bytes32).
    w2n c < w2n l ==>
    w2n (c + 1w) = w2n c + 1 /\
    w2n l - w2n (c + 1w) < w2n l - w2n c
Proof
  rpt strip_tac >>
  `w2n l < dimword(:256)` by (MATCH_ACCEPT_TAC w2n_lt) >>
  `w2n c + w2n (1w:bytes32) < dimword(:256)` by
    (simp[] >> decide_tac) >>
  drule w2n_add_2 >> simp[] >> decide_tac
QED

(* The condition consumes one block, including the halted-state alternative.
   Instruction indices are relative, so the fact also applies after a prefix. *)
Theorem dynstorage_condition_outcome[local]:
  !G ctx fn s bb len ctr lt done l c id1 id2 id3 body exit.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id1 LT [Var ctr; Var len] [lt]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst id2 ISZERO [Var lt] [done]) /\
    get_instruction bb (SUC (SUC s.vs_inst_idx)) =
      SOME (mk_inst id3 JNZ [Var done; Label exit; Label body] []) /\
    lookup_var len s = SOME l /\ lookup_var ctr s = SOME c /\
    len <> lt /\ len <> done /\ ctr <> lt /\ ctr <> done ==>
    let s1 = (update_var lt (bool_to_word (w2n c < w2n l)) s)
               with vs_inst_idx := SUC s.vs_inst_idx in
    let s2 = (update_var done (bool_to_word (~(w2n c < w2n l))) s1)
               with vs_inst_idx := SUC (SUC s.vs_inst_idx) in
    fuel_outcome G ctx fn s 1
      (\t. t = jump_to (if w2n c < w2n l then body else exit) s2)
Proof
  rpt strip_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `jump_to dest s2` >>
  `!f. run_from f ctx fn s = run_from f ctx fn s2` by
    (gen_tac >>
     simp[run_from_def, Once exec_block_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, mk_inst_def, is_terminator_def,
          exec_pure2_def, eval_operand_def] >>
     simp[Once exec_block_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, mk_inst_def, is_terminator_def,
          exec_pure1_def, eval_operand_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE, Abbr `s2`, bool_to_word_def] >>
     Cases_on `w2n c < w2n l` >> gvs[lookup_var_def, bool_to_word_def]) >>
  `fuel_outcome G ctx fn s2 1 (\t. t = jump_to dest s2)`
    suffices_by gvs[fuel_outcome_def] >>
  irule fuel_outcome_jump >>
  conj_tac >- simp[] >>
  qexistsl [`bb`,
    `mk_inst id3 JNZ [Var done; Label exit; Label body'] []`, `dest`] >>
  simp[Abbr `s2`, Abbr `dest`, mk_inst_def, is_terminator_def,
       step_inst_base_opcode_eqs, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >>
  Cases_on `w2n c < w2n l` >> simp[bool_to_word_def]
QED

Theorem dynstorage_increment_outcome[local]:
  !G ctx fn s bb len ctr tmp l c id1 id2 id3 cond.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id1 ADD [Var ctr; Lit 1w] [tmp]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst id2 ASSIGN [Var tmp] [ctr]) /\
    get_instruction bb (SUC (SUC s.vs_inst_idx)) =
      SOME (mk_inst id3 JMP [Label cond] []) /\
    lookup_var len s = SOME l /\ lookup_var ctr s = SOME c /\
    len <> ctr /\ len <> tmp ==>
    let s1 = (update_var tmp (c + 1w) s)
               with vs_inst_idx := SUC s.vs_inst_idx in
    let s2 = (update_var ctr (c + 1w) s1)
               with vs_inst_idx := SUC (SUC s.vs_inst_idx) in
    fuel_outcome G ctx fn s 1 (\t. t = jump_to cond s2)
Proof
  rpt strip_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `jump_to cond s2` >>
  `!f. run_from f ctx fn s = run_from f ctx fn s2` by
    (gen_tac >>
     simp[run_from_def, Once exec_block_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, mk_inst_def, is_terminator_def,
          exec_pure2_def, eval_operand_def] >>
     simp[Once exec_block_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, mk_inst_def, is_terminator_def,
          eval_operand_def, eval_operands_def, lookup_var_def,
          update_var_def, FLOOKUP_UPDATE, Abbr `s2`]) >>
  `fuel_outcome G ctx fn s2 1 (\t. t = jump_to cond s2)`
    suffices_by gvs[fuel_outcome_def] >>
  irule fuel_outcome_jump >>
  conj_tac >- simp[] >>
  qexistsl [`bb`, `mk_inst id3 JMP [Label cond] []`, `cond`] >>
  simp[Abbr `s2`, mk_inst_def, is_terminator_def,
       step_inst_base_opcode_eqs, update_var_def]
QED

(* The length is loaded into a fresh variable before the loop; the loop
   counts a fresh counter from 0 while it is below that length.  Each round
   copies one element (one word, or a word-copy loop over a literal count)
   and adds 1; the body writes only the counter and variables it allocates
   itself, so the length stays fixed and the loop leaves within 2 ** 256
   rounds. *)
(* The copy slice stops before the counter update and the back edge. *)
Theorem fuel_ok_dynstorage_copy_body[local]:
  !src_ptr dst_slot counter elem_words elem_mem_size transient Wv E.
    fuel_ok Wv {} E
      (if elem_words = 1 then
         do mul_op <- emit_op MUL [Var counter; Lit 32w];
            src_off <- emit_op ADD [Lit 32w; mul_op];
            src_elem <- emit_op ADD [src_ptr; src_off];
            val_op <- emit_op MLOAD [src_elem];
            slot_off <- emit_op ADD [Var counter; Lit 1w];
            dst_elem <- emit_op ADD [dst_slot; slot_off];
            (if transient then emit_void TSTORE [dst_elem; val_op]
             else emit_void SSTORE [dst_elem; val_op])
         od
       else
         do mul_op <- emit_op MUL [Var counter; Lit (n2w elem_mem_size)];
            src_off <- emit_op ADD [Lit 32w; mul_op];
            src_elem <- emit_op ADD [src_ptr; src_off];
            slot_mul <- emit_op MUL [Var counter; Lit (n2w elem_words)];
            slot_off <- emit_op ADD [Lit 1w; slot_mul];
            dst_elem <- emit_op ADD [dst_slot; slot_off];
            compile_word_copy_loop src_elem dst_elem elem_words
              LocMemory (if transient then LocTransient else LocStorage) F;
            return ()
         od)
Proof
  rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             CONJUNCT2 fuel_ok_compile_word_copy_loop] >>
  simp[is_terminator_def]
QED

(* An empty write set keeps both loop registers, even across a nested copy.
   The bound is fixed at compile time, before the runtime state is chosen. *)
Theorem dynstorage_copy_body_outcome[local]:
  !m st x st' len counter.
    fuel_ok {} {} {} m /\ m st = (x, st') /\
    var_below st.cs_next_var len /\ var_below st.cs_next_var counter ==>
    ?Kb. frag_fuel {} {} {} st st' Kb /\
      !G ctx fn s.
        no_phi_fn fn /\ fn_has_code st st' fn /\
        callees_stable G ctx fn /\ at_point st s ==>
        ?j. j <= Kb /\
          fuel_outcome G ctx fn s j
            (\t. vars_kept st.cs_next_var {} s t /\
                 lookup_var len t = lookup_var len s /\
                 lookup_var counter t = lookup_var counter s /\
                 at_point st' t)
Proof
  rpt gen_tac >> strip_tac >>
  fs[fuel_ok_def] >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `Kb` >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `frag_fuel _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[frag_fuel_def] >>
  disch_then (qspecl_then [`G`, `st.cs_next_var`, `ctx`, `fn`, `s`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `j` >> simp[] >>
  irule fuel_outcome_weaken >>
  goal_assum (drule_at Any) >>
  simp[vars_kept_def]
QED

(* Entry either fixes an exceptional result or loads an arbitrary word and
   starts the counter at zero.  No validity premise on the source is needed. *)
Theorem dynstorage_entry_outcome[local]:
  !G ctx fn s bb s0 s8 src lv counter id1 id2 id3 cond.
    no_phi_fn fn /\ at_point s0 s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id1 MLOAD [src] [lv]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst id2 ASSIGN [Lit 0w] [counter]) /\
    get_instruction bb (SUC (SUC s.vs_inst_idx)) =
      SOME (mk_inst id3 JMP [Label cond] []) /\
    lv <> counter /\
    ~var_below s0.cs_next_var lv /\
    ~var_below s0.cs_next_var counter /\
    s8.cs_current_bb = cond /\ s8.cs_current_insts = [] ==>
    fuel_outcome G ctx fn s 1
      (\t. at_point s8 t /\ lookup_var counter t = SOME 0w /\
           (?l:bytes32. lookup_var lv t = SOME l) /\
           vars_kept s0.cs_next_var {} s t)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `eval_operand src s`
  >- (`!f. run_from f ctx fn s = Error "undefined operand"` by
        (gen_tac >> simp[run_from_def, Once exec_block_def,
          step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
          exec_read1_def]) >>
      simp[fuel_outcome_def]) >>
  qmatch_asmsub_rename_tac `eval_operand src s = SOME addr` >>
  qabbrev_tac `s1 = (update_var lv (mload (w2n addr) s) s)
                     with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `s2 = (update_var counter 0w s1)
                     with vs_inst_idx := SUC (SUC s.vs_inst_idx)` >>
  `!f. run_from f ctx fn s = run_from f ctx fn s2` by
    (gen_tac >>
     simp[run_from_def, Once exec_block_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def] >>
     simp[Once exec_block_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, mk_inst_def, is_terminator_def,
          eval_operands_def, eval_operand_def, Abbr `s1`, Abbr `s2`,
          update_var_def]) >>
  `fuel_outcome G ctx fn s2 1
      (\t. at_point s8 t /\ lookup_var counter t = SOME 0w /\
           (?l:bytes32. lookup_var lv t = SOME l) /\
           vars_kept s0.cs_next_var {} s t)`
    suffices_by gvs[fuel_outcome_def] >>
  irule fuel_outcome_jump >> conj_tac >- simp[] >>
  qexistsl [`bb`, `mk_inst id3 JMP [Label cond] []`, `cond`] >>
  simp[Abbr `s2`, Abbr `s1`, mk_inst_def, is_terminator_def,
       step_inst_base_opcode_eqs, at_point_def, jump_to_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, vars_kept_def] >>
  metis_tac[]
QED

Theorem fuel_ok_compile_dynarray_to_storage:
  !src_ptr dst_slot elem_words elem_mem_size transient Wv E.
    fuel_ok Wv {} E
      (compile_dynarray_to_storage src_ptr dst_slot elem_words elem_mem_size
         transient)
Proof
  rpt gen_tac >> rewrite_tac[fuel_ok_def] >> rpt gen_tac >> strip_tac >>
  drule dynstorage_structure >> strip_tac >> simp[] >>
  cheat
QED
