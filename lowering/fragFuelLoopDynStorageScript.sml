(*
 * Fuel bound for the dynamic-array-to-storage copy loop.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_dynarray_to_storage
 *)

Theory fragFuelLoopDynStorage
Ancestors
  fragFuel fragFuelContextBase fragFuelContext compileEnv emitHelper context
  venomInst
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

(* The length is loaded into a fresh variable before the loop; the loop
   counts a fresh counter from 0 while it is below that length.  Each round
   copies one element (one word, or a word-copy loop over a literal count)
   and adds 1; the body writes only the counter and variables it allocates
   itself, so the length stays fixed and the loop leaves within 2 ** 256
   rounds. *)
Theorem fuel_ok_compile_dynarray_to_storage:
  !src_ptr dst_slot elem_words elem_mem_size transient Wv E.
    fuel_ok Wv {} E
      (compile_dynarray_to_storage src_ptr dst_slot elem_words elem_mem_size
         transient)
Proof
  cheat
QED
