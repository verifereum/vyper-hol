(*
 * Fuel bound for the word-copy loop of the context helpers.
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_word_copy_loop_base
 *)

Theory fragFuelLoopWcopy
Ancestors
  fragFuel fragFuelContextBase fragExec compileEnv emitHelper context venomInst
  venomExecSemantics venomState venomInstProofs
Libs
  fragFuelLib

(* Structural obligations do not require closing the back edge: all labels
   may be exits while establishing this compile-time boundary. *)
Theorem word_copy_loop_structure[local]:
  !src dst cnt ld sd ctor imm st r st'.
    compile_word_copy_loop_base src dst cnt ld sd ctor imm st = (r, st') ==>
    cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
    (cs_no_phi st ==> cs_no_phi st')
Proof
  rpt gen_tac >> strip_tac >>
  `fuel_ok UNIV {} UNIV
     (compile_word_copy_loop_base src dst cnt ld sd ctor imm)` suffices_by
    metis_tac[fuel_ok_def] >>
  simp_tac std_ss [compile_word_copy_loop_base_def] >>
  fuel_auto [fuel_ok_emit_inst_jmp, fuel_ok_emit_inst_jnz,
             fuel_ok_emit_op, fuel_ok_emit_inst, fuel_ok_compile_ptr_load,
             fuel_ok_compile_ptr_store] >>
  simp[is_terminator_def]
QED

(* Named compiler cut points.  The body deliberately ends before the
   counter increment, so its fresh-variable framing can be used separately. *)
Theorem word_copy_loop_cut_points[local]:
  !src dst cnt ld sd ctor imm st r st'.
    compile_word_copy_loop_base src dst cnt ld sd ctor imm st = (r, st') ==>
    ?cl bl el cv s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       s12 s13 s14 s15 s16 s17 done src_off value dst_off new_ctr.
      fresh_label "wcopy_cond" st = (cl, s1) /\
      fresh_label "wcopy_body" s1 = (bl, s2) /\
      fresh_label "wcopy_exit" s2 = (el, s3) /\
      fresh_var s3 = (cv, s4) /\
      emit_inst ASSIGN [Lit 0w] [cv] s4 = ((), s5) /\
      emit_inst JMP [Label cl] [] s5 = ((), s6) /\
      new_block cl s6 = (s6.cs_current_bb, s7) /\
      emit_op EQ [Var cv; cnt] s7 = (done, s8) /\
      emit_inst JNZ [done; Label el; Label bl] [] s8 = ((), s9) /\
      new_block bl s9 = (s9.cs_current_bb, s10) /\
      (if word_scale ld = 1 then emit_op ADD [src; Var cv]
       else comp_bind (emit_op MUL [Var cv; Lit (n2w (word_scale ld))])
              (\scaled. emit_op ADD [src; scaled])) s10 = (src_off, s11) /\
      compile_ptr_load ctor imm ld src_off s11 = (value, s12) /\
      (if word_scale sd = 1 then emit_op ADD [dst; Var cv]
       else comp_bind (emit_op MUL [Var cv; Lit (n2w (word_scale sd))])
              (\scaled. emit_op ADD [dst; scaled])) s12 = (dst_off, s13) /\
      compile_ptr_store ctor imm sd dst_off value s13 = ((), s14) /\
      emit_op ADD [Var cv; Lit 1w] s14 = (new_ctr, s15) /\
      emit_inst ASSIGN [new_ctr] [cv] s15 = ((), s16) /\
      emit_inst JMP [Label cl] [] s16 = ((), s17) /\
      new_block el s17 = (r, st')
Proof
  rpt gen_tac >>
  simp_tac std_ss [compile_word_copy_loop_base_def, LET_THM,
                  comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> fs[]) >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >> fs[new_block_def]
QED

Theorem word_copy_loop_prefix[local]:
  !st cl bl el cv s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 done cnt.
    fresh_label "wcopy_cond" st = (cl, s1) /\
    fresh_label "wcopy_body" s1 = (bl, s2) /\
    fresh_label "wcopy_exit" s2 = (el, s3) /\
    fresh_var s3 = (cv, s4) /\
    emit_inst ASSIGN [Lit 0w] [cv] s4 = ((), s5) /\
    emit_inst JMP [Label cl] [] s5 = ((), s6) /\
    new_block cl s6 = (s6.cs_current_bb, s7) /\
    emit_op EQ [Var cv; cnt] s7 = (done, s8) /\
    emit_inst JNZ [done; Label el; Label bl] [] s8 = ((), s9) /\
    new_block bl s9 = (s9.cs_current_bb, s10) ==>
    cv = "%" ++ toString st.cs_next_var /\
    s7.cs_next_var = st.cs_next_var + 1 /\
    s10.cs_next_var = st.cs_next_var + 2 /\
    s7.cs_current_bb = cl /\ s7.cs_current_insts = [] /\
    s10.cs_current_bb = bl /\ s10.cs_current_insts = []
Proof
  rpt gen_tac >>
  simp[new_block_def, fresh_label_def, fresh_var_def, emit_op_def,
       emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[]
QED

Theorem word_copy_loop_initial_code[local]:
  !sa sb sc sd cv cl fn.
    emit_inst ASSIGN [Lit 0w] [cv] sa = ((), sb) /\
    emit_inst JMP [Label cl] [] sb = ((), sc) /\
    new_block cl sc = (sc.cs_current_bb, sd) /\
    fn_has_code sc sd fn ==>
    lookup_block sa.cs_current_bb fn.fn_blocks =
      SOME <| bb_label := sa.cs_current_bb;
              bb_instructions := sa.cs_current_insts ++
                [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv];
                 mk_inst (sa.cs_next_id + 1) JMP [Label cl] []] |>
Proof
  rpt strip_tac >> drule_all fn_has_code_new_block >>
  gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def,
      listTheory.APPEND_ASSOC]
QED

Theorem word_copy_loop_condition_code[local]:
  !sa sb sc sd cv cnt done el bl fn.
    sa.cs_current_insts = [] /\
    emit_op EQ [Var cv; cnt] sa = (done, sb) /\
    emit_inst JNZ [done; Label el; Label bl] [] sb = ((), sc) /\
    new_block bl sc = (sc.cs_current_bb, sd) /\
    fn_has_code sc sd fn ==>
    done = Var ("%" ++ toString sa.cs_next_var) /\
    lookup_block sa.cs_current_bb fn.fn_blocks =
      SOME <| bb_label := sa.cs_current_bb;
              bb_instructions :=
                [mk_inst sa.cs_next_id EQ [Var cv; cnt]
                   ["%" ++ toString sa.cs_next_var];
                 mk_inst (sa.cs_next_id + 1) JNZ
                   [done; Label el; Label bl] []] |>
Proof
  rpt strip_tac >> drule_all fn_has_code_new_block >>
  gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def]
QED

Theorem word_copy_loop_increment_code[local]:
  !sa sb sc sd se cv next cl el r fn.
    emit_op ADD [Var cv; Lit 1w] sa = (next, sb) /\
    emit_inst ASSIGN [next] [cv] sb = ((), sc) /\
    emit_inst JMP [Label cl] [] sc = ((), sd) /\
    new_block el sd = (r, se) /\ fn_has_code sd se fn ==>
    next = Var ("%" ++ toString sa.cs_next_var) /\
    lookup_block sa.cs_current_bb fn.fn_blocks =
      SOME <| bb_label := sa.cs_current_bb;
              bb_instructions := sa.cs_current_insts ++
                [mk_inst sa.cs_next_id ADD [Var cv; Lit 1w]
                   ["%" ++ toString sa.cs_next_var];
                 mk_inst (sa.cs_next_id + 1) ASSIGN [next] [cv];
                 mk_inst (sa.cs_next_id + 2) JMP [Label cl] []] |> /\
    se.cs_current_bb = el /\ se.cs_current_insts = []
Proof
  rpt strip_tac >> drule_all fn_has_code_new_block >>
  gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def,
      new_block_def, listTheory.APPEND_ASSOC]
QED

(* Counter arithmetic is modular: the distance to the bound decreases even
   when incrementing the counter wraps around. *)
Theorem wcopy_distance_bound[local]:
  !b c:256 word. w2n (b - c) < 2 ** 256
Proof
  rpt gen_tac >> mp_tac (Q.ISPEC `b - c : 256 word` wordsTheory.w2n_lt) >>
  simp[wordsTheory.dimword_def]
QED

Theorem wcopy_distance_decreases[local]:
  !b c:256 word. c <> b ==>
    w2n (b - (c + 1w)) < w2n (b - c)
Proof
  rpt strip_tac >>
  `b - (c + 1w) = (b - c) - 1w` by wordsLib.WORD_DECIDE_TAC >>
  pure_asm_rewrite_tac[] >> irule wordsTheory.WORD_PRED_THM >>
  simp[wordsTheory.WORD_EQ_SUB_ZERO]
QED

(* Instruction-level interfaces use code lookups, independently of how the
   compiler obtained the blocks. Exact resulting states also expose framing. *)
Theorem wcopy_assign_jump_outcome[local]:
  !G ctx fn s bb ai ji ctr lbl value_op v.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME ai /\
    ai.inst_opcode = ASSIGN /\ ai.inst_operands = [value_op] /\
    ai.inst_outputs = [ctr] /\ eval_operand value_op s = SOME v /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME ji /\
    ji.inst_opcode = JMP /\ ji.inst_operands = [Label lbl] ==>
    fuel_outcome G ctx fn s 1
      (\t. t = jump_to lbl (update_var ctr v s))
Proof
  rpt strip_tac >>
  qabbrev_tac `s1 = (update_var ctr v s) with
                     vs_inst_idx := SUC s.vs_inst_idx` >>
  `!f. run_from f ctx fn s = run_from f ctx fn s1` by
    (gen_tac >> unabbrev_all_tac >> irule run_from_step >>
     qexistsl_tac [`bb`, `ai`] >>
     simp[is_terminator_def, step_inst_base_opcode_eqs, eval_operand_def]) >>
  simp[fuel_outcome_def] >>
  `fuel_outcome G ctx fn s1 1
     (\t. t = jump_to lbl (update_var ctr v s))` suffices_by
     simp[fuel_outcome_def] >>
  irule fuel_outcome_jump >> simp[] >>
  qexistsl_tac [`bb`, `ji`, `lbl`] >>
  simp[Abbr `s1`, update_var_def, is_terminator_def,
       step_inst_base_opcode_eqs, jump_to_def]
QED

Theorem wcopy_cond_outcome[local]:
  !G ctx fn s bb ei ji ctr done count_op c yes no.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME ei /\
    ei.inst_opcode = EQ /\ ei.inst_operands = [Var ctr; count_op] /\
    ei.inst_outputs = [done] /\ lookup_var ctr s = SOME c /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME ji /\
    ji.inst_opcode = JNZ /\
    ji.inst_operands = [Var done; Label yes; Label no] ==>
    fuel_outcome G ctx fn s 1
      (\t. ?b. eval_operand count_op s = SOME b /\
        t = jump_to (if c = b then yes else no)
              (update_var done (bool_to_word (c = b)) s))
Proof
  rpt strip_tac >> Cases_on `eval_operand count_op s`
  >- (simp[fuel_outcome_def] >> rpt strip_tac >>
      `!f. run_from f ctx fn s = Error "undefined operand"` by
        (gen_tac >> drule run_from_nonterm >> disch_then drule >>
         simp[is_terminator_def, step_inst_non_invoke,
              step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def] >>
         disch_then irule) >> simp[]) >>
  rename1 `eval_operand count_op s = SOME b` >>
  qabbrev_tac `s1 = (update_var done (bool_to_word (c = b)) s) with
                     vs_inst_idx := SUC s.vs_inst_idx` >>
  `!f. run_from f ctx fn s = run_from f ctx fn s1` by
    (gen_tac >> unabbrev_all_tac >> irule run_from_step >>
     qexistsl_tac [`bb`, `ei`] >>
     simp[is_terminator_def, step_inst_base_opcode_eqs,
          exec_pure2_def, eval_operand_def]) >>
  simp[fuel_outcome_def] >>
  `fuel_outcome G ctx fn s1 1
     (\t. t = jump_to (if c = b then yes else no)
                (update_var done (bool_to_word (c = b)) s))` suffices_by
     simp[fuel_outcome_def] >>
  irule fuel_outcome_jump >> simp[] >>
  qexistsl_tac [`bb`, `ji`, `if c = b then yes else no`] >>
  simp[Abbr `s1`, update_var_def, is_terminator_def,
       step_inst_base_opcode_eqs, jump_to_def, eval_operand_def,
       lookup_var_def, bool_to_word_def] >>
  Cases_on `c = b` >> simp[finite_mapTheory.FLOOKUP_UPDATE, bool_to_word_def]
QED

Theorem wcopy_increment_outcome[local]:
  !G ctx fn s bb ni ai ji ctr tmp lbl c.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME ni /\
    ni.inst_opcode = ADD /\ ni.inst_operands = [Var ctr; Lit 1w] /\
    ni.inst_outputs = [tmp] /\ lookup_var ctr s = SOME c /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME ai /\
    ai.inst_opcode = ASSIGN /\ ai.inst_operands = [Var tmp] /\
    ai.inst_outputs = [ctr] /\
    get_instruction bb (SUC (SUC s.vs_inst_idx)) = SOME ji /\
    ji.inst_opcode = JMP /\ ji.inst_operands = [Label lbl] ==>
    fuel_outcome G ctx fn s 1
      (\t. t = jump_to lbl
        (update_var ctr (c + 1w) (update_var tmp (c + 1w) s)))
Proof
  rpt strip_tac >>
  qabbrev_tac `s1 = (update_var tmp (c + 1w) s) with
                     vs_inst_idx := SUC s.vs_inst_idx` >>
  `!f. run_from f ctx fn s = run_from f ctx fn s1` by
    (gen_tac >> unabbrev_all_tac >> irule run_from_step >>
     qexistsl_tac [`bb`, `ni`] >>
     simp[is_terminator_def, step_inst_base_opcode_eqs,
          exec_pure2_def, eval_operand_def]) >>
  simp[fuel_outcome_def] >>
  `fuel_outcome G ctx fn s1 1
     (\t. t = jump_to lbl (update_var ctr (c + 1w) s1))` suffices_by
    simp[fuel_outcome_def, Abbr `s1`, update_var_def, jump_to_def] >>
  irule wcopy_assign_jump_outcome >> simp[] >>
  qexistsl_tac [`ai`, `bb`, `ji`, `Var tmp`] >>
  simp[Abbr `s1`, update_var_def, eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Straight-line body, stopping before the counter update. *)
Theorem fuel_ok_word_copy_body[local]:
  !counter_var src_op dst_op load_loc store_loc is_ctor imm.
    fuel_ok {} {} {}
      (do
        src_off <- (if word_scale load_loc = 1 then
          emit_op ADD [src_op; Var counter_var]
        else do
          scaled <- emit_op MUL [Var counter_var; Lit (n2w (word_scale load_loc))];
          emit_op ADD [src_op; scaled]
        od);
        val_loaded <- compile_ptr_load is_ctor imm load_loc src_off;
        dst_off <- (if word_scale store_loc = 1 then
          emit_op ADD [dst_op; Var counter_var]
        else do
          scaled <- emit_op MUL [Var counter_var; Lit (n2w (word_scale store_loc))];
          emit_op ADD [dst_op; scaled]
        od);
        compile_ptr_store is_ctor imm store_loc dst_off val_loaded
      od)
Proof
  rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_compile_ptr_load,
             fuel_ok_compile_ptr_store] >>
  simp[is_terminator_def]
QED

(* Compiler-side code frames, keeping intermediate states abstract. *)
Theorem wcopy_emit_op_frame[local]:
  !opc ops sa v sb.
    ~is_terminator opc /\ emit_op opc ops sa = (v,sb) ==>
    sa.cs_next_var <= sb.cs_next_var /\
    ?code. sb.cs_blocks = sa.cs_blocks /\
      sb.cs_current_bb = sa.cs_current_bb /\
      sb.cs_current_insts = sa.cs_current_insts ++ code /\
      EVERY (\i. (i.inst_opcode <> INVALID ==> ~is_terminator i.inst_opcode) /\
        (!x. MEM x i.inst_outputs ==> ~var_below sa.cs_next_var x)) code
Proof
  rpt gen_tac >>
  simp[emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  simp[mk_inst_def, var_below_fresh]
QED

Theorem wcopy_emit_void_frame[local]:
  !opc ops sa v sb.
    (opc <> INVALID ==> ~is_terminator opc) /\
    emit_void opc ops sa = (v,sb) ==>
    sa.cs_next_var <= sb.cs_next_var /\
    ?code. sb.cs_blocks = sa.cs_blocks /\
      sb.cs_current_bb = sa.cs_current_bb /\
      sb.cs_current_insts = sa.cs_current_insts ++ code /\
      EVERY (\i. (i.inst_opcode <> INVALID ==> ~is_terminator i.inst_opcode) /\
        (!x. MEM x i.inst_outputs ==> ~var_below sa.cs_next_var x)) code
Proof
  rpt gen_tac >>
  simp[emit_void_def, emit_inst_def, fresh_id_def, emit_def, comp_bind_def] >>
  rpt strip_tac >> gvs[] >> simp[mk_inst_def]
QED

Theorem wcopy_code_frame_append[local]:
  !sa sb sc a b.
    sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_next_var <= sc.cs_next_var /\
    sb.cs_blocks = sa.cs_blocks /\ sc.cs_blocks = sb.cs_blocks /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sc.cs_current_bb = sb.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ a /\
    sc.cs_current_insts = sb.cs_current_insts ++ b /\
    EVERY (\i. (i.inst_opcode <> INVALID ==> ~is_terminator i.inst_opcode) /\
      (!x. MEM x i.inst_outputs ==> ~var_below sa.cs_next_var x)) a /\
    EVERY (\i. (i.inst_opcode <> INVALID ==> ~is_terminator i.inst_opcode) /\
      (!x. MEM x i.inst_outputs ==> ~var_below sb.cs_next_var x)) b ==>
    sa.cs_next_var <= sc.cs_next_var /\
    sc.cs_blocks = sa.cs_blocks /\ sc.cs_current_bb = sa.cs_current_bb /\
    sc.cs_current_insts = sa.cs_current_insts ++ (a ++ b) /\
    EVERY (\i. (i.inst_opcode <> INVALID ==> ~is_terminator i.inst_opcode) /\
      (!x. MEM x i.inst_outputs ==> ~var_below sa.cs_next_var x)) (a ++ b)
Proof
  rpt gen_tac >> strip_tac >> simp[listTheory.APPEND_ASSOC] >>
  fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  fs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem wcopy_ptr_load_frame[local]:
  !ctor imm loc op sa v sb.
    compile_ptr_load ctor imm loc op sa = (v,sb) ==>
    sa.cs_next_var <= sb.cs_next_var /\
    ?code. sb.cs_blocks = sa.cs_blocks /\
      sb.cs_current_bb = sa.cs_current_bb /\
      sb.cs_current_insts = sa.cs_current_insts ++ code /\
      EVERY (\i. (i.inst_opcode <> INVALID ==> ~is_terminator i.inst_opcode) /\
        (!x. MEM x i.inst_outputs ==> ~var_below sa.cs_next_var x)) code
Proof
  rpt gen_tac >> Cases_on `ctor` >> Cases_on `imm` >> Cases_on `loc` >>
  simp[compile_ptr_load_def, compile_imm_load_word_def] >>
  simp[comp_bind_def] >> rpt strip_tac >>
  TRY (pairarg_tac >> gvs[]) >>
  imp_res_tac wcopy_emit_op_frame >> gvs[is_terminator_def] >>
  fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  fs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem wcopy_ptr_store_frame[local]:
  !ctor imm loc dst value sa v sb.
    compile_ptr_store ctor imm loc dst value sa = (v,sb) ==>
    sa.cs_next_var <= sb.cs_next_var /\
    ?code. sb.cs_blocks = sa.cs_blocks /\
      sb.cs_current_bb = sa.cs_current_bb /\
      sb.cs_current_insts = sa.cs_current_insts ++ code /\
      EVERY (\i. (i.inst_opcode <> INVALID ==> ~is_terminator i.inst_opcode) /\
        (!x. MEM x i.inst_outputs ==> ~var_below sa.cs_next_var x)) code
Proof
  rpt gen_tac >> Cases_on `ctor` >> Cases_on `imm` >> Cases_on `loc` >>
  simp[compile_ptr_store_def, compile_imm_store_word_def] >>
  simp[comp_bind_def] >> rpt strip_tac >>
  TRY (pairarg_tac >> gvs[]) >>
  imp_res_tac wcopy_emit_op_frame >>
  imp_res_tac wcopy_emit_void_frame >> gvs[is_terminator_def] >>
  fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  fs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem wcopy_offset_frame[local]:
  !scale op ctr sa v sb.
    (if scale = 1 then emit_op ADD [op; Var ctr]
     else do scaled <- emit_op MUL [Var ctr; Lit (n2w scale)];
             emit_op ADD [op; scaled] od) sa = (v,sb) ==>
    sa.cs_next_var <= sb.cs_next_var /\
    ?code. sb.cs_blocks = sa.cs_blocks /\
      sb.cs_current_bb = sa.cs_current_bb /\
      sb.cs_current_insts = sa.cs_current_insts ++ code /\
      EVERY (\i. (i.inst_opcode <> INVALID ==> ~is_terminator i.inst_opcode) /\
        (!x. MEM x i.inst_outputs ==> ~var_below sa.cs_next_var x)) code
Proof
  rpt gen_tac >> Cases_on `scale = 1` >> simp[comp_bind_def] >>
  rpt strip_tac >> TRY (pairarg_tac >> gvs[]) >>
  imp_res_tac wcopy_emit_op_frame >> gvs[is_terminator_def] >>
  fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  fs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem wcopy_body_code_frame[local]:
  !ctr src dst ll sl ctor imm sa s1 s2 s3 sb so value d.
    (if word_scale ll = 1 then emit_op ADD [src; Var ctr]
     else do k <- emit_op MUL [Var ctr; Lit (n2w (word_scale ll))];
             emit_op ADD [src; k] od) sa = (so,s1) /\
    compile_ptr_load ctor imm ll so s1 = (value,s2) /\
    (if word_scale sl = 1 then emit_op ADD [dst; Var ctr]
     else do k <- emit_op MUL [Var ctr; Lit (n2w (word_scale sl))];
             emit_op ADD [dst; k] od) s2 = (d,s3) /\
    compile_ptr_store ctor imm sl d value s3 = ((),sb) ==>
    sa.cs_next_var <= sb.cs_next_var /\
    ?code. sb.cs_blocks = sa.cs_blocks /\
      sb.cs_current_bb = sa.cs_current_bb /\
      sb.cs_current_insts = sa.cs_current_insts ++ code /\
      EVERY (\i. (i.inst_opcode <> INVALID ==> ~is_terminator i.inst_opcode) /\
        (!x. MEM x i.inst_outputs ==> ~var_below sa.cs_next_var x)) code
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac wcopy_offset_frame >>
  imp_res_tac wcopy_ptr_load_frame >>
  imp_res_tac wcopy_ptr_store_frame >>
  gvs[] >>
  fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  fs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Successful straight-line execution keeps the label map in the same
   witness as its old-variable frame. *)
Theorem wcopy_straight_framed[local]:
  !code s G ctx fn N bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    callees_stable G ctx fn /\
    EVERY (\i. (i.inst_opcode <> INVALID ==> ~is_terminator i.inst_opcode) /\
      (!x. MEM x i.inst_outputs ==> ~var_below N x)) code ==>
    fuel_outcome G ctx fn s 0
      (\t. t.vs_current_bb = s.vs_current_bb /\
        t.vs_inst_idx = s.vs_inst_idx + LENGTH code /\
        vars_kept N {} s t /\ t.vs_labels = s.vs_labels)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- simp[fuel_outcome_refl] >>
  fs[] >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = h :: rest /\
          isPREFIX code rest` by
    (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]) >>
  drule DROP_EQ_CONS >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    simp[get_instruction_def] >>
  Cases_on `h.inst_opcode = INVALID`
  >- (simp[fuel_outcome_def] >> disj2_tac >> rpt strip_tac >>
      simp[run_from_def, Once exec_block_def, step_inst_non_invoke,
           step_inst_base_opcode_eqs] >>
      simp[Once exec_block_def, step_inst_non_invoke,
           step_inst_base_opcode_eqs]) >>
  `~is_terminator h.inst_opcode` by simp[] >>
  drule_all run_from_nonterm_stable >> strip_tac
  >- (qabbrev_tac `u = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
      `vars_kept N {} s u /\ u.vs_labels = s.vs_labels /\
       u.vs_current_bb = s.vs_current_bb /\
       u.vs_inst_idx = SUC s.vs_inst_idx` by
        (simp[Abbr `u`, vars_kept_def] >> conj_tac
         >- (rpt strip_tac >>
             `~MEM x h.inst_outputs` by metis_tac[] >>
             gvs[lookup_var_def]) >>
         drule_all step_preserves_labels >> simp[]) >>
      first_x_assum (qspecl_then [`u`, `G`, `ctx`, `fn`, `N`, `bb`] mp_tac) >>
      simp[] >> strip_tac >>
      fs[fuel_outcome_def] >>
      disj1_tac >> goal_assum (drule_at Any) >>
      gvs[vars_kept_trans, arithmeticTheory.ADD1] >>
      metis_tac[vars_kept_trans]) >>
  simp[fuel_outcome_def]
QED

(* The loop counts a fresh counter from 0 up to the value of count_op,
   leaving through the exit block when they are equal.  Each round runs
   the body's straight-line code and one JMP back to the condition block.
   count_op was allocated before the loop, and the body writes only the
   counter and variables it allocates itself, so the bound stays fixed and
   the number of rounds is below 2 ** 256. *)
Theorem wcopy_body_framed_outcome[local]:
  !ctr src dst ll sl ctor imm sa s1 s2 s3 sb so value d G ctx fn s.
    (if word_scale ll = 1 then emit_op ADD [src; Var ctr]
     else do k <- emit_op MUL [Var ctr; Lit (n2w (word_scale ll))];
             emit_op ADD [src; k] od) sa = (so,s1) /\
    compile_ptr_load ctor imm ll so s1 = (value,s2) /\
    (if word_scale sl = 1 then emit_op ADD [dst; Var ctr]
     else do k <- emit_op MUL [Var ctr; Lit (n2w (word_scale sl))];
             emit_op ADD [dst; k] od) s2 = (d,s3) /\
    compile_ptr_store ctor imm sl d value s3 = ((),sb) /\
    fn_has_code sa sb fn /\ callees_stable G ctx fn /\ at_point sa s ==>
    fuel_outcome G ctx fn s 0
      (\t. at_point sb t /\ vars_kept sa.cs_next_var {} s t /\
           t.vs_labels = s.vs_labels)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all wcopy_body_code_frame >> strip_tac >>
  fs[fn_has_code_def, at_point_def] >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[rich_listTheory.IS_PREFIX_APPEND] >> simp[listTheory.DROP_APPEND]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all wcopy_straight_framed >>
  simp[fuel_outcome_def, at_point_def] >>
  metis_tac[]
QED

Theorem fuel_okS_compile_word_copy_loop_base:
  !src_op dst_op count_op load_loc store_loc is_ctor imm Wv E.
    fuel_okS (\st. !x. count_op = Var x ==> var_below st.cs_next_var x) Wv {} E
      (compile_word_copy_loop_base src_op dst_op count_op load_loc store_loc
         is_ctor imm)
Proof
  rpt gen_tac >> pure_rewrite_tac [fuel_okS_def] >>
  rpt gen_tac >> strip_tac >>
  drule word_copy_loop_structure >> strip_tac >> simp[] >>
  drule word_copy_loop_cut_points >> strip_tac >>
  FAIL_TAC "assembled compiler cut points; runtime round interface required"
QED
