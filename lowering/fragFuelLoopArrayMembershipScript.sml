(*
 * Fuel bound for the array-membership search loop.
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_array_membership_loop
 *)

Theory fragFuelLoopArrayMembership
Ancestors
  fragFuel fragFuelContextBase exprLowering compileEnv emitHelper context
  venomInst
Libs
  fragFuelLib

(* The normal loader witness keeps both the index and a non-label bound. *)
Theorem loader_keeps_loop_operands[local]:
  !N s t idx op.
    vars_kept N {} s t /\ var_below N idx /\
    (!x. op = Var x ==> var_below N x) /\ (!l. op <> Label l) ==>
    lookup_var idx t = lookup_var idx s /\
    eval_operand op t = eval_operand op s
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[venomStateTheory.eval_operand_def, vars_kept_def] >> metis_tac[]
QED

(* Modular distance decreases even when the index itself wraps.  Its
   uniform bound is wordsTheory.w2n_lt (with dimword(:256) = 2 ** 256). *)
Theorem loop_distance_decreases[local]:
  !(i:256 word) l.
    i <> l ==> w2n (l - (i + 1w)) < w2n (l - i)
Proof
  rpt strip_tac >> rewrite_tac[wordsTheory.WORD_SUB_PLUS] >>
  irule wordsTheory.WORD_PRED_THM >>
  strip_tac >>
  `i + (l - i) = l` by simp[wordsTheory.WORD_SUB_ADD2] >>
  gvs[wordsTheory.WORD_ADD_0]
QED

(* With every jump treated as an exit, the loop has a compositional
   structural certificate; this does not discharge its back edge. *)
Theorem array_membership_loop_open_exits[local]:
  !loader.
    (!a Wv E. fuel_ok Wv {} E (loader a)) ==>
    !needle arr_op len_op elem_size offset_base bound_opt is_in Wv.
      fuel_ok Wv {} UNIV
        (compile_array_membership_loop needle arr_op len_op elem_size
           offset_base loader bound_opt is_in)
Proof
  rpt strip_tac >> rewrite_tac[compile_array_membership_loop_def] >>
  Cases_on `bound_opt` >>
  fuel_auto [fuel_ok_emit_inst_jmp, fuel_ok_emit_inst_jnz,
             fuel_ok_emit_inst, fuel_ok_emit_op] >>
  simp[is_terminator_def] >>
  fuel_auto [fuel_ok_emit_inst_jmp, fuel_ok_emit_inst_jnz,
             fuel_ok_emit_inst, fuel_ok_emit_op] >>
  simp[is_terminator_def]
QED

(* Compiler-run cuts.  Each block-opening operation stays with its
   predecessor, so all named block entries are empty. *)
Theorem array_membership_loop_run_cuts[local]:
  !needle arr_op len_op elem_size offset_base loader bound_opt is_in st r st'.
    compile_array_membership_loop needle arr_op len_op elem_size
      offset_base loader bound_opt is_in st = (r, st') ==>
    ?res idx cond body found incr exit C B addr A val Z F I X u1 u2 u3 u4.
      (do res <- fresh_var;
          entry <- fresh_label "in_entry";
          cond <- fresh_label "in_cond";
          body <- fresh_label "in_body";
          found <- fresh_label "in_found";
          incr <- fresh_label "in_incr";
          exit <- fresh_label "in_exit";
          emit_inst JMP [Label entry] [];
          new_block entry;
          idx <- fresh_var;
          emit_inst ASSIGN [Lit 0w] [idx];
          emit_inst ASSIGN [Lit 0w] [res];
          (case bound_opt of
             SOME cap => do inv <- emit_op GT [len_op; Lit (n2w cap)];
                            valid <- emit_op ISZERO [inv];
                            emit_inst ASSERT [valid] [] od
           | NONE => return ());
          emit_inst JMP [Label cond] [];
          new_block cond;
          return (res,idx,cond,body,found,incr,exit)
       od) st = ((res,idx,cond,body,found,incr,exit), C) /\
      (do d <- emit_op EQ [Var idx; len_op];
          emit_inst JNZ [d; Label exit; Label body] [];
          new_block body od) C = (u1, B) /\
      (do off <- emit_op MUL [Var idx; Lit (n2w elem_size)];
          total <- (if offset_base > 0 then
                      emit_op ADD [Lit (n2w offset_base); off]
                    else return off);
          emit_op ADD [arr_op; total] od) B = (addr,A) /\
      loader addr A = (val,Z) /\
      (do m <- emit_op EQ [val; needle];
          emit_inst JNZ [m; Label found; Label incr] [];
          new_block found od) Z = (u2,F) /\
      (do emit_inst ASSIGN [Lit 1w] [res];
          emit_inst JMP [Label exit] [];
          new_block incr od) F = (u3,I) /\
      (do n <- emit_op ADD [Var idx; Lit 1w];
          emit_inst ASSIGN [n] [idx];
          emit_inst JMP [Label cond] [];
          new_block exit od) I = (u4,X) /\
      (if is_in then return (Var res) else emit_op ISZERO [Var res]) X = (r,st')
Proof
  simp[compile_array_membership_loop_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, pairTheory.UNCURRY_EQ] >>
  rpt strip_tac >> simp[]
QED

(* Small instruction cuts apply to both comparisons without reselecting
   the whole loop's layout witnesses. *)
Theorem array_membership_compare_cut[local]:
  (do d <- emit_op EQ [a;b];
      emit_inst JNZ [d;Label yes;Label no] [];
      new_block next od) s = (u,t) ==>
  ?d T U. emit_op EQ [a;b] s = (d,T) /\
          emit_inst JNZ [d;Label yes;Label no] [] T = ((),U) /\
          new_block next U = (u,t)
Proof
  simp[comp_bind_def, comp_ignore_bind_def, pairTheory.UNCURRY_EQ] >>
  rpt strip_tac >> simp[]
QED

Theorem array_membership_incr_cut[local]:
  (do n <- emit_op ADD [Var idx;Lit 1w];
      emit_inst ASSIGN [n] [idx];
      emit_inst JMP [Label cond] [];
      new_block exit od) s = (u,t) ==>
  ?n T U V. emit_op ADD [Var idx;Lit 1w] s = (n,T) /\
      emit_inst ASSIGN [n] [idx] T = ((),U) /\
      emit_inst JMP [Label cond] [] U = ((),V) /\
      new_block exit V = (u,t)
Proof
  simp[comp_bind_def, comp_ignore_bind_def, pairTheory.UNCURRY_EQ] >>
  rpt strip_tac >> simp[]
QED

Theorem array_membership_found_cut[local]:
  (do emit_inst ASSIGN [Lit 1w] [res];
      emit_inst JMP [Label exit] [];
      new_block incr od) s = (u,t) ==>
  ?T U. emit_inst ASSIGN [Lit 1w] [res] s = ((),T) /\
      emit_inst JMP [Label exit] [] T = ((),U) /\
      new_block incr U = (u,t)
Proof
  simp[comp_bind_def, comp_ignore_bind_def, pairTheory.UNCURRY_EQ] >>
  rpt strip_tac >> simp[]
QED

Theorem array_membership_compare_structure[local]:
  (do d <- emit_op EQ [a;b];
      emit_inst JNZ [d;Label yes;Label no] [];
      new_block next od) s = (u,t) ==>
  cs_extends s t /\ s.cs_next_var <= t.cs_next_var /\
  (cs_no_phi s ==> cs_no_phi t) /\
  t.cs_current_bb = next /\ t.cs_current_insts = [] /\
  ?K. frag_fuel {} {} {yes;no} s t K
Proof
  strip_tac >>
  `fuel_ok {} {} {yes;no}
    (do d <- emit_op EQ [a;b];
        emit_inst JNZ [d;Label yes;Label no] [];
        new_block next od)` by
    (fuel_auto [fuel_ok_emit_inst_jnz, fuel_ok_emit_op] >>
     simp[is_terminator_def]) >>
  drule (iffLR fuel_ok_def) >>
  disch_then drule >> strip_tac >> simp[] >>
  drule array_membership_compare_cut >>
  simp[new_block_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem array_membership_incr_structure[local]:
  (do n <- emit_op ADD [Var idx;Lit 1w];
      emit_inst ASSIGN [n] [idx];
      emit_inst JMP [Label cond] [];
      new_block exit od) s = (u,t) ==>
  cs_extends s t /\ s.cs_next_var <= t.cs_next_var /\
  (cs_no_phi s ==> cs_no_phi t) /\
  t.cs_current_bb = exit /\ t.cs_current_insts = []
Proof
  strip_tac >>
  `fuel_ok UNIV {} UNIV
    (do n <- emit_op ADD [Var idx;Lit 1w];
        emit_inst ASSIGN [n] [idx];
        emit_inst JMP [Label cond] [];
        new_block exit od)` by
    (fuel_auto [fuel_ok_emit_inst_jmp, fuel_ok_emit_inst,
                fuel_ok_emit_op] >> simp[is_terminator_def]) >>
  drule (iffLR fuel_ok_def) >>
  disch_then drule >> strip_tac >> simp[] >>
  drule array_membership_incr_cut >>
  simp[new_block_def] >> rpt strip_tac >> gvs[]
QED

Theorem array_membership_found_structure[local]:
  (do emit_inst ASSIGN [Lit 1w] [res];
      emit_inst JMP [Label exit] [];
      new_block incr od) s = (u,t) ==>
  cs_extends s t /\ s.cs_next_var <= t.cs_next_var /\
  (cs_no_phi s ==> cs_no_phi t) /\
  t.cs_current_bb = incr /\ t.cs_current_insts = [] /\
  ?K. frag_fuel {res} {} {exit} s t K
Proof
  strip_tac >>
  `fuel_ok {res} {} {exit}
    (do emit_inst ASSIGN [Lit 1w] [res];
        emit_inst JMP [Label exit] [];
        new_block incr od)` by
    (fuel_auto [fuel_ok_emit_inst_jmp, fuel_ok_emit_inst] >>
     simp[is_terminator_def]) >>
  drule (iffLR fuel_ok_def) >>
  disch_then drule >> strip_tac >> simp[] >>
  drule array_membership_found_cut >>
  simp[new_block_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem array_membership_address_structure[local]:
  (do off <- emit_op MUL [Var idx; Lit (n2w elem_size)];
      total <- (if offset_base > 0 then
                  emit_op ADD [Lit (n2w offset_base);off]
                else return off);
      emit_op ADD [arr_op;total] od) s = (addr,t) ==>
  cs_extends s t /\ s.cs_next_var <= t.cs_next_var /\
  (cs_no_phi s ==> cs_no_phi t) /\
  ?K. frag_fuel {} {} {} s t K
Proof
  strip_tac >>
  `fuel_ok {} {} {}
    (do off <- emit_op MUL [Var idx; Lit (n2w elem_size)];
        total <- (if offset_base > 0 then
                    emit_op ADD [Lit (n2w offset_base);off]
                  else return off);
        emit_op ADD [arr_op;total] od)` by
    (Cases_on `offset_base > 0` >>
     fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def]) >>
  drule (iffLR fuel_ok_def) >> disch_then drule >> simp[]
QED

Theorem array_membership_tail_structure[local]:
  (if is_in then return (Var res) else emit_op ISZERO [Var res]) s = (r,t) ==>
  cs_extends s t /\ s.cs_next_var <= t.cs_next_var /\
  (cs_no_phi s ==> cs_no_phi t)
Proof
  strip_tac >>
  `fuel_ok UNIV {} UNIV
    (if is_in then return (Var res) else emit_op ISZERO [Var res])` by
    (Cases_on `is_in` >> simp[] >> fuel_auto [fuel_ok_emit_op] >>
     simp[is_terminator_def]) >>
  drule (iffLR fuel_ok_def) >> disch_then drule >> simp[]
QED

Theorem array_membership_entry_structure[local]:
  !len_op bound_opt s res idx cond body found incr exit t.
  (do res <- fresh_var;
      entry <- fresh_label "in_entry";
      cond <- fresh_label "in_cond";
      body <- fresh_label "in_body";
      found <- fresh_label "in_found";
      incr <- fresh_label "in_incr";
      exit <- fresh_label "in_exit";
      emit_inst JMP [Label entry] [];
      new_block entry;
      idx <- fresh_var;
      emit_inst ASSIGN [Lit 0w] [idx];
      emit_inst ASSIGN [Lit 0w] [res];
      (case bound_opt of
         SOME cap => do inv <- emit_op GT [len_op;Lit (n2w cap)];
                        valid <- emit_op ISZERO [inv];
                        emit_inst ASSERT [valid] [] od
       | NONE => return ());
      emit_inst JMP [Label cond] [];
      new_block cond;
      comp_return (res,idx,cond,body,found,incr,exit)
   od) (s:compile_state) = ((res,idx,cond,body,found,incr,exit),t) ==>
  cs_extends s t /\ s.cs_next_var <= t.cs_next_var /\
  (cs_no_phi s ==> cs_no_phi t) /\
  t.cs_current_bb = cond /\ t.cs_current_insts = [] /\
  ~var_below s.cs_next_var res /\ ~var_below s.cs_next_var idx /\
  res <> idx /\ var_below t.cs_next_var res /\ var_below t.cs_next_var idx
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `action s` >>
  `fuel_ok UNIV {} UNIV action` by
    (unabbrev_all_tac >> Cases_on `bound_opt` >> simp[] >>
     fuel_auto [fuel_ok_emit_inst_jmp, fuel_ok_emit_inst,
                fuel_ok_emit_op] >> simp[is_terminator_def] >>
     fuel_auto [fuel_ok_emit_inst_jmp, fuel_ok_emit_inst,
                fuel_ok_emit_op] >> simp[is_terminator_def]) >>
  drule (iffLR fuel_ok_def) >> disch_then drule >> strip_tac >> simp[] >>
  qpat_x_assum `Abbrev _` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_label_def, new_block_def,
      emit_inst_def, emit_op_def, fresh_id_def, emit_def,
      pairTheory.UNCURRY_EQ] >>
  Cases_on `bound_opt` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_label_def, new_block_def,
      emit_inst_def, emit_op_def, fresh_id_def, emit_def,
      pairTheory.UNCURRY_EQ, var_below_def]
QED

(* The two comparison instructions are adjacent, even when the next
   compiler block is different from either runtime branch target. *)
Theorem array_membership_compare_code[local]:
  !a b yes no next C u B fn.
  (do d <- emit_op EQ [a;b];
      emit_inst JNZ [d;Label yes;Label no] [];
      new_block next od) C = (u,B) /\ fn_has_code C B fn ==>
  ?bb. lookup_block C.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH C.cs_current_insts) =
      SOME (mk_inst C.cs_next_id EQ [a;b]
        [STRING #"%" (toString C.cs_next_var)]) /\
    get_instruction bb (SUC (LENGTH C.cs_current_insts)) =
      SOME (mk_inst (C.cs_next_id + 1) JNZ
        [Var (STRING #"%" (toString C.cs_next_var));Label yes;Label no] [])
Proof
  rpt gen_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_inst_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def, new_block_def] >>
  strip_tac >> gvs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  simp[venomInstTheory.get_instruction_def, listTheory.EL_APPEND_EQN,
       arithmeticTheory.ADD1]
QED

Theorem array_membership_cond_outcome[local]:
  !idx len_op exit body C u B fn G ctx s i l N.
  (do d <- emit_op EQ [Var idx;len_op];
      emit_inst JNZ [d;Label exit;Label body] [];
      new_block body od) C = (u,B) /\
  fn_has_code C B fn /\ no_phi_fn fn /\ at_point C s /\
  N <= C.cs_next_var /\ var_below C.cs_next_var idx /\
  (!x. len_op = Var x ==> var_below C.cs_next_var x) /\
  (!lbl. len_op <> Label lbl) /\
  lookup_var idx s = SOME i /\ eval_operand len_op s = SOME l ==>
  ?j. j <= 1 /\ fuel_outcome G ctx fn s j
    (\t. vars_kept N {} s t /\ lookup_var idx t = SOME i /\
         eval_operand len_op t = SOME l /\ t.vs_inst_idx = 0 /\
         ((i=l /\ t.vs_current_bb=exit) \/
          (i<>l /\ t.vs_current_bb=body)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all array_membership_compare_code >> strip_tac >>
  qmatch_asmsub_abbrev_tac `Var q` >>
  qabbrev_tac `v = (update_var q (if i=l then 1w else 0w) s)
                    with vs_inst_idx := SUC s.vs_inst_idx` >>
  `!f. run_from f ctx fn s = run_from f ctx fn v` by
    (gen_tac >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
       gvs[at_point_def] >>
     `get_instruction bb s.vs_inst_idx =
        SOME (mk_inst C.cs_next_id EQ [Var idx;len_op] [q])` by
       gvs[at_point_def] >>
     drule run_from_nonterm >>
     disch_then (qspecl_then [`f`,`ctx`] mp_tac) >>
     disch_then drule >>
     simp[venomInstTheory.is_terminator_def, venomInstTheory.mk_inst_def,
          at_point_def] >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke,
          venomExecSemanticsTheory.step_inst_base_opcode_eqs,
          venomInstTheory.mk_inst_def,
          venomExecSemanticsTheory.exec_pure2_def,
          venomExecSemanticsTheory.bool_to_word_def,
          venomStateTheory.eval_operand_def, Abbr `v`] >>
     Cases_on `i=l` >> simp[venomExecSemanticsTheory.bool_to_word_def]) >>
  qexists_tac `1` >> simp[] >>
  qmatch_goalsub_abbrev_tac `fuel_outcome _ _ _ _ _ P` >>
  `fuel_outcome G ctx fn v 1 P` suffices_by simp[fuel_outcome_def] >>
  irule fuel_outcome_jump >> simp[] >>
  rename1 `get_instruction bb (SUC _) =
    SOME (mk_inst _ JNZ [Var _;Label _;Label body_lbl] [])` >>
  qexistsl_tac [`bb`,
    `mk_inst (C.cs_next_id + 1) JNZ [Var q;Label exit;Label body_lbl] []`,
    `if i=l then exit else body_lbl`] >>
  simp[Abbr `v`, at_point_def, venomStateTheory.update_var_def,
       venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def] >>
  gvs[at_point_def] >> Cases_on `i=l` >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, Abbr `P`,
       venomStateTheory.jump_to_def, vars_kept_def,
       venomStateTheory.lookup_var_def] >>
  `~var_below C.cs_next_var q` by simp[Abbr `q`, var_below_fresh] >>
  `~var_below N q` by simp[Abbr `q`, var_below_fresh] >>
  `q <> idx` by metis_tac[] >>
  simp[venomInstTheory.mk_inst_def] >> strip_tac >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  simp[] >> Cases_on `len_op` >>
  gvs[venomStateTheory.eval_operand_def,
      venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem array_membership_cond_failed[local]:
  !idx len_op exit body C u B fn G ctx s.
  (do d <- emit_op EQ [Var idx;len_op];
      emit_inst JNZ [d;Label exit;Label body] [];
      new_block body od) C = (u,B) /\
  fn_has_code C B fn /\ at_point C s /\
  (lookup_var idx s = NONE \/ eval_operand len_op s = NONE) ==>
  fuel_outcome G ctx fn s 0 (\t. F)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all array_membership_compare_code >> strip_tac >>
  simp[fuel_outcome_def] >>
  `!f. run_from f ctx fn s = Error "undefined operand"` suffices_by
    (strip_tac >> simp[]) >>
  gen_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    gvs[at_point_def] >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst C.cs_next_id EQ [Var idx;len_op]
      [STRING #"%" (toString C.cs_next_var)])` by gvs[at_point_def] >>
  drule run_from_nonterm >>
  disch_then (qspecl_then [`f`,`ctx`] mp_tac) >> disch_then drule >>
  simp[venomInstTheory.is_terminator_def, venomInstTheory.mk_inst_def,
       venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_pure2_def,
       venomStateTheory.eval_operand_def] >>
  Cases_on `lookup_var idx s` >> simp[]
QED

Theorem array_membership_nonterm_outcome[local]:
  !s fn bb inst ctx t G j P.
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\
  (!f. step_inst f ctx inst s = OK t) /\
  fuel_outcome G ctx fn (t with vs_inst_idx := SUC s.vs_inst_idx) j P ==>
  fuel_outcome G ctx fn s j P
Proof
  rpt strip_tac >>
  `!f. run_from f ctx fn s =
       run_from f ctx fn (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    (gen_tac >> drule_all run_from_nonterm >> simp[]) >>
  gvs[fuel_outcome_def] >> metis_tac[]
QED

Theorem array_membership_incr_code[local]:
  !idx cond exit C u B fn.
  (do n <- emit_op ADD [Var idx;Lit 1w];
      emit_inst ASSIGN [n] [idx];
      emit_inst JMP [Label cond] [];
      new_block exit od) C = (u,B) /\ fn_has_code C B fn ==>
  ?bb. lookup_block C.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH C.cs_current_insts) =
      SOME (mk_inst C.cs_next_id ADD [Var idx;Lit 1w]
        [STRING #"%" (toString C.cs_next_var)]) /\
    get_instruction bb (SUC (LENGTH C.cs_current_insts)) =
      SOME (mk_inst (C.cs_next_id + 1) ASSIGN
        [Var (STRING #"%" (toString C.cs_next_var))] [idx]) /\
    get_instruction bb (SUC (SUC (LENGTH C.cs_current_insts))) =
      SOME (mk_inst (C.cs_next_id + 2) JMP [Label cond] [])
Proof
  rpt gen_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_inst_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def, new_block_def] >>
  strip_tac >> gvs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  simp[venomInstTheory.get_instruction_def, listTheory.EL_APPEND_EQN,
       arithmeticTheory.ADD1]
QED

Theorem array_membership_incr_outcome[local]:
  !idx len_op cond exit C u B fn G ctx s i l N.
  (do n <- emit_op ADD [Var idx;Lit 1w];
      emit_inst ASSIGN [n] [idx];
      emit_inst JMP [Label cond] [];
      new_block exit od) C = (u,B) /\
  fn_has_code C B fn /\ no_phi_fn fn /\ at_point C s /\
  N <= C.cs_next_var /\ var_below C.cs_next_var idx /\
  ~var_below N idx /\
  (!x. len_op = Var x ==> var_below N x) /\
  (!lbl. len_op <> Label lbl) /\
  lookup_var idx s = SOME i /\ eval_operand len_op s = SOME l ==>
  ?j. j <= 1 /\ fuel_outcome G ctx fn s j
    (\t. vars_kept N {} s t /\ lookup_var idx t = SOME (i+1w) /\
         eval_operand len_op t = SOME l /\ t.vs_current_bb = cond /\
         t.vs_inst_idx = 0)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all array_membership_incr_code >> strip_tac >>
  qmatch_asmsub_abbrev_tac `Var q` >>
  `q <> idx` by metis_tac[var_below_fresh, arithmeticTheory.LESS_EQ_REFL] >>
  qexists_tac `1` >> simp[] >>
  irule array_membership_nonterm_outcome >>
  qexistsl_tac [`bb`, `mk_inst C.cs_next_id ADD [Var idx;Lit 1w] [q]`,
               `update_var q (i+1w) s`] >>
  simp[at_point_def, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def,
       venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_pure2_def,
       venomStateTheory.eval_operand_def] >>
  gvs[at_point_def, GSYM venomInstTheory.mk_inst_def] >>
  irule array_membership_nonterm_outcome >>
  qexistsl_tac [`bb`, `mk_inst (C.cs_next_id + 1) ASSIGN [Var q] [idx]`,
    `update_var idx (i+1w) (update_var q (i+1w) s)
      with vs_inst_idx := SUC (LENGTH C.cs_current_insts)`] >>
  simp[venomStateTheory.update_var_def, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def,
       venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  irule fuel_outcome_jump >> simp[] >>
  qexists_tac `cond` >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomStateTheory.jump_to_def, vars_kept_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `~var_below N q` by simp[Abbr `q`, var_below_fresh] >>
  simp[GSYM venomInstTheory.mk_inst_def] >> strip_tac >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  Cases_on `len_op` >>
  gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem array_membership_kept_refine[local]:
  !M W s t N idx len_op.
  vars_kept M W s t /\ N<=M /\ var_below M idx /\ idx NOTIN W /\
  (!x. var_below N x ==> x NOTIN W) /\
  (!x. len_op=Var x ==> var_below N x) /\ (!l. len_op<>Label l) ==>
  vars_kept N {} s t /\ lookup_var idx t=lookup_var idx s /\
  eval_operand len_op t=eval_operand len_op s
Proof
  rpt strip_tac
  >- (gvs[vars_kept_def] >> rpt strip_tac >> first_x_assum irule >>
      simp[] >> gvs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS])
  >- metis_tac[vars_kept_def] >>
  Cases_on `len_op` >> gvs[venomStateTheory.eval_operand_def] >>
  gvs[vars_kept_def] >> first_x_assum irule >> simp[] >>
  gvs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem array_membership_frag_outcome[local]:
  !C D K W E N idx len_op fn G ctx.
  frag_fuel W {} E C D K /\ N<=C.cs_next_var /\
  var_below C.cs_next_var idx /\ idx NOTIN W /\
  (!x. var_below N x ==> x NOTIN W) /\
  (!x. len_op=Var x ==> var_below N x) /\ (!lbl. len_op<>Label lbl) /\
  no_phi_fn fn /\ fn_has_code C D fn /\ callees_stable G ctx fn ==>
  !s i l. at_point C s /\ lookup_var idx s=SOME i /\
    eval_operand len_op s=SOME l ==>
  ?j. j<=K /\ fuel_outcome G ctx fn s j
    (\t. vars_kept N {} s t /\ lookup_var idx t=SOME i /\
         eval_operand len_op t=SOME l /\
         (at_point D t \/ (t.vs_current_bb IN E /\ t.vs_inst_idx=0)))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `frag_fuel Wv {} E C D Kb` >>
  `?j. j<=Kb /\ fuel_outcome G ctx fn s j
    (\t. vars_kept C.cs_next_var Wv s t /\
         (at_point D t \/ (t.vs_current_bb IN E /\ t.vs_inst_idx=0)))` by
    (irule (iffLR frag_fuel_def) >> simp[] >>
     qexistsl_tac [`{}`, `C`] >> simp[]) >>
  qexists_tac `j` >> simp[] >> irule fuel_outcome_weaken >>
  goal_assum (drule_at Any) >> rpt strip_tac >> simp[] >>
  metis_tac[array_membership_kept_refine]
QED

Theorem array_membership_body_outcome[local]:
  !idx len_op arr_op elem_size offset_base addr elem needle res found incr exit
    B A Z F I u2 u3 N KL.
  (do off <- emit_op MUL [Var idx;Lit (n2w elem_size)];
      total <- (if offset_base > 0 then
                  emit_op ADD [Lit (n2w offset_base);off] else return off);
      emit_op ADD [arr_op;total] od) B = (addr,A) /\
  (do m <- emit_op EQ [elem;needle];
      emit_inst JNZ [m;Label found;Label incr] [];
      new_block found od) Z = (u2,F) /\
  (do emit_inst ASSIGN [Lit 1w] [res];
      emit_inst JMP [Label exit] []; new_block incr od) F = (u3,I) /\
  N <= B.cs_next_var /\ B.cs_next_var <= Z.cs_next_var /\
  var_below B.cs_next_var idx /\ ~var_below N res /\ idx <> res /\
  (!x. len_op=Var x ==> var_below N x) /\ (!lbl. len_op<>Label lbl) ==>
  ?Kbody. !fn G ctx.
  fn_has_code B A fn /\ fn_has_code Z F fn /\ fn_has_code F I fn /\
  no_phi_fn fn /\ callees_stable G ctx fn /\
  (!s. at_point A s ==> ?j. j<=KL /\ fuel_outcome G ctx fn s j
    (\t. at_point Z t /\ vars_kept N {} s t /\
         lookup_var idx t=lookup_var idx s /\
         eval_operand len_op t=eval_operand len_op s)) ==>
  !s i l. at_point B s /\ lookup_var idx s=SOME i /\
    eval_operand len_op s=SOME l ==>
    ?j. j<=Kbody /\ fuel_outcome G ctx fn s j
      (\t. vars_kept N {} s t /\ lookup_var idx t=SOME i /\
           eval_operand len_op t=SOME l /\ t.vs_inst_idx=0 /\
           (t.vs_current_bb=exit \/ t.vs_current_bb=incr))
Proof
  rpt gen_tac >> strip_tac >>
  drule array_membership_address_structure >> strip_tac >>
  drule array_membership_compare_structure >> strip_tac >>
  drule array_membership_found_structure >> strip_tac >>
  rename1 `frag_fuel {} {} {} B A Ka` >>
  rename1 `frag_fuel {} {} {found;incr} Z SF Kc` >>
  rename1 `frag_fuel {res} {} {exit} SF SI Kf` >>
  `N <= Z.cs_next_var /\ N <= SF.cs_next_var /\
   var_below Z.cs_next_var idx /\ var_below SF.cs_next_var idx` by
    (gvs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  suspend "compose_segments"
QED

Resume array_membership_body_outcome[compose_segments]:
  qexists_tac `Ka + KL + Kc + Kf` >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `?ja. ja<=Ka /\ fuel_outcome G ctx fn s ja
    (\t. vars_kept N {} s t /\ lookup_var idx t=SOME i /\
         eval_operand len_op t=SOME l /\
         (at_point A t \/ (t.vs_current_bb IN {} /\ t.vs_inst_idx=0)))` by
    (irule array_membership_frag_outcome >> simp[] >>
     qexistsl_tac [`B`, `{}`] >> simp[]) >>
  qabbrev_tac `Q = \t. vars_kept N {} s t /\ lookup_var idx t=SOME i /\
    eval_operand len_op t=SOME l /\ t.vs_inst_idx=0 /\
    (t.vs_current_bb=exit \/ t.vs_current_bb=incr)` >>
  `?j. j <= ja + (KL + (Kc + Kf)) /\ fuel_outcome G ctx fn s j Q`
    suffices_by (strip_tac >> qexists_tac `j` >> simp[] >> decide_tac) >>
  irule fuel_outcome_compose >> goal_assum (drule_at Any) >>
  qx_gen_tac `sa` >> simp[] >> strip_tac >>
  qpat_x_assum `!s. at_point A s ==> _` drule >> strip_tac >>
  rename1 `jl <= KL` >>
  `?j. j <= jl + (Kc + Kf) /\ fuel_outcome G ctx fn sa j Q`
    suffices_by (strip_tac >> qexists_tac `j` >> simp[] >> decide_tac) >>
  irule fuel_outcome_compose >> goal_assum (drule_at Any) >>
  qx_gen_tac `sz` >> simp[] >> strip_tac >>
  `?jc. jc<=Kc /\ fuel_outcome G ctx fn sz jc
    (\t. vars_kept N {} sz t /\ lookup_var idx t=SOME i /\
         eval_operand len_op t=SOME l /\
         (at_point SF t \/ (t.vs_current_bb IN {found;incr} /\ t.vs_inst_idx=0)))` by
    (irule array_membership_frag_outcome >> simp[] >>
     qexistsl_tac [`Z`, `{}`] >> simp[]) >>
  `?j. j <= jc + Kf /\ fuel_outcome G ctx fn sz j Q`
    suffices_by (strip_tac >> qexists_tac `j` >> simp[] >> decide_tac) >>
  irule fuel_outcome_compose >> goal_assum (drule_at Any) >>
  qx_gen_tac `sc` >> simp[] >> strip_tac >>
  (Cases_on `sc.vs_current_bb=incr`
  >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_refl >>
      simp[Abbr `Q`] >>
      metis_tac[vars_kept_trans, at_point_def, listTheory.LENGTH_NIL]) >>
  `at_point SF sc` by
    (gvs[at_point_def] >> metis_tac[]) >>
  `?jf. jf<=Kf /\ fuel_outcome G ctx fn sc jf
    (\t. vars_kept N {} sc t /\ lookup_var idx t=SOME i /\
         eval_operand len_op t=SOME l /\
         (at_point SI t \/ (t.vs_current_bb IN {exit} /\ t.vs_inst_idx=0)))` by
    (irule array_membership_frag_outcome >> simp[] >>
     qexistsl_tac [`SF`, `{res}`] >> simp[] >> metis_tac[]) >>
  qexists_tac `jf` >> simp[] >> irule fuel_outcome_weaken >>
  goal_assum (drule_at Any) >> simp[Abbr `Q`, at_point_def] >>
  metis_tac[vars_kept_trans])
QED

Finalise array_membership_body_outcome

Theorem array_membership_loop_round[local]:
  !idx len_op arr_op elem_size offset_base addr elem needle res cond body found incr exit
    C B A Z F I X u1 u2 u3 u4 N KL.
  (do d <- emit_op EQ [Var idx;len_op];
      emit_inst JNZ [d;Label exit;Label body] []; new_block body od) C=(u1,B) /\
  (do off <- emit_op MUL [Var idx;Lit (n2w elem_size)];
      total <- (if offset_base > 0 then
                  emit_op ADD [Lit (n2w offset_base);off] else return off);
      emit_op ADD [arr_op;total] od) B=(addr,A) /\
  (do m <- emit_op EQ [elem;needle];
      emit_inst JNZ [m;Label found;Label incr] []; new_block found od) Z=(u2,F) /\
  (do emit_inst ASSIGN [Lit 1w] [res];
      emit_inst JMP [Label exit] []; new_block incr od) F=(u3,I) /\
  (do n <- emit_op ADD [Var idx;Lit 1w]; emit_inst ASSIGN [n] [idx];
      emit_inst JMP [Label cond] []; new_block exit od) I=(u4,X) /\
  C.cs_current_bb=cond /\ C.cs_current_insts=[] /\
  N<=C.cs_next_var /\ C.cs_next_var<=B.cs_next_var /\
  B.cs_next_var<=Z.cs_next_var /\ Z.cs_next_var<=I.cs_next_var /\
  var_below C.cs_next_var idx /\ ~var_below N idx /\
  ~var_below N res /\ idx<>res /\
  (!x. len_op=Var x ==> var_below N x) /\ (!lbl. len_op<>Label lbl) /\
  (!i l:256 word. i<>l ==> w2n(l-(i+1w)) < w2n(l-i)) ==>
  ?Kround. !fn G ctx.
  fn_has_code C B fn /\ fn_has_code B A fn /\ fn_has_code Z F fn /\
  fn_has_code F I fn /\ fn_has_code I X fn /\
  no_phi_fn fn /\ callees_stable G ctx fn /\
  (!s. at_point A s ==> ?j. j<=KL /\ fuel_outcome G ctx fn s j
    (\t. at_point Z t /\ vars_kept N {} s t /\
         lookup_var idx t=lookup_var idx s /\
         eval_operand len_op t=eval_operand len_op s)) ==>
  !s i l. at_point C s /\ lookup_var idx s=SOME i /\
    eval_operand len_op s=SOME l ==>
    ?j. j<=Kround /\ fuel_outcome G ctx fn s j
      (\t. vars_kept N {} s t /\
        (at_point X t \/ (at_point C t /\ eval_operand len_op t=SOME l /\
          ?i'. lookup_var idx t=SOME i' /\ w2n(l-i') < w2n(l-i))))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `(do m <- emit_op EQ [elem;needle];
      emit_inst JNZ [m;Label found;Label incr] []; new_block found od) Z=(u2,SF)` >>
  rename1 `(do n <- emit_op ADD [Var idx;Lit 1w]; emit_inst ASSIGN [n] [idx];
      emit_inst JMP [Label cond] []; new_block exit od) SI=(u4,X)` >>
  rename1 `(do d <- emit_op EQ [Var idx;len_op];
      emit_inst JNZ [d;Label exit;Label body_lbl] []; new_block body_lbl od) C=(u1,B)` >>
  `B.cs_current_bb=body_lbl /\ B.cs_current_insts=[]` by
    metis_tac[array_membership_compare_structure] >>
  drule array_membership_incr_structure >> strip_tac >>
  drule array_membership_found_structure >> strip_tac >>
  `N<=B.cs_next_var /\ N<=SI.cs_next_var /\
   var_below B.cs_next_var idx /\ var_below SI.cs_next_var idx /\
   (!x. len_op=Var x ==> var_below C.cs_next_var x)` by
    (gvs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  drule_all array_membership_body_outcome >>
  disch_then (qspec_then `KL` (qx_choose_then `Kb` assume_tac)) >>
  suspend "compose_round"
QED

Resume array_membership_loop_round[compose_round]:
  qexists_tac `1+Kb+1` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!fn G ctx. _`
    (qspecl_then [`fn`,`G`,`ctx`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule_all array_membership_cond_outcome >>
  disch_then (qspecl_then [`G`,`ctx`] mp_tac) >>
  disch_then (qx_choose_then `jc` strip_assume_tac) >>
  qabbrev_tac `Q = \t. vars_kept N {} s t /\
    (at_point X t \/ (at_point C t /\ eval_operand len_op t=SOME l /\
      ?i'. lookup_var idx t=SOME i' /\ w2n(l-i') < w2n(l-i)))` >>
  `?j. j<=jc+(Kb+1) /\ fuel_outcome G ctx fn s j Q`
    suffices_by (strip_tac >> qexists_tac `j` >> simp[] >> decide_tac) >>
  irule fuel_outcome_compose >> goal_assum (drule_at Any) >>
  qx_gen_tac `sb` >> simp[] >> strip_tac >>
  (Cases_on `i=l`
  >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_refl >>
      gvs[Abbr `Q`, at_point_def]) >>
  gvs[] >>
  `at_point B sb` by gvs[at_point_def] >>
  qpat_x_assum `!s i l. at_point B s /\ _ ==> _` drule >>
  disch_then (qspecl_then [`i`,`l`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `jb` strip_assume_tac) >>
  `?j. j<=jb+1 /\ fuel_outcome G ctx fn sb j Q`
    suffices_by (strip_tac >> qexists_tac `j` >> simp[] >> decide_tac) >>
  irule fuel_outcome_compose >> goal_assum (drule_at Any) >>
  qx_gen_tac `si` >> simp[] >> strip_tac >>
  (Cases_on `si.vs_current_bb=X.cs_current_bb`
  >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_refl >>
      simp[Abbr `Q`, at_point_def] >> metis_tac[vars_kept_trans]) >>
  gvs[] >>
  `at_point SI si` by gvs[at_point_def] >>
  `N<=SI.cs_next_var` by decide_tac >>
  drule_all array_membership_incr_outcome >>
  disch_then (qspecl_then [`G`,`ctx`] mp_tac) >>
  disch_then (qx_choose_then `ji` strip_assume_tac) >>
  qexists_tac `ji` >> simp[] >> irule fuel_outcome_weaken >>
  goal_assum (drule_at Any) >> simp[Abbr `Q`, at_point_def] >>
  metis_tac[vars_kept_trans]))
QED

Finalise array_membership_loop_round

Theorem array_membership_iteration_fuel[local]:
  !G ctx fn C X idx len_op N Kr.
  (!s i l. at_point C s /\ lookup_var idx s = SOME i /\
    eval_operand len_op s = SOME l ==>
    ?j. j<=Kr /\ fuel_outcome G ctx fn s j
      (\t. vars_kept N {} s t /\
        (at_point X t \/ (at_point C t /\ eval_operand len_op t = SOME l /\
          ?i':256 word. lookup_var idx t = SOME i' /\
            w2n(l-i') < w2n(l-i))))) /\
  (!s. at_point C s /\
    (lookup_var idx s = NONE \/ eval_operand len_op s = NONE) ==>
    fuel_outcome G ctx fn s 0 (\t. F)) ==>
  !s. at_point C s ==>
  ?j. j <= 1 + (2 ** 256) * Kr /\ fuel_outcome G ctx fn s j
    (\t. vars_kept N {} s t /\ at_point X t)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `lookup_var idx s` >> Cases_on `eval_operand len_op s`
  >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_weaken >>
      qexists_tac `\t. F` >> simp[])
  >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_weaken >>
      qexists_tac `\t. F` >> simp[])
  >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_weaken >>
      qexists_tac `\t. F` >> simp[]) >>
  rename1 `eval_operand len_op s = SOME l` >>
  qabbrev_tac `H = \t. at_point C t /\ vars_kept N {} s t /\
    eval_operand len_op t = SOME l /\ IS_SOME (lookup_var idx t)` >>
  qabbrev_tac `Q = \t. vars_kept N {} s t /\ at_point X t` >>
  qabbrev_tac `mu = \t. w2n (l - THE (lookup_var idx t))` >>
  `(!t. H t ==> mu t < 2 ** 256) /\
   (!t. H t ==> ?j. j<=Kr /\ fuel_outcome G ctx fn t j
     (\u. Q u \/ (H u /\ mu u < mu t)))` by
    (conj_tac
     >- (simp[Abbr `mu`] >> rpt strip_tac >>
         mp_tac (wordsTheory.w2n_lt |> Q.ISPEC `l - THE (lookup_var idx t)`) >>
         simp[wordsTheory.dimword_def, venomLayoutTheory.dimindex_256]) >>
     qx_gen_tac `t` >> simp[Abbr `H`] >> strip_tac >>
     Cases_on `lookup_var idx t` >> gvs[] >>
     qpat_x_assum `!s i l. _` (qspec_then `t` mp_tac) >>
     disch_then (qspecl_then [`x'`,`l`] mp_tac) >>
     simp[] >> strip_tac >> qexists_tac `j` >> simp[] >>
     irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
     simp[Abbr `Q`, Abbr `mu`] >> rpt strip_tac >>
     gvs[] >> metis_tac[vars_kept_trans]) >>
  `?j. j <= (2 ** 256) * Kr /\ fuel_outcome G ctx fn s j Q`
    suffices_by (strip_tac >> qexists_tac `j` >> gvs[]) >>
  irule fuel_outcome_iterate >> qexistsl_tac [`H`, `mu`] >>
  simp[Abbr `H`]
QED

Theorem array_membership_tail_fuel[local]:
  !is_in res s r t.
  (if is_in then return (Var res) else emit_op ISZERO [Var res]) s = (r,t) ==>
  ?K. frag_fuel {} {} {} s t K
Proof
  rpt gen_tac >> strip_tac >>
  `fuel_ok {} {} {}
    (if is_in then return (Var res) else emit_op ISZERO [Var res])` by
    (Cases_on `is_in` >> simp[] >> fuel_auto [fuel_ok_emit_op] >>
     simp[is_terminator_def]) >>
  drule (iffLR fuel_ok_def) >> disch_then drule >> simp[]
QED

Theorem array_membership_entry_fuel[local]:
  !len_op bound_opt s res idx cond body found incr exit t.
  (do res <- fresh_var;
      entry <- fresh_label "in_entry";
      cond <- fresh_label "in_cond";
      body <- fresh_label "in_body";
      found <- fresh_label "in_found";
      incr <- fresh_label "in_incr";
      exit <- fresh_label "in_exit";
      emit_inst JMP [Label entry] [];
      new_block entry;
      idx <- fresh_var;
      emit_inst ASSIGN [Lit 0w] [idx];
      emit_inst ASSIGN [Lit 0w] [res];
      (case bound_opt of
         SOME cap => do inv <- emit_op GT [len_op;Lit (n2w cap)];
                        valid <- emit_op ISZERO [inv];
                        emit_inst ASSERT [valid] [] od
       | NONE => return ());
      emit_inst JMP [Label cond] [];
      new_block cond;
      comp_return (res,idx,cond,body,found,incr,exit)
   od) (s:compile_state) = ((res,idx,cond,body,found,incr,exit),t) ==>
  ?K. frag_fuel {} {} {} s t K
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `action s` >>
  `fuel_ok {} {} {} action` by
    (unabbrev_all_tac >> Cases_on `bound_opt` >> simp[] >>
     fuel_auto [fuel_ok_emit_inst_jmp, fuel_ok_emit_inst,
                fuel_ok_emit_op] >> simp[is_terminator_def] >>
     fuel_auto [fuel_ok_emit_inst_jmp, fuel_ok_emit_inst,
                fuel_ok_emit_op] >> simp[is_terminator_def]) >>
  drule (iffLR fuel_ok_def) >> disch_then drule >> simp[]
QED

(* The loop counts a fresh idx_var from 0 up by 1 per round until it equals
   len_op, leaving through the exit block (or earlier through the found
   block).  len_op was allocated before the function (or is a literal; never
   a label, whose value the loader's bound says nothing about), and
   the loop writes only idx_var, result_var and variables it allocates
   itself, so the bound is fixed during the body on the loader's normal
   continuation.  Modular distance to the bound decreases on each back
   edge, giving a uniform finite bound even when idx_var wraps. *)
Theorem fuel_okS_compile_array_membership_loop:
  !loader.
    (!a Wv E. fuel_ok Wv {} E (loader a)) ==>
    !needle arr_op len_op elem_size offset_base bound_opt is_in Wv E.
      fuel_okS (\st. (!x. len_op = Var x ==> var_below st.cs_next_var x) /\
                     !l. len_op <> Label l)
        Wv {} E
        (compile_array_membership_loop needle arr_op len_op elem_size
           offset_base loader bound_opt is_in)
Proof
  gen_tac >> strip_tac >> rpt gen_tac >>
  rewrite_tac[fuel_okS_def] >> rpt gen_tac >> strip_tac >>
  `fuel_ok Wv {} UNIV
    (compile_array_membership_loop needle arr_op len_op elem_size
       offset_base loader bound_opt is_in)` by
    (irule array_membership_loop_open_exits >> simp[]) >>
  drule (iffLR fuel_ok_def) >> disch_then drule >> strip_tac >> simp[] >>
  drule array_membership_loop_run_cuts >> strip_tac >>
  rename1 `loader addr A = (elem,Z)` >>
  rename1 `(do m <- emit_op EQ [elem;needle];
      emit_inst JNZ [m;Label found;Label incr] []; new_block found od) Z=(u2,SF)` >>
  rename1 `(do n <- emit_op ADD [Var idx;Lit 1w]; emit_inst ASSIGN [n] [idx];
      emit_inst JMP [Label cond] []; new_block exit od) SI=(u4,X)` >>
  drule array_membership_entry_structure >> strip_tac >>
  drule array_membership_compare_structure >> strip_tac >>
  drule array_membership_address_structure >> strip_tac >>
  drule array_membership_found_structure >> strip_tac >>
  drule array_membership_incr_structure >> strip_tac >>
  drule array_membership_tail_structure >> strip_tac >>
  `fuel_ok {} {} {} (loader addr)` by simp[] >>
  drule (iffLR fuel_ok_def) >> disch_then drule >> strip_tac >>
  drule array_membership_entry_fuel >> strip_tac >>
  drule array_membership_tail_fuel >> strip_tac >>
  suspend "select_round"
QED

Resume fuel_okS_compile_array_membership_loop[select_round]:
  `cs_extends C B /\ C.cs_next_var <= B.cs_next_var` by
    metis_tac[array_membership_compare_structure] >>
  `st.cs_next_var <= B.cs_next_var /\ B.cs_next_var <= Z.cs_next_var /\
   Z.cs_next_var <= SI.cs_next_var /\
   (!y. len_op=Var y ==> var_below st.cs_next_var y) /\
   (!lbl. len_op<>Label lbl)` by
    (gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `idx <> res` by metis_tac[] >>
  assume_tac loop_distance_decreases >>
  drule_all array_membership_loop_round >>
  disch_then (qspec_then `Kb'` (qx_choose_then `Kr` assume_tac)) >>
  suspend "fragment"
QED

Resume fuel_okS_compile_array_membership_loop[fragment]:
  rename1 `frag_fuel {} {} {} A Z KL` >>
  rename1 `frag_fuel {} {} {} st C Ke` >>
  rename1 `frag_fuel {} {} {} X st' Kt` >>
  `cs_extends SI st' /\ cs_extends SF st' /\ cs_extends Z st' /\
   cs_extends A st' /\ cs_extends B st' /\ cs_extends C st'` by
    metis_tac[compileEnvTheory.cs_extends_trans] >>
  qexists_tac `Ke + (1 + (2 ** 256) * Kr) + Kt` >>
  rewrite_tac[frag_fuel_def] >> rpt gen_tac >> simp[] >> strip_tac >>
  `fn_has_code st C fn /\ fn_has_code C st' fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code C B fn /\ fn_has_code B st' fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code B A fn /\ fn_has_code A st' fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code A Z fn /\ fn_has_code Z st' fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code Z SF fn /\ fn_has_code SF st' fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code SF SI fn /\ fn_has_code SI st' fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code SI X fn /\ fn_has_code X st' fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  suspend "loader_interface"
QED

Resume fuel_okS_compile_array_membership_loop[loader_interface]:
  `var_below A.cs_next_var idx /\ st.cs_next_var <= A.cs_next_var /\
   (!y. len_op = Var y ==> var_below A.cs_next_var y)` by
    (gvs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!s. at_point A s ==> ?j. j <= KL /\
    fuel_outcome G ctx fn s j (\t. at_point Z t /\
      vars_kept st.cs_next_var {} s t /\
      lookup_var idx t = lookup_var idx s /\
      eval_operand len_op t = eval_operand len_op s)` by
    (rpt strip_tac >>
     qpat_x_assum `frag_fuel {} {} {} A Z KL` mp_tac >>
     rewrite_tac[frag_fuel_def] >>
     disch_then (qspecl_then [`G`, `A.cs_next_var`, `ctx`, `fn`, `s'`] mp_tac) >>
     simp[] >> strip_tac >> qexists_tac `j` >> simp[] >>
     irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
     rpt strip_tac >> gvs[] >>
     drule_all loader_keeps_loop_operands >> strip_tac >>
     simp[] >> gvs[vars_kept_def, var_below_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  suspend "runtime_compose"
QED

Resume fuel_okS_compile_array_membership_loop[runtime_compose]:
  qpat_x_assum `!fn G ctx. _` (qspecl_then [`fn`,`G`,`ctx`] mp_tac) >>
  simp[] >> strip_tac >>
  `!t. at_point C t /\
    (lookup_var idx t = NONE \/ eval_operand len_op t = NONE) ==>
    fuel_outcome G ctx fn t 0 (\u. F)` by
    (rpt strip_tac >> irule array_membership_cond_failed >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `!t. at_point C t ==> ?j. j <= 1 + (2 ** 256) * Kr /\
    fuel_outcome G ctx fn t j
      (\u. vars_kept st.cs_next_var {} t u /\ at_point X u)` by
    (rpt strip_tac >> irule array_membership_iteration_fuel >>
     metis_tac[]) >>
  suspend "entry_composition"
QED

Resume fuel_okS_compile_array_membership_loop[entry_composition]:
  `!t. at_point X t ==> ?j. j <= Kt /\
    fuel_outcome G ctx fn t j
      (\u. vars_kept st.cs_next_var {} t u /\ at_point st' u)` by
    (rpt strip_tac >>
     qpat_assum `frag_fuel {} {} {} X st' Kt` mp_tac >>
     rewrite_tac[frag_fuel_def] >>
     disch_then (qspecl_then [`G`,`st.cs_next_var`,`ctx`,`fn`,`t`] mp_tac) >>
     simp[]) >>
  `!t. at_point C t ==> ?j. j <= (1 + (2 ** 256) * Kr) + Kt /\
    fuel_outcome G ctx fn t j
      (\u. vars_kept st.cs_next_var {} t u /\ at_point st' u)` by
    (rpt strip_tac >>
     qpat_x_assum `!t. at_point C t ==> _` (drule_then strip_assume_tac) >>
     drule fuel_outcome_compose >>
     disch_then (qspecl_then
       [`\u. vars_kept st.cs_next_var {} t u /\ at_point st' u`, `Kt`] mp_tac) >>
     impl_tac
     >- (simp[] >> rpt strip_tac >>
         qpat_x_assum `!t. at_point X t ==> _` (drule_then strip_assume_tac) >>
         qexists_tac `j'` >> simp[] >>
         irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
         simp[] >> metis_tac[vars_kept_trans]) >>
     strip_tac >> qexists_tac `j'` >> gvs[]) >>
  suspend "finish_composition"
QED

Resume fuel_okS_compile_array_membership_loop[finish_composition]:
  qpat_x_assum `frag_fuel {} {} {} st C Ke` mp_tac >>
  rewrite_tac[frag_fuel_def] >>
  disch_then (qspecl_then [`G`,`st.cs_next_var`,`ctx`,`fn`,`s`] mp_tac) >>
  simp[] >> strip_tac >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then
    [`\u. vars_kept N Wv s u /\
       (at_point st' u \/ u.vs_current_bb IN E /\ u.vs_inst_idx = 0)`,
     `(1 + (2 ** 256) * Kr) + Kt`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_x_assum `!t. at_point C t ==> _` (drule_then strip_assume_tac) >>
      qexists_tac `j'` >> gvs[] >>
      irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >> simp[] >>
      `vars_kept st.cs_next_var {} s t'` by metis_tac[vars_kept_trans] >>
      gvs[vars_kept_def, var_below_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  strip_tac >> qexists_tac `j'` >> gvs[]
QED

Finalise fuel_okS_compile_array_membership_loop
