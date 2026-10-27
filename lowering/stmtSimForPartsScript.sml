(*
 * Statement simulation: the pieces of For over a range (#637)
 *
 * The source side of For over a range with constant ends (literals,
 * max_value and the like), and the blocks the lowering emits for it
 * (entry, condition, increment) with what each one does, as
 * stmtSimForLoop uses them.
 *
 * TOP-LEVEL:
 *   eval_stmt_for_range, eval_for_cons_cases — the source loop
 *   for_entry_block, for_cond_block, for_incr_block, for_start_block
 *   compile_for_range_parts — the code compile_stmt emits for the loop
 *   eval_stmt_for_range_lit, compile_for_range_lit_parts — the same for
 *     literal ends
 *)

Theory stmtSimForParts
Ancestors
  stmtSim
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

(* ===== for over a range with constant ends ===== *)

(* A range whose ends evaluate to integers without changing the state:
   its values. *)
Theorem eval_iterator_range:
  !cx e1 n1 e2 n2 es.
    eval_expr cx e1 es = (INL (Value (IntV n1)), es) /\
    eval_expr cx e2 es = (INL (Value (IntV n2)), es) /\ n1 <= n2 ==>
    eval_iterator cx (Range e1 e2) es =
    (INL (GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1))), es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, LET_THM, return_def] >>
  simp[get_range_limits_def, lift_sum_def, return_def]
QED

Theorem eval_expr_int_lit:
  !cx a n es. eval_expr cx (Literal a (IntL n)) es = (INL (Value (IntV n)), es)
Proof
  simp[Once evaluate_def, return_def, evaluate_literal_def]
QED

Theorem eval_iterator_range_lit:
  !cx a1 n1 a2 n2 es.
    n1 <= n2 ==>
    eval_iterator cx (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) es =
    (INL (GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1))), es)
Proof
  rpt strip_tac >> irule eval_iterator_range >> simp[eval_expr_int_lit]
QED

(* A range of such ends, nonempty or empty, within the loop's bound: the
   loop over its values. *)
Theorem eval_stmt_for_range:
  !cx id fty e1 n1 e2 n2 bound body es res es' tyv.
    eval_stmt cx (For id fty (Range e1 e2) bound body) es = (res, es') /\
    eval_expr cx e1 es = (INL (Value (IntV n1)), es) /\
    eval_expr cx e2 es = (INL (Value (IntV n2)), es) /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ n1 <= n2 /\
    Num (n2 - n1) <= bound ==>
    eval_for cx tyv id body (GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1)))
      es = (res, es')
Proof
  rpt gen_tac >> strip_tac >>
  drule_all eval_iterator_range >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, LET_THM,
       lift_option_type_def, lift_option_def, return_def, raise_def] >>
  simp[check_def, assert_def, compatible_bound_def]
QED

Theorem eval_stmt_for_range_lit:
  !cx id fty a1 n1 a2 n2 bound stmts es res es' tyv.
    eval_stmt cx
      (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts) es = (res, es') /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ n1 <= n2 /\
    Num (n2 - n1) <= bound ==>
    eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1)))
      es = (res, es')
Proof
  rpt strip_tac >>
  qspecl_then [`cx`, `id`, `fty`, `Literal a1 (IntL n1)`, `n1`,
               `Literal a2 (IntL n2)`, `n2`, `bound`, `stmts`, `es`, `res`,
               `es'`, `tyv`] mp_tac eval_stmt_for_range >>
  impl_tac >- simp[eval_expr_int_lit] >> simp[]
QED

(* One iteration: the body in a scope holding the loop variable, which is
   popped after it; a normal end or a continue goes on with the rest of the
   values, a break ends the loop, any other exception leaves it. *)
Theorem eval_for_cons_cases:
  !cx tyv nm stmts v vs es res es'.
    eval_for cx tyv nm stmts (v::vs) es = (res, es') /\
    lookup_scopes nm es.scopes = NONE ==>
    ?r2 es2 sc rest.
      eval_stmts cx stmts
        (es with scopes :=
           (FEMPTY |+ (nm, <| assignable := F; type := tyv; value := v |>)) ::
           es.scopes) = (r2, es2) /\
      es2.scopes = sc :: rest /\ MAP FDOM rest = MAP FDOM es.scopes /\
      (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
      ((r2 = INL () \/ r2 = INR ContinueException) /\
       eval_for cx tyv nm stmts vs (es2 with scopes := rest) = (res, es') \/
       r2 = INR BreakException /\ res = INL () /\
       es' = es2 with scopes := rest \/
       (?e. r2 = INR e /\ e <> BreakException /\ e <> ContinueException) /\
       res = r2 /\ es' = es2 with scopes := rest)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, push_scope_with_var_def,
       finally_def, try_def, return_def] >>
  `!x. x with scopes updated_by
         CONS (FEMPTY |+ (nm, <| assignable := F; type := tyv; value := v |>)) =
       x with scopes :=
         (FEMPTY |+ (nm, <| assignable := F; type := tyv; value := v |>)) ::
         x.scopes` by
    simp[evaluation_state_component_equality] >>
  simp[] >>
  qabbrev_tac `esA = es with scopes :=
     (FEMPTY |+ (nm, <| assignable := F; type := tyv; value := v |>)) ::
     es.scopes` >>
  Cases_on `eval_stmts cx stmts esA` >> rename1 `_ = (r2, es2)` >>
  `es2.scopes <> [] /\ MAP FDOM (TL es2.scopes) = MAP FDOM es.scopes` by
    (drule eval_stmts_preserves_scopes_dom >>
     simp[preserves_scopes_dom_def, Abbr `esA`]) >>
  Cases_on `es2.scopes` >> fs[] >> rename1 `es2.scopes = top2 :: rest2` >>
  `!id. id IN FDOM top2 ==> lookup_scopes id rest2 = NONE` by
    (rpt strip_tac >> Cases_on `id = nm`
     >- (gvs[] >> irule lookup_scopes_none_map_fdom >> metis_tac[]) >>
     drule eval_stmts_new_in_head_not_in_tail >> simp[Abbr `esA`]) >>
  Cases_on `r2` >> fs[pop_scope_def, return_def, raise_def] >>
  rename1 `handle_loop_exception ex` >>
  Cases_on `ex = ContinueException` >> Cases_on `ex = BreakException` >>
  fs[handle_loop_exception_def, return_def, raise_def, pop_scope_def] >>
  rw[] >> fs[]
QED

(* The increment block of a range loop: the counter cv goes up by one and
   the run goes back to the condition block. *)
Theorem for_incr_block:
  !ctx func dd cv nv c lbl cond_lbl i1 i2 i3.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl;
              bb_instructions := [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
                                  mk_inst i2 ASSIGN [Var nv] [cv];
                                  mk_inst i3 JMP [Label cond_lbl] []] |> /\
    dd.vs_current_bb = lbl /\ dd.vs_inst_idx = 0 /\ ~dd.vs_halted /\
    lookup_var cv dd = SOME c ==>
    !fuel rr.
      run_from fuel ctx func
        (jump_to cond_lbl
           (update_var cv (c + 1w) (update_var nv (c + 1w) dd))) = rr /\
      (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func dd = rr
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bb = <| bb_label := lbl;
              bb_instructions := [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
                                  mk_inst i2 ASSIGN [Var nv] [cv];
                                  mk_inst i3 JMP [Label cond_lbl] []] |>` >>
  `!fu. run_from fu ctx func dd =
        run_from fu ctx func (update_var nv (c + 1w) dd with vs_inst_idx := 1)` by
    (gen_tac >>
     qspecl_then [`fu`, `ctx`, `func`, `dd`, `bb`,
                  `mk_inst i1 ADD [Var cv; Lit 1w] [nv]`,
                  `update_var nv (c + 1w) dd`] mp_tac run_from_step >>
     impl_tac
     >- (simp[Abbr `bb`, get_instruction_def, venomInstTheory.mk_inst_def,
              is_terminator_def] >>
         `step_inst_base (mk_inst i1 ADD [Var cv; Lit 1w] [nv]) dd =
          OK (update_var nv (c + 1w) dd)` by
           (irule step_ADD >> simp[eval_operand_def]) >>
         fs[venomInstTheory.mk_inst_def]) >>
     simp[]) >>
  qabbrev_tac `d1 = update_var nv (c + 1w) dd with vs_inst_idx := 1` >>
  `!fu. run_from fu ctx func d1 =
        run_from fu ctx func (update_var cv (c + 1w) d1 with vs_inst_idx := 2)` by
    (gen_tac >>
     qspecl_then [`fu`, `ctx`, `func`, `d1`, `bb`,
                  `mk_inst i2 ASSIGN [Var nv] [cv]`,
                  `update_var cv (c + 1w) d1`] mp_tac run_from_step >>
     impl_tac
     >- (simp[Abbr `bb`, Abbr `d1`, get_instruction_def,
              venomInstTheory.mk_inst_def, is_terminator_def,
              update_var_def] >>
         simp[step_inst_base_def, eval_operand_def, lookup_var_def,
              update_var_def, FLOOKUP_UPDATE]) >>
     simp[Abbr `d1`]) >>
  qabbrev_tac `d2 = update_var cv (c + 1w) d1 with vs_inst_idx := 2` >>
  `jump_to cond_lbl d2 =
   jump_to cond_lbl (update_var cv (c + 1w) (update_var nv (c + 1w) dd))` by
    simp[Abbr `d2`, Abbr `d1`, jump_to_def, update_var_def] >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  `run_from (SUC fuel) ctx func d2 = rr` by
    (qspecl_then [`fuel`, `ctx`, `func`, `d2`, `bb`,
                  `mk_inst i3 JMP [Label cond_lbl] []`, `cond_lbl`, `rr`]
       mp_tac run_from_jump_result >>
     impl_tac >- (fs[Abbr `bb`, Abbr `d2`, Abbr `d1`, get_instruction_def,
                     venomInstTheory.mk_inst_def, is_terminator_def,
                     update_var_def, step_jmp_behavior]) >>
     simp[]) >>
  fs[]
QED

(* The condition block of a range loop: the counter cv against the end ev,
   to the exit block when they are equal and to the body otherwise. *)
Theorem for_cond_block:
  !ctx func cc cv ev dv a b lbl exit_lbl body_lbl j1 j2.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var cv; Var ev] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
    cc.vs_current_bb = lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    lookup_var cv cc = SOME a /\ lookup_var ev cc = SOME b ==>
    !fuel rr.
      run_from fuel ctx func
        (jump_to (if a = b then exit_lbl else body_lbl)
           (update_var dv (bool_to_word (a = b)) cc)) = rr /\
      (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func cc = rr
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bb = <| bb_label := lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var cv; Var ev] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |>` >>
  `!fu. run_from fu ctx func cc =
        run_from fu ctx func
          (update_var dv (bool_to_word (a = b)) cc with vs_inst_idx := 1)` by
    (gen_tac >>
     qspecl_then [`fu`, `ctx`, `func`, `cc`, `bb`,
                  `mk_inst j1 EQ [Var cv; Var ev] [dv]`,
                  `update_var dv (bool_to_word (a = b)) cc`]
       mp_tac run_from_step >>
     impl_tac
     >- (simp[Abbr `bb`, get_instruction_def, venomInstTheory.mk_inst_def,
              is_terminator_def] >>
         `step_inst_base (mk_inst j1 EQ [Var cv; Var ev] [dv]) cc =
          OK (update_var dv (bool_to_word (a = b)) cc)` by
           (irule step_EQ >> simp[eval_operand_def]) >>
         fs[venomInstTheory.mk_inst_def]) >>
     simp[]) >>
  qabbrev_tac `d1 = update_var dv (bool_to_word (a = b)) cc with
                      vs_inst_idx := 1` >>
  `jump_to (if a = b then exit_lbl else body_lbl) d1 =
   jump_to (if a = b then exit_lbl else body_lbl)
     (update_var dv (bool_to_word (a = b)) cc)` by
    simp[Abbr `d1`, jump_to_def, update_var_def] >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  `run_from (SUC fuel) ctx func d1 = rr` by
    (qspecl_then [`fuel`, `ctx`, `func`, `d1`, `bb`,
                  `mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []`,
                  `if a = b then exit_lbl else body_lbl`, `rr`]
       mp_tac run_from_jump_result >>
     impl_tac
     >- (fs[Abbr `bb`, Abbr `d1`, get_instruction_def,
            venomInstTheory.mk_inst_def, is_terminator_def,
            update_var_def] >>
         qmatch_goalsub_abbrev_tac `step_inst_base _ ss` >>
         `eval_operand (Var dv) ss = SOME (bool_to_word (a = b))` by
           simp[Abbr `ss`, eval_operand_def, lookup_var_def,
                FLOOKUP_UPDATE] >>
         drule step_jnz_behavior >>
         disch_then (qspecl_then [`exit_lbl`, `body_lbl`, `j2`] mp_tac) >>
         simp[] >> strip_tac >>
         Cases_on `a = b` >> fs[bool_to_word_def, Abbr `ss`, jump_to_def]) >>
     simp[]) >>
  fs[]
QED

(* The entry block of a range loop with literal ends: the counter cv starts
   at a, the end ev is a + b, and the run goes to the condition block. *)
Theorem for_entry_block:
  !ctx func ee cv ev a b lbl cond_lbl i1 i2 i3.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl;
              bb_instructions := [mk_inst i1 ASSIGN [Lit a] [cv];
                                  mk_inst i2 ADD [Lit a; Lit b] [ev];
                                  mk_inst i3 JMP [Label cond_lbl] []] |> /\
    ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted ==>
    !fuel rr.
      run_from fuel ctx func
        (jump_to cond_lbl (update_var ev (a + b) (update_var cv a ee))) = rr /\
      (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func ee = rr
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bb = <| bb_label := lbl;
              bb_instructions := [mk_inst i1 ASSIGN [Lit a] [cv];
                                  mk_inst i2 ADD [Lit a; Lit b] [ev];
                                  mk_inst i3 JMP [Label cond_lbl] []] |>` >>
  `!fu. run_from fu ctx func ee =
        run_from fu ctx func (update_var cv a ee with vs_inst_idx := 1)` by
    (gen_tac >>
     qspecl_then [`fu`, `ctx`, `func`, `ee`, `bb`,
                  `mk_inst i1 ASSIGN [Lit a] [cv]`, `update_var cv a ee`]
       mp_tac run_from_step >>
     impl_tac
     >- simp[Abbr `bb`, get_instruction_def, venomInstTheory.mk_inst_def,
             is_terminator_def, step_inst_base_def, eval_operand_def] >>
     simp[]) >>
  qabbrev_tac `d1 = update_var cv a ee with vs_inst_idx := 1` >>
  `!fu. run_from fu ctx func d1 =
        run_from fu ctx func (update_var ev (a + b) d1 with vs_inst_idx := 2)` by
    (gen_tac >>
     qspecl_then [`fu`, `ctx`, `func`, `d1`, `bb`,
                  `mk_inst i2 ADD [Lit a; Lit b] [ev]`,
                  `update_var ev (a + b) d1`] mp_tac run_from_step >>
     impl_tac
     >- (simp[Abbr `bb`, Abbr `d1`, get_instruction_def,
              venomInstTheory.mk_inst_def, is_terminator_def,
              update_var_def] >>
         qspecl_then [`Lit a`, `Lit b`, `a`, `b`, `i2`, `ev`,
           `ee with <|vs_vars := ee.vs_vars |+ (cv, a); vs_inst_idx := 1|>`]
           mp_tac step_ADD >>
         simp[eval_operand_def, venomInstTheory.mk_inst_def,
              update_var_def]) >>
     simp[Abbr `d1`]) >>
  qabbrev_tac `d2 = update_var ev (a + b) d1 with vs_inst_idx := 2` >>
  `jump_to cond_lbl d2 =
   jump_to cond_lbl (update_var ev (a + b) (update_var cv a ee))` by
    simp[Abbr `d2`, Abbr `d1`, jump_to_def, update_var_def] >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  `run_from (SUC fuel) ctx func d2 = rr` by
    (qspecl_then [`fuel`, `ctx`, `func`, `d2`, `bb`,
                  `mk_inst i3 JMP [Label cond_lbl] []`, `cond_lbl`, `rr`]
       mp_tac run_from_jump_result >>
     impl_tac >- (fs[Abbr `bb`, Abbr `d2`, Abbr `d1`, get_instruction_def,
                     venomInstTheory.mk_inst_def, is_terminator_def,
                     update_var_def, step_jmp_behavior]) >>
     simp[]) >>
  fs[]
QED

(* The end of the block a range loop starts in: the loop variable's ALLOCA,
   then the jump to the entry block. *)
Theorem for_start_block:
  !ctx func s0 s1 aa pre lbl entry_lbl i.
    lookup_block s0.vs_current_bb func.fn_blocks =
      SOME <| bb_label := lbl;
              bb_instructions :=
                pre ++ [aa; mk_inst i JMP [Label entry_lbl] []] |> /\
    s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
    aa.inst_opcode = ALLOCA /\ step_inst_base aa s0 = OK s1 /\
    s1.vs_current_bb = s0.vs_current_bb /\ ~s1.vs_halted ==>
    !fuel rr.
      run_from fuel ctx func (jump_to entry_lbl s1) = rr /\
      (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func s0 = rr
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bb = <| bb_label := lbl;
              bb_instructions :=
                pre ++ [aa; mk_inst i JMP [Label entry_lbl] []] |>` >>
  `!fu. run_from fu ctx func s0 =
        run_from fu ctx func (s1 with vs_inst_idx := SUC (LENGTH pre))` by
    (gen_tac >>
     qspecl_then [`fu`, `ctx`, `func`, `s0`, `bb`, `aa`, `s1`]
       mp_tac run_from_step >>
     impl_tac
     >- simp[Abbr `bb`, get_instruction_def, EL_LENGTH_APPEND,
             is_terminator_def] >>
     simp[]) >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  `jump_to entry_lbl (s1 with vs_inst_idx := SUC (LENGTH pre)) =
   jump_to entry_lbl s1` by simp[jump_to_def] >>
  qspecl_then [`fuel`, `ctx`, `func`, `s1 with vs_inst_idx := SUC (LENGTH pre)`,
               `bb`, `mk_inst i JMP [Label entry_lbl] []`, `entry_lbl`, `rr`]
    mp_tac run_from_jump_result >>
  impl_tac
  >- (fs[Abbr `bb`, get_instruction_def, venomInstTheory.mk_inst_def,
         is_terminator_def, step_jmp_behavior] >>
      simp[EL_APPEND2]) >>
  fs[]
QED

(* An integer literal lowers to its word. *)
Theorem lower_value_int_lit:
  !cenv ty a n st.
    lower_value compile_expr cenv ty (Literal a (IntL n)) st = (Lit (i2w n), st)
Proof
  simp[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
       compile_literal_vv_def, unwrap_value_def]
QED

(* The code of a range loop whose ends lower to words without emitting
   anything (literals, max_value, ...), its locals held through
   pointers: the loop variable's ALLOCA ending the block it starts in, the
   entry block (the counter and the end), the condition block, the body
   block (the counter stored into the loop variable, then the body), the
   increment block, and the exit block, where the code ends. *)
Theorem compile_for_range_parts:
  !cenv lctx ty id fty e1 w1 e2 w2 bound stmts st st' func.
    compile_stmt cenv lctx ty (For id fty (Range e1 e2) bound stmts) st =
      ((), st') /\
    lower_value compile_expr cenv fty e1 st = (Lit w1, st) /\
    lower_value compile_expr cenv fty e2 st = (Lit w2, st) /\
    cenv.ce_alloca_locals /\ fn_has_code st st' func /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb) ==>
    ?p cv ev dv entry_lbl cond_lbl body_lbl incr_lbl exit_lbl bc sb0 sb1 sj
     nv.
      p = STRING #"%" (toString st.cs_next_var) /\
      cv = STRING #"%" (toString (st.cs_next_var + 1)) /\
      ev = STRING #"%" (toString (st.cs_next_var + 2)) /\
      dv = STRING #"%" (toString (st.cs_next_var + 3)) /\
      entry_lbl = fresh_label_output "for_entry" st.cs_next_label /\
      cond_lbl = fresh_label_output "for_cond" (st.cs_next_label + 1) /\
      body_lbl = fresh_label_output "for_body" (st.cs_next_label + 2) /\
      incr_lbl = fresh_label_output "for_incr" (st.cs_next_label + 3) /\
      exit_lbl = fresh_label_output "for_exit" (st.cs_next_label + 4) /\
      declare_local cenv id fty st =
        (bc, st with cs_next_var := st.cs_next_var + 1) /\
      sb0.cs_current_bb = body_lbl /\
      sb0.cs_current_insts =
        [mk_inst (st.cs_next_id + 7) MSTORE [Var p; Var cv] []] /\
      sb0.cs_next_var = st.cs_next_var + 4 /\ cs_extends st sb0 /\
      compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((), sb1) /\
      fn_has_code sb0 sb1 func /\
      lookup_block st.cs_current_bb func.fn_blocks =
        SOME <| bb_label := st.cs_current_bb;
                bb_instructions :=
                  st.cs_current_insts ++
                  [mk_inst st.cs_next_id ALLOCA
                     [Lit (n2w (type_memory_bytes cenv fty))] [p];
                   mk_inst (st.cs_next_id + 1) JMP [Label entry_lbl] []] |> /\
      lookup_block entry_lbl func.fn_blocks =
        SOME <| bb_label := entry_lbl;
                bb_instructions :=
                  [mk_inst (st.cs_next_id + 2) ASSIGN [Lit w1] [cv];
                   mk_inst (st.cs_next_id + 3) ADD [Lit w1; Lit (w2 - w1)] [ev];
                   mk_inst (st.cs_next_id + 4) JMP [Label cond_lbl] []] |> /\
      lookup_block cond_lbl func.fn_blocks =
        SOME <| bb_label := cond_lbl;
                bb_instructions :=
                  [mk_inst (st.cs_next_id + 5) EQ [Var cv; Var ev] [dv];
                   mk_inst (st.cs_next_id + 6) JNZ
                     [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
      (?bbb. lookup_block body_lbl func.fn_blocks = SOME bbb /\
             get_instruction bbb 0 =
               SOME (mk_inst (st.cs_next_id + 7) MSTORE [Var p; Var cv] [])) /\
      (~block_is_terminated sb1 ==>
       sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
       sj.cs_current_insts =
         sb1.cs_current_insts ++
         [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
       fn_has_code sb1 sj func) /\
      sj.cs_next_var = sb1.cs_next_var /\
      nv = STRING #"%" (toString sj.cs_next_var) /\
      lookup_block incr_lbl func.fn_blocks =
        SOME <| bb_label := incr_lbl;
                bb_instructions :=
                  [mk_inst sj.cs_next_id ADD [Var cv; Lit 1w] [nv];
                   mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [cv];
                   mk_inst (sj.cs_next_id + 2) JMP [Label cond_lbl] []] |> /\
      st'.cs_current_bb = exit_lbl /\ st'.cs_current_insts = []
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       LET_THM] >>
  Cases_on `declare_local cenv id fty st` >> rename1 `_ = (bc, st1)` >>
  drule_all declare_local_ptr >> strip_tac >> gvs[] >>
  simp[emit_local_alloca_def, fresh_label_def, emit_inst_def, emit_op_def,
       emit_void_def, fresh_id_def, emit_def, new_block_def, fresh_var_def,
       emit_jmp_if_not_terminated_def, comp_get_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_stmts bc _ ty stmts _ = ((), sb1)` >>
  qpat_x_assum `(if block_is_terminated sb1 then _ else _) _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [comp_bind_def, comp_return_def,
                                         fresh_id_def, emit_def, LET_THM]) >>
  rename1 `_ = ((), sj)` >>
  qmatch_asmsub_abbrev_tac `compile_stmts bc _ ty stmts sb0 = _` >>
  strip_tac >> qexistsl_tac [`sb0`, `sb1`, `sj`] >>
  `cs_extends sb0 sb1` by metis_tac[] >>
  `cs_extends st sb0` by
    (simp[cs_extends_def, Abbr `sb0`] >> qexists_tac `[_; _; _]` >> simp[]) >>
  `sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
   sj.cs_next_var = sb1.cs_next_var /\ cs_extends sb1 sj /\
   (~block_is_terminated sb1 ==>
    sj.cs_current_insts =
      sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP
         [Label (fresh_label_output "for_incr" (st.cs_next_label + 3))] []])` by
    (Cases_on `block_is_terminated sb1` >>
     fs[comp_return_def, comp_bind_def, fresh_id_def, emit_def, LET_THM] >>
     gvs[cs_extends_refl] >>
     irule cs_extends_same_block >> simp[]) >>
  `cs_extends sj st'` by
    (qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >> simp[cs_extends_def] >>
     qexists_tac `[_; <| bb_label := sj.cs_current_bb;
                         bb_instructions := sj.cs_current_insts |>]` >>
     simp[]) >>
  `?nb. sb1.cs_blocks = nb ++ sb0.cs_blocks` by
    (qpat_x_assum `cs_extends sb0 sb1` mp_tac >> simp[cs_extends_def] >>
     metis_tac[]) >>
  `!l b. MEM b (emitted_blocks st st') /\ b.bb_label = l ==>
         lookup_block l func.fn_blocks = SOME b` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `emitted_blocks st st' =
   [HD st'.cs_blocks; HD (TL st'.cs_blocks)] ++ nb ++
   [HD sb0.cs_blocks; HD (TL sb0.cs_blocks); HD (TL (TL sb0.cs_blocks))]` by
    (irule emitted_blocks_append >>
     qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >> simp[Abbr `sb0`]) >>
  `cs_extends sb1 st' /\ cs_extends sb0 st'` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sb0 sb1 func /\ fn_has_code sb1 sj func` by
    metis_tac[fn_has_code_mid, cs_extends_trans] >>
  `?bbb. lookup_block sb0.cs_current_bb func.fn_blocks = SOME bbb /\
         isPREFIX sb0.cs_current_insts bbb.bb_instructions` by
    metis_tac[fn_has_code_start] >>
  qpat_x_assum `_ = st'` (assume_tac o SYM) >> rpt conj_tac
  >- simp[Abbr `sb0`]
  >- simp[Abbr `sb0`]
  >- simp[Abbr `sb0`]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `!l b. MEM b _ /\ _ ==> _` irule >>
      conj_tac >- simp_tac (srw_ss()) [] >>
      qpat_assum `emitted_blocks _ _ = _` (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [MEM_APPEND, MEM] >> disj2_tac >> disj2_tac >> disj2_tac >>
      qunabbrev_tac `sb0` >> simp_tac (srw_ss()) [])
  >- (qpat_assum `!l b. MEM b _ /\ _ ==> _` irule >>
      conj_tac >- simp_tac (srw_ss()) [] >>
      qpat_assum `emitted_blocks _ _ = _` (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [MEM_APPEND, MEM] >> disj2_tac >> disj2_tac >> disj1_tac >>
      qunabbrev_tac `sb0` >> simp_tac (srw_ss()) [])
  >- (qpat_assum `!l b. MEM b _ /\ _ ==> _` irule >>
      conj_tac >- simp_tac (srw_ss()) [] >>
      qpat_assum `emitted_blocks _ _ = _` (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [MEM_APPEND, MEM] >> disj2_tac >> disj1_tac >>
      qunabbrev_tac `sb0` >> simp_tac (srw_ss()) [])
  >- (qexists_tac `bbb` >>
      qpat_x_assum `lookup_block sb0.cs_current_bb _ = _` mp_tac >>
      qpat_x_assum `isPREFIX sb0.cs_current_insts _` mp_tac >>
      qunabbrev_tac `sb0` >> simp_tac (srw_ss()) [] >> rpt strip_tac >>
      Cases_on `bbb.bb_instructions` >> fs[get_instruction_def])
  >- (strip_tac >>
      qpat_x_assum `~block_is_terminated sb1 ==> _` drule >> strip_tac >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `!l b. MEM b _ /\ _ ==> _` irule >>
      conj_tac >- simp_tac (srw_ss()) [] >>
      qpat_assum `emitted_blocks _ _ = _` (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [MEM_APPEND, MEM] >> disj1_tac >> disj1_tac >> disj1_tac >>
      qpat_assum `st' = _` (fn th => REWRITE_TAC [th]) >>
      simp_tac (srw_ss()) [])
  >- (qpat_assum `st' = _` (fn th => REWRITE_TAC [th]) >>
      simp_tac (srw_ss()) []) >>
  qpat_assum `st' = _` (fn th => REWRITE_TAC [th]) >>
  simp_tac (srw_ss()) []
QED

(* The literal-ends case. *)
Theorem compile_for_range_lit_parts:
  !cenv lctx ty id fty a1 n1 a2 n2 bound stmts st st' func.
    compile_stmt cenv lctx ty
      (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts) st = ((), st') /\
    cenv.ce_alloca_locals /\ fn_has_code st st' func /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb) ==>
    ?p cv ev dv entry_lbl cond_lbl body_lbl incr_lbl exit_lbl bc sb0 sb1 sj
     nv.
      p = STRING #"%" (toString st.cs_next_var) /\
      cv = STRING #"%" (toString (st.cs_next_var + 1)) /\
      ev = STRING #"%" (toString (st.cs_next_var + 2)) /\
      dv = STRING #"%" (toString (st.cs_next_var + 3)) /\
      entry_lbl = fresh_label_output "for_entry" st.cs_next_label /\
      cond_lbl = fresh_label_output "for_cond" (st.cs_next_label + 1) /\
      body_lbl = fresh_label_output "for_body" (st.cs_next_label + 2) /\
      incr_lbl = fresh_label_output "for_incr" (st.cs_next_label + 3) /\
      exit_lbl = fresh_label_output "for_exit" (st.cs_next_label + 4) /\
      declare_local cenv id fty st =
        (bc, st with cs_next_var := st.cs_next_var + 1) /\
      sb0.cs_current_bb = body_lbl /\
      sb0.cs_current_insts =
        [mk_inst (st.cs_next_id + 7) MSTORE [Var p; Var cv] []] /\
      sb0.cs_next_var = st.cs_next_var + 4 /\ cs_extends st sb0 /\
      compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((), sb1) /\
      fn_has_code sb0 sb1 func /\
      lookup_block st.cs_current_bb func.fn_blocks =
        SOME <| bb_label := st.cs_current_bb;
                bb_instructions :=
                  st.cs_current_insts ++
                  [mk_inst st.cs_next_id ALLOCA
                     [Lit (n2w (type_memory_bytes cenv fty))] [p];
                   mk_inst (st.cs_next_id + 1) JMP [Label entry_lbl] []] |> /\
      lookup_block entry_lbl func.fn_blocks =
        SOME <| bb_label := entry_lbl;
                bb_instructions :=
                  [mk_inst (st.cs_next_id + 2) ASSIGN [Lit (i2w n1)] [cv];
                   mk_inst (st.cs_next_id + 3) ADD
                     [Lit (i2w n1); Lit (i2w n2 - i2w n1)] [ev];
                   mk_inst (st.cs_next_id + 4) JMP [Label cond_lbl] []] |> /\
      lookup_block cond_lbl func.fn_blocks =
        SOME <| bb_label := cond_lbl;
                bb_instructions :=
                  [mk_inst (st.cs_next_id + 5) EQ [Var cv; Var ev] [dv];
                   mk_inst (st.cs_next_id + 6) JNZ
                     [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
      (?bbb. lookup_block body_lbl func.fn_blocks = SOME bbb /\
             get_instruction bbb 0 =
               SOME (mk_inst (st.cs_next_id + 7) MSTORE [Var p; Var cv] [])) /\
      (~block_is_terminated sb1 ==>
       sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
       sj.cs_current_insts =
         sb1.cs_current_insts ++
         [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
       fn_has_code sb1 sj func) /\
      sj.cs_next_var = sb1.cs_next_var /\
      nv = STRING #"%" (toString sj.cs_next_var) /\
      lookup_block incr_lbl func.fn_blocks =
        SOME <| bb_label := incr_lbl;
                bb_instructions :=
                  [mk_inst sj.cs_next_id ADD [Var cv; Lit 1w] [nv];
                   mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [cv];
                   mk_inst (sj.cs_next_id + 2) JMP [Label cond_lbl] []] |> /\
      st'.cs_current_bb = exit_lbl /\ st'.cs_current_insts = []
Proof
  rpt strip_tac >>
  qspecl_then [`cenv`, `lctx`, `ty`, `id`, `fty`, `Literal a1 (IntL n1)`,
               `i2w n1`, `Literal a2 (IntL n2)`, `i2w n2`, `bound`, `stmts`,
               `st`, `st'`, `func`] mp_tac compile_for_range_parts >>
  impl_tac >- (simp[lower_value_int_lit] >> first_assum ACCEPT_TAC) >>
  simp[]
QED

(* The counter of a range loop over [n1, n2), as a word. *)
Theorem i2w_counter_ne:
  !n1 n2 k. n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) ==>
            (i2w (n1 + &k) : bytes32) <> i2w n2
Proof
  rpt strip_tac >>
  qabbrev_tac `N = Num (n2 - n1)` >>
  `&N = n2 - n1` by (simp[Abbr `N`] >> intLib.ARITH_TAC) >>
  `n2 = (n1 + &k) + &(N - k)` by
    (`&(N - k) = &N - &k : int` by simp[integerTheory.INT_SUB] >>
     intLib.ARITH_TAC) >>
  `(i2w n2 : bytes32) = i2w (n1 + &k) + n2w (N - k)` by
    (qpat_x_assum `n2 = _`
       (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
     simp[GSYM integer_wordTheory.word_i2w_add,
          integer_wordTheory.i2w_pos]) >>
  `i2w (n1 + &k) + n2w (N - k) = (i2w (n1 + &k) : bytes32)` by metis_tac[] >>
  `(n2w (N - k) : bytes32) = 0w` by
    metis_tac[wordsTheory.WORD_ADD_RID_UNIQ, wordsTheory.WORD_ADD_COMM] >>
  `N - k < dimword (:256) /\ 0 < N - k` by decide_tac >>
  qpat_x_assum `n2w (N - k) = 0w` mp_tac >>
  fs[wordsTheory.n2w_11, arithmeticTheory.LESS_MOD]
QED

Theorem i2w_counter_end:
  !n1 n2. n1 <= n2 ==> (i2w (n1 + &Num (n2 - n1)) : bytes32) = i2w n2
Proof
  rpt strip_tac >>
  `n1 + &Num (n2 - n1) = n2` by
    (`&Num (n2 - n1) = n2 - n1` by intLib.ARITH_TAC >> intLib.ARITH_TAC) >>
  simp[]
QED

Theorem i2w_counter_suc:
  !n1 k. (i2w (n1 + &k) : bytes32) + 1w = i2w (n1 + &(k + 1))
Proof
  rpt gen_tac >>
  `(1w : bytes32) = i2w 1` by simp[integer_wordTheory.i2w_pos] >>
  pop_assum SUBST1_TAC >> simp[integer_wordTheory.word_i2w_add] >>
  AP_TERM_TAC >> intLib.ARITH_TAC
QED
