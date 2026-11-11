(*
 * Statement simulation: the range loop (#637)
 *
 * The loop of For over a range, from the condition block: one iteration
 * (condition, body, increment) and, by induction from any counter value,
 * the loop to its end, a break, or an exit.
 *
 * TOP-LEVEL:
 *   for_code       — the loop's blocks and instructions, and the variables
 *                    and environment they use
 *   for_body_entry — the relation at the body's environment on entry
 *   for_iteration  — one pass of the range loop
 *   for_loop       — the range loop from any counter value
 *)

Theory stmtSimForLoop
Ancestors
  stmtSimProps
  stmtSimDefs
  loweringPosts
   stmtSimForParts stmtSimDeclStore
  list rich_list finite_map pred_set
  fragExec localPtrsProps  loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv loweringStateRelDefs valueEncoding valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation
  gasOutcome gasContext gasExemptCert gasSummary gasSummaryCompose stmtSimForRounds
  fragGasSeq fragGasMode fragGasPath gasCount
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

(* The block before a range loop, from its ALLOCA on: the ALLOCA and the
   JMP to the loop's entry block, charging nothing. *)
Theorem for_start_zero_path:
  !ctx func s0 s1 aa pre lbl entry_lbl i.
    lookup_block s0.vs_current_bb func.fn_blocks =
      SOME <| bb_label := lbl; bb_instructions :=
        pre ++ [aa; mk_inst i JMP [Label entry_lbl] []] |> /\
    s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
    aa.inst_opcode = ALLOCA /\ step_inst_base aa s0 = OK s1 /\
    s1.vs_current_bb = s0.vs_current_bb /\ ~s1.vs_halted ==>
    gas_marked_path F ctx func s0 0 (OK (jump_to entry_lbl s1))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = s1 with vs_inst_idx := SUC (LENGTH pre)` >>
  `gas_path_edge ctx func s0 0 (OK u)` by
    (simp[gas_path_edge_def] >> qexists_tac `0` >>
     simp[get_instruction_def, EL_LENGTH_APPEND, step_inst_non_invoke,
          gas_count_step_def, is_terminator_def, Abbr `u`]) >>
  `gas_path_edge ctx func u 0 (OK (jump_to entry_lbl s1))` by
    (simp[gas_path_edge_def, Abbr `u`] >> qexists_tac `0` >>
     simp[get_instruction_def, EL_APPEND2, step_inst_non_invoke,
          mk_inst_def, gas_count_step_def, is_terminator_def,
          step_jmp_behavior, jump_to_def] >>
     disj2_tac >> disj1_tac >> qexists_tac `entry_lbl` >> simp[]) >>
  `gas_path ctx func (jump_to entry_lbl s1) 0
      (OK (jump_to entry_lbl s1))` by
    (irule (cj 1 gas_path_rules) >> simp[jump_to_def]) >>
  drule (cj 2 gas_path_rules) >> disch_then drule >> simp[] >> strip_tac >>
  qpat_x_assum `gas_path_edge _ _ s0 _ _` mp_tac >>
  disch_then (mp_then Any mp_tac (cj 2 gas_path_rules)) >>
  disch_then drule >> simp[gas_marked_path_def]
QED

Theorem for_cond_zero_path[local]:
  !ctx func s cv ev dv a b lbl exit_lbl body_lbl j1 j2.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl; bb_instructions :=
        [mk_inst j1 EQ [Var cv; Var ev] [dv];
         mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
    s.vs_current_bb = lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    lookup_var cv s = SOME a /\ lookup_var ev s = SOME b ==>
    gas_marked_path F ctx func s 0
      (OK (jump_to (if a = b then exit_lbl else body_lbl)
        (update_var dv (bool_to_word (a = b)) s)))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = update_var dv (bool_to_word (a = b)) s with vs_inst_idx := 1` >>
  `gas_path_edge ctx func s 0 (OK u)` by
    (simp[gas_path_edge_def] >> qexists_tac `0` >>
     simp[get_instruction_def, mk_inst_def, step_inst_non_invoke,
          gas_count_step_def, is_terminator_def] >>
     `step_inst_base (mk_inst j1 EQ [Var cv; Var ev] [dv]) s =
        OK (update_var dv (bool_to_word (a = b)) s)` by
       (irule step_EQ >> simp[eval_operand_def]) >>
     gvs[mk_inst_def, Abbr `u`, update_var_def]) >>
  `gas_path_edge ctx func u 0
    (OK (jump_to (if a = b then exit_lbl else body_lbl)
      (update_var dv (bool_to_word (a = b)) s)))` by
    (`eval_operand (Var dv) u = SOME (bool_to_word (a = b))` by
       simp[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     drule venomExecProofsTheory.step_jnz_behavior >>
     disch_then (qspecl_then [`exit_lbl`, `body_lbl`, `j2`] assume_tac) >>
     simp[gas_path_edge_def, Abbr `u`, update_var_def] >>
     qexists_tac `0` >>
     simp[get_instruction_def, mk_inst_def, step_inst_non_invoke,
          gas_count_step_def, is_terminator_def] >>
     disj2_tac >> disj1_tac >>
     qexists_tac `if a = b then exit_lbl else body_lbl` >>
     Cases_on `a = b` >>
     gvs[bool_to_word_def, update_var_def, jump_to_def]) >>
  rewrite_tac[gas_marked_path_def] >>
  `gas_path ctx func
    (jump_to (if a = b then exit_lbl else body_lbl)
      (update_var dv (bool_to_word (a = b)) s)) 0
    (OK (jump_to (if a = b then exit_lbl else body_lbl)
      (update_var dv (bool_to_word (a = b)) s)))` by
    (irule (cj 1 gas_path_rules) >> simp[jump_to_def, update_var_def]) >>
  drule (cj 2 gas_path_rules) >> disch_then drule >> simp[] >> strip_tac >>
  qpat_x_assum `gas_path_edge _ _ s _ _` mp_tac >>
  disch_then (mp_then Any mp_tac (cj 2 gas_path_rules)) >>
  disch_then drule >> simp[]
QED

Theorem for_incr_zero_path[local]:
  !ctx func s cv nv c lbl cond_lbl i1 i2 i3.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl; bb_instructions :=
        [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
         mk_inst i2 ASSIGN [Var nv] [cv];
         mk_inst i3 JMP [Label cond_lbl] []] |> /\
    s.vs_current_bb = lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    lookup_var cv s = SOME c ==>
    gas_marked_path F ctx func s 0
      (OK (jump_to cond_lbl
        (update_var cv (c + 1w) (update_var nv (c + 1w) s))))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `code = [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
                       mk_inst i2 ASSIGN [Var nv] [cv]]` >>
  qabbrev_tac `t = update_var cv (c + 1w) (update_var nv (c + 1w) s)` >>
  `run_inst_seq code s = OK t` by
    (`step_inst_base (mk_inst i1 ADD [Var cv; Lit 1w] [nv]) s =
        OK (update_var nv (c + 1w) s)` by
       (irule step_ADD >> simp[eval_operand_def]) >>
     simp[Abbr `code`, Abbr `t`, run_inst_seq_def] >>
     simp[step_inst_base_def, mk_inst_def, eval_operand_def,
          lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `func`,
    `<| bb_label := lbl; bb_instructions := code ++
        [mk_inst i3 JMP [Label cond_lbl] []] |>`] mp_tac) >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >> strip_tac >>
  `gas_path_edge ctx func (t with vs_inst_idx := 2) 0
     (OK (jump_to cond_lbl t))` by
    (simp[gas_path_edge_def, Abbr `t`, update_var_def] >>
     qexists_tac `0` >>
     simp[get_instruction_def, step_inst_non_invoke, mk_inst_def,
          gas_count_step_def, is_terminator_def, step_jmp_behavior,
          jump_to_def, update_var_def] >>
     disj2_tac >> disj1_tac >> qexists_tac `cond_lbl` >> simp[]) >>
  `gas_path ctx func (jump_to cond_lbl t) 0 (OK (jump_to cond_lbl t))` by
    (irule (cj 1 gas_path_rules) >> simp[Abbr `t`, jump_to_def, update_var_def]) >>
  drule (cj 2 gas_path_rules) >> disch_then drule >> simp[] >> strip_tac >>
  qpat_x_assum `gas_path _ _ s _ _` mp_tac >>
  disch_then (mp_then Any mp_tac gas_path_then) >>
  disch_then drule >> simp[gas_marked_path_def, Abbr `t`]
QED

Theorem for_store_zero_path[local]:
  !ctx func s bb iid p cv w value.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst iid MSTORE [Var p; Var cv] []) /\
    ~s.vs_halted /\ lookup_var p s = SOME w /\ lookup_var cv s = SOME value ==>
    gas_marked_path F ctx func s 0
      (OK (mstore (w2n w) value s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst iid MSTORE [Var p; Var cv] []) s =
     OK (mstore (w2n w) value s)` by
    (irule step_MSTORE >> simp[eval_operand_def]) >>
  `gas_path_edge ctx func s 0
     (OK (mstore (w2n w) value s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (simp[gas_path_edge_def] >> qexists_tac `0` >>
     simp[step_inst_non_invoke, gas_count_step_def, mk_inst_def,
          is_terminator_def] >> gvs[mk_inst_def, mstore_def, LET_THM]) >>
  rewrite_tac[gas_marked_path_def] >>
  `gas_path ctx func (mstore (w2n w) value s with vs_inst_idx := SUC s.vs_inst_idx)
     0 (OK (mstore (w2n w) value s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule (cj 1 gas_path_rules) >> simp[mstore_def, LET_THM]) >>
  drule (cj 2 gas_path_rules) >> disch_then drule >> simp[]
QED

Theorem for_round_source_cases[local]:
  !cx tyv id stmts v es gs res ee.
    (do push_scope_with_var id tyv v;
        finally (try (do eval_stmts cx stmts; return F od)
                     handle_loop_exception) pop_scope od)
      (es with gas_obs := gs) = (res, ee) ==>
    ?r2 es2 sc rest.
      eval_stmts cx stmts
        (es with <| scopes :=
          (FEMPTY |+ (id, <| assignable := F; type := tyv;
                             value := v; popped := [] |>)) :: es.scopes;
                    gas_obs := gs |>) = (r2, es2) /\
      es2.scopes = sc :: rest /\
      MAP FDOM rest = MAP FDOM es.scopes /\
      ee = es2 with scopes := rest /\
      ((r2 = INL () \/ r2 = INR ContinueException) /\ res = INL F \/
       r2 = INR BreakException /\ res = INL T \/
       (?e. r2 = INR e /\ e <> BreakException /\ e <> ContinueException /\
            res = INR e))
Proof
  rpt gen_tac >>
  `!x. x with scopes updated_by
         CONS (FEMPTY |+ (id, <| assignable := F; type := tyv;
                                value := v; popped := [] |>)) =
       x with scopes :=
         (FEMPTY |+ (id, <| assignable := F; type := tyv;
                            value := v; popped := [] |>)) :: x.scopes` by
    simp[evaluation_state_component_equality] >>
  simp[ignore_bind_def, bind_def, push_scope_with_var_def, return_def] >>
  qmatch_goalsub_abbrev_tac `eval_stmts cx stmts entry` >>
  Cases_on `eval_stmts cx stmts entry` >> rename1 `_ = (r2, es2)` >>
  `es2.scopes <> [] /\ MAP FDOM (TL es2.scopes) = MAP FDOM es.scopes` by
    (drule eval_stmts_preserves_scopes_dom >>
     simp[preserves_scopes_dom_def, Abbr `entry`]) >>
  Cases_on `es2.scopes` >> gvs[] >>
  Cases_on `r2` >>
  simp[finally_def, try_def, ignore_bind_def, bind_def, return_def, pop_scope_def,
       raise_def] >>
  rename1 `handle_loop_exception ex` >>
  Cases_on `ex = ContinueException` >> Cases_on `ex = BreakException` >>
  gvs[handle_loop_exception_def, finally_def, return_def, raise_def,
      pop_scope_def, bind_def] >> metis_tac[]
QED

Theorem for_body_gas_admissible[local]:
  !cx tyv id stmts v vs lctx es exit_lbl incr_lbl.
    gas_admissible (eval_for cx tyv id stmts (Value v::vs))
      (stmt_res_ok lctx) es /\ lookup_scopes id es.scopes = NONE ==>
    gas_admissible (eval_stmts cx stmts)
      (stmt_res_ok (InLoop exit_lbl incr_lbl))
      (es with <| scopes :=
        (FEMPTY |+ (id, <| assignable := F; type := tyv;
                           value := v; popped := [] |>)) :: es.scopes;
                  gas_obs := [] |>)
Proof
  rpt gen_tac >> strip_tac >>
  simp[gas_admissible_def] >> rpt gen_tac >> strip_tac >>
  rename1 `eval_stmts cx stmts _ = (res, ee)` >>
  Cases_on `eval_for cx tyv id stmts (Value v::vs) (es with gas_obs := gs)` >>
  rename1 `_ = (lr, le)` >>
  `stmt_res_ok lctx lr` by
    (gvs[gas_admissible_def] >> metis_tac[]) >>
  drule eval_for_cons_cases >> simp[] >> strip_tac >>
  gvs[] >> metis_tac[stmt_res_ok_def]
QED

Theorem for_round_preserves[local]:
  !P cx tyv id stmts n1 n2 j es gs ee.
    (!ei k obs r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ k < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with <| scopes :=
           (FEMPTY |+ (id, <| assignable := F; type := tyv;
                              value := IntV (n1 + &k); popped := [] |>)) :: ei.scopes;
                     gas_obs := obs |>) = (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==> P (es2 with scopes := rest)) /\
    P es /\ lookup_scopes id es.scopes = NONE /\ j < Num (n2 - n1) /\
    (do push_scope_with_var id tyv (IntV (n1 + &j));
        finally (try (do eval_stmts cx stmts; return F od)
                     handle_loop_exception) pop_scope od)
      (es with gas_obs := gs) = (INL F, ee) ==>
    P ee /\ lookup_scopes id ee.scopes = NONE
Proof
  rpt gen_tac >> strip_tac >>
  drule for_round_source_cases >> strip_tac >> gvs[] >>
  (conj_tac >- metis_tac[] >>
   qspecl_then [`id`, `es.scopes`, `rest`] mp_tac
     vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom >> simp[])
QED
Theorem for_round_exempt_cert[local]:
  !memory tops ctx func cx tyv id stmts v es s t marks err ee leaf finish.
    gas_marked_exec memory (ctx,func) (push_scope_with_var id tyv v)
      (es,s) [] (INL ())
      (es with scopes :=
        (FEMPTY |+ (id, <| assignable := F; type := tyv;
                           value := v; popped := [] |>)) :: es.scopes) (OK t) /\
    gas_exempt_cert memory tops (ctx,func)
      (ignore_bind (eval_stmts cx stmts) (return ()))
      (es with <| scopes :=
        (FEMPTY |+ (id, <| assignable := F; type := tyv;
                           value := v; popped := [] |>)) :: es.scopes;
                  gas_obs := [] |>,t) marks (err,ee) (leaf,finish) ==>
    ?sc rest. ee.scopes = sc :: rest /\
      gas_exempt_cert memory tops (ctx,func)
        (ignore_bind
          (do push_scope_with_var id tyv v;
              finally (try (do eval_stmts cx stmts; return F od)
                           handle_loop_exception) pop_scope od) (return ()))
        (es,s) marks (err,ee with scopes := rest) (leaf,finish)
Proof
  rpt gen_tac >> strip_tac >>
  `?sc rest. ee.scopes = sc :: rest` by
    (drule gas_exempt_cert_execution >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     simp[ignore_bind_def, bind_def] >>
     qmatch_goalsub_abbrev_tac `eval_stmts cx stmts entry` >>
     Cases_on `eval_stmts cx stmts entry` >>
     rename1 `_ = (res,st)` >> Cases_on `res` >>
     simp[return_def] >> strip_tac >> gvs[] >>
     drule eval_stmts_preserves_scopes_dom >>
     simp[preserves_scopes_dom_def, Abbr `entry`] >>
     Cases_on `ee.scopes` >> simp[]) >>
  qexistsl_tac [`sc`, `rest`] >> simp[] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  drule gas_exempt_cert_bind_unit >> simp[] >> disch_then irule >>
  rewrite_tac[GSYM ignore_bind_def, ignore_bind_finally_unit,
              ignore_bind_try_unit, ignore_bind_return_twice] >>
  irule gas_exempt_cert_cleanup >> qexists_tac `ee` >>
  conj_tac >- simp[pop_scope_def, return_def] >>
  irule gas_exempt_cert_handler >> qexists_tac `ee` >>
  simp[handle_loop_exception_def, ignore_bind_def, bind_def, raise_def]
QED


Theorem stmt_state_rel_declare_word_alloca[local]:
  !func cenv cx es s id p sz w inst v tyv sc rest a ctx.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    32 <= sz /\ word_value v /\ type_memory_size tyv = 32 /\
    word_memory_type tyv ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
         (sc |+ (id, <| assignable := a; type := tyv; value := v; popped := [] |>)) :: rest)
      (mstore (w2n w) (val_to_w256 v) s)
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes s /\
   immutable_alloca_sep func cenv cx es s /\
   immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
     (mstore (w2n w) (val_to_w256 v) s)` by
    (irule immutables_rel_mstore_alloca >>
     simp[] >> qexistsl_tac [`w2n w`, `func`, `inst`, `sz`] >> simp[]) >>
  irule stmt_state_rel_declare_memory >>
  simp[word_value_wf] >> qexistsl_tac [`inst`, `s`, `w`] >>
  simp[word_value_memory_rel] >> conj_tac
  >- (rpt strip_tac >>
      `regions_disjoint (w2n w) sz b sz'` by
        (irule local_ptrs_rel_alloca_disjoint >>
         qexistsl_tac [`cenv`, `func`, `inst`, `n`, `p`, `es.scopes`, `s`] >> fs[stmt_state_rel_def]) >>
      irule EQ_SYM >> irule mstore_mem_bytes_at_disjoint >>
      fs[regions_disjoint_def] >> decide_tac) >>
  simp[mstore_def, lookup_var_def, LET_THM] >> metis_tac[]
QED

(* ===== The range loop ===== *)

(* A range loop's iteration starts: the condition block finds the counter
   short of the end and jumps to the body block, whose MSTORE stores the
   counter into the loop variable.  The relation then holds at the body's
   environment bc, for the source state with the loop variable's scope
   pushed. *)
Theorem for_body_entry_alloca[local]:
  !ctx func cenv bc cx esk cc id tyv p sz w ainst cv ev dv n1 n2 k
   cond_lbl exit_lbl body_lbl j1 j2 j3 bbb.
    lookup_block cond_lbl func.fn_blocks =
      SOME <| bb_label := cond_lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var cv; Var ev] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
    lookup_block body_lbl func.fn_blocks = SOME bbb /\
    get_instruction bbb 0 = SOME (mk_inst j3 MSTORE [Var p; Var cv] []) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel ctx func cenv cx esk cc /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) /\
    n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) /\
    lookup_scopes id esk.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!n. n <> id ==> FLOOKUP bc.ce_vars n = FLOOKUP cenv.ce_vars n) /\
    bc.ce_module_vars = cenv.ce_module_vars /\
    bc.ce_module = cenv.ce_module /\ bc.ce_is_ctor = cenv.ce_is_ctor /\
    bc.ce_imm_alloca = cenv.ce_imm_alloca /\
    bc.ce_module_var_type = cenv.ce_module_var_type /\
    not_local_ptr cenv esk.scopes dv /\
    not_local_ptr bc (FEMPTY :: esk.scopes) p /\ dv <> p /\ dv <> cv /\
    MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
    ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
    32 <= sz /\ type_memory_size tyv = 32 /\ word_memory_type tyv ==>
    ?s2. s2.vs_current_bb = body_lbl /\ s2.vs_inst_idx = 1 /\
         ~s2.vs_halted /\
         stmt_state_rel ctx func bc cx
           (esk with scopes :=
              (FEMPTY |+ (id, <| assignable := F; type := tyv;
                                 value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes)
           s2 /\
         (!x. x <> dv ==> lookup_var x s2 = lookup_var x cc) /\
         s2.vs_allocas = cc.vs_allocas /\
         gas_marked_path F ctx func cc 0 (OK s2) /\
         !fuel rr. run_from fuel ctx func s2 = rr /\ (!e. rr <> Error e) ==>
                   ?fuel'. run_from fuel' ctx func cc = rr
Proof
  rpt gen_tac >> strip_tac >>
  `(i2w (n1 + &k) : bytes32) <> i2w n2` by metis_tac[i2w_counter_ne] >>
  qabbrev_tac `s1 = jump_to body_lbl (update_var dv (bool_to_word F) cc)` >>
  `gas_marked_path F ctx func cc 0 (OK s1)` by
    (drule_all for_cond_zero_path >> simp[Abbr `s1`]) >>
  `lookup_var p s1 = SOME w /\ lookup_var cv s1 = SOME (i2w (n1 + &k)) /\
   s1.vs_current_bb = body_lbl /\ s1.vs_inst_idx = 0 /\ ~s1.vs_halted /\
   s1.vs_allocas = cc.vs_allocas /\
   (!x. x <> dv ==> lookup_var x s1 = lookup_var x cc)` by
    (simp[Abbr `s1`, jump_to_def, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE] >> fs[lookup_var_def]) >>
  qabbrev_tac `s2 = mstore (w2n w) (i2w (n1 + &k)) s1 with vs_inst_idx := 1` >>
  `gas_marked_path F ctx func s1 0 (OK s2)` by
    (`gas_marked_path F ctx func s1 0
       (OK (mstore (w2n w) (i2w (n1 + &k)) s1 with
            vs_inst_idx := SUC s1.vs_inst_idx))` suffices_by simp[Abbr `s2`] >>
     irule for_store_zero_path >> simp[] >> qexistsl_tac [`cv`, `j3`, `p`] >> simp[]) >>
  `gas_marked_path F ctx func cc 0 (OK s2)` by
    (qpat_x_assum `gas_marked_path F ctx func cc _ (OK s1)` mp_tac >>
     disch_then (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then drule >> simp[]) >>
  `!fuel rr. run_from fuel ctx func s2 = rr /\ (!e. rr <> Error e) ==>
             ?fuel'. run_from fuel' ctx func cc = rr` by
    (qpat_x_assum `gas_marked_path F ctx func cc _ (OK s2)` mp_tac >>
     simp[gas_marked_path_def] >> metis_tac[gas_path_normal]) >>
  `stmt_state_rel ctx func cenv cx (esk with scopes := FEMPTY :: esk.scopes) s1` by
    (simp[Abbr `s1`, stmt_state_rel_jump_to, stmt_state_rel_push_scope] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `stmt_state_rel ctx func bc cx (esk with scopes := FEMPTY :: esk.scopes) s1` by
    (irule stmt_state_rel_cenv_cong >> qexists_tac `cenv` >> simp[] >>
     rpt strip_tac >> Cases_on `n = id` >> gvs[lookup_scopes_def] >>
     res_tac >> gvs[]) >>
  `stmt_state_rel ctx func bc cx
     (esk with scopes :=
       (FEMPTY |+ (id, <| assignable := F; type := tyv;
                          value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes)
     (mstore (w2n w) (i2w (n1 + &k)) s1)` by
    (rewrite_tac[GSYM val_to_w256_def] >>
     irule (SRULE [] (Q.SPECL [`func`, `bc`, `cx`,
       `esk with scopes := FEMPTY :: esk.scopes`] stmt_state_rel_declare_word_alloca)) >>
     simp[lookup_scopes_def, word_value_def] >>
     qexists_tac `ainst` >> simp[]) >>
  qexists_tac `s2` >>
  simp[Abbr `s2`, stmt_state_rel_inst_idx] >>
  rpt conj_tac
  >- simp[mstore_def, LET_THM]
  >- simp[mstore_def, LET_THM]
  >- (rpt strip_tac >> fs[mstore_def, LET_THM, lookup_var_def])
  >- simp[mstore_def, LET_THM] >>
  metis_tac[]
QED


Theorem for_body_entry:
  !ctx func cenv bc cx esk cc id tyv p sz w ainst cv ev dv n1 n2 k
   cond_lbl exit_lbl body_lbl j1 j2 j3 bbb cap.
    lookup_block cond_lbl func.fn_blocks =
      SOME <| bb_label := cond_lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var cv; Var ev] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
    lookup_block body_lbl func.fn_blocks = SOME bbb /\
    get_instruction bbb 0 = SOME (mk_inst j3 MSTORE [Var p; Var cv] []) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel ctx func cenv cx esk cc /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) /\
    n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) /\
    lookup_scopes id esk.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!n. n <> id ==> FLOOKUP bc.ce_vars n = FLOOKUP cenv.ce_vars n) /\
    bc.ce_module_vars = cenv.ce_module_vars /\
    bc.ce_module = cenv.ce_module /\ bc.ce_is_ctor = cenv.ce_is_ctor /\
    bc.ce_imm_alloca = cenv.ce_imm_alloca /\
    bc.ce_module_var_type = cenv.ce_module_var_type /\
    not_local_ptr cenv esk.scopes dv /\
    not_local_ptr bc (FEMPTY :: esk.scopes) p /\ dv <> p /\ dv <> cv /\
    MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
    ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
    32 <= sz /\ type_memory_size tyv = 32 /\ word_memory_type tyv /\
    cap <= w2n w /\
    (cenv.ce_is_ctor ==>
       immutable_prefix_bound cenv cx.txn.target cenv.ce_module esk cap) ==>
    ?s2. s2.vs_current_bb = body_lbl /\ s2.vs_inst_idx = 1 /\
         ~s2.vs_halted /\
         stmt_state_rel ctx func bc cx
           (esk with scopes :=
              (FEMPTY |+ (id, <| assignable := F; type := tyv;
                                 value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes)
           s2 /\
         (!x. x <> dv ==> lookup_var x s2 = lookup_var x cc) /\
         s2.vs_allocas = cc.vs_allocas /\
         !fuel rr. run_from fuel ctx func s2 = rr /\ (!e. rr <> Error e) ==>
                   ?fuel'. run_from fuel' ctx func cc = rr
Proof
  rpt gen_tac >> strip_tac >> drule_all for_body_entry_alloca >>
  strip_tac >> qexists_tac `s2` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  qexists_tac `fuel` >> simp[]
QED
(* Every non-Error result from a is one from b, and from b one from c:
   then from a one from c. *)
Theorem run_from_results_trans[local]:
  !ctx func a b c.
    (!fuel r. run_from fuel ctx func a = r /\ (!e. r <> Error e) ==>
              ?fuel'. run_from fuel' ctx func b = r) /\
    (!fuel r. run_from fuel ctx func b = r /\ (!e. r <> Error e) ==>
              ?fuel'. run_from fuel' ctx func c = r) ==>
    !fuel r. run_from fuel ctx func a = r /\ (!e. r <> Error e) ==>
             ?fuel'. run_from fuel' ctx func c = r
Proof
  metis_tac[]
QED

(* The range loop's code, as compile_for_range_parts lays it out, and the
   facts about its variables and environments that every iteration uses:
   the condition, body and increment blocks; the body's code between sb0
   and sb1 and its jump to the increment block at sj; the loop variable's
   ALLOCA ainst and its pointer p in bc, which is cenv with id bound; the
   counter cv, end ev, condition dv and next counter nv, distinct from p
   and from each other as the loop needs, and cv, dv and nv no local's
   pointers.  The loop variable has a scalar word layout, not merely a
   32-byte footprint (which could also describe an aggregate). *)
Definition for_code_def:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj <=>
    lookup_block cond_lbl func.fn_blocks =
      SOME <| bb_label := cond_lbl;
              bb_instructions :=
                [mk_inst j1 EQ [Var cv; Var ev] [dv];
                 mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
    lookup_block body_lbl func.fn_blocks = SOME bbb /\
    get_instruction bbb 0 = SOME (mk_inst j3 MSTORE [Var p; Var cv] []) /\
    lookup_block incr_lbl func.fn_blocks =
      SOME <| bb_label := incr_lbl;
              bb_instructions := [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
                                  mk_inst i2 ASSIGN [Var nv] [cv];
                                  mk_inst i3 JMP [Label cond_lbl] []] |> /\
    compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((), sb1) /\
    fn_has_code sb0 sb1 func /\ local_ptrs_reserved bc sb0 /\
    sb0.cs_current_bb = body_lbl /\ LENGTH sb0.cs_current_insts = 1 /\
    ~block_is_terminated sb0 /\
    (~block_is_terminated sb1 ==>
     sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
     sj.cs_current_insts =
       sb1.cs_current_insts ++
       [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
     fn_has_code sb1 sj func) /\
    fn_inst_ids_distinct func /\
    MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
    ainst.inst_outputs = [p] /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!n. n <> id ==> FLOOKUP bc.ce_vars n = FLOOKUP cenv.ce_vars n) /\
    bc with <| ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
               ce_dynarray_capacity := cenv.ce_dynarray_capacity |> = cenv /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!scs. not_local_ptr cenv scs cv /\ not_local_ptr cenv scs dv /\
           not_local_ptr cenv scs nv) /\
    dv <> p /\ dv <> cv /\ dv <> ev /\ nv <> cv /\ nv <> ev /\ nv <> p /\
    cv <> ev /\ cv <> p /\ ev <> p /\
    not_fresh_at sb0 cv /\ not_fresh_at sb0 ev /\ not_fresh_at sb0 p /\
    32 <= sz /\ type_memory_size tyv = 32 /\ word_memory_type tyv
End

Theorem for_body_lands_path[local]:
  !ctx func sb sj s res exit_lbl incr_lbl.
    stmt_lands (InLoop exit_lbl incr_lbl) sb res s /\ ~s.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb) /\
    (~block_is_terminated sb ==>
      sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
      sj.cs_current_insts = sb.cs_current_insts ++
        [mk_inst sb.cs_next_id JMP [Label incr_lbl] []] /\
      fn_has_code sb sj func) ==>
    gas_marked_path F ctx func s 0
      (OK (if res = INL () then jump_to incr_lbl s else s)) /\
    (if res = INL () then jump_to incr_lbl s else s).vs_inst_idx = 0 /\
    (res = INR BreakException ==> s.vs_current_bb = exit_lbl) /\
    (res <> INR BreakException ==>
      (if res = INL () then jump_to incr_lbl s else s).vs_current_bb = incr_lbl)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `res = INL ()`
  >- (gvs[stmt_lands_def] >>
      `gas_path ctx func s 0 (OK (jump_to incr_lbl s))` by
        (irule emit_jump_zero_path >> simp[] >> qexistsl_tac [`sb`, `sj`] >> simp[]) >>
      simp[gas_marked_path_def, jump_to_def]) >>
  gvs[stmt_lands_def] >> simp[jump_to_def] >>
  rewrite_tac[gas_marked_path_def] >> irule (cj 1 gas_path_rules) >> simp[]
QED

Theorem for_exec_zero_suffix[local]:
  !memory ctx func source es s marks res ee t u.
    gas_marked_exec memory (ctx,func) source (es,s) marks res ee (OK t) /\
    gas_marked_path memory ctx func t 0 (OK u) ==>
    gas_marked_exec memory (ctx,func) source (es,s) marks res ee (OK u)
Proof
  rpt gen_tac >> rewrite_tac[gas_marked_exec_def] >> strip_tac >> simp[] >>
  qpat_x_assum `gas_marked_path _ _ _ s _ _` mp_tac >>
  disch_then (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[]
QED

Theorem for_body_exit_cleanup[local]:
  !RetQ ee res r rest.
    (!tail. stmt_exit RetQ (ee with gas_obs := tail) res r) ==>
    ?ex. res = INR ex /\ ex <> BreakException /\ ex <> ContinueException /\
      !tail. stmt_exit RetQ ((ee with scopes := rest) with gas_obs := tail)
        (INR ex) r
Proof
  rpt gen_tac >> strip_tac >>
  `res <> INL () /\ res <> INR BreakException /\ res <> INR ContinueException` by
    (first_x_assum (qspec_then `[]` mp_tac) >> metis_tac[stmt_exit_loop_ctl]) >>
  Cases_on `res` >> gvs[] >>
  gvs[stmt_exit_def]
QED

Theorem for_body_cleanup_exec[local]:
  !memory ctx func cx stmts es s marks res ee r sc rest.
    gas_marked_exec memory (ctx,func) (eval_stmts cx stmts)
      (es,s) marks res ee r /\ ee.scopes = sc :: rest ==>
    gas_marked_exec memory (ctx,func)
      (finally (try (do eval_stmts cx stmts; return F od)
                    handle_loop_exception) pop_scope)
      (es,s) marks
      (case res of INL u => INL F
       | INR ex => if ex = BreakException then INL T
                   else if ex = ContinueException then INL F else INR ex)
      (ee with scopes := rest) r
Proof
  rpt gen_tac >> simp[gas_marked_exec_def] >> strip_tac >> simp[] >>
  gen_tac >> simp[finally_def, try_def, ignore_bind_def, bind_def] >>
  Cases_on `res` >> simp[return_def, pop_scope_def, bind_def] >>
  rename1 `handle_loop_exception ex` >>
  Cases_on `ex = BreakException` >> Cases_on `ex = ContinueException` >>
  gvs[handle_loop_exception_def, return_def, raise_def, bind_def, pop_scope_def]
QED

Theorem for_incr_finish[local]:
  !ctx func cenv cx ee s cv nv ev p c e w lbl cond_lbl i1 i2 i3 st old.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl; bb_instructions :=
        [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
         mk_inst i2 ASSIGN [Var nv] [cv];
         mk_inst i3 JMP [Label cond_lbl] []] |> /\
    s.vs_current_bb = lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    stmt_state_rel ctx func cenv cx ee s /\
    not_local_ptr cenv ee.scopes cv /\ not_local_ptr cenv ee.scopes nv /\
    lookup_var cv s = SOME c /\ lookup_var ev s = SOME e /\
    lookup_var p s = SOME w /\ cv <> ev /\ nv <> ev /\ cv <> p /\ nv <> p /\
    (!x. not_fresh_at st x ==> x <> cv /\ x <> nv) /\
    (!x v. not_fresh_at st x /\ lookup_var x old = SOME v ==> lookup_var x s = SOME v) /\
    (!a b. FLOOKUP old.vs_allocas a = SOME b ==> FLOOKUP s.vs_allocas a = SOME b) ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      t.vs_current_bb = cond_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      stmt_state_rel ctx func cenv cx ee t /\
      lookup_var cv t = SOME (c + 1w) /\ lookup_var ev t = SOME e /\
      lookup_var p t = SOME w /\
      (!x v. not_fresh_at st x /\ lookup_var x old = SOME v ==> lookup_var x t = SOME v) /\
      (!a b. FLOOKUP old.vs_allocas a = SOME b ==> FLOOKUP t.vs_allocas a = SOME b)
Proof
  rpt gen_tac >> strip_tac >> drule_all for_incr_zero_path >> strip_tac >>
  qexists_tac `jump_to cond_lbl (update_var cv (c + 1w) (update_var nv (c + 1w) s))` >>
  `stmt_state_rel ctx func cenv cx ee
     (update_var cv (c + 1w) (update_var nv (c + 1w) s))` by
    (irule stmt_state_rel_update_var >> simp[] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  simp[stmt_state_rel_jump_to] >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >> metis_tac[lookup_var_def]
QED

Theorem for_body_scopes[local]:
  !cx stmts entry res ee sc rest.
    eval_stmts cx stmts entry = (res,ee) /\ entry.scopes = sc :: rest /\
    (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
    preserves_scopes_dom entry ee /\ ee.scopes <> [] /\
    (!n. n IN FDOM (HD ee.scopes) ==>
         lookup_scopes n (TL ee.scopes) = NONE)
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_stmts_preserves_scopes_dom >> strip_tac >>
  (conj_tac >- simp[]) >>
  `ee.scopes <> [] /\ MAP FDOM rest = MAP FDOM (TL ee.scopes)` by
    gvs[preserves_scopes_dom_def] >>
  simp[] >> rpt strip_tac >> Cases_on `n IN FDOM sc`
  >- (irule lookup_scopes_none_map_fdom >> qexists_tac `rest` >> simp[]) >>
  drule eval_stmts_new_in_head_not_in_tail >>
  disch_then (qspec_then `n` mp_tac) >> simp[]
QED

Theorem for_body_post_pop[local]:
  !ctx func cx lctx bc bc' sa sb s0 res ee t cenv entry sc rest.
    stmt_post ctx func cx lctx bc bc' sa sb s0 res ee t /\
    cenv_top_ext cenv bc entry.scopes /\ entry.scopes = sc :: rest /\
    preserves_scopes_dom entry ee /\
    (!n. n IN FDOM (HD ee.scopes) ==> lookup_scopes n (TL ee.scopes) = NONE) ==>
    ?sc' rest'. ee.scopes = sc' :: rest' /\
      stmt_state_rel ctx func cenv cx (ee with scopes := rest') t
Proof
  rpt gen_tac >> simp[stmt_post_def] >> strip_tac >>
  gvs[preserves_scopes_dom_def] >>
  Cases_on `ee.scopes` >> gvs[] >>
  rename1 `ee.scopes = sc' :: rest'` >>
  `cenv_top_ext cenv cenv'' (sc' :: rest')` by
    (irule cenv_top_ext_trans >> qexistsl_tac [`bc`, `entry.scopes`] >> simp[]) >>
  irule stmt_state_rel_pop_top_ext >>
  (conj_tac >- (qexists_tac `sc'` >> simp[])) >>
  qexists_tac `cenv''` >> simp[]
QED

Theorem for_round_prepare[local]:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  not_local_ptr bc (FEMPTY :: esk.scopes) p /\
  st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
  (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
  n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) /\
  cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
  stmt_state_rel ctx func cenv cx esk cc /\ lookup_scopes id esk.scopes = NONE /\
  lookup_var cv cc = SOME (i2w (n1 + &k)) /\
  lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
  FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) /\
  stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
    (esk with <| scopes := (FEMPTY |+ (id, <| assignable := F; type := tyv;
      value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes; gas_obs := [] |>) /\
  gas_admissible (eval_for cx tyv id stmts (Value (IntV (n1 + &k)) :: vs))
    (stmt_res_ok lctx) esk ==>
  ?s2. gas_marked_exec F (ctx,func)
      (push_scope_with_var id tyv (IntV (n1 + &k))) (esk,cc) [] (INL ())
      (esk with scopes := (FEMPTY |+ (id, <| assignable := F; type := tyv;
        value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes) (OK s2) /\
    (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==> lookup_var x s2 = SOME v) /\
    lookup_var cv s2 = SOME (i2w (n1 + &k)) /\
    lookup_var ev s2 = SOME (i2w n2) /\ lookup_var p s2 = SOME w /\
    s2.vs_allocas = cc.vs_allocas /\
    gas_outcome F (cx_tops cx) (ctx,func) (eval_stmts cx stmts)
      (esk with <| scopes := (FEMPTY |+ (id, <| assignable := F; type := tyv;
        value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes; gas_obs := [] |>,s2)
      (stmt_post ctx func cx (InLoop exit_lbl incr_lbl) bc
        (FST (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0)) sb0 sb1 s2)
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >> fs[for_code_def] >>
  `bc.ce_module_vars = cenv.ce_module_vars /\
   bc.ce_module = cenv.ce_module /\ bc.ce_is_ctor = cenv.ce_is_ctor /\
   bc.ce_imm_alloca = cenv.ce_imm_alloca /\
   bc.ce_module_var_type = cenv.ce_module_var_type` by
    (qpat_assum `_ = cenv` (fn th => ONCE_REWRITE_TAC [SYM th]) >> simp[]) >>
  `not_local_ptr cenv esk.scopes dv` by metis_tac[] >>
  drule_all for_body_entry_alloca >> strip_tac >>
  `ret_pc_ok bc sb0 s2` by
    (drule ret_pc_ok_frame >> disch_then (qspecl_then [`bc`, `sb0`, `s2`] mp_tac) >>
     (impl_tac >- (conj_tac
     >- (qpat_assum `_ = cenv` (fn th => ONCE_REWRITE_TAC [SYM th]) >> simp[]) >>
     (conj_tac >- simp[]) >> rpt strip_tac >>
     qpat_x_assum `!x. not_fresh_at st x ==> _` drule >> strip_tac >>
     qpat_x_assum `!x. x <> dv ==> lookup_var x s2 = _` drule >> simp[])) >> simp[]) >>
  `gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit_lbl incr_lbl))
    (esk with <| scopes :=
       (FEMPTY |+ (id, <| assignable := F; type := tyv;
                          value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes;
                 gas_obs := [] |>)` by
    (drule_all for_body_gas_admissible >> simp[]) >>
  qexists_tac `s2` >>
  (conj_tac >- simp[gas_marked_exec_def, push_scope_with_var_def, return_def,
    evaluation_state_component_equality, combinTheory.o_DEF]) >>
  (conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[])) >>
  simp[] >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [stmt_frag_def, stmt_framed_frag_def]) >>
  disch_then (qspecl_then [`sb0`, `sb1`, `s2`,
     `FST (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0)`] mp_tac) >>
  (impl_tac >- (gvs[compile_stmts_env] >>
    drule msg_gas_state_frame >>
    disch_then (qspecl_then [`s2.vs_gas_readings`, `s2.vs_inst_idx`, `[]`]
      (mp_tac o SIMP_RULE (srw_ss()) [])) >> simp[])) >> simp[]
QED

Theorem for_body_finish[local]:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  st.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at st x ==> x <> cv /\ x <> nv) /\
  entry.scopes = (FEMPTY |+ (id, <| assignable := F; type := tyv;
    value := IntV v; popped := [] |>)) :: esk.scopes /\
  lookup_scopes id esk.scopes = NONE /\
  preserves_scopes_dom entry ee /\ ee.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
  stmt_post ctx func cx (InLoop exit_lbl incr_lbl) bc bc' sb0 sb1 s2 res ee t /\
  lookup_var cv s2 = SOME c /\ lookup_var ev s2 = SOME e /\ lookup_var p s2 = SOME w /\
  (!x z. not_fresh_at st x /\ lookup_var x old = SOME z ==> lookup_var x s2 = SOME z) /\
  (!a b. FLOOKUP old.vs_allocas a = SOME b ==> FLOOKUP s2.vs_allocas a = SOME b) ==>
  ?broke u. (res = INR BreakException <=> broke) /\
    gas_marked_path F ctx func t 0 (OK u) /\
    u.vs_inst_idx = 0 /\ ~u.vs_halted /\
    stmt_state_rel ctx func cenv cx (ee with scopes := rest) u /\
    (!x z. not_fresh_at st x /\ lookup_var x old = SOME z ==> lookup_var x u = SOME z) /\
    (!a b. FLOOKUP old.vs_allocas a = SOME b ==> FLOOKUP u.vs_allocas a = SOME b) /\
    (broke ==> u.vs_current_bb = exit_lbl) /\
    (~broke ==> u.vs_current_bb = cond_lbl /\ lookup_var cv u = SOME (c + 1w) /\
      lookup_var ev u = SOME e /\ lookup_var p u = SOME w)
Proof
  strip_tac >>
  `cenv_top_ext cenv bc entry.scopes` by
    (fs[for_code_def, cenv_top_ext_def] >> rpt strip_tac >>
     `n = id` by metis_tac[] >> gvs[] >> metis_tac[]) >>
  `!n. n IN FDOM (HD ee.scopes) ==> lookup_scopes n (TL ee.scopes) = NONE`
    by simp[] >>
  drule_all for_body_post_pop >> strip_tac >> gvs[] >>
  fs[for_code_def, stmt_post_def] >>
  `(!x z. not_fresh_at st x /\ lookup_var x old = SOME z ==> lookup_var x t = SOME z) /\
   lookup_var cv t = SOME c /\ lookup_var ev t = SOME e /\ lookup_var p t = SOME w /\
   (!a b. FLOOKUP old.vs_allocas a = SOME b ==> FLOOKUP t.vs_allocas a = SOME b)` by
    (rpt conj_tac >> rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `res = INL () ==> ~block_is_terminated sb1` by simp[] >>
  drule_all for_body_lands_path >> strip_tac >>
  Cases_on `res = INR BreakException`
  >- (qexists_tac `t` >> simp[] >>
      fs[stmt_lands_def] >> simp[]) >>
  qpat_x_assum `!ctx. gas_marked_path _ _ _ _ _ _ /\ _`
    (qspec_then `ctx` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_marked_path F ctx func t 0 (OK land)` >>
  `~land.vs_halted /\ stmt_state_rel ctx func cenv cx (ee with scopes := rest) land /\
   lookup_var cv land = SOME c /\ lookup_var ev land = SOME e /\ lookup_var p land = SOME w /\
   (!x z. not_fresh_at st x /\ lookup_var x old = SOME z ==> lookup_var x land = SOME z) /\
   (!a b. FLOOKUP old.vs_allocas a = SOME b ==> FLOOKUP land.vs_allocas a = SOME b)` by
    (Cases_on `res = INL ()` >>
     simp[Abbr `land`, stmt_state_rel_jump_to] >>
     fs[jump_to_def, lookup_var_def]) >>
  `not_local_ptr cenv (ee with scopes := rest).scopes cv /\
   not_local_ptr cenv (ee with scopes := rest).scopes nv` by simp[] >>
  `land.vs_current_bb = incr_lbl` by simp[] >>
  qpat_assum `lookup_var ev land = SOME e`
    (mp_then (Pos (el 9)) mp_tac for_incr_finish) >>
  disch_then (fn th => qpat_assum `lookup_var p land = SOME w`
    (mp_then (Pos (el 9)) mp_tac th)) >>
  disch_then drule_all >> strip_tac >>
  qexists_tac `t'` >> simp[] >>
  qpat_x_assum `gas_marked_path F ctx func t 0 (OK land)` mp_tac >>
  disch_then (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[]
QED

(* One iteration of a range loop, from the condition block with the counter
   at n1 + k short of the end: the body runs in the loop variable's scope,
   at bc, from the body block's MSTORE on.  On a normal end or a continue
   the run comes back to the condition block with the counter at
   n1 + k + 1, related at the source state after the iteration (the
   loop variable's scope popped); on a break it reaches the exit block; on
   any other outcome it exits as the body does. *)
Theorem for_iteration_alloca[local]:
  !ctx func cenv bc cx lctx RetQ ty stmts esk cc id tyv p sz w ainst cv ev dv
   nv n1 n2 k cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3
   sb0 sb1 sj st vs.
    (* the code and the variables *)
    for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
    not_local_ptr bc (FEMPTY :: esk.scopes) p /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
    (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
    (* the iteration *)
    n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel ctx func cenv cx esk cc /\
    lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) /\
    stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
      (esk with <| scopes :=
         (FEMPTY |+ (id, <| assignable := F; type := tyv;
                            value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes;
                   gas_obs := [] |>) /\
    gas_admissible (eval_for cx tyv id stmts (Value (IntV (n1 + &k)) :: vs))
      (stmt_res_ok lctx) esk ==>
    gas_outcome F (cx_tops cx) (ctx, func)
      (do push_scope_with_var id tyv (IntV (n1 + &k));
          finally
            (try (do eval_stmts cx stmts; return F od) handle_loop_exception)
            pop_scope
       od) (esk, cc)
      (\res ee t. ?broke. res = INL broke /\
         t.vs_inst_idx = 0 /\ ~t.vs_halted /\
         stmt_state_rel ctx func cenv cx ee t /\
         (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                lookup_var x t = SOME v) /\
         (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                FLOOKUP t.vs_allocas a = SOME b) /\
         (broke ==> t.vs_current_bb = exit_lbl) /\
         (~broke ==> t.vs_current_bb = cond_lbl /\
                     lookup_var cv t = SOME (i2w (n1 + &(k + 1))) /\
                     lookup_var ev t = SOME (i2w n2) /\
                     lookup_var p t = SOME w))
      (\res ee r. ?ex. res = INR ex /\
         !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome F (cx_tops cx) (ctx,func) round (esk,cc) Q R` >>
  drule_all for_round_prepare >> strip_tac >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_admissible _ _ _` kall_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ cc` kall_tac >>
  qpat_x_assum `ret_pc_ok _ _ _` kall_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "ordinary"
  >> suspend "exempt"
QED

Resume for_iteration_alloca[exempt]:
  drule_all for_round_exempt_cert >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >>
  simp[Abbr `round`] >> goal_assum (drule_at Any)
QED
Resume for_iteration_alloca[ordinary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_summary_at_def] >>
  disch_then (qx_choose_then `res` (qx_choose_then `es_end`
    (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
  `preserves_scopes_dom
      (esk with <| scopes := (FEMPTY |+ (id, <| assignable := F; type := tyv;
        value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes; gas_obs := [] |>)
      es_end /\ es_end.scopes <> [] /\
    (!n. n IN FDOM (HD es_end.scopes) ==>
      lookup_scopes n (TL es_end.scopes) = NONE)` by
    (qpat_assum `gas_marked_exec _ _ (eval_stmts _ _) _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> strip_tac >>
     drule for_body_scopes >>
     disch_then (qspecl_then [`FEMPTY |+ (id, <| assignable := F; type := tyv;
       value := IntV (n1 + &k); popped := [] |>)`, `esk.scopes`] mp_tac) >>
     simp[preserves_scopes_dom_def]) >>
  Cases_on `es_end.scopes` >- gvs[] >>
  rename1 `es_end.scopes = sc :: rest` >>
  drule_all for_body_cleanup_exec >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_marked_exec F (ctx,func) cleanup _ _ wrapped fin r` >>
  `gas_marked_exec F (ctx,func) round (esk,cc) marks wrapped fin r` by
    (simp[Abbr `round`, ignore_bind_def] >>
     irule (SRULE [] (Q.INST [`left` |-> `[]`] gas_marked_exec_bind_normal)) >>
     goal_assum (drule_at Any) >> simp[]) >>
  strip_tac >- suspend "normal_finish" >> suspend "exit_finish"
QED
Resume for_iteration_alloca[exit_finish]:
  fs[] >> drule for_body_exit_cleanup >> disch_then (qspec_then `rest` mp_tac) >> strip_tac >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`wrapped`, `fin`, `r`] >> simp[] >>
  disj2_tac >> simp[Abbr `R`, Abbr `fin`, Abbr `wrapped`] >>
  fs[stmt_exit_def]
QED
Resume for_iteration_alloca[normal_finish]:
  fs[] >>
  qmatch_asmsub_abbrev_tac `preserves_scopes_dom entry es_end` >>
  `preserves_scopes_dom entry (es_end with gas_obs := [])` by
    fs[preserves_scopes_dom_def] >>
  `(es_end with gas_obs := []).scopes = sc :: rest` by simp[] >>
  `!x. not_fresh_at st x ==> x <> cv /\ x <> nv` by metis_tac[] >>
  `!a b. FLOOKUP cc.vs_allocas a = SOME b ==> FLOOKUP s2.vs_allocas a = SOME b` by simp[] >>
  `entry.scopes = (FEMPTY |+ (id, <| assignable := F; type := tyv;
    value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes` by simp[Abbr `entry`] >>
  `wrapped = INL (res = INR BreakException)` by
    (qpat_x_assum `stmt_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[stmt_post_def, stmt_lands_def] >> strip_tac >>
     gvs[Abbr `wrapped`]) >>
  drule_all for_body_finish >> strip_tac >>
  qpat_x_assum `for_code _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  `gas_marked_exec F (ctx,func) round (esk,cc) marks wrapped fin (OK u)` by
    (irule for_exec_zero_suffix >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`wrapped`, `fin`, `OK u`] >> simp[] >> disj1_tac >>
  simp[Abbr `Q`, Abbr `fin`] >>
  simp[i2w_counter_suc]
QED
Finalise for_iteration_alloca

Theorem for_iteration:
  !ctx func cenv bc cx lctx RetQ ty stmts esk cc id tyv p sz w ainst cv ev dv
   nv n1 n2 k cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3
   sb0 sb1 sj st vs cap.
    (* the code and the variables *)
    for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
    not_local_ptr bc (FEMPTY :: esk.scopes) p /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
    (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
    (* the iteration *)
    n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel ctx func cenv cx esk cc /\
    lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) /\
    cap <= w2n w /\
    (cenv.ce_is_ctor ==>
       immutable_prefix_bound cenv cx.txn.target cenv.ce_module esk cap) /\
    stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
      (esk with <| scopes :=
         (FEMPTY |+ (id, <| assignable := F; type := tyv;
                            value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes;
                   gas_obs := [] |>) /\
    gas_admissible (eval_for cx tyv id stmts (Value (IntV (n1 + &k)) :: vs))
      (stmt_res_ok lctx) esk ==>
    gas_outcome F (cx_tops cx) (ctx, func)
      (do push_scope_with_var id tyv (IntV (n1 + &k));
          finally
            (try (do eval_stmts cx stmts; return F od) handle_loop_exception)
            pop_scope
       od) (esk, cc)
      (\res ee t. ?broke. res = INL broke /\
         t.vs_inst_idx = 0 /\ ~t.vs_halted /\
         stmt_state_rel ctx func cenv cx ee t /\
         (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                lookup_var x t = SOME v) /\
         (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                FLOOKUP t.vs_allocas a = SOME b) /\
         (broke ==> t.vs_current_bb = exit_lbl) /\
         (~broke ==> t.vs_current_bb = cond_lbl /\
                     lookup_var cv t = SOME (i2w (n1 + &(k + 1))) /\
                     lookup_var ev t = SOME (i2w n2) /\
                     lookup_var p t = SOME w))
      (\res ee r. ?ex. res = INR ex /\
         !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)
Proof
  rpt gen_tac >> strip_tac >> drule_all for_iteration_alloca >> simp[]
QED

Theorem gas_outcome_exec_conseq[local]:
  gas_outcome memory tops (ctx,func) source (es,s) Q R /\
  (!marks res mid t.
     gas_marked_exec memory (ctx,func) source (es,s) marks res mid (OK t) /\
     Q res (mid with gas_obs := []) t ==>
     Q' res (mid with gas_obs := []) t) /\
  (!res mid r. R res mid r ==> R' res mid r) ==>
  gas_outcome memory tops (ctx,func) source (es,s) Q' R'
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac)
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_summary_at_def] >> strip_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED

Theorem for_round_exec_preserves[local]:
  (!ei j gs r2 es2 sc rest.
     P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
     eval_stmts cx stmts
       (ei with <| scopes :=
         (FEMPTY |+ (id, <| assignable := F; type := tyv;
           value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
         gas_obs := gs |>) = (r2,es2) /\
     (r2 = INL () \/ r2 = INR ContinueException) /\ es2.scopes = sc :: rest ==>
     P (es2 with scopes := rest)) /\
  P (es with gas_obs := []) /\ lookup_scopes id es.scopes = NONE /\
  j < Num (n2 - n1) /\
  gas_marked_exec memory (ctx,func)
    (do push_scope_with_var id tyv (IntV (n1 + &j));
        finally (try (do eval_stmts cx stmts; return F od)
          handle_loop_exception) pop_scope od)
    (es,s) marks (INL F) ee r ==>
  P (ee with gas_obs := []) /\ lookup_scopes id ee.scopes = NONE
Proof
  strip_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  simp[] >> strip_tac >>
  mp_tac (for_round_preserves |> SPEC_ALL |>
    Q.INST [`es` |-> `es with gas_obs := []`,
            `ee` |-> `ee with gas_obs := []`,
            `gs` |-> `gas_explicit marks s.vs_gas_readings`]) >>
  simp[] >> disch_then irule >> first_assum ACCEPT_TAC
QED

(* A range loop from its condition block with the counter at n1 + k and m
   iterations left: it reaches the exit block on the source's normal end
   (a break included), related at the source state after the loop, or
   exits as the source's outcome allows. *)
Theorem for_loop_alloca:
  !m P ctx func cenv bc cx lctx RetQ ty stmts id tyv p sz ainst cv ev dv nv
   n1 n2 cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3
   sb0 sb1 sj st k esk cc w.
    (* the code and the variables *)
    for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
    (!scs. lookup_scopes id scs = NONE ==>
           not_local_ptr bc (FEMPTY :: scs) p) /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
    (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
    (* the body, at the iteration states over a source state where P holds *)
    (!ei j.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) ==>
       stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
         (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)) /\
    (* P holds again after an iteration that goes on, whatever the gas *)
    (!ei j gs r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with <| scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
                     gas_obs := gs |>) = (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) /\
    n1 <= n2 /\ Num (n2 - n1) < dimword (:256) /\
    (* the loop from iteration k *)
    k + m = Num (n2 - n1) /\
    gas_admissible (eval_for cx tyv id stmts (GENLIST (\j. Value (IntV (n1 + &(k + j)))) m))
      (stmt_res_ok lctx) esk /\
    P (esk with gas_obs := []) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel ctx func cenv cx esk cc /\
    lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) ==>
    gas_outcome F (cx_tops cx) (ctx, func)
      (eval_for cx tyv id stmts (GENLIST (\j. Value (IntV (n1 + &(k + j)))) m))
      (esk, cc)
      (\res ee s. res = INL () /\ s.vs_current_bb = exit_lbl /\
         s.vs_inst_idx = 0 /\ ~s.vs_halted /\
         stmt_state_rel ctx func cenv cx ee s /\
         (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                lookup_var x s = SOME v) /\
         (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                FLOOKUP s.vs_allocas a = SOME b))
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `Inv = \j ee t.
    j <= m /\ P (ee with gas_obs := []) /\
    lookup_scopes id ee.scopes = NONE /\ ret_pc_ok cenv st t /\
    t.vs_current_bb = cond_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx ee t /\
    lookup_var cv t = SOME (i2w (n1 + &(k+j))) /\
    lookup_var ev t = SOME (i2w n2) /\ lookup_var p t = SOME w /\
    FLOOKUP t.vs_allocas ainst.inst_id = SOME (w2n w,sz) /\
    (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
       lookup_var x t = SOME v) /\
    (!a b. FLOOKUP cc.vs_allocas a = SOME b ==> FLOOKUP t.vs_allocas a = SOME b)` >>
  qabbrev_tac `Done = \ee t.
    t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx ee t /\
    (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==> lookup_var x t = SOME v) /\
    (!a b. FLOOKUP cc.vs_allocas a = SOME b ==> FLOOKUP t.vs_allocas a = SOME b)` >>
  qabbrev_tac `R = \ex ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r` >>
  `(!j es s.
      j < LENGTH (GENLIST (\j. Value (IntV (n1 + &(k+j)))) m) /\ Inv j es s /\
      gas_admissible (eval_for cx tyv id stmts
        (DROP j (GENLIST (\j. Value (IntV (n1 + &(k+j)))) m))) (stmt_res_ok lctx) es ==>
      gas_outcome F (cx_tops cx) (ctx,func)
        (do v <- read_result cx (EL j (GENLIST (\j. Value (IntV (n1 + &(k+j)))) m));
            push_scope_with_var id tyv v;
            finally (try (do eval_stmts cx stmts; return F od)
              handle_loop_exception) pop_scope od) (es,s)
        (\res ee t. ?broke. res = INL broke /\
          (broke ==> Done ee t) /\ (~broke ==> Inv (SUC j) ee t))
        (\res ee r. ?ex. res = INR ex /\ R ex ee r)) /\
    (!es s. Inv (LENGTH (GENLIST (\j. Value (IntV (n1 + &(k+j)))) m)) es s ==>
      ?t. gas_marked_path F ctx func s 0 (OK t) /\ Done (es with gas_obs := []) t)` by
    (conj_tac >- suspend "round" >> suspend "last") >>
  drule eval_for_rounds >>
  disch_then (qspecl_then [`0`, `esk`, `cc`] mp_tac) >>
  simp[Abbr `Inv`] >>
  (impl_tac >- (qpat_x_assum `gas_admissible _ _ esk` mp_tac >> simp[arithmeticTheory.ADD_COMM])) >>
  strip_tac >> drule gas_outcome_exec_conseq >> disch_then irule >>
  simp[Abbr `Done`, Abbr `R`] >> metis_tac[]
QED

Resume for_loop_alloca[round]:
  rpt gen_tac >> simp[EL_GENLIST, read_result_def, bind_return] >> strip_tac >>
  fs[Abbr `Inv`] >>
  `j + k < Num (n2 - n1)` by decide_tac >>
  `DROP j (GENLIST (\h. Value (IntV (n1 + &(h+k)))) m) =
    Value (IntV (n1 + &(j+k))) :: DROP (SUC j) (GENLIST (\h. Value (IntV (n1 + &(h+k)))) m)` by
    (qspecl_then [`j`, `GENLIST (\h. Value (IntV (n1 + &(h+k)))) m`] mp_tac
       DROP_CONS_EL >> simp[EL_GENLIST]) >>
  `gas_admissible (eval_for cx tyv id stmts
    (Value (IntV (n1 + &(j+k))) :: DROP (SUC j) (GENLIST (\h. Value (IntV (n1 + &(h+k)))) m)))
    (stmt_res_ok lctx) es` by metis_tac[] >>
  `not_local_ptr bc (FEMPTY :: es.scopes) p` by metis_tac[] >>
  `stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
    (es with <|scopes := (FEMPTY |+ (id, <|assignable := F; type := tyv;
      value := IntV (n1 + &(j+k)); popped := []|>)) :: es.scopes; gas_obs := []|>)` by
    (qpat_x_assum `!ei j. _ ==> stmt_frag _ _ _ _ _ _ _ _ _` (qspecl_then [`es with gas_obs := []`, `j+k`] mp_tac) >>
     simp[]) >>
  qpat_x_assum `ret_pc_ok cenv st cc` kall_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ esk cc` kall_tac >>
  qpat_x_assum `gas_admissible _ _ esk` kall_tac >>
  drule_all for_iteration_alloca >> strip_tac >>
  drule gas_outcome_exec_conseq >> disch_then irule >>
  reverse conj_tac >- simp[Abbr `R`] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  conj_tac
  >- (strip_tac >> simp[Abbr `Done`]) >>
  strip_tac >> gvs[] >>
  drule_all for_round_exec_preserves >> strip_tac >> simp[] >>
  conj_tac
  >- (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s`, `st`] >> simp[]) >>
  `j + (k + 1) = k + SUC j` by decide_tac >> simp[]
QED

Resume for_loop_alloca[last]:
  simp[] >> rpt gen_tac >> simp[Abbr `Inv`] >> strip_tac >>
  `(i2w (n1 + &Num (n2 - n1)) : bytes32) = i2w n2` by
    simp[i2w_counter_end] >>
  `lookup_block cond_lbl func.fn_blocks =
    SOME <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var cv; Var ev] [dv];
       mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|>` by
    fs[for_code_def] >>
  `!scs. not_local_ptr cenv scs dv` by fs[for_code_def] >>
  `lookup_var cv s = SOME (i2w n2)` by simp[] >>
  qpat_x_assum `cc.vs_current_bb = cond_lbl` kall_tac >>
  drule_all for_cond_zero_path >> simp[] >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s.vs_gas_readings`, `s.vs_inst_idx`, `[]`] mp_tac) >>
     simp[stmt_state_rel_inst_idx]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := [])
    (jump_to exit_lbl (update_var dv 1w s))` by
    (simp[stmt_state_rel_jump_to] >> irule stmt_state_rel_update_var >> simp[]) >>
  qexists_tac `jump_to exit_lbl (update_var dv 1w s)` >>
  simp[Abbr `Done`] >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  qpat_x_assum `!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==> _`
    (qspecl_then [`x`, `v`] mp_tac) >> simp[lookup_var_def]
QED
Finalise for_loop_alloca

Theorem for_loop:
  !m P ctx func cenv bc cx lctx RetQ ty stmts id tyv p sz ainst cv ev dv nv
   n1 n2 cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3
   sb0 sb1 sj st k esk cc w cap.
    (* the code and the variables *)
    for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
    (!scs. lookup_scopes id scs = NONE ==>
           not_local_ptr bc (FEMPTY :: scs) p) /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
    (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
    (!ei. P ei /\ cenv.ce_is_ctor ==>
       immutable_prefix_bound cenv cx.txn.target cenv.ce_module ei cap) /\
    (* the body, at the iteration states over a source state where P holds *)
    (!ei j.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) ==>
       stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
         (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)) /\
    (* P holds again after an iteration that goes on, whatever the gas *)
    (!ei j gs r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with <| scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
                     gas_obs := gs |>) = (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) /\
    n1 <= n2 /\ Num (n2 - n1) < dimword (:256) /\
    (* the loop from iteration k *)
    k + m = Num (n2 - n1) /\
    gas_admissible (eval_for cx tyv id stmts (GENLIST (\j. Value (IntV (n1 + &(k + j)))) m))
      (stmt_res_ok lctx) esk /\
    P (esk with gas_obs := []) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel ctx func cenv cx esk cc /\
    lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) /\
    cap <= w2n w ==>
    gas_outcome F (cx_tops cx) (ctx, func)
      (eval_for cx tyv id stmts (GENLIST (\j. Value (IntV (n1 + &(k + j)))) m))
      (esk, cc)
      (\res ee s. res = INL () /\ s.vs_current_bb = exit_lbl /\
         s.vs_inst_idx = 0 /\ ~s.vs_halted /\
         stmt_state_rel ctx func cenv cx ee s /\
         (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                lookup_var x s = SOME v) /\
         (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                FLOOKUP s.vs_allocas a = SOME b))
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  rpt gen_tac >> strip_tac >> drule_all for_loop_alloca >> simp[]
QED

(* A pointer variable handed out at or after st is no local's pointer. *)
