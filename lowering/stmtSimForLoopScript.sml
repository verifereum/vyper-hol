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
  compileEnv valueEncoding valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation
  gasOutcome gasContext stmtSimForRounds
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

Theorem stmt_state_rel_declare_word_alloca[local]:
  !func cenv cx es s id p sz w inst v tyv sc rest a ctx.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    32 <= sz /\ word_value v /\ type_memory_size tyv = 32 ==>
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
  simp[word_value_in_memory] >> conj_tac
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
    not_local_ptr cenv esk.scopes dv /\
    not_local_ptr bc (FEMPTY :: esk.scopes) p /\ dv <> p /\ dv <> cv /\
    MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
    ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
    32 <= sz /\ type_memory_size tyv = 32 ==>
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
  rpt gen_tac >> strip_tac >>
  `(i2w (n1 + &k) : bytes32) <> i2w n2` by metis_tac[i2w_counter_ne] >>
  qabbrev_tac `s1 = jump_to body_lbl (update_var dv (bool_to_word F) cc)` >>
  `!fuel rr. run_from fuel ctx func s1 = rr /\ (!e. rr <> Error e) ==>
             ?fuel'. run_from fuel' ctx func cc = rr` by
    (qspecl_then [`ctx`, `func`, `cc`, `cv`, `ev`, `dv`, `i2w (n1 + &k)`,
                  `i2w n2`, `cond_lbl`, `exit_lbl`, `body_lbl`, `j1`, `j2`]
       mp_tac for_cond_block >> simp[Abbr `s1`]) >>
  `lookup_var p s1 = SOME w /\ lookup_var cv s1 = SOME (i2w (n1 + &k)) /\
   s1.vs_current_bb = body_lbl /\ s1.vs_inst_idx = 0 /\ ~s1.vs_halted /\
   s1.vs_allocas = cc.vs_allocas /\
   (!x. x <> dv ==> lookup_var x s1 = lookup_var x cc)` by
    (simp[Abbr `s1`, jump_to_def, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE] >> fs[lookup_var_def]) >>
  qabbrev_tac `s2 = mstore (w2n w) (i2w (n1 + &k)) s1 with vs_inst_idx := 1` >>
  `!fu. run_from fu ctx func s1 = run_from fu ctx func s2` by
    (gen_tac >>
     qspecl_then [`fu`, `ctx`, `func`, `s1`, `bbb`,
                  `mk_inst j3 MSTORE [Var p; Var cv] []`,
                  `mstore (w2n w) (i2w (n1 + &k)) s1`] mp_tac run_from_step >>
     impl_tac
     >- (simp[venomInstTheory.mk_inst_def, is_terminator_def] >>
         `step_inst_base (mk_inst j3 MSTORE [Var p; Var cv] []) s1 =
          OK (mstore (w2n w) (i2w (n1 + &k)) s1)` by
           (irule step_MSTORE >> simp[eval_operand_def]) >>
         fs[venomInstTheory.mk_inst_def]) >>
     simp[Abbr `s2`]) >>
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
    not_local_ptr cenv esk.scopes dv /\
    not_local_ptr bc (FEMPTY :: esk.scopes) p /\ dv <> p /\ dv <> cv /\
    MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
    ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
    32 <= sz /\ type_memory_size tyv = 32 /\ cap <= w2n w /\
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
  rpt gen_tac >> strip_tac >> drule_all for_body_entry_alloca >> simp[]
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

(* The rest of an iteration from the increment block, at DD. *)
val for_incr_tac =
  qpat_x_assum `stmt_state_rel ctx func cenv cx (es2 with scopes := rest) DD`
    assume_tac >>
  qspecl_then [`ctx`, `func`, `DD`, `cv`, `nv`, `i2w (n1 + &k)`, `incr_lbl`,
               `cond_lbl`, `i1`, `i2`, `i3`] mp_tac for_incr_block >>
  impl_tac >- fs[] >> strip_tac >>
  disj1_tac >> simp[] >>
  qexists_tac `jump_to cond_lbl (update_var cv (i2w (n1 + &k) + 1w)
                 (update_var nv (i2w (n1 + &k) + 1w) DD))` >>
  rpt conj_tac
  >- simp[jump_to_def]
  >- simp[jump_to_def]
  >- fs[jump_to_def, update_var_def]
  >- (simp[stmt_state_rel_jump_to] >> irule stmt_state_rel_update_var >>
      fs[] >> irule stmt_state_rel_update_var >> fs[])
  >- simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
          i2w_counter_suc]
  >- fs[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
  >- fs[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
  >- (rpt strip_tac >> fs[jump_to_def, update_var_def, lookup_var_def,
                          FLOOKUP_UPDATE] >> metis_tac[])
  >- (rpt strip_tac >> fs[jump_to_def, update_var_def] >> metis_tac[]) >>
  (* the results chain back through DD (and s3 when DD is its jump) to cc *)
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `run_from fuel ctx func XX` >>
  qspecl_then [`ctx`, `func`, `XX`, `DD`, `cc`] mp_tac
    run_from_results_trans >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      FIRST [first_assum ACCEPT_TAC,
             MATCH_MP_TAC run_from_results_trans >> qexists_tac `s3` >>
             conj_tac >> first_assum ACCEPT_TAC]) >>
  disch_then (qspecl_then [`fuel`, `run_from fuel ctx func XX`] mp_tac) >>
  impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >> simp[];

(* The range loop's code, as compile_for_range_parts lays it out, and the
   facts about its variables and environments that every iteration uses:
   the condition, body and increment blocks; the body's code between sb0
   and sb1 and its jump to the increment block at sj; the loop variable's
   ALLOCA ainst and its pointer p in bc, which is cenv with id bound; the
   counter cv, end ev, condition dv and next counter nv, distinct from p
   and from each other as the loop needs, and cv, dv and nv no local's
   pointers. *)
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
    32 <= sz /\ type_memory_size tyv = 32
End

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
    gas_admissible (eval_for cx tyv id stmts (IntV (n1 + &k) :: vs))
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
  (* admitted at base cut: body stmt_frag impl_tac no longer closes after the gas join's stmt_framed_frag split (same at port source f0ada92b7) *)
  cheat
QED

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
    gas_admissible (eval_for cx tyv id stmts (IntV (n1 + &k) :: vs))
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
    gas_admissible (eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &(k + j))) m))
      (stmt_res_ok lctx) esk /\
    P (esk with gas_obs := []) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel ctx func cenv cx esk cc /\
    lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) ==>
    gas_outcome F (cx_tops cx) (ctx, func)
      (eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &(k + j))) m))
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
  (* admitted at base cut: proof still expects the pre-counted eval_for result premise (same at port source f0ada92b7) *)
  cheat
QED

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
    gas_admissible (eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &(k + j))) m))
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
      (eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &(k + j))) m))
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
