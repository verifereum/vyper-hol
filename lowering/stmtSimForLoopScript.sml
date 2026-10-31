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
  stmtSim stmtSimForParts stmtSimDeclStore
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

Theorem stmt_state_rel_declare_word_alloca[local]:
  !func cenv cx es s id p sz w inst v tyv sc rest a.
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    32 <= sz /\ word_value v /\ type_memory_size tyv = 32 ==>
    stmt_state_rel func cenv cx
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
    stmt_state_rel func cenv cx esk cc /\
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
    not_local_ptr cenv esk.scopes dv /\
    not_local_ptr bc (FEMPTY :: esk.scopes) p /\ dv <> p /\ dv <> cv /\
    MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
    ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
    32 <= sz /\ type_memory_size tyv = 32 ==>
    ?s2. s2.vs_current_bb = body_lbl /\ s2.vs_inst_idx = 1 /\
         ~s2.vs_halted /\
         stmt_state_rel func bc cx
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
  `stmt_state_rel func cenv cx (esk with scopes := FEMPTY :: esk.scopes) s1` by
    (simp[Abbr `s1`, stmt_state_rel_jump_to, stmt_state_rel_push_scope] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `stmt_state_rel func bc cx (esk with scopes := FEMPTY :: esk.scopes) s1` by
    (irule stmt_state_rel_cenv_cong >> qexists_tac `cenv` >> simp[] >>
     rpt strip_tac >> Cases_on `n = id` >> gvs[lookup_scopes_def] >>
     res_tac >> gvs[]) >>
  `stmt_state_rel func bc cx
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
    stmt_state_rel func cenv cx esk cc /\
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
    not_local_ptr cenv esk.scopes dv /\
    not_local_ptr bc (FEMPTY :: esk.scopes) p /\ dv <> p /\ dv <> cv /\
    MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
    ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
    32 <= sz /\ type_memory_size tyv = 32 /\ cap <= w2n w /\
    (cenv.ce_is_ctor ==>
       immutable_prefix_bound cenv cx.txn.target cenv.ce_module esk cap) ==>
    ?s2. s2.vs_current_bb = body_lbl /\ s2.vs_inst_idx = 1 /\
         ~s2.vs_halted /\
         stmt_state_rel func bc cx
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
  qpat_x_assum `stmt_state_rel func cenv cx (es2 with scopes := rest) DD`
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
  !ctx func cenv bc cx RetQ ty stmts esk cc id tyv p sz w ainst cv ev dv nv
   n1 n2 k cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3
   sb0 sb1 sj st r2 es2 sc rest.
    (* the code and the variables *)
    for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
    not_local_ptr bc (FEMPTY :: esk.scopes) p /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
    (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
    (* the iteration *)
    n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel func cenv cx esk cc /\
    lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) /\
    eval_stmts cx stmts
      (esk with scopes :=
         (FEMPTY |+ (id, <| assignable := F; type := tyv;
                            value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes) =
      (r2, es2) /\
    stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts)
      (esk with scopes :=
         (FEMPTY |+ (id, <| assignable := F; type := tyv;
                            value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes)
      r2 es2 /\
    stmt_res_ok (InLoop exit_lbl incr_lbl) r2 /\
    es2.scopes = sc :: rest /\
    (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
    ((r2 = INL () \/ r2 = INR ContinueException) /\
     ?cc'. cc'.vs_current_bb = cond_lbl /\ cc'.vs_inst_idx = 0 /\
           ~cc'.vs_halted /\
           stmt_state_rel func cenv cx (es2 with scopes := rest) cc' /\
           lookup_var cv cc' = SOME (i2w (n1 + &(k + 1))) /\
           lookup_var ev cc' = SOME (i2w n2) /\ lookup_var p cc' = SOME w /\
           (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                  lookup_var x cc' = SOME v) /\
           (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                  FLOOKUP cc'.vs_allocas a = SOME b) /\
           !fuel rr. run_from fuel ctx func cc' = rr /\ (!e. rr <> Error e) ==>
                     ?fuel'. run_from fuel' ctx func cc = rr) \/
    (r2 = INR BreakException /\
     ?s. s.vs_current_bb = exit_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
         stmt_state_rel func cenv cx (es2 with scopes := rest) s /\
         (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                lookup_var x s = SOME v) /\
         (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                FLOOKUP s.vs_allocas a = SOME b) /\
         !fuel rr. run_from fuel ctx func s = rr /\ (!e. rr <> Error e) ==>
                   ?fuel'. run_from fuel' ctx func cc = rr) \/
    (?fuel rr. run_from fuel ctx func cc = rr /\ exit_result rr /\
               stmt_exit RetQ (es2 with scopes := rest) r2 rr)
Proof
  rpt gen_tac >> REWRITE_TAC [for_code_def] >> strip_tac >>
  `bc.ce_module_vars = cenv.ce_module_vars /\
   bc.ce_module = cenv.ce_module /\ bc.ce_is_ctor = cenv.ce_is_ctor` by
    (qpat_assum `_ = cenv` (fn th => ONCE_REWRITE_TAC [SYM th]) >> simp[]) >>
  `not_local_ptr cenv esk.scopes dv` by metis_tac[] >>
  drule_all for_body_entry_alloca >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  `ret_pc_ok bc sb0 s2` by
    (qspecl_then [`cenv`, `bc`, `st`, `sb0`, `cc`, `s2`] mp_tac
       ret_pc_ok_frame >>
     impl_tac
     >- (rpt conj_tac
         >- first_assum ACCEPT_TAC
         >- (qpat_assum `_ = cenv` (fn th => ONCE_REWRITE_TAC [SYM th]) >>
             simp[])
         >- first_assum ACCEPT_TAC >>
         rpt strip_tac >>
         qpat_x_assum `!x. not_fresh_at st x ==> _` drule >> strip_tac >>
         qpat_x_assum `!x. x <> dv ==> lookup_var x s2 = _` drule >> simp[]) >>
     simp[]) >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [stmt_frag_def]) >>
  disch_then (qspecl_then [`sb0`, `sb1`, `s2`,
     `FST (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0)`] mp_tac) >>
  impl_tac
  >- (fs[compile_stmts_env] >>
      Cases_on `stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts sb0` >>
      gvs[]) >>
  strip_tac
  >- (
    (* the body reaches its end, the increment block or the exit block *)
    rename1 `stmt_state_rel func c3 cx es2 s3` >>
    qabbrev_tac `esA = esk with scopes :=
           (FEMPTY |+ (id, <| assignable := F; type := tyv;
                              value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes` >>
    `cenv_top_ext cenv bc esA.scopes` by
      (simp[cenv_top_ext_def, Abbr `esA`] >> rpt strip_tac >>
       Cases_on `n = id` >> gvs[]) >>
    `cenv_top_ext cenv c3 es2.scopes` by
      (irule cenv_top_ext_trans >> qexistsl_tac [`bc`, `esA.scopes`] >>
       simp[] >>
       qpat_x_assum `eval_stmts _ _ _ = _`
         (strip_assume_tac o MATCH_MP eval_stmts_preserves_scopes_dom) >>
       gvs[preserves_scopes_dom_def, Abbr `esA`]) >>
    `stmt_state_rel func cenv cx (es2 with scopes := rest) s3` by
      (qspecl_then [`func`, `cenv`, `c3`, `cx`, `es2`, `s3`, `sc`, `rest`]
         mp_tac stmt_state_rel_pop_top_ext >> simp[]) >>
    `!x v. not_fresh_at sb0 x /\ x <> dv /\ lookup_var x cc = SOME v ==>
           lookup_var x s3 = SOME v` by
      (rpt strip_tac >> first_x_assum irule >> fs[]) >>
    `lookup_var cv s3 = SOME (i2w (n1 + &k)) /\
     lookup_var ev s3 = SOME (i2w n2) /\ lookup_var p s3 = SOME w` by
      (rpt conj_tac >> first_x_assum irule >> fs[]) >>
    `!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
           FLOOKUP s3.vs_allocas a = SOME b` by
      (rpt strip_tac >> first_x_assum irule >> fs[]) >>
    `!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
           lookup_var x s3 = SOME v` by
      (rpt strip_tac >> first_x_assum irule >> fs[not_fresh_at_def] >>
       rw[] >> first_x_assum irule >> decide_tac) >>
    `!fuel rr. run_from fuel ctx func s3 = rr /\ (!e. rr <> Error e) ==>
               ?fuel'. run_from fuel' ctx func cc = rr` by
      (rpt strip_tac >>
       qpat_x_assum `!fuel r. run_from fuel ctx func s3 = r /\ _ ==> _`
         (qspecl_then [`fuel`, `rr`] mp_tac) >> simp[] >> strip_tac >>
       qpat_x_assum `!fuel rr. run_from fuel ctx func s2 = rr /\ _ ==> _`
         (qspecl_then [`fuel'`, `rr`] mp_tac) >> simp[]) >>
    qpat_x_assum `stmt_lands _ _ _ _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [stmt_lands_def])
    >- (
      (* its end: the JMP to the increment block *)
      `~block_is_terminated sb1` by fs[] >>
      qpat_x_assum `~block_is_terminated sb1 ==> _` drule >> strip_tac >>
      qspecl_then [`ctx`, `func`, `sb1`, `sj`, `s3`,
                   `mk_inst sb1.cs_next_id JMP [Label incr_lbl] []`, `incr_lbl`]
        mp_tac run_from_jump_end >>
      impl_tac
      >- simp[venomInstTheory.mk_inst_def, step_jmp_behavior,
              is_terminator_def] >>
      strip_tac >> qabbrev_tac `DD = jump_to incr_lbl s3` >>
      `DD.vs_current_bb = incr_lbl /\ DD.vs_inst_idx = 0 /\ ~DD.vs_halted /\
       (!x. lookup_var x DD = lookup_var x s3) /\
       DD.vs_allocas = s3.vs_allocas /\
       stmt_state_rel func cenv cx (es2 with scopes := rest) DD` by
        simp[Abbr `DD`, jump_to_def, lookup_var_def, stmt_state_rel_jump_to] >>
      for_incr_tac)
    >- (
      (* a break: the exit block *)
      disj2_tac >> disj1_tac >> simp[] >> qexists_tac `s3` >> fs[]) >>
    (* a continue: the increment block *)
    qabbrev_tac `DD = s3` >> for_incr_tac) >>
  (* the body exits *)
  disj2_tac >> disj2_tac >>
  qpat_x_assum `!fuel rr. run_from fuel ctx func s2 = rr /\ _ ==> _`
    (qspecl_then [`fuel`, `run_from fuel ctx func s2`] mp_tac) >>
  impl_tac >- metis_tac[exit_result_not_error] >> strip_tac >>
  qexistsl_tac [`fuel'`, `run_from fuel ctx func s2`] >>
  gvs[stmt_exit_def]
QED

Theorem for_iteration:
  !ctx func cenv bc cx RetQ ty stmts esk cc id tyv p sz w ainst cv ev dv nv
   n1 n2 k cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3
   sb0 sb1 sj st r2 es2 sc rest cap.
    for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
    not_local_ptr bc (FEMPTY :: esk.scopes) p /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
    (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
    n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel func cenv cx esk cc /\
    lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) /\
    cap <= w2n w /\
    (cenv.ce_is_ctor ==>
       immutable_prefix_bound cenv cx.txn.target cenv.ce_module esk cap) /\
    eval_stmts cx stmts
      (esk with scopes :=
         (FEMPTY |+ (id, <| assignable := F; type := tyv;
                            value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes) =
      (r2, es2) /\
    stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts)
      (esk with scopes :=
         (FEMPTY |+ (id, <| assignable := F; type := tyv;
                            value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes)
      r2 es2 /\
    stmt_res_ok (InLoop exit_lbl incr_lbl) r2 /\
    es2.scopes = sc :: rest /\
    (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
    ((r2 = INL () \/ r2 = INR ContinueException) /\
     ?cc'. cc'.vs_current_bb = cond_lbl /\ cc'.vs_inst_idx = 0 /\
           ~cc'.vs_halted /\
           stmt_state_rel func cenv cx (es2 with scopes := rest) cc' /\
           lookup_var cv cc' = SOME (i2w (n1 + &(k + 1))) /\
           lookup_var ev cc' = SOME (i2w n2) /\ lookup_var p cc' = SOME w /\
           (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                  lookup_var x cc' = SOME v) /\
           (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                  FLOOKUP cc'.vs_allocas a = SOME b) /\
           !fuel rr. run_from fuel ctx func cc' = rr /\ (!e. rr <> Error e) ==>
                     ?fuel'. run_from fuel' ctx func cc = rr) \/
    (r2 = INR BreakException /\
     ?s. s.vs_current_bb = exit_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
         stmt_state_rel func cenv cx (es2 with scopes := rest) s /\
         (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                lookup_var x s = SOME v) /\
         (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                FLOOKUP s.vs_allocas a = SOME b) /\
         !fuel rr. run_from fuel ctx func s = rr /\ (!e. rr <> Error e) ==>
                   ?fuel'. run_from fuel' ctx func cc = rr) \/
    (?fuel rr. run_from fuel ctx func cc = rr /\ exit_result rr /\
               stmt_exit RetQ (es2 with scopes := rest) r2 rr)
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
   sb0 sb1 sj st k esk cc w res es'.
    (* the code and the variables *)
    for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
    (!scs. lookup_scopes id scs = NONE ==>
           not_local_ptr bc (FEMPTY :: scs) p) /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
    (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
    (* the body, at the iteration states over a source state where P holds *)
    (!ei j r2 es2.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes) = (r2, es2) ==>
       stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
         (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes) r2 es2) /\
    (* P holds again after an iteration that goes on *)
    (!ei j r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes) = (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) /\
    n1 <= n2 /\ Num (n2 - n1) < dimword (:256) /\
    (* the loop from iteration k *)
    k + m = Num (n2 - n1) /\
    eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &(k + j))) m) esk =
      (res, es') /\
    stmt_res_ok lctx res /\ P esk /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel func cenv cx esk cc /\
    lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) ==>
    (?s. res = INL () /\ s.vs_current_bb = exit_lbl /\ s.vs_inst_idx = 0 /\
         ~s.vs_halted /\ stmt_state_rel func cenv cx es' s /\
         (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                lookup_var x s = SOME v) /\
         (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                FLOOKUP s.vs_allocas a = SOME b) /\
         !fuel rr. run_from fuel ctx func s = rr /\ (!e. rr <> Error e) ==>
                   ?fuel'. run_from fuel' ctx func cc = rr) \/
    (?fuel rr. run_from fuel ctx func cc = rr /\ exit_result rr /\
               stmt_exit RetQ es' res rr)
Proof
  Induct
  >- (
    (* no iteration left: the counter is at the end *)
    rpt gen_tac >> REWRITE_TAC [for_code_def] >> strip_tac >>
    `(i2w (n1 + &k) : bytes32) = i2w n2` by
      (`k = Num (n2 - n1)` by decide_tac >> simp[i2w_counter_end]) >>
    qpat_x_assum `eval_for _ _ _ _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, return_def] >> strip_tac >>
    qpat_x_assum `res = INL ()` SUBST_ALL_TAC >>
    qpat_x_assum `esk = es'` (SUBST_ALL_TAC o SYM) >>
    qspecl_then [`ctx`, `func`, `cc`, `cv`, `ev`, `dv`, `i2w (n1 + &k)`,
                 `i2w n2`, `cond_lbl`, `exit_lbl`, `body_lbl`, `j1`, `j2`]
      mp_tac for_cond_block >> simp[] >> strip_tac >>
    disj1_tac >> qexists_tac `jump_to exit_lbl (update_var dv 1w cc)` >>
    rpt conj_tac
    >- simp[jump_to_def]
    >- simp[jump_to_def]
    >- fs[jump_to_def, update_var_def]
    >- (simp[stmt_state_rel_jump_to] >> irule stmt_state_rel_update_var >>
        fs[])
    >- (rpt strip_tac >> fs[jump_to_def, update_var_def, lookup_var_def,
                            FLOOKUP_UPDATE] >> metis_tac[])
    >- fs[jump_to_def, update_var_def] >>
    metis_tac[]) >>
  (* an iteration, then the loop from the next counter *)
  pop_assum (mk_asm "loop_ih") >> rpt gen_tac >> strip_tac >>
  qpat_assum `for_code _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [for_code_def]) >>
  `k < Num (n2 - n1)` by decide_tac >>
  `GENLIST (\j. (IntV (n1 + &(k + j)) : value)) (SUC m) =
   (IntV (n1 + &k) : value) ::
   GENLIST (\j. (IntV (n1 + &(k + 1 + j)) : value)) m` by
    (simp[GENLIST_CONS, combinTheory.o_DEF] >>
     simp[GENLIST_FUN_EQ] >> rpt strip_tac >>
     `k + SUC x = x + (k + 1)` by decide_tac >> simp[]) >>
  qpat_x_assum `eval_for _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `GENLIST _ (SUC m) = _` (fn th => REWRITE_TAC [th]) >>
  strip_tac >> drule_all eval_for_cons_cases >>
  disch_then (qx_choosel_then [`r2`, `es2`, `sc`, `rest`]
                (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `stmt_res_ok (InLoop exit_lbl incr_lbl) r2` by
    (qpat_assum `_ /\ eval_for _ _ _ _ _ _ = _ \/ _` strip_assume_tac >>
     fs[stmt_res_ok_def]) >>
  `not_local_ptr bc (FEMPTY :: esk.scopes) p` by
    (qpat_assum `!scs. lookup_scopes id scs = NONE ==> _` irule >> simp[]) >>
  `stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
     (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts)
     (esk with scopes :=
       (FEMPTY |+ (id, <| assignable := F; type := tyv;
                          value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes)
     r2 es2` by
    (first_x_assum irule >> simp[]) >>
  drule_all for_iteration_alloca >>
  (* the iteration's outcome: breaks, exits, or goes on *)
  disch_then (DISJ_CASES_THEN2 (DISJ_CASES_THEN strip_assume_tac)
                (CONJUNCTS_THEN2 assume_tac strip_assume_tac) o
              ONCE_REWRITE_RULE [DISJ_COMM])
  >- (
    (* a break lands at the exit block *)
    `res = INL () /\ es' = es2 with scopes := rest` by
      (qpat_x_assum `_ /\ eval_for _ _ _ _ _ _ = _ \/ _` mp_tac >>
       qpat_assum `r2 = _` (fn th => REWRITE_TAC [th]) >> simp[]) >>
    disj1_tac >> qexists_tac `s` >> fs[])
  >- (
    (* another exception exits, and so does the loop *)
    `res = r2 /\ es' = es2 with scopes := rest` by
      (qpat_x_assum `_ /\ eval_for _ _ _ _ _ _ = _ \/ _` mp_tac >>
       qpat_x_assum `stmt_exit _ _ r2 _` mp_tac >>
       rpt (pop_assum kall_tac) >> rpt strip_tac >>
       gvs[stmt_exit_loop_ctl]) >>
    disj2_tac >> qexistsl_tac [`fuel`, `rr`] >>
    qpat_x_assum `res = _` SUBST_ALL_TAC >>
    qpat_x_assum `es' = _` SUBST_ALL_TAC >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &(k + 1 + j))) m)
     (es2 with scopes := rest) = (res, es')` by
    (qpat_x_assum `_ /\ eval_for _ _ _ _ _ _ = _ \/ _` mp_tac >>
     qpat_x_assum `r2 = _ \/ _` strip_assume_tac >>
     pop_assum (fn th => REWRITE_TAC [th]) >> simp[]) >>
  (* the loop goes on from the incremented counter, where P holds again *)
  `P (es2 with scopes := rest)` by
    (qpat_assum `!ei j r2 es2 sc rest. P ei /\ _ ==> P _` drule_all >> simp[]) >>
  `ret_pc_ok cenv st cc'` by
    (qspecl_then [`cenv`, `cenv`, `st`, `st`, `cc`, `cc'`] mp_tac
       ret_pc_ok_frame >>
     impl_tac >- fs[] >> simp[]) >>
  `k + 1 + m = Num (n2 - n1)` by decide_tac >>
  `lookup_scopes id (es2 with scopes := rest).scopes = NONE` by
    (simp[] >> irule lookup_scopes_none_map_fdom >>
     qexists_tac `esk.scopes` >> fs[]) >>
  `FLOOKUP cc'.vs_allocas ainst.inst_id = SOME (w2n w, sz)` by
    (first_x_assum irule >> simp[]) >>
  asm_x "loop_ih" drule_all >>
  (strip_tac
    >- (rename1 `stmt_state_rel func cenv cx es' s9` >> disj1_tac >>
        qexists_tac `s9` >> simp[] >> rpt strip_tac >>
        qpat_x_assum `!fuel rr. run_from fuel ctx func s9 = rr /\ _ ==> _`
          (qspec_then `fuel` mp_tac) >> simp[] >> strip_tac >>
        qpat_x_assum `!fuel rr. run_from fuel ctx func cc' = rr /\ _ ==> _`
          (qspec_then `fuel'` mp_tac) >> simp[]) >>
    disj2_tac >> rename1 `run_from f9 ctx func cc' = r9` >>
    drule exit_result_not_error >> strip_tac >>
    qpat_x_assum `!fuel rr. run_from fuel ctx func cc' = rr /\ _ ==> _`
      (qspecl_then [`f9`, `r9`] mp_tac) >> simp[] >> strip_tac >>
    metis_tac[])
QED

Theorem for_loop:
  !m P ctx func cenv bc cx lctx RetQ ty stmts id tyv p sz ainst cv ev dv nv
   n1 n2 cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3
   sb0 sb1 sj st k esk cc w res es' cap.
    for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
    (!scs. lookup_scopes id scs = NONE ==>
           not_local_ptr bc (FEMPTY :: scs) p) /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
    (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
    (!ei. P ei /\ cenv.ce_is_ctor ==>
       immutable_prefix_bound cenv cx.txn.target cenv.ce_module ei cap) /\
    (!ei j r2 es2.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes) = (r2, es2) ==>
       stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
         (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes) r2 es2) /\
    (!ei j r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes) = (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) /\
    n1 <= n2 /\ Num (n2 - n1) < dimword (:256) /\
    k + m = Num (n2 - n1) /\
    eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &(k + j))) m) esk =
      (res, es') /\
    stmt_res_ok lctx res /\ P esk /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel func cenv cx esk cc /\
    lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) /\
    cap <= w2n w ==>
    (?s. res = INL () /\ s.vs_current_bb = exit_lbl /\ s.vs_inst_idx = 0 /\
         ~s.vs_halted /\ stmt_state_rel func cenv cx es' s /\
         (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                lookup_var x s = SOME v) /\
         (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                FLOOKUP s.vs_allocas a = SOME b) /\
         !fuel rr. run_from fuel ctx func s = rr /\ (!e. rr <> Error e) ==>
                   ?fuel'. run_from fuel' ctx func cc = rr) \/
    (?fuel rr. run_from fuel ctx func cc = rr /\ exit_result rr /\
               stmt_exit RetQ es' res rr)
Proof
  rpt gen_tac >> strip_tac >> drule_all for_loop_alloca >> simp[]
QED

(* A pointer variable handed out at or after st is no local's pointer. *)
