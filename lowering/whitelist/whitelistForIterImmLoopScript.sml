(* Compiler cuts for immutable-source counted iteration.  Source preparation
   uses LocCode; the memory-only array loop contracts cannot certify it. *)
Theory whitelistForIterImmLoop
Ancestors
  whitelistForIterImmCopy whitelistForIterImmFrame whitelistForIterDynLoop
  exprSimTopLevelImmutable stmtLowering exprLoweringProps compileEnv context
  vyperAST list finite_map stmtSimForArrayParts stmtSimProps emitHelper venomInst fragExec
  stmtSimForArrayLoop stmtSimForArrayFrag stmtSimDefs venomState venomExecSemantics
  venomExecProofs loweringPosts fragGasMode fragGasPath
  fragGasSeq gasCount gasSummary gasExemptCert gasContext gasOutcome
  gasSummaryCompose stmtSimForRounds vyperInterpreter vyperState
  words arithmetic rich_list emitHelperProps exprSimBopRestWordLoads
  exprSimBopRestWordLayout exprSimProps
Libs
  monadsyntax

Theorem compile_for_immutable_stages:
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  compile_stmt cenv lctx ty
    (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) n stmts) st =
    ((),st') ==>
  ?lvo st1 bc entry cond bod incr exit idx offo toto epo sa sb0 sb1 sj.
    (if (case bd of Dynamic _ => T | Fixed _ => F) then
       compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
     else return (Lit (n2w (bound_length bd)))) st = (lvo,st1) /\
    (do bc <- declare_local cenv id et;
        emit_local_alloca bc id;
        entry <- fresh_label "iter_entry";
        cond <- fresh_label "iter_cond";
        bod <- fresh_label "iter_body";
        incr <- fresh_label "iter_incr";
        exit <- fresh_label "iter_exit";
        emit_inst JMP [Label entry] [];
        new_block entry;
        idx <- fresh_var;
        emit_inst ASSIGN [Lit 0w] [idx];
        (if (case bd of Dynamic _ => T | Fixed _ => F) then
           do invalid <- emit_op GT [lvo; Lit (n2w (bound_length bd))];
              valid <- emit_op ISZERO [invalid];
              emit_void ASSERT [valid]
           od
         else return ());
        emit_inst JMP [Label cond] [];
        new_block cond;
        done <- emit_op EQ [Var idx; lvo];
        emit_inst JNZ [done; Label exit; Label bod] [];
        new_block bod;
        offv <- emit_op MUL [Var idx;
                   Lit (n2w (elem_size_in_location cenv LocCode et))];
        tot <- (if (case bd of Dynamic _ => T | Fixed _ => F) then
                  emit_op ADD [Lit 32w; offv]
                else return offv);
        ep <- emit_op ADD [Lit (n2w off); tot];
        return (bc,entry,cond,bod,incr,exit,idx,offv,tot,ep)
     od) st1 = ((bc,entry,cond,bod,incr,exit,idx,offo,toto,epo),sa) /\
    (case FLOOKUP bc.ce_vars id of
       SOME (MemLoc dst _) =>
         compile_iter_elem_copy cenv epo (Lit (n2w dst))
           (elem_size_in_location cenv LocCode et) LocCode F et et
     | SOME (PtrVar ptr_op _) =>
         compile_iter_elem_copy cenv epo ptr_op
           (elem_size_in_location cenv LocCode et) LocCode F et et
     | _ => emit_void INVALID []) sa = ((),sb0) /\
    compile_stmts bc (InLoop exit incr) ty stmts sb0 = ((),sb1) /\
    emit_jmp_if_not_terminated incr sb1 = ((),sj) /\
    (do new_block incr;
        next <- emit_op ADD [Var idx; Lit 1w];
        emit_inst ASSIGN [next] [idx];
        emit_inst JMP [Label cond] [];
        new_block exit;
        return ()
     od) sj = ((),st')
Proof
  strip_tac >> drule compile_toplevel_immutable_ptr >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  Cases_on `bd` >>
  simp[Once compile_stmt_def, expr_type_def, LET_THM, vv_location_def,
       vv_operand_def, mk_ptr_def, is_slot_addressed_def,
       compile_ptr_load_def, word_scale_def, bound_length_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 10 (pairarg_tac >> gvs[]) >>
  ntac 10 (pairarg_tac >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> metis_tac[]
QED

(* The prefix certificate starts after the optional immutable length load.
   Fixed arrays reuse the MUL result; only dynamic arrays add a header. *)
Theorem compile_for_immutable_prefix:
  cenv.ce_alloca_locals /\
  (do bc <- declare_local cenv id et;
      emit_local_alloca bc id;
      entry <- fresh_label "iter_entry";
      cond <- fresh_label "iter_cond";
      bod <- fresh_label "iter_body";
      incr <- fresh_label "iter_incr";
      exit <- fresh_label "iter_exit";
      emit_inst JMP [Label entry] [];
      new_block entry;
      idx <- fresh_var;
      emit_inst ASSIGN [Lit 0w] [idx];
      (if dyn then
         do invalid <- emit_op GT [lvo; Lit (n2w cap)];
            valid <- emit_op ISZERO [invalid];
            emit_void ASSERT [valid] od
       else return ());
      emit_inst JMP [Label cond] [];
      new_block cond;
      done <- emit_op EQ [Var idx; lvo];
      emit_inst JNZ [done; Label exit; Label bod] [];
      new_block bod;
      offv <- emit_op MUL [Var idx;
                 Lit (n2w (elem_size_in_location cenv LocCode et))];
      tot <- (if dyn then emit_op ADD [Lit 32w; offv] else return offv);
      ep <- emit_op ADD [Lit (n2w off); tot];
      return (bc,entry,cond,bod,incr,exit,idx,offv,tot,ep)
   od) st1 = ((bc,entry,cond,bod,incr,exit,idx,offo,toto,epo),sa) ==>
  ?p dv ov ep h.
    p = STRING #"%" (toString st1.cs_next_var) /\
    idx = STRING #"%" (toString (st1.cs_next_var + 1)) /\
    dv = STRING #"%" (toString (st1.cs_next_var + (if dyn then 4 else 2))) /\
    ov = STRING #"%" (toString (st1.cs_next_var + (if dyn then 5 else 3))) /\
    ep = STRING #"%" (toString (st1.cs_next_var + (if dyn then 7 else 4))) /\
    h = st1.cs_next_id + (if dyn then 9 else 6) /\
    offo = Var ov /\ epo = Var ep /\
    (if dyn then ?tv. toto = Var tv else toto = Var ov) /\
    entry = fresh_label_output "iter_entry" st1.cs_next_label /\
    cond = fresh_label_output "iter_cond" (st1.cs_next_label + 1) /\
    bod = fresh_label_output "iter_body" (st1.cs_next_label + 2) /\
    incr = fresh_label_output "iter_incr" (st1.cs_next_label + 3) /\
    exit = fresh_label_output "iter_exit" (st1.cs_next_label + 4) /\
    declare_local cenv id et st1 =
      (bc, st1 with cs_next_var := st1.cs_next_var + 1) /\
    FLOOKUP bc.ce_vars id =
      SOME (PtrVar (Var p) (type_memory_bytes cenv et)) /\
    sa.cs_current_bb = bod /\
    sa.cs_current_insts =
      [mk_inst h MUL
         [Var idx; Lit (n2w (elem_size_in_location cenv LocCode et))] [ov]] ++
      (if dyn then [mk_inst (h + 1) ADD [Lit 32w; Var ov]
                       [STRING #"%" (toString (st1.cs_next_var + 6))]] else []) ++
      [mk_inst (h + (if dyn then 2 else 1)) ADD
         [Lit (n2w off); toto] [ep]] /\
    sa.cs_next_var = st1.cs_next_var + (if dyn then 8 else 5) /\
    sa.cs_next_id = h + (if dyn then 3 else 2) /\
    sa.cs_next_label = st1.cs_next_label + 5 /\
      sa.cs_blocks =
        [<|bb_label := cond; bb_instructions :=
           [mk_inst (h - 2) EQ [Var idx; lvo] [dv];
            mk_inst (h - 1) JNZ [Var dv; Label exit; Label bod] []]|>;
         <|bb_label := entry; bb_instructions :=
           [mk_inst (st1.cs_next_id + 2) ASSIGN [Lit 0w] [idx]] ++
           (if dyn then
             [mk_inst (st1.cs_next_id + 3) GT [lvo; Lit (n2w cap)]
                [STRING #"%" (toString (st1.cs_next_var + 2))];
              mk_inst (st1.cs_next_id + 4) ISZERO
                [Var (STRING #"%" (toString (st1.cs_next_var + 2)))]
                [STRING #"%" (toString (st1.cs_next_var + 3))];
              mk_inst (st1.cs_next_id + 5) ASSERT
                [Var (STRING #"%" (toString (st1.cs_next_var + 3)))] []]
            else []) ++
           [mk_inst (h - 3) JMP [Label cond] []]|>;
         <|bb_label := st1.cs_current_bb; bb_instructions :=
           st1.cs_current_insts ++
           [mk_inst st1.cs_next_id ALLOCA
              [Lit (n2w (type_memory_bytes cenv et))] [p];
            mk_inst (st1.cs_next_id + 1) JMP [Label entry] []]|>] ++ st1.cs_blocks
Proof
  strip_tac >>
  Cases_on `declare_local cenv id et st1` >>
  rename1 `declare_local cenv id et st1 = (bc0,st2)` >>
  drule_all declare_local_ptr >> strip_tac >>
  qpat_x_assum `_ st1 = ((bc,entry,cond,bod,incr,exit,idx,offo,toto,epo),sa)` mp_tac >>
  Cases_on `dyn` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[emit_local_alloca_def, fresh_label_def, emit_inst_def, emit_op_def,
       emit_void_def, fresh_id_def, emit_def, new_block_def, fresh_var_def,
       comp_get_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       LET_THM] >> strip_tac >> gvs[] >>
  simp[GSYM arithmeticTheory.ADD_ASSOC] >> metis_tac[]
QED

(* The entry certificate keeps compiler ownership separate from runtime
   source readiness.  The literal source base is never a memory pointer. *)
Theorem compile_for_immutable_entry_code:
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  compile_stmt cenv lctx ty
    (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) n stmts) st =
    ((),st') /\ cenv.ce_alloca_locals /\ fn_has_code st st' func /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
                cs_extends sa sb) ==>
  ?dyn lvo st1 bc p idx dv ov ep h entry cond bod incr exit toto
   sa sb0 sb1 sj nv.
    dyn = (case bd of Dynamic _ => T | Fixed _ => F) /\
    (if dyn then
       compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
     else return (Lit (n2w (bound_length bd)))) st = (lvo,st1) /\
    p = STRING #"%" (toString st1.cs_next_var) /\
    idx = STRING #"%" (toString (st1.cs_next_var + 1)) /\
    dv = STRING #"%" (toString (st1.cs_next_var + (if dyn then 4 else 2))) /\
    ov = STRING #"%" (toString (st1.cs_next_var + (if dyn then 5 else 3))) /\
    ep = STRING #"%" (toString (st1.cs_next_var + (if dyn then 7 else 4))) /\
    h = st1.cs_next_id + (if dyn then 9 else 6) /\
    nv = STRING #"%" (toString sj.cs_next_var) /\
    (if dyn then ?tv. toto = Var tv else toto = Var ov) /\
    entry = fresh_label_output "iter_entry" st1.cs_next_label /\
    cond = fresh_label_output "iter_cond" (st1.cs_next_label + 1) /\
    bod = fresh_label_output "iter_body" (st1.cs_next_label + 2) /\
    incr = fresh_label_output "iter_incr" (st1.cs_next_label + 3) /\
    exit = fresh_label_output "iter_exit" (st1.cs_next_label + 4) /\
    declare_local cenv id et st1 =
      (bc, st1 with cs_next_var := st1.cs_next_var + 1) /\
    FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv et)) /\
    sa.cs_current_bb = bod /\
    sa.cs_current_insts =
      [mk_inst h MUL
         [Var idx; Lit (n2w (elem_size_in_location cenv LocCode et))] [ov]] ++
      (if dyn then [mk_inst (h + 1) ADD [Lit 32w; Var ov]
                       [STRING #"%" (toString (st1.cs_next_var + 6))]] else []) ++
      [mk_inst (h + (if dyn then 2 else 1)) ADD [Lit (n2w off); toto] [ep]] /\
    sa.cs_next_var = st1.cs_next_var + (if dyn then 8 else 5) /\
    sa.cs_next_id = h + (if dyn then 3 else 2) /\
    sa.cs_next_label = st1.cs_next_label + 5 /\
    compile_iter_elem_copy cenv (Var ep) (Var p)
      (elem_size_in_location cenv LocCode et) LocCode F et et sa = ((),sb0) /\
    same_blocks sa sb0 /\ sb0.cs_current_bb = bod /\
    sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0 /\
    ~block_is_terminated sb0 /\ sa.cs_next_var <= sb0.cs_next_var /\
    compile_stmts bc (InLoop exit incr) ty stmts sb0 = ((),sb1) /\
    emit_jmp_if_not_terminated incr sb1 = ((),sj) /\
    sj.cs_next_var = sb1.cs_next_var /\
    (~block_is_terminated sb1 ==>
      sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
      sj.cs_current_insts = sb1.cs_current_insts ++
        [mk_inst sb1.cs_next_id JMP [Label incr] []]) /\
    cs_extends st st1 /\ cs_extends st1 sa /\ cs_extends sa sb0 /\
    cs_extends sb0 sb1 /\ cs_extends sb1 sj /\ cs_extends sj st' /\
    fn_has_code st1 sa func /\ fn_has_code sa sb0 func /\
    fn_has_code sb0 sb1 func /\ fn_has_code sb1 sj func /\
    fn_has_code sj st' func /\
    lookup_block st1.cs_current_bb func.fn_blocks =
      SOME <|bb_label := st1.cs_current_bb; bb_instructions :=
        st1.cs_current_insts ++
        [mk_inst st1.cs_next_id ALLOCA
           [Lit (n2w (type_memory_bytes cenv et))] [p];
         mk_inst (st1.cs_next_id + 1) JMP [Label entry] []]|> /\
    lookup_block entry func.fn_blocks =
      SOME <|bb_label := entry; bb_instructions :=
        [mk_inst (st1.cs_next_id + 2) ASSIGN [Lit 0w] [idx]] ++
        (if dyn then
          [mk_inst (st1.cs_next_id + 3) GT [lvo; Lit (n2w (bound_length bd))]
             [STRING #"%" (toString (st1.cs_next_var + 2))];
           mk_inst (st1.cs_next_id + 4) ISZERO
             [Var (STRING #"%" (toString (st1.cs_next_var + 2)))]
             [STRING #"%" (toString (st1.cs_next_var + 3))];
           mk_inst (st1.cs_next_id + 5) ASSERT
             [Var (STRING #"%" (toString (st1.cs_next_var + 3)))] []]
         else []) ++
        [mk_inst (h - 3) JMP [Label cond] []]|> /\
    lookup_block cond func.fn_blocks =
      SOME <|bb_label := cond; bb_instructions :=
        [mk_inst (h - 2) EQ [Var idx; lvo] [dv];
         mk_inst (h - 1) JNZ [Var dv; Label exit; Label bod] []]|> /\
    lookup_block incr func.fn_blocks =
      SOME <|bb_label := incr; bb_instructions :=
        [mk_inst sj.cs_next_id ADD [Var idx; Lit 1w] [nv];
         mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [idx];
         mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|> /\
    st'.cs_current_bb = exit /\ st'.cs_current_insts = []
Proof
  strip_tac >> drule_all compile_for_immutable_stages >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` kall_tac >>
  drule_all compile_for_immutable_prefix >> strip_tac >>
  dxrule compile_for_array_suffix >> strip_tac >>
  `cs_extends st st1` by
    (Cases_on `bd`
     >- (gvs[comp_return_def] >> simp[cs_extends_def]) >>
     gvs[] >> drule immutable_iter_load_static >> simp[]) >>
  `cs_extends st1 sa` by (irule array_prefix_extends >> metis_tac[]) >>
  `~block_is_terminated sa` by
    (Cases_on `bd` >>
     simp[block_is_terminated_def, mk_inst_def, is_terminator_def]) >>
  qpat_x_assum `_ sa = ((),sb0)` mp_tac >> simp[] >> strip_tac >>
  drule_all immutable_iter_copy_static >> strip_tac >>
  drule array_body_backedge >> strip_tac >>
  `cs_extends sb0 sb1` by metis_tac[] >>
  `cs_extends st sa` by metis_tac[cs_extends_trans] >>
  drule_all array_stages_code >> strip_tac >>
  `fn_has_code st1 sa func` by
    metis_tac[fn_has_code_split] >>
  qmatch_asmsub_abbrev_tac `sa.cs_blocks = prefix_blocks ++ st1.cs_blocks` >>
  qmatch_asmsub_abbrev_tac `st'.cs_blocks = suffix_blocks ++ sj.cs_blocks` >>
  qexistsl_tac [`toto`, `sa`, `sb0`, `sb1`, `sj`] >>
  fs[] >>
  conj_tac >- (Cases_on `bd` >> gvs[]) >>
  conj_tac >- fs[exprLoweringPropsTheory.same_blocks_def] >>
  conj_tac
  >- (irule array_emitted_block_lookup >> simp[] >>
      qexistsl_tac [`prefix_blocks`, `st1`, `sa`] >>
      conj_tac >- asm_rewrite_tac[] >>
      reverse conj_tac >- asm_rewrite_tac[] >>
      simp_tac bool_ss [Abbr `prefix_blocks`, MEM] >>
      disj2_tac >> disj2_tac >> asm_rewrite_tac[]) >>
  conj_tac
  >- (irule array_emitted_block_lookup >> simp[] >>
      qexistsl_tac [`prefix_blocks`, `st1`, `sa`] >>
      conj_tac >- asm_rewrite_tac[] >>
      reverse conj_tac >- asm_rewrite_tac[] >>
      simp_tac bool_ss [Abbr `prefix_blocks`, MEM] >>
      disj2_tac >> disj1_tac >> asm_rewrite_tac[]) >>
  conj_tac
  >- (irule array_emitted_block_lookup >> simp[] >>
      qexistsl_tac [`prefix_blocks`, `st1`, `sa`] >>
      conj_tac >- asm_rewrite_tac[] >>
      reverse conj_tac >- asm_rewrite_tac[] >>
      simp_tac bool_ss [Abbr `prefix_blocks`, MEM] >>
      disj1_tac >> asm_rewrite_tac[]) >>
  irule array_emitted_block_lookup >> simp[] >>
  qexistsl_tac [`suffix_blocks`, `sj`, `st'`] >>
  simp[Abbr `suffix_blocks`]
QED

(* Body cleanup depends on the increment block, not on the source location. *)
Theorem counted_array_body_finish:
  k < LENGTH vs /\
  (~block_is_terminated sb1 ==>
    sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
    sj.cs_current_insts = sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb1 sj func) /\
  lookup_block incr_lbl func.fn_blocks =
    SOME <|bb_label := incr_lbl; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond_lbl] []]|> /\
  (!scopes. not_local_ptr cenv scopes idx /\ not_local_ptr cenv scopes nv) /\
  p <> idx /\ p <> nv /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
  gas_marked_exec F (ctx,func) (eval_stmts cx stmts) (entry,s2) marks res ee (OK t) /\
  stmt_post ctx func cx (InLoop exit_lbl incr_lbl) bc bc' sb0 sb1 s2
    res (ee with gas_obs := []) t /\
  cenv_top_ext cenv bc entry.scopes /\
  (!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) /\
  lookup_var idx s2 = SOME (n2w k) /\ lookup_var p s2 = SOME dst /\
  eval_operand saved_base s2 = SOME arr_base /\
  FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  ret_pc_ok bc sb0 s2 /\ ret_pc_ok cenv st s2 /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. saved_base = Var x ==> not_fresh_at sb0 x) /\
  (!l. saved_base <> Label l) /\
  (!x. not_fresh_at caller x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  array_caller_frame caller cc s2 ==>
  ?rest u. ee.scopes <> [] /\ rest = TL ee.scopes /\
    gas_marked_path F ctx func t 0 (OK u) /\ array_caller_frame caller cc u /\
    ((res = INR BreakException /\ u.vs_current_bb = exit_lbl /\
      u.vs_inst_idx = 0 /\ ~u.vs_halted /\
      stmt_state_rel ctx func cenv cx
        (ee with <|scopes := rest; gas_obs := []|>) u) \/
     ((res = INL () \/ res = INR ContinueException) /\
      array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
        ainst cond_lbl st (SUC k) (ee with <|scopes := rest; gas_obs := []|>) u))
Proof
  strip_tac >> drule_all array_body_counted_post >> strip_tac >>
  `array_caller_frame caller cc t` by
    (fs[array_caller_frame_def] >> metis_tac[]) >>
  Cases_on `res = INR BreakException`
  >- (qexistsl_tac [`rest`, `t`] >>
      fs[stmt_lands_def, gas_marked_path_def, gas_path_rules]) >>
  `res = INL () \/ res = INR ContinueException` by fs[stmt_lands_def] >>
  drule_all array_body_runtime_frame >> strip_tac >>
  `~t.vs_halted /\ stmt_state_rel ctx func cenv cx
      (ee with <|scopes := rest; gas_obs := []|>) t` by fs[] >>
  `array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst t.vs_current_bb st k (ee with <|scopes := rest; gas_obs := []|>)
    (t with vs_inst_idx := 0)` by
      (fs[array_loop_inv_def, stmt_state_rel_inst_idx, lookup_var_def,
           ret_pc_ok_def] >>
       Cases_on `saved_base` >> gvs[eval_operand_def, lookup_var_def]) >>
  `?next. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
     ainst cond_lbl st (k+1) (ee with <|scopes := rest; gas_obs := []|>) next /\
     (!x. x <> idx /\ x <> nv ==> lookup_var x next = lookup_var x t) /\
     next.vs_allocas = t.vs_allocas /\ gas_marked_path F ctx func t 0 (OK next)` by
    (irule array_body_continue_iteration_framed >> simp[] >>
     goal_assum (drule_at (Pat `lookup_block _ _ = _`)) >>
     goal_assum (drule_at (Pat `stmt_lands _ _ _ _`)) >>
     qexists_tac `sj` >> simp[]) >>
  qexistsl_tac [`rest`, `next`] >> simp[arithmeticTheory.ADD1] >>
  fs[array_caller_frame_def] >> metis_tac[]
QED

(* Gas cleanup consumes a prepared body and its ordinary finishing callback.
   Neither preparation nor finishing here assumes a memory-valued source. *)
Theorem counted_array_round_from_body:
  entry = es with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
    gas_obs := []|> /\
  gas_marked_exec F (ctx,func) (push_scope_with_var id tv (EL k vs))
    (es,cc) [] (INL ())
    (es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes)
    (OK s2) /\
  gas_outcome F (cx_tops cx) (ctx,func) (eval_stmts cx stmts) (entry,s2)
    (stmt_post ctx func cx (InLoop exit_lbl incr_lbl) bc bc' sb0 sb1 s2)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r) /\
  (!gs r es2. eval_stmts cx stmts (entry with gas_obs := gs) = (r,es2) ==>
    stmt_res_ok (InLoop exit_lbl incr_lbl) r /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) /\
  (!marks res ee t.
    gas_marked_exec F (ctx,func) (eval_stmts cx stmts)
      (entry,s2) marks res ee (OK t) /\
    stmt_post ctx func cx (InLoop exit_lbl incr_lbl) bc bc' sb0 sb1 s2
      res (ee with gas_obs := []) t ==>
    ?rest u. ee.scopes <> [] /\ rest = TL ee.scopes /\
      gas_marked_path F ctx func t 0 (OK u) /\ array_caller_frame caller cc u /\
      ((res = INR BreakException /\ u.vs_current_bb = exit_lbl /\
        u.vs_inst_idx = 0 /\ ~u.vs_halted /\
        stmt_state_rel ctx func cenv cx
          (ee with <|scopes := rest; gas_obs := []|>) u) \/
       ((res = INL () \/ res = INR ContinueException) /\
        array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
          ainst cond_lbl st (SUC k) (ee with <|scopes := rest; gas_obs := []|>) u))) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do push_scope_with_var id tv (EL k vs);
        finally (try (do eval_stmts cx stmts; return F od) handle_loop_exception)
          pop_scope od) (es,cc)
    (\res ee t. ?broke. res = INL broke /\ array_caller_frame caller cc t /\
      (broke ==> t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
        stmt_state_rel ctx func cenv cx ee t) /\
      (~broke ==> array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base
        p dst sz ainst cond_lbl st (SUC k) ee t))
    (\res ee r. ?ex. res = INR ex /\
      !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome F (cx_tops cx) (ctx,func) round (es,cc) Q R` >>
  qhdtm_x_assum `gas_outcome` mp_tac >> rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "ordinary"
  >> suspend "exempt"
QED

Resume counted_array_round_from_body[exempt]:
  `?sc rest. ee.scopes = sc :: rest` by
    (drule gas_exempt_cert_execution >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     simp[ignore_bind_def, bind_def, return_def, AllCaseEqs()] >> strip_tac >>
     qpat_x_assum `!gs r es2. _`
       (qspec_then `gas_explicit marks s2.vs_gas_readings` mp_tac) >>
     gvs[] >> strip_tac >> goal_assum (drule_at Any)) >>
  gvs[] >>
  drule_all loop_round_exempt_cert >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >>
  simp[Abbr `round`] >> goal_assum (drule_at Any)
QED

Resume counted_array_round_from_body[ordinary]:
  qhdtm_x_assum `gas_summary_at` mp_tac >>
  rewrite_tac[gas_summary_at_def] >>
  disch_then (qx_choose_then `res` (qx_choose_then `ee`
    (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
  `?sc rest. ee.scopes = sc :: rest` by
    (qhdtm_assum `gas_marked_exec` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     qpat_x_assum `!gs r es2. _`
       (qspec_then `gas_explicit marks s2.vs_gas_readings` mp_tac) >>
     gvs[] >> strip_tac >> goal_assum (drule_at Any)) >>
  drule_all loop_body_cleanup_exec >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_marked_exec F (ctx,func) cleanup _ _ wrapped fin r` >>
  `gas_marked_exec F (ctx,func) round (es,cc) marks wrapped fin r` by
    (simp[Abbr `round`, ignore_bind_def] >>
     irule (SRULE [] (Q.INST [`left` |-> `[]`] gas_marked_exec_bind_normal)) >>
     goal_assum (drule_at Any) >> gvs[]) >>
  strip_tac >- suspend "normal_finish" >> suspend "exit_finish"
QED

Resume counted_array_round_from_body[exit_finish]:
  fs[] >>
  `res <> INL () /\ res <> INR BreakException /\ res <> INR ContinueException` by
    (qpat_x_assum `!tail. stmt_exit _ _ _ _` (qspec_then `[]` mp_tac) >>
     metis_tac[stmt_exit_loop_ctl]) >>
  Cases_on `res` >- gvs[] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`wrapped`, `fin`, `r`] >> simp[] >> disj2_tac >>
  gvs[Abbr `R`, Abbr `fin`, Abbr `wrapped`, stmt_exit_def]
QED

Resume counted_array_round_from_body[normal_finish]:
  fs[] >>
  qpat_x_assum `!marks res ee t. _` drule_all >> strip_tac >>
  `gas_marked_exec F (ctx,func) round (es,cc) marks wrapped fin (OK u)` by
    (qhdtm_x_assum `gas_marked_path` mp_tac >>
     qpat_x_assum `gas_marked_exec _ _ round _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[gas_marked_exec_def] >>
     rpt strip_tac >> simp[] >>
     qpat_x_assum `gas_marked_path _ _ _ cc _ _` mp_tac >>
     disch_then (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then drule >> simp[]) >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`wrapped`, `fin`, `OK u`] >> simp[] >> disj1_tac >>
  simp[Abbr `Q`, Abbr `fin`, Abbr `wrapped`] >> gvs[]
QED
Finalise counted_array_round_from_body

(* Once the location-aware entry has produced the body state, invocation is
   independent of the element's source representation. *)
Theorem immutable_round_prepare:
  gas_marked_path F ctx func cc 0 (OK s2) /\
  s2.vs_current_bb = sb0.cs_current_bb /\
  s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
  stmt_state_rel ctx func bc cx
    (es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) s2 /\
  ret_pc_ok bc sb0 s2 /\
  ei = es with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes;
    gas_obs := []|> /\
  stmt_frag ctx func cx lctx RetQ bc m source ei /\
  m sb0 = (bc',sb1) /\ fn_has_code sb0 sb1 func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved bc sb0 /\
  ~block_is_terminated sb0 /\ gas_admissible source (stmt_res_ok lctx) ei ==>
  gas_marked_exec F (ctx,func) (push_scope_with_var id tv v) (es,cc) []
    (INL ()) (es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes)
    (OK s2) /\
  gas_outcome F (cx_tops cx) (ctx,func) source (ei,s2)
    (stmt_post ctx func cx lctx bc bc' sb0 sb1 s2)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  (conj_tac >- (irule push_scope_with_var_zero_exec >> simp[])) >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_frag_def, stmt_framed_frag_def] >>
  disch_then irule >> simp[] >>
  `!E. stmt_state_rel ctx func bc cx E s2 ==>
       stmt_state_rel ctx func bc cx (E with gas_obs := []) s2` by
    (rpt strip_tac >>
     `s2 = s2 with <|vs_gas_readings := s2.vs_gas_readings;
                     vs_inst_idx := s2.vs_inst_idx|>` by
       simp[venomStateTheory.venom_state_component_equality] >>
     pop_assum SUBST1_TAC >> irule msg_gas_state_frame >> simp[]) >>
  first_x_assum (qspec_then `es with scopes :=
    (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
      :: es.scopes` mp_tac) >>
  impl_tac >- fs[] >>
  match_mp_tac EQ_IMPLIES >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[vyperStateTheory.evaluation_state_component_equality]
QED

Theorem immutable_address_prefix_run:
  lookup_var idx s = SOME (n2w k) /\ ov <> tot ==>
  run_inst_seq
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
     (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
     [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]]) s =
  OK (update_var ep (n2w off + n2w ((if dyn then 32 else 0) + k * stride))
       (if dyn then update_var tot (n2w (32 + k * stride))
          (update_var ov (n2w (k * stride)) s)
        else update_var ov (n2w (k * stride)) s))
Proof
  strip_tac >> Cases_on `dyn`
  >- (simp[GSYM word_add_n2w, AC WORD_ADD_ASSOC WORD_ADD_COMM] >>
      irule (SRULE [GSYM word_add_n2w, AC WORD_ADD_ASSOC WORD_ADD_COMM]
        dynarray_address_prefix_run) >> simp[eval_operand_def]) >>
  simp[] >>
  `step_inst_base (mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]) s =
   OK (update_var ov (n2w (k * stride)) s)` by
    (simp[GSYM word_mul_n2w] >> irule step_MUL >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst j5 ADD [Lit (n2w off); Var ov] [ep])
      (update_var ov (n2w (k * stride)) s) =
   OK (update_var ep (n2w off + n2w (k * stride))
      (update_var ov (n2w (k * stride)) s))` by
    (irule step_ADD >> simp[eval_operand_def, lookup_var_update_var]) >>
  simp[run_inst_seq_def]
QED

Theorem immutable_value_holds_transport:
  cenv_top_ext cenv bc scopes /\
  es'.immutables = es.immutables /\ t.vs_memory = s.vs_memory /\
  immutable_holds cenv cx ty (Value v) a es s ==>
  immutable_holds bc cx ty (Value v) a es' t
Proof
  simp[cenv_top_ext_def] >> strip_tac >>
  qpat_x_assum `_ = cenv` (SUBST_ALL_TAC o SYM) >>
  gvs[immutable_holds_def, read_result_def, return_def] >>
  qexistsl_tac [`name`, `off`, `itv`, `iv`, `k`] >> simp[]
QED

Theorem immutable_iter_copy_top_ext:
  cenv_top_ext cenv bc scopes ==>
  compile_iter_elem_copy cenv src dst bytes LocCode F et et =
  compile_iter_elem_copy bc src dst bytes LocCode F et et
Proof
  simp[cenv_top_ext_def] >> strip_tac >>
  qpat_x_assum `_ = cenv` (SUBST_ALL_TAC o SYM) >>
  simp[compile_iter_elem_copy_def]
QED

(* The straight-line execution cut retains the copy's allocation/static frame;
   the later path wrapper accounts for instruction indices. *)
Theorem immutable_array_entry_seq:
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocCode F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ 0 < stride /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes tot /\
  not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ lookup_var p s = SOME dst /\
  p <> ov /\ p <> tot /\ p <> ep /\ ov <> tot /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  w2n dst + stride < dimword (:256) /\
  immutable_holds cenv cx et (Value v)
    (n2w off + n2w ((if dyn then 32 else 0) + k * stride)) es s ==>
  ?s1 t.
    s1 = update_var ep (n2w off + n2w ((if dyn then 32 else 0) + k * stride))
      (if dyn then update_var tot (n2w (32 + k * stride))
         (update_var ov (n2w (k * stride)) s)
       else update_var ov (n2w (k * stride)) s) /\
    run_inst_seq
      ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
       (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
       [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]] ++
       emitted_insts sa sb0) s = OK t /\
    copy_runtime_frame sa s1 sb0 t /\
    stmt_state_rel ctx func bc cx
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) t
Proof
  strip_tac >>
  qabbrev_tac `rhs = update_var ep
    (n2w off + n2w ((if dyn then 32 else 0) + k * stride))
    (if dyn then update_var tot (n2w (32 + k * stride))
       (update_var ov (n2w (k * stride)) s)
     else update_var ov (n2w (k * stride)) s)` >>
  qexists_tac `rhs` >> simp[] >>
  `run_inst_seq
      ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
       (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
       [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]]) s = OK rhs` by
    (qunabbrev_tac `rhs` >> irule immutable_address_prefix_run >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es rhs` by
    (Cases_on `dyn` >> simp[Abbr `rhs`] >>
     rpt (irule stmt_state_rel_update_var >> simp[])) >>
  `stmt_state_rel ctx func bc cx (es with scopes := FEMPTY :: es.scopes) rhs` by
    (irule array_empty_scope_rel_transport >> qexists_tac `cenv` >> simp[]) >>
  `immutable_holds bc cx et (Value v)
     (n2w off + n2w ((if dyn then 32 else 0) + k * stride))
     (es with scopes := FEMPTY :: es.scopes) rhs` by
    (irule immutable_value_holds_transport >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `FEMPTY :: es.scopes` >> simp[] >>
     Cases_on `dyn` >> simp[Abbr `rhs`, update_var_def]) >>
  `compile_iter_elem_copy bc (Var ep) (Var p) stride LocCode F et et sa = ((),sb0)` by
    (drule immutable_iter_copy_top_ext >> disch_then (fn th => fs[GSYM th])) >>
  `lookup_var p rhs = SOME dst /\
   FLOOKUP rhs.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
   eval_operand (Var ep) rhs =
     SOME (n2w off + n2w ((if dyn then 32 else 0) + k * stride))` by
    (Cases_on `dyn` >>
     simp[Abbr `rhs`, lookup_var_update_var, eval_operand_def] >>
     simp[update_var_def]) >>
  `copy_old_operand sa (Var ep)` by simp[exprSimCopyTheory.copy_old_operand_def] >>
  `!q. q = p \/ ~not_local_ptr bc
      (es with scopes := FEMPTY :: es.scopes).scopes q ==> not_fresh_at sa q` by
    (simp[] >> metis_tac[array_copy_live_ptrs_reserved]) >>
  `(es with scopes := FEMPTY :: es.scopes).scopes = FEMPTY :: es.scopes /\
   lookup_scopes id (es with scopes := FEMPTY :: es.scopes).scopes = NONE /\
   not_local_ptr bc (es with scopes := FEMPTY :: es.scopes).scopes p` by
    simp[lookup_scopes_def] >>
  drule_all immutable_iter_copy_declare_rel >>
  disch_then (qspec_then `F` strip_assume_tac) >>
  qexists_tac `z` >> simp[] >>
  qpat_assum `run_inst_seq _ s = OK rhs`
    (mp_then Any (qspec_then `emitted_insts sa sb0` mp_tac) run_inst_seq_append) >>
  fs[exprSimCopyTheory.copy_runtime_frame_def]
QED

(* This control boundary only advances an instruction prefix, not the source
   memory view: immutable constructor copies may update memory. *)
Theorem immutable_copy_prefix_path:
  compile_iter_elem_copy cenv src dst bytes LocCode F et et sa = ((),sb) /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. MEM i.inst_opcode [MUL; ADD]) sa.cs_current_insts /\
  run_inst_seq sb.cs_current_insts s = OK t /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb.cs_current_insts bb.bb_instructions /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
  gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; DLOAD; MSTORE])
     (emitted_insts sa sb)` by
    (drule immutable_iter_copy_opcodes >> strip_tac >>
     gvs[emitted_insts_def, DROP_PREFIX]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     sb.cs_current_insts /\
   EVERY (\i. i.inst_opcode <> GAS) sb.cs_current_insts` by
    (qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >>
     simp[EVERY_APPEND] >>
     rpt conj_tac >>
     irule listTheory.EVERY_MONOTONIC >> goal_assum (drule_at Any) >>
     simp[is_terminator_def] >> rpt strip_tac >> gvs[is_terminator_def]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) sb.cs_current_insts) = 0` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `isPREFIX sb.cs_current_insts (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `s.vs_inst_idx = 0` (fn th => pure_rewrite_tac[th, DROP_0]) >>
     first_assum ACCEPT_TAC) >>
  drule_all tuple_run_inst_seq_gas_path >>
  simp[gas_marked_path_def]
QED

Theorem immutable_entry_seq_frames:
  compile_iter_elem_copy cenv src dst bytes LocCode F et et sa = ((),sb) /\
  copy_runtime_frame sa rhs sb t /\
  rhs = update_var ep a
    (if dyn then update_var tot b (update_var ov c s) else update_var ov c s) ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb /\
  t.vs_halted = s.vs_halted /\
  (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
       lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  drule_all immutable_iter_copy_state_frame >>
  simp[venom_state_component_equality] >> strip_tac >>
  fs[exprSimCopyTheory.copy_runtime_frame_def] >>
  Cases_on `dyn` >>
  fs[update_var_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem immutable_array_entry_run:
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocCode F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ 0 < stride /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes tot /\
  not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ lookup_var p s = SOME dst /\
  p <> ov /\ p <> tot /\ p <> ep /\ ov <> tot /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  w2n dst + stride < dimword (:256) /\
  immutable_holds cenv cx et (Value v)
    (n2w off + n2w ((if dyn then 32 else 0) + k * stride)) es s /\
  sa.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
    (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
    [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]] /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  s.vs_current_bb = sb0.cs_current_bb /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  not_fresh_at sa idx /\ idx <> ov /\ idx <> tot /\ idx <> ep /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  ret_pc_ok bc sb0 s /\ ret_pc_ok cenv st s /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) ==>
  ?s2. s2.vs_current_bb = sb0.cs_current_bb /\
    s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
    stmt_state_rel ctx func bc cx
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) s2 /\
    ret_pc_ok bc sb0 s2 /\ ret_pc_ok cenv st s2 /\
    lookup_var idx s2 = SOME (n2w k) /\ lookup_var p s2 = SOME dst /\
    FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    array_caller_frame caller s s2 /\ gas_marked_path F ctx func s 0 (OK s2)
Proof
  strip_tac >> drule_all immutable_array_entry_seq >>
  disch_then (qspecl_then [`j5`, `j4`, `j3`] strip_assume_tac) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb /\
   t.vs_halted = s.vs_halted /\
   (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
        lookup_var x t = lookup_var x s)` by
    (drule_all immutable_entry_seq_frames >> simp[]) >>
  `not_fresh_at sa p` by metis_tac[array_copy_live_ptrs_reserved] >>
  `sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0` by
    fs[exprSimCopyTheory.copy_runtime_frame_def] >>
  `run_inst_seq sb0.cs_current_insts s = OK t` by gvs[] >>
  `EVERY (\i. MEM i.inst_opcode [MUL; ADD]) sa.cs_current_insts` by
    (Cases_on `dyn` >> simp[mk_inst_def]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `gas_marked_path F ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sb0.cs_current_insts))` by
    (drule_all immutable_copy_prefix_path >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb0.cs_current_insts` >> simp[] >>
  conj_tac
  >- (qpat_x_assum `stmt_state_rel _ _ bc _ _ t`
        (mp_then Any (qspecl_then [`t.vs_gas_readings`,
          `LENGTH sb0.cs_current_insts`, `es.gas_obs`] mp_tac) msg_gas_state_frame) >>
      simp[]) >>
  fs[ret_pc_ok_def, array_caller_frame_def, lookup_var_def] >> metis_tac[]
QED

(* The length operand is a literal for Fixed and an immutable load result for
   Dynamic.  Condition execution does not depend on its origin. *)
Theorem immutable_condition_boundary:
  lookup_block cond_lbl func.fn_blocks =
    SOME <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var idx; lvo] [dv];
       mk_inst j2 JNZ [Var dv; Label exit_lbl; Label bod] []]|> /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st k es cc /\
  eval_operand lvo cc = SOME (n2w (LENGTH vs)) /\ LENGTH vs < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv) ==>
  ?next.
    array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst (if k = LENGTH vs then exit_lbl else bod) st k es next /\
    (!x. x <> dv ==> lookup_var x next = lookup_var x cc) /\
    next.vs_allocas = cc.vs_allocas /\
    gas_marked_path F ctx func cc 0 (OK next) /\
    (!fuel rr. run_from fuel ctx func next = rr /\ (!e. rr <> Error e) ==>
       ?fuel'. run_from fuel' ctx func cc = rr)
Proof
  strip_tac >>
  `k <= LENGTH vs` by fs[array_loop_inv_def] >>
  `(n2w k : bytes32) = n2w (LENGTH vs) <=> k = LENGTH vs` by
    (`k < dimword (:256)` by decide_tac >> simp[n2w_11]) >>
  qexists_tac `jump_to (if k = LENGTH vs then exit_lbl else bod)
    (update_var dv (bool_to_word (k = LENGTH vs)) cc)` >>
  conj_tac
  >- (fs[array_loop_inv_def, lookup_var_def] >>
      `stmt_state_rel ctx func cenv cx es
         (update_var dv (bool_to_word (k = LENGTH vs)) cc)` by
        (irule stmt_state_rel_update_var >> simp[]) >>
      fs[stmt_state_rel_jump_to, jump_to_def, update_var_def,
           lookup_var_def, FLOOKUP_UPDATE] >>
      conj_tac
      >- (Cases_on `saved_base` >>
          gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
      fs[ret_pc_ok_def] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >> simp[] >>
      Cases_on `x = dv` >> gvs[lookup_var_def, FLOOKUP_UPDATE]) >>
  conj_tac >- simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[jump_to_def, update_var_def] >>
  conj_tac
  >- (`gas_marked_path F ctx func cc 0
        (OK (jump_to (if (n2w k : bytes32) = n2w (LENGTH vs) then exit_lbl else bod)
          (update_var dv (bool_to_word ((n2w k : bytes32) = n2w (LENGTH vs))) cc)))`
        suffices_by simp[] >>
      irule eq_branch_zero_path >> fs[array_loop_inv_def] >>
      simp[get_instruction_def, mk_inst_def, eval_operand_def]) >>
  fs[array_loop_inv_def] >> drule eq_condition_block >>
  simp[] >> disch_then (qspecl_then [`ctx`, `cc`, `n2w k`, `n2w (LENGTH vs)`] mp_tac) >>
  simp[eval_operand_def] >> gvs[n2w_11]
QED

Theorem immutable_loop_last:
  lookup_block cond_lbl func.fn_blocks =
    SOME <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var idx; lvo] [dv];
       mk_inst j2 JNZ [Var dv; Label exit_lbl; Label bod] []]|> /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond_lbl st (LENGTH vs) es s /\
  eval_operand lvo s = SOME (n2w (LENGTH vs)) /\ LENGTH vs < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv) /\
  (!x. not_fresh_at caller x ==> x <> dv) /\ array_caller_frame caller old s ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx (es with gas_obs := []) t /\
    array_caller_frame caller old t
Proof
  strip_tac >> drule_all immutable_condition_boundary >> simp[] >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) next` by
    (fs[array_loop_inv_def] >> drule msg_gas_state_frame >>
     disch_then (qspecl_then [`next.vs_gas_readings`, `next.vs_inst_idx`, `[]`] mp_tac) >>
     simp[stmt_state_rel_inst_idx]) >>
  qexists_tac `next` >> fs[array_loop_inv_def] >>
  fs[array_caller_frame_def] >> metis_tac[]
QED

(* The entry guard consumes a length operand; Fixed omits it altogether. *)
Theorem immutable_entry_block_run:
  eval_operand lvo s = SOME (n2w L) /\ L <= cap /\ cap < dimword (:256) /\
  ALL_DISTINCT [idx; g; vld] /\
  (!x. lvo = Var x ==> x <> idx) ==>
  run_inst_seq
    ([mk_inst i1 ASSIGN [Lit 0w] [idx]] ++
     if dyn then
       [mk_inst i2 GT [lvo; Lit (n2w cap)] [g];
        mk_inst i3 ISZERO [Var g] [vld];
        mk_inst i4 ASSERT [Var vld] []]
     else []) s =
  OK (if dyn then update_var vld 1w (update_var g 0w (update_var idx 0w s))
      else update_var idx 0w s)
Proof
  strip_tac >> fs[ALL_DISTINCT] >>
  `step_inst_base (mk_inst i1 ASSIGN [Lit 0w] [idx]) s =
   OK (update_var idx 0w s)` by
    simp[mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def] >>
  reverse (Cases_on `dyn`) >- simp[run_inst_seq_def] >>
  qabbrev_tac `s1 = update_var idx 0w s` >>
  `eval_operand lvo s1 = SOME (n2w L)` by
    (simp[Abbr `s1`] >> irule eval_operand_update_var_mstore >> simp[]) >>
  `L < dimword (:256)` by decide_tac >>
  `bool_to_word (w2n (n2w L : bytes32) > w2n (n2w cap : bytes32)) = 0w` by
    simp[bool_to_word_def] >>
  `step_inst_base (mk_inst i2 GT [lvo; Lit (n2w cap)] [g]) s1 =
   OK (update_var g 0w s1)` by
    (qpat_x_assum `bool_to_word _ = 0w` (SUBST1_TAC o SYM) >>
     irule step_GT >> simp[eval_operand_def]) >>
  qabbrev_tac `s2 = update_var g 0w s1` >>
  `step_inst_base (mk_inst i3 ISZERO [Var g] [vld]) s2 =
   OK (update_var vld 1w s2)` by
    (`1w = bool_to_word ((0w:bytes32) = 0w)` by simp[bool_to_word_def] >>
     pop_assum SUBST1_TAC >> irule step_ISZERO >>
     simp[Abbr `s2`, eval_operand_def, lookup_var_update_var]) >>
  qabbrev_tac `s3 = update_var vld 1w s2` >>
  `step_inst_base (mk_inst i4 ASSERT [Var vld] []) s3 = OK s3` by
    (irule step_ASSERT_ok >>
     simp[Abbr `s3`, eval_operand_def, lookup_var_update_var]) >>
  simp[run_inst_seq_def]
QED

(* Initialization after the optional source-header load.  The source pointer
   is a literal code offset, while the loaded length is framed as an operand. *)
Theorem immutable_allocate_initialize:
  ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  MEM ainst (fn_insts func) /\ fn_inst_ids_distinct func /\
  ainst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [ainst; mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst e1 ASSIGN [Lit 0w] [idx]] ++
      (if dyn then
        [mk_inst e2 GT [lvo; Lit (n2w cap)] [g];
         mk_inst e3 ISZERO [Var g] [vld];
         mk_inst e4 ASSERT [Var vld] []] else []) ++
      [mk_inst e5 JMP [Label cond_lbl] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  stmt_state_rel ctx func cenv cx es s0 /\ P es /\
  lookup_scopes id es.scopes = NONE /\
  eval_operand lvo s0 = SOME (n2w (LENGTH vs)) /\
  LENGTH vs <= cap /\ cap < dimword (:256) /\
  ret_pc_ok cenv st s0 /\ ALL_DISTINCT [p; idx; g; vld] /\
  not_local_ptr cenv es.scopes p /\ not_local_ptr cenv es.scopes idx /\
  not_local_ptr cenv es.scopes g /\ not_local_ptr cenv es.scopes vld /\
  (!x. lvo = Var x ==> ~MEM x [p; idx; g; vld]) /\
  (!x. not_fresh_at st x ==> ~MEM x [p; idx; g; vld]) ==>
  ?dst cc.
    array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz ainst cond_lbl st 0 es cc /\
    eval_operand lvo cc = SOME (n2w (LENGTH vs)) /\
    array_caller_frame st s0 cc /\
    gas_marked_path F ctx func s0 0 (OK cc)
Proof
  strip_tac >> fs[ALL_DISTINCT] >>
  `eval_operand (Lit (n2w off)) s0 = SOME (n2w off : bytes32)` by
    simp[eval_operand_def] >>
  `!x. Lit (n2w off : bytes32) = Var x ==> x <> p` by simp[] >>
  drule_all array_allocate_ready >> strip_tac >>
  rename1 `exec_alloca ainst s0 (n2w sz : bytes32) = OK s1` >>
  rename1 `lookup_var p s1 = SOME dst` >>
  drule_all array_alloca_frame >> strip_tac >>
  `step_inst_base ainst s0 = OK s1` by
    simp[step_inst_base_opcode_eqs, eval_operand_def] >>
  `gas_marked_path F ctx func s0 0 (OK (jump_to entry s1))` by
    (irule inst_seq_jump_zero_path >> simp[] >>
     qexistsl_tac [`[ainst]`, `j`] >>
     simp[DROP_LENGTH_APPEND, run_inst_seq_def, is_terminator_def]) >>
  `s1.vs_labels = s0.vs_labels` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     simp[exec_alloca_def] >>
     gvs[AllCaseEqs(), update_var_def] >> rpt strip_tac >> gvs[]) >>
  `eval_operand lvo s1 = SOME (n2w (LENGTH vs))` by
    (Cases_on `lvo` >> gvs[eval_operand_def] >> metis_tac[]) >>
  qabbrev_tac `e0 = jump_to entry s1` >>
  `eval_operand lvo e0 = SOME (n2w (LENGTH vs)) /\
   e0.vs_current_bb = entry /\ e0.vs_inst_idx = 0 /\ ~e0.vs_halted` by
    (Cases_on `lvo` >> gvs[Abbr `e0`, jump_to_def, eval_operand_def, lookup_var_def]) >>
  qabbrev_tac `is = [mk_inst e1 ASSIGN [Lit 0w] [idx]] ++
    if dyn then
      [mk_inst e2 GT [lvo; Lit (n2w cap)] [g];
       mk_inst e3 ISZERO [Var g] [vld];
       mk_inst e4 ASSERT [Var vld] []] else []` >>
  qabbrev_tac `e4s = if dyn then
    update_var vld 1w (update_var g 0w (update_var idx 0w e0))
    else update_var idx 0w e0` >>
  `run_inst_seq is e0 = OK e4s` by
    (qunabbrev_tac `is` >> qunabbrev_tac `e4s` >>
     irule immutable_entry_block_run >> simp[ALL_DISTINCT] >>
     conj_tac >- metis_tac[] >>
     qexists_tac `LENGTH vs` >> simp[]) >>
  `gas_marked_path F ctx func e0 0 (OK (jump_to cond_lbl e4s))` by
    (irule inst_seq_jump_zero_path >> simp[] >>
     qexists_tac `e5` >>
     gvs[Abbr `is`, is_terminator_def] >> Cases_on `dyn` >> simp[is_terminator_def]) >>
  qabbrev_tac `cc = jump_to cond_lbl e4s` >>
  `!x. x <> idx /\ x <> g /\ x <> vld ==> lookup_var x cc = lookup_var x s1` by
    (Cases_on `dyn` >> simp[Abbr `cc`, Abbr `e4s`, Abbr `e0`,
       jump_to_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `cc.vs_allocas = s1.vs_allocas /\ cc.vs_current_bb = cond_lbl /\
   cc.vs_inst_idx = 0 /\ ~cc.vs_halted` by
    (Cases_on `dyn` >> simp[Abbr `cc`, Abbr `e4s`, Abbr `e0`,
       jump_to_def, update_var_def]) >>
  `stmt_state_rel ctx func cenv cx es cc` by
    (Cases_on `dyn` >> simp[Abbr `cc`, stmt_state_rel_jump_to, Abbr `e4s`] >>
     rpt (irule stmt_state_rel_update_var >> simp[]) >>
     simp[Abbr `e0`, stmt_state_rel_jump_to]) >>
  `lookup_var idx cc = SOME (n2w 0)` by
    (Cases_on `dyn` >> simp[Abbr `cc`, Abbr `e4s`, jump_to_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `lookup_var p cc = SOME dst` by metis_tac[] >>
  `ret_pc_ok cenv st cc` by
    (Cases_on `dyn` >> simp[Abbr `cc`, ret_pc_ok_jump_to, Abbr `e4s`,
       array_ret_pc_update, Abbr `e0`]) >>
  `cc.vs_labels = s1.vs_labels` by
    (Cases_on `dyn` >> simp[Abbr `cc`, Abbr `e4s`, Abbr `e0`,
       jump_to_def, update_var_def]) >>
  qexistsl_tac [`dst`, `cc`] >> rpt conj_tac
  >- simp[array_loop_inv_def, eval_operand_def]
  >- (Cases_on `lvo` >> gvs[eval_operand_def] >> metis_tac[])
  >- (simp[array_caller_frame_def] >> metis_tac[]) >>
  drule_all gas_marked_path_then >> simp[]
QED

(* Typed immutable-header reading is independent of the allocation prefix. *)
Theorem immutable_length_load_boundary:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  immutable_holds cenv cx (ArrayT et (Dynamic cap)) (Value (ArrayV av))
    (n2w off) es s /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
  LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av /\
  compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off)) sa = (lvo,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ret_pc_ok cenv sa s ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    eval_operand lvo u = SOME (n2w (LENGTH vs)) /\
    stmt_state_rel ctx func cenv cx es u /\ ret_pc_ok cenv sa u /\
    array_caller_frame sa s u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >>
  `context$compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode
     (Lit (n2w off)) sa = (lvo,sb)` by simp[compile_ptr_load_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off : bytes32)` by
    simp[eval_operand_def] >>
  drule_all rest_word_array_immutable_header_path >> strip_tac >>
  drule rest_word_ptr_load_fresh >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (simp[lookup_var_def] >> rpt strip_tac >> first_x_assum irule >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es (s with vs_vars := u.vs_vars)` by
    (irule stmt_state_rel_vars_frame >> simp[lookup_var_def] >>
     fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es
     ((s with vs_vars := u.vs_vars) with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    metis_tac[stmt_state_rel_inst_idx] >>
  `stmt_state_rel ctx func cenv cx es u` by
    (qpat_x_assum `u = _` SUBST1_TAC >> simp[] >> fs[]) >>
  qexists_tac `u` >> simp[gas_marked_path_def] >>
  conj_tac
  >- (fs[ret_pc_ok_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[array_caller_frame_def] >>
      qpat_x_assum `u = _` SUBST1_TAC >> simp[]) >>
  qpat_x_assum `u = _` SUBST1_TAC >> simp[]
QED

(* A Fixed length is already a literal; a Dynamic length is a typed immutable
   header.  Both expose the same entry-state/operand interface. *)
Theorem immutable_optional_length_boundary:
  (if dyn then
     compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
   else return (Lit (n2w cap))) sa = (lvo,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (dyn ==>
    immutable_holds cenv cx (ArrayT et (Dynamic cap)) (Value (ArrayV av))
      (n2w off) es s /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
    LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
  (~dyn ==> LENGTH vs = cap) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ret_pc_ok cenv sa s ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    eval_operand lvo u = SOME (n2w (LENGTH vs)) /\
    stmt_state_rel ctx func cenv cx es u /\ ret_pc_ok cenv sa u /\
    array_caller_frame sa s u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  Cases_on `dyn` >> simp[comp_return_def] >> strip_tac
  >- (drule_all immutable_length_load_boundary >> strip_tac >>
      qexists_tac `u` >> simp[]) >>
  gvs[] >> qexists_tac `s` >> simp[eval_operand_def] >>
  simp[gas_marked_path_def, gas_path_rules]
QED

(* Complete source-independent initialization: optional header read, loop
   variable allocation, then index initialization and the optional guard. *)
Theorem immutable_loop_initialize:
  (if dyn then
     compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
   else return (Lit (n2w cap))) sa = (lvo,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (dyn ==>
    immutable_holds cenv cx (ArrayT et (Dynamic cap)) (Value (ArrayV av))
      (n2w off) es s /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
    LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
  (~dyn ==> LENGTH vs = cap) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ret_pc_ok cenv sa s /\
  ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  MEM ainst (fn_insts func) /\ fn_inst_ids_distinct func /\
  ainst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) /\
  lookup_block sb.cs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      sb.cs_current_insts ++ [ainst; mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst e1 ASSIGN [Lit 0w] [idx]] ++
      (if dyn then
        [mk_inst e2 GT [lvo; Lit (n2w cap)] [g];
         mk_inst e3 ISZERO [Var g] [vld];
         mk_inst e4 ASSERT [Var vld] []] else []) ++
      [mk_inst e5 JMP [Label cond_lbl] []]|> /\
  P es /\ lookup_scopes id es.scopes = NONE /\
  LENGTH vs <= cap /\ cap < dimword (:256) /\
  ALL_DISTINCT [p; idx; g; vld] /\
  not_local_ptr cenv es.scopes p /\ not_local_ptr cenv es.scopes idx /\
  not_local_ptr cenv es.scopes g /\ not_local_ptr cenv es.scopes vld /\
  (!x. lvo = Var x ==> ~MEM x [p; idx; g; vld]) /\
  (!x. not_fresh_at sa x ==> ~MEM x [p; idx; g; vld]) ==>
  ?dst cc.
    array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz ainst cond_lbl sa 0 es cc /\
    eval_operand lvo cc = SOME (n2w (LENGTH vs)) /\
    array_caller_frame sa s cc /\
    gas_marked_path F ctx func s 0 (OK cc)
Proof
  strip_tac >> drule_all immutable_optional_length_boundary >> strip_tac >>
  `lookup_block u.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      sb.cs_current_insts ++ [ainst; mk_inst j JMP [Label entry] []]|>` by simp[] >>
  drule_all immutable_allocate_initialize >>
  disch_then (qspec_then `off` strip_assume_tac) >>
  qexistsl_tac [`dst`, `cc`] >> simp[] >> conj_tac
  >- (drule_all array_caller_frame_trans >> simp[]) >>
  drule_all gas_marked_path_then >> simp[]
QED
