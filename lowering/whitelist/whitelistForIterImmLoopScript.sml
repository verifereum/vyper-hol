(* Compiler cuts for immutable-source counted iteration.  Source preparation
   uses LocCode; the memory-only array loop contracts cannot certify it. *)
Theory whitelistForIterImmLoop
Ancestors
  whitelistForIterImmCopy whitelistForIterImmFrame whitelistForIterDynLoop
  exprSimTopLevelImmutable stmtLowering exprLoweringProps compileEnv context
  vyperAST list finite_map stmtSimForArrayParts stmtSimProps emitHelper venomInst fragExec
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
