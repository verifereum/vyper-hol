(*
 * Code shape, loop entry and stmt_frag for `for x in arr` where `arr` is a
 * local DynArray name.
 *
 * Before the loop, compile_stmt loads the length word into a register
 * (MLOAD), then allocates the loop variable as in the fixed case.  The entry
 * block sets the index to 0 and checks the length against the capacity
 * (GT/ISZERO/ASSERT).  The condition block compares the index with the length
 * register, and element addresses skip the length word.  The loop itself is
 * whitelistForIterDynLoop's dynarray_for_loop_counted, run with the length
 * register in its caller frame.
 *
 * TOP-LEVEL:
 *   compile_for_dynarray_frag - stmt_frag for the dynamic-array name loop
 *)
Theory whitelistForIterDynFrag
Ancestors
  loweringPosts stmtSimDefs stmtSimProps whitelistForIterDynLoop
  stmtSimForArrayFrag stmtSimForArrayLoop stmtSimForArrayParts
  stmtLowering exprLowering compileEnv context emitHelper
  exprLoweringProps fragExec loweringSlice localPtrsProps emitHelperProps
  venomInst venomState venomExecSemantics list rich_list finite_map
  arithmetic words stmtSimForParts gasOutcome gasContext stmtSimForRounds
  vyperInterpreter fragGasPath fragGasMode gasSummaryCompose gasSummary
  gasExemptCert vyperState vyperValue stmtSimDeclGas stmtSimDeclCompose
  exprSimMemDefs vyperAST
Libs
  monadsyntax

(* Evaluating a memory-local dynamic array emits no instructions. *)
Theorem compile_array_name_dynamic:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar arr_op sz) ==>
  compile_expr cenv (ArrayT et (Dynamic c))
    (Name (ArrayT et (Dynamic c)) name) st =
  (LocatedValue (ArrayT et (Dynamic c)) (mk_ptr arr_op LocMemory), st)
Proof
  strip_tac >>
  simp[Once compile_expr_def, compile_name_vv_def, comp_return_def,
       expr_type_def]
QED

(* Cut the compiler at the length load, the copy, the body and the back edge. *)
Theorem compile_for_dynarray_stages:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar arr_op arr_sz) /\
  compile_stmt cenv lctx ty
    (For id et (Array (Name (ArrayT et (Dynamic c)) name)) n stmts) st =
    ((),st') ==>
  ?lvo st1 bc entry cond bod incr exit idx offo toto epo sa sb0 sb1 sj.
    emit_op MLOAD [arr_op] st = (lvo,st1) /\
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
        (do invalid <- emit_op GT [lvo; Lit (n2w c)];
            valid <- emit_op ISZERO [invalid];
            emit_void ASSERT [valid]
         od);
        emit_inst JMP [Label cond] [];
        new_block cond;
        done <- emit_op EQ [Var idx; lvo];
        emit_inst JNZ [done; Label exit; Label bod] [];
        new_block bod;
        off <- emit_op MUL [Var idx;
                   Lit (n2w (elem_size_in_location cenv LocMemory et))];
        tot <- emit_op ADD [Lit 32w; off];
        ep <- emit_op ADD [arr_op; tot];
        return (bc,entry,cond,bod,incr,exit,idx,off,tot,ep)
     od) st1 = ((bc,entry,cond,bod,incr,exit,idx,offo,toto,epo),sa) /\
    (case FLOOKUP bc.ce_vars id of
       SOME (MemLoc dst _) =>
         compile_iter_elem_copy cenv epo (Lit (n2w dst))
           (elem_size_in_location cenv LocMemory et) LocMemory F et et
     | SOME (PtrVar ptr_op _) =>
         compile_iter_elem_copy cenv epo ptr_op
           (elem_size_in_location cenv LocMemory et) LocMemory F et et
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
  strip_tac >> drule compile_array_name_dynamic >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, expr_type_def, LET_THM, vv_location_def,
       vv_operand_def, mk_ptr_def, is_slot_addressed_def,
       compile_ptr_load_def, word_scale_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  metis_tac[]
QED

Theorem compile_for_dynarray_prefix:
  cenv.ce_alloca_locals /\
  emit_op MLOAD [arr_op] st = (lvo,st1) /\
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
      (do invalid <- emit_op GT [lvo; Lit (n2w c)];
          valid <- emit_op ISZERO [invalid];
          emit_void ASSERT [valid]
       od);
      emit_inst JMP [Label cond] [];
      new_block cond;
      done <- emit_op EQ [Var idx; lvo];
      emit_inst JNZ [done; Label exit; Label bod] [];
      new_block bod;
      off <- emit_op MUL [Var idx;
                 Lit (n2w (elem_size_in_location cenv LocMemory et))];
      tot <- emit_op ADD [Lit 32w; off];
      ep <- emit_op ADD [arr_op; tot];
      return (bc,entry,cond,bod,incr,exit,idx,off,tot,ep)
   od) st1 = ((bc,entry,cond,bod,incr,exit,idx,offo,toto,epo),sa) ==>
  ?lv p g vld dv ov tot ep.
    lv = STRING #"%" (toString st.cs_next_var) /\
    p = STRING #"%" (toString (st.cs_next_var + 1)) /\
    idx = STRING #"%" (toString (st.cs_next_var + 2)) /\
    g = STRING #"%" (toString (st.cs_next_var + 3)) /\
    vld = STRING #"%" (toString (st.cs_next_var + 4)) /\
    dv = STRING #"%" (toString (st.cs_next_var + 5)) /\
    ov = STRING #"%" (toString (st.cs_next_var + 6)) /\
    tot = STRING #"%" (toString (st.cs_next_var + 7)) /\
    ep = STRING #"%" (toString (st.cs_next_var + 8)) /\
    lvo = Var lv /\ offo = Var ov /\ toto = Var tot /\ epo = Var ep /\
    st1.cs_next_var = st.cs_next_var + 1 /\
    entry = fresh_label_output "iter_entry" st.cs_next_label /\
    cond = fresh_label_output "iter_cond" (st.cs_next_label + 1) /\
    bod = fresh_label_output "iter_body" (st.cs_next_label + 2) /\
    incr = fresh_label_output "iter_incr" (st.cs_next_label + 3) /\
    exit = fresh_label_output "iter_exit" (st.cs_next_label + 4) /\
    declare_local cenv id et st1 =
      (bc, st1 with cs_next_var := st1.cs_next_var + 1) /\
    FLOOKUP bc.ce_vars id =
      SOME (PtrVar (Var p) (type_memory_bytes cenv et)) /\
    sa.cs_current_bb = bod /\
    sa.cs_current_insts =
      [mk_inst (st.cs_next_id + 10) MUL
         [Var idx; Lit (n2w (elem_size_in_location cenv LocMemory et))] [ov];
       mk_inst (st.cs_next_id + 11) ADD [Lit 32w; Var ov] [tot];
       mk_inst (st.cs_next_id + 12) ADD [arr_op; Var tot] [ep]] /\
    sa.cs_next_var = st.cs_next_var + 9 /\
    sa.cs_next_id = st.cs_next_id + 13 /\
    sa.cs_next_label = st.cs_next_label + 5 /\
    sa.cs_blocks =
      [<|bb_label := cond;
         bb_instructions :=
           [mk_inst (st.cs_next_id + 8) EQ [Var idx; Var lv] [dv];
            mk_inst (st.cs_next_id + 9) JNZ [Var dv; Label exit; Label bod] []]|>;
       <|bb_label := entry;
         bb_instructions :=
           [mk_inst (st.cs_next_id + 3) ASSIGN [Lit 0w] [idx];
            mk_inst (st.cs_next_id + 4) GT [Var lv; Lit (n2w c)] [g];
            mk_inst (st.cs_next_id + 5) ISZERO [Var g] [vld];
            mk_inst (st.cs_next_id + 6) ASSERT [Var vld] [];
            mk_inst (st.cs_next_id + 7) JMP [Label cond] []]|>;
       <|bb_label := st.cs_current_bb;
         bb_instructions := st.cs_current_insts ++
           [mk_inst st.cs_next_id MLOAD [arr_op] [lv];
            mk_inst (st.cs_next_id + 1) ALLOCA
              [Lit (n2w (type_memory_bytes cenv et))] [p];
            mk_inst (st.cs_next_id + 2) JMP [Label entry] []]|>] ++ st.cs_blocks
Proof
  strip_tac >>
  Cases_on `declare_local cenv id et st1` >>
  rename1 `declare_local cenv id et st1 = (bc0,st2)` >>
  drule_all declare_local_ptr >> strip_tac >>
  qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
  simp[emit_op_def, fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `_ = ((bc,entry,cond,bod,incr,exit,idx,offo,toto,epo),sa)` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[emit_local_alloca_def, fresh_label_def, emit_inst_def, emit_op_def,
       emit_void_def, fresh_id_def, emit_def, new_block_def, fresh_var_def,
       comp_get_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       LET_THM] >> strip_tac >> gvs[] >>
  simp[GSYM arithmeticTheory.ADD_ASSOC] >> metis_tac[]
QED

(* A block emitted between two states is found by its label; the emitted
   blocks are read off the state equation, so simp never sees the context. *)
(* The register and label names the prefix lemma fixes (lv = STRING ..). *)
fun name_eq t =
  is_eq t andalso is_var (lhs t) andalso
  (can (match_term ``STRING c s``) (rhs t) orelse
   can (match_term ``fresh_label_output l n``) (rhs t))

(* An equation between two states' finished blocks (sj.cs_blocks =
   sb1.cs_blocks when the body's block was left open). *)
fun blocks_eq t =
  is_eq t andalso
  can (match_term ``(x:compile_state).cs_blocks``) (lhs t) andalso
  can (match_term ``(x:compile_state).cs_blocks``) (rhs t)

fun emitted_lookup_tac pat a b =
  let
    fun front t =
      if listSyntax.is_append t then fst (listSyntax.dest_append t)
      else
        let
          fun strip t = if listSyntax.is_cons t then
                          let val (h, tl) = listSyntax.dest_cons t
                          in h :: strip tl end
                        else []
          val hs = strip t
        in listSyntax.mk_list (hs, type_of (hd hs)) end
  in
    irule array_emitted_block_lookup >>
    conj_tac >- rewrite_tac [venomInstTheory.basic_block_accfupds, combinTheory.K_THM] >>
    qpat_assum pat (fn th =>
      exists_tac (front (rhs (concl th))) >> qexistsl_tac [a, b] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      (fn (asl, g) =>
        rewrite_tac (th :: map ASSUME (filter (fn t => name_eq t orelse blocks_eq t) asl) @
                     [listTheory.MEM, listTheory.APPEND]) (asl, g)))
  end


(* Static producer, as compile_for_array_parts: the body stays opaque. *)
Theorem compile_for_dynarray_parts:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar arr_op arr_sz) /\
  compile_stmt cenv lctx ty
    (For id et (Array (Name (ArrayT et (Dynamic c)) name)) n stmts) st =
    ((),st') /\ cenv.ce_alloca_locals /\ fn_has_code st st' func /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
                cs_extends sa sb) ==>
  ?st1 bc lv p idx g vld dv ov tot ep nv entry cond bod incr exit
   sa sb0 sb1 sj.
    lv = STRING #"%" (toString st.cs_next_var) /\
    p = STRING #"%" (toString (st.cs_next_var + 1)) /\
    idx = STRING #"%" (toString (st.cs_next_var + 2)) /\
    g = STRING #"%" (toString (st.cs_next_var + 3)) /\
    vld = STRING #"%" (toString (st.cs_next_var + 4)) /\
    dv = STRING #"%" (toString (st.cs_next_var + 5)) /\
    ov = STRING #"%" (toString (st.cs_next_var + 6)) /\
    tot = STRING #"%" (toString (st.cs_next_var + 7)) /\
    ep = STRING #"%" (toString (st.cs_next_var + 8)) /\
    nv = STRING #"%" (toString sj.cs_next_var) /\
    st1.cs_next_var = st.cs_next_var + 1 /\
    declare_local cenv id et st1 =
      (bc, st1 with cs_next_var := st1.cs_next_var + 1) /\
    FLOOKUP bc.ce_vars id =
      SOME (PtrVar (Var p) (type_memory_bytes cenv et)) /\
    sa.cs_current_bb = bod /\
    sa.cs_current_insts =
      [mk_inst (st.cs_next_id + 10) MUL
         [Var idx; Lit (n2w (elem_size_in_location cenv LocMemory et))] [ov];
       mk_inst (st.cs_next_id + 11) ADD [Lit 32w; Var ov] [tot];
       mk_inst (st.cs_next_id + 12) ADD [arr_op; Var tot] [ep]] /\
    sa.cs_next_var = st.cs_next_var + 9 /\
    compile_iter_elem_copy cenv (Var ep) (Var p)
      (elem_size_in_location cenv LocMemory et) LocMemory F et et sa = ((),sb0) /\
    sb0.cs_current_bb = bod /\ same_blocks sa sb0 /\
    sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0 /\
    ~block_is_terminated sb0 /\ sa.cs_next_var <= sb0.cs_next_var /\
    compile_stmts bc (InLoop exit incr) ty stmts sb0 = ((),sb1) /\
    emit_jmp_if_not_terminated incr sb1 = ((),sj) /\
    sj.cs_next_var = sb1.cs_next_var /\
    (~block_is_terminated sb1 ==>
      sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
      sj.cs_current_insts = sb1.cs_current_insts ++
        [mk_inst sb1.cs_next_id JMP [Label incr] []]) /\
    cs_extends st sa /\ cs_extends sa sb0 /\ cs_extends sb0 sb1 /\
    cs_extends sb1 sj /\ cs_extends sj st' /\
    fn_has_code st sa func /\ fn_has_code sa sb0 func /\
    fn_has_code sb0 sb1 func /\ fn_has_code sb1 sj func /\
    fn_has_code sj st' func /\
    lookup_block st.cs_current_bb func.fn_blocks =
      SOME <|bb_label := st.cs_current_bb;
             bb_instructions := st.cs_current_insts ++
               [mk_inst st.cs_next_id MLOAD [arr_op] [lv];
                mk_inst (st.cs_next_id + 1) ALLOCA
                  [Lit (n2w (type_memory_bytes cenv et))] [p];
                mk_inst (st.cs_next_id + 2) JMP [Label entry] []]|> /\
    lookup_block entry func.fn_blocks =
      SOME <|bb_label := entry; bb_instructions :=
        [mk_inst (st.cs_next_id + 3) ASSIGN [Lit 0w] [idx];
         mk_inst (st.cs_next_id + 4) GT [Var lv; Lit (n2w c)] [g];
         mk_inst (st.cs_next_id + 5) ISZERO [Var g] [vld];
         mk_inst (st.cs_next_id + 6) ASSERT [Var vld] [];
         mk_inst (st.cs_next_id + 7) JMP [Label cond] []]|> /\
    lookup_block cond func.fn_blocks =
      SOME <|bb_label := cond; bb_instructions :=
        [mk_inst (st.cs_next_id + 8) EQ [Var idx; Var lv] [dv];
         mk_inst (st.cs_next_id + 9) JNZ [Var dv; Label exit; Label bod] []]|> /\
    lookup_block incr func.fn_blocks =
      SOME <|bb_label := incr; bb_instructions :=
        [mk_inst sj.cs_next_id ADD [Var idx; Lit 1w] [nv];
         mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [idx];
         mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|> /\
    st'.cs_current_bb = exit /\ st'.cs_current_insts = []
Proof
  strip_tac >> drule_all compile_for_dynarray_stages >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` kall_tac >>
  drule_all compile_for_dynarray_prefix >> strip_tac >>
  dxrule compile_for_array_suffix >> strip_tac >>
  `cs_extends st sa` by (irule array_prefix_extends >> simp[] >> metis_tac[]) >>
  `~block_is_terminated sa` by
    simp[block_is_terminated_def, mk_inst_def, is_terminator_def] >>
  qpat_x_assum `_ sa = ((),sb0)` mp_tac >>
  simp[] >> strip_tac >>
  drule_all array_iter_copy_static >> strip_tac >>
  drule array_body_backedge >> strip_tac >>
  `cs_extends sb0 sb1` by metis_tac[] >>
  drule_all array_stages_code >> strip_tac >>
  qexistsl_tac [`st1`, `bc`, `entry`, `cond`, `incr`, `sa`, `sb0`, `sb1`, `sj`] >>
  fs[] >>
  rpt conj_tac
  >- fs[same_blocks_def]
  >- emitted_lookup_tac `sa.cs_blocks = _` `st` `sa`
  >- emitted_lookup_tac `sa.cs_blocks = _` `st` `sa`
  >- emitted_lookup_tac `sa.cs_blocks = _` `st` `sa`
  >> emitted_lookup_tac `st'.cs_blocks = _` `sj` `st'`
QED

Theorem dynarray_register_frame[local]:
  local_ptrs_reserved cenv st /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar arr_op arr_sz) /\
  st.cs_next_var + 9 <= sj.cs_next_var /\
  lv = STRING #"%" (toString st.cs_next_var) /\
  p = STRING #"%" (toString (st.cs_next_var + 1)) /\
  idx = STRING #"%" (toString (st.cs_next_var + 2)) /\
  g = STRING #"%" (toString (st.cs_next_var + 3)) /\
  vld = STRING #"%" (toString (st.cs_next_var + 4)) /\
  dv = STRING #"%" (toString (st.cs_next_var + 5)) /\
  ov = STRING #"%" (toString (st.cs_next_var + 6)) /\
  tot = STRING #"%" (toString (st.cs_next_var + 7)) /\
  ep = STRING #"%" (toString (st.cs_next_var + 8)) /\
  nv = STRING #"%" (toString sj.cs_next_var) ==>
  ALL_DISTINCT [idx; dv; ov; tot; ep; nv; p; lv; g; vld] /\
  (!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs dv /\
         not_local_ptr cenv scs ov /\ not_local_ptr cenv scs tot /\
         not_local_ptr cenv scs ep /\ not_local_ptr cenv scs nv /\
         not_local_ptr cenv scs lv /\ not_local_ptr cenv scs g /\
         not_local_ptr cenv scs vld) /\
  (!x. not_fresh_at st x ==>
     ~MEM x [idx; dv; ov; tot; ep; nv; p; lv; g; vld]) /\
  (!x. arr_op = Var x ==> not_fresh_at st x)
Proof
  strip_tac >>
  `!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs dv /\
         not_local_ptr cenv scs ov /\ not_local_ptr cenv scs tot /\
         not_local_ptr cenv scs ep /\ not_local_ptr cenv scs nv /\
         not_local_ptr cenv scs lv /\ not_local_ptr cenv scs g /\
         not_local_ptr cenv scs vld` by
    (gen_tac >> rpt conj_tac >> simp[] >>
     irule local_ptrs_reserved_fresh >> qexists_tac `st` >> simp[]) >>
  `!x. arr_op = Var x ==> not_fresh_at st x` by
    (rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  simp[] >> simp[not_fresh_at_def] >> rpt strip_tac >> gvs[]
QED

(* Everything the loop and its entry need from the compiled code. *)
Theorem compile_for_dynarray_code_ready:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar arr_op arr_sz) /\
  compile_stmt cenv lctx ty
    (For id et (Array (Name (ArrayT et (Dynamic c)) name)) n stmts) st =
    ((),st') /\ cenv.ce_alloca_locals /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv st /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) ==>
  ?st1 bc lv p idx g vld dv ov tot ep nv entry cond bod incr exit
   sa sb0 sb1 sj ainst.
    dynarray_for_code func cenv bc ty stmts id et tv
      (type_memory_bytes cenv et) arr_op p (type_memory_bytes cenv et)
      ainst idx dv ov tot ep nv lv cond exit bod incr
      (st.cs_next_id + 8) (st.cs_next_id + 9) (st.cs_next_id + 10)
      (st.cs_next_id + 11) (st.cs_next_id + 12)
      sj.cs_next_id (sj.cs_next_id + 1) (sj.cs_next_id + 2) sa sb0 sb1 sj /\
    ainst = mk_inst (st.cs_next_id + 1) ALLOCA
      [Lit (n2w (type_memory_bytes cenv et))] [p] /\
    lookup_block st.cs_current_bb func.fn_blocks =
      SOME <|bb_label := st.cs_current_bb;
             bb_instructions := st.cs_current_insts ++
               [mk_inst st.cs_next_id MLOAD [arr_op] [lv]; ainst;
                mk_inst (st.cs_next_id + 2) JMP [Label entry] []]|> /\
    lookup_block entry func.fn_blocks =
      SOME <|bb_label := entry; bb_instructions :=
        [mk_inst (st.cs_next_id + 3) ASSIGN [Lit 0w] [idx];
         mk_inst (st.cs_next_id + 4) GT [Var lv; Lit (n2w c)] [g];
         mk_inst (st.cs_next_id + 5) ISZERO [Var g] [vld];
         mk_inst (st.cs_next_id + 6) ASSERT [Var vld] [];
         mk_inst (st.cs_next_id + 7) JMP [Label cond] []]|> /\
    st'.cs_current_bb = exit /\ st'.cs_current_insts = [] /\
    (?sd. declare_local cenv id et st1 = (bc,sd)) /\
    ALL_DISTINCT [lv; p; idx; g; vld] /\
    (!scs. not_local_ptr cenv scs lv /\ not_local_ptr cenv scs g /\
           not_local_ptr cenv scs vld /\ not_local_ptr cenv scs idx) /\
    (!x. arr_op = Var x ==> ~MEM x [lv; p; idx; g; vld]) /\
    (!x. not_fresh_at st x ==> ~MEM x [lv; p; idx; g; vld]) /\
    (!x. not_fresh_at st x ==> not_fresh_at st1 x) /\
    (!x. not_fresh_at st1 x ==>
      not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> tot /\ x <> ep) /\
    (!x. not_fresh_at st1 x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
    not_fresh_at st1 lv /\
    not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
    (!x. arr_op = Var x ==> not_fresh_at sb0 x)
Proof
  strip_tac >>
  `!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
                cs_extends sa sb` by metis_tac[] >>
  drule_all compile_for_dynarray_parts >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `st.cs_next_var + 9 <= sj.cs_next_var` by
    (qpat_x_assum `!c lc sa sb. _ ==> _ /\ _` drule >> simp[]) >>
  drule_all dynarray_register_frame >> strip_tac >>
  `local_ptrs_reserved cenv st1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[]) >>
  `st1.cs_next_var + 1 <= sa.cs_next_var` by simp[] >>
  drule_all array_declared_reserved >> strip_tac >>
  `MEM (mk_inst (st.cs_next_id + 1) ALLOCA
          [Lit (n2w (type_memory_bytes cenv et))] [p]) (fn_insts func)` by
    (irule lookup_block_fn_insts >>
     qpat_assum `lookup_block st.cs_current_bb _ = _` (irule_at (Pos hd)) >>
     simp[]) >>
  qexistsl_tac [`st1`, `bc`, `lv`, `p`, `idx`, `g`, `vld`, `dv`, `ov`, `tot`,
    `ep`, `nv`, `entry`, `cond`, `bod`, `incr`, `exit`, `sa`, `sb0`, `sb1`,
    `sj`] >>
  simp[] >> rpt conj_tac
  >- (`elem_size_in_location cenv LocMemory et = type_memory_size tv` by
        simp[elem_size_in_location_def, is_slot_addressed_def] >>
      simp[dynarray_for_code_def, mk_inst_def] >> gvs[ALL_DISTINCT] >>
      qpat_x_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      qpat_x_assum `MEM _ (fn_insts func)` mp_tac >>
      simp[mk_inst_def] >> rpt strip_tac >> simp[not_fresh_at_def] >>
      rpt strip_tac >> qpat_x_assum `!x. arr_op = Var x ==> _` drule >>
      rewrite_tac[not_fresh_at_def] >>
      disch_then (qspec_then `n'` mp_tac) >> simp[])
  >- gvs[ALL_DISTINCT]
  >- (rpt strip_tac >> gvs[] >> fs[not_fresh_at_def])
  >- (rpt strip_tac >> qpat_x_assum `not_fresh_at st _` mp_tac >>
      simp[not_fresh_at_def])
  >- simp[not_fresh_at_def]
  >- (simp[not_fresh_at_def] >> rpt strip_tac >> gvs[])
  >- (simp[not_fresh_at_def] >> rpt strip_tac >> gvs[])
  >- simp[not_fresh_at_def]
  >- simp[not_fresh_at_def]
  >> rpt strip_tac >>
  qpat_x_assum `!x. arr_op = Var x ==> not_fresh_at st x` drule >>
  rewrite_tac[not_fresh_at_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> simp[]
QED

(* The entry block: index zero, then the capacity check passes. *)
Theorem dynarray_entry_block_run[local]:
  lookup_var lv s = SOME (n2w L) /\ L <= c /\ c < dimword (:256) /\
  ALL_DISTINCT [lv; idx; g; vld] ==>
  run_inst_seq
    [mk_inst i1 ASSIGN [Lit 0w] [idx];
     mk_inst i2 GT [Var lv; Lit (n2w c)] [g];
     mk_inst i3 ISZERO [Var g] [vld];
     mk_inst i4 ASSERT [Var vld] []] s =
  OK (update_var vld 1w (update_var g 0w (update_var idx 0w s)))
Proof
  strip_tac >> fs[ALL_DISTINCT] >>
  `step_inst_base (mk_inst i1 ASSIGN [Lit 0w] [idx]) s =
   OK (update_var idx 0w s)` by
    simp[mk_inst_def, step_inst_base_def, eval_operand_def] >>
  qabbrev_tac `s1 = update_var idx 0w s` >>
  `L < dimword (:256)` by decide_tac >>
  `bool_to_word (w2n (n2w L : bytes32) > w2n (n2w c : bytes32)) = 0w` by
    simp[bool_to_word_def] >>
  `step_inst_base (mk_inst i2 GT [Var lv; Lit (n2w c)] [g]) s1 =
   OK (update_var g 0w s1)` by
    (qpat_x_assum `bool_to_word _ = 0w` (SUBST1_TAC o SYM) >>
     irule step_GT >>
     simp[Abbr `s1`, eval_operand_def, lookup_var_update_var]) >>
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

(* Load the length, allocate the loop variable, run the entry block. *)
Theorem dynarray_loop_initialize:
  ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  MEM ainst (fn_insts func) /\ fn_inst_ids_distinct func /\
  ainst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [mk_inst mi MLOAD [saved_base] [lv]; ainst;
              mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst e1 ASSIGN [Lit 0w] [idx];
       mk_inst e2 GT [Var lv; Lit (n2w c)] [g];
       mk_inst e3 ISZERO [Var g] [vld];
       mk_inst e4 ASSERT [Var vld] [];
       mk_inst e5 JMP [Label cond] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  stmt_state_rel ctx func cenv cx es s0 /\ P es /\
  lookup_scopes id es.scopes = NONE /\
  eval_operand saved_base s0 = SOME array_base /\
  mload (w2n array_base) s0 = n2w (LENGTH vs) /\
  LENGTH vs <= c /\ c < dimword (:256) /\
  ret_pc_ok cenv st s0 /\
  ALL_DISTINCT [lv; p; idx; g; vld] /\
  not_local_ptr cenv es.scopes lv /\ not_local_ptr cenv es.scopes p /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes g /\
  not_local_ptr cenv es.scopes vld /\
  (!x. saved_base = Var x ==> ~MEM x [lv; p; idx; g; vld]) /\
  (!x. not_fresh_at st x ==> ~MEM x [lv; p; idx; g; vld]) ==>
  ?dst cc.
    array_loop_inv ctx func cenv cx P vs id idx saved_base array_base p dst sz
      ainst cond st 0 es cc /\
    lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
    array_caller_frame st s0 cc /\
    gas_marked_path F ctx func s0 0 (OK cc)
Proof
  strip_tac >> fs[ALL_DISTINCT] >>
  qabbrev_tac `sl = update_var lv (n2w (LENGTH vs)) s0` >>
  `step_inst_base (mk_inst mi MLOAD [saved_base] [lv]) s0 = OK sl` by
    (simp[Abbr `sl`] >> qpat_x_assum `mload _ _ = _` (SUBST1_TAC o SYM) >>
     irule step_MLOAD >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es sl` by
    (simp[Abbr `sl`] >> irule stmt_state_rel_update_var >> simp[]) >>
  `eval_operand saved_base sl = SOME array_base` by
    (Cases_on `saved_base` >>
     gvs[Abbr `sl`, eval_operand_def, lookup_var_update_var]) >>
  `ret_pc_ok cenv st sl` by simp[Abbr `sl`, array_ret_pc_update] >>
  `!x. saved_base = Var x ==> x <> p` by metis_tac[] >>
  drule_all array_allocate_ready >> strip_tac >>
  rename1 `exec_alloca ainst sl (n2w sz : bytes32) = OK s1` >>
  rename1 `lookup_var p s1 = SOME dst` >>
  drule_all array_alloca_frame >> strip_tac >>
  `step_inst_base ainst sl = OK s1` by
    simp[step_inst_base_def, eval_operand_def] >>
  `gas_marked_path F ctx func s0 0 (OK (jump_to entry s1))` by
    (qspecl_then [`[mk_inst mi MLOAD [saved_base] [lv]; ainst]`, `s0`, `s1`,
       `ctx`, `func`,
       `<|bb_label := lbl; bb_instructions :=
          pre ++ [mk_inst mi MLOAD [saved_base] [lv]; ainst;
                  mk_inst j JMP [Label entry] []]|>`, `j`, `entry`]
       mp_tac inst_seq_jump_zero_path >>
     simp[DROP_LENGTH_APPEND, run_inst_seq_def, is_terminator_def]) >>
  `lookup_var lv s1 = SOME (n2w (LENGTH vs))` by
    (`lookup_var lv s1 = lookup_var lv sl` by metis_tac[] >>
     simp[Abbr `sl`, lookup_var_update_var]) >>
  `~s1.vs_halted` by fs[Abbr `sl`, update_var_def] >>
  qabbrev_tac `e0 = jump_to entry s1` >>
  `lookup_var lv e0 = SOME (n2w (LENGTH vs)) /\ e0.vs_current_bb = entry /\
   e0.vs_inst_idx = 0 /\ ~e0.vs_halted` by
    fs[Abbr `e0`, jump_to_def, lookup_var_def] >>
  `run_inst_seq
     [mk_inst e1 ASSIGN [Lit 0w] [idx];
      mk_inst e2 GT [Var lv; Lit (n2w c)] [g];
      mk_inst e3 ISZERO [Var g] [vld];
      mk_inst e4 ASSERT [Var vld] []] e0 =
   OK (update_var vld 1w (update_var g 0w (update_var idx 0w e0)))` by
    (irule dynarray_entry_block_run >> simp[ALL_DISTINCT] >>
     qexists_tac `LENGTH vs` >> simp[]) >>
  qabbrev_tac `e4s = update_var vld 1w (update_var g 0w (update_var idx 0w e0))` >>
  `gas_marked_path F ctx func e0 0 (OK (jump_to cond e4s))` by
    (qspecl_then [`[mk_inst e1 ASSIGN [Lit 0w] [idx];
                    mk_inst e2 GT [Var lv; Lit (n2w c)] [g];
                    mk_inst e3 ISZERO [Var g] [vld];
                    mk_inst e4 ASSERT [Var vld] []]`, `e0`, `e4s`, `ctx`, `func`,
       `<|bb_label := entry; bb_instructions :=
          [mk_inst e1 ASSIGN [Lit 0w] [idx];
           mk_inst e2 GT [Var lv; Lit (n2w c)] [g];
           mk_inst e3 ISZERO [Var g] [vld];
           mk_inst e4 ASSERT [Var vld] [];
           mk_inst e5 JMP [Label cond] []]|>`, `e5`, `cond`]
       mp_tac inst_seq_jump_zero_path >>
     simp[is_terminator_def]) >>
  qabbrev_tac `cc = jump_to cond e4s` >>
  `!x. x <> idx /\ x <> g /\ x <> vld ==> lookup_var x cc = lookup_var x s1` by
    simp[Abbr `cc`, Abbr `e4s`, Abbr `e0`, jump_to_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `cc.vs_allocas = s1.vs_allocas /\ cc.vs_current_bb = cond /\
   cc.vs_inst_idx = 0 /\ ~cc.vs_halted` by
    simp[Abbr `cc`, Abbr `e4s`, Abbr `e0`, jump_to_def, update_var_def] >>
  `stmt_state_rel ctx func cenv cx es cc` by
    (simp[Abbr `cc`, stmt_state_rel_jump_to, Abbr `e4s`] >>
     rpt (irule stmt_state_rel_update_var >> simp[]) >>
     simp[Abbr `e0`, stmt_state_rel_jump_to]) >>
  `lookup_var idx cc = SOME (n2w 0)` by
    simp[Abbr `cc`, Abbr `e4s`, jump_to_def, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE] >>
  `eval_operand saved_base cc = SOME array_base` by
    (Cases_on `saved_base` >>
     fs[eval_operand_def, Abbr `cc`, Abbr `e4s`, Abbr `e0`, jump_to_def,
        update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `lookup_var p cc = SOME dst` by metis_tac[] >>
  `ret_pc_ok cenv st cc` by
    simp[Abbr `cc`, ret_pc_ok_jump_to, Abbr `e4s`, array_ret_pc_update,
         Abbr `e0`] >>
  qexistsl_tac [`dst`, `cc`] >>
  rpt conj_tac
  >- simp[array_loop_inv_def]
  >- metis_tac[]
  >- (simp[array_caller_frame_def] >> rpt strip_tac
      >- (`lookup_var x cc = lookup_var x s1` by metis_tac[] >>
          `lookup_var x s1 = lookup_var x sl` by metis_tac[] >>
          `x <> lv` by metis_tac[] >>
          gvs[Abbr `sl`, lookup_var_update_var]) >>
      `FLOOKUP sl.vs_allocas aid = SOME b` by
        simp[Abbr `sl`, update_var_def] >>
      metis_tac[]) >>
  drule_all gas_marked_path_then >> simp[]
QED

(* The source loads the iterable and checks its length before the loop. *)
Theorem for_source_prefix_bounded:
  (!gs. eval_iterator cx it (es with gas_obs := gs) =
        (INL vs, es with gas_obs := gs)) /\
  LENGTH vs <= n /\ evaluate_type (get_tenv cx) et = SOME tv /\
  ~s.vs_halted /\
  gas_outcome F tops (ctx,func) (eval_for cx tv id stmts vs)
    (es with gas_obs := [],s) Q R ==>
  gas_outcome F tops (ctx,func) (eval_stmt cx (For id et it n stmts)) (es,s) Q R
Proof
  strip_tac >>
  `!msg. assert T msg = return ()` by
    simp[FUN_EQ_THM, vyperStateTheory.assert_def, return_def] >>
  simp[Once evaluate_def, lift_option_type_def, lift_option_def,
       bind_return] >>
  irule array_values_prefix_outcome >> simp[] >>
  simp[compatible_bound_def, check_def, vyperStateTheory.assert_def,
    ignore_bind_def, bind_return]
QED

Theorem dynarray_frame_weaken[local]:
  (!x. not_fresh_at st x ==> not_fresh_at st1 x) /\
  array_caller_frame st s0 cc /\ array_caller_frame st1 cc t ==>
  array_caller_frame st s0 t
Proof
  simp[array_caller_frame_def] >> metis_tac[]
QED

Theorem dynarray_public_entry_ready[local]:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var arr_ptr) arr_sz) /\
  compile_stmt cenv lctx ty
    (For id et (Array (Name (ArrayT et (Dynamic c)) name)) n stmts) st =
    ((),st') /\ cenv.ce_alloca_locals /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv st /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) /\
  LENGTH vs <= c /\ c < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s0 /\ P es /\
  lookup_scopes id es.scopes = NONE /\ name <> id /\
  ret_pc_ok cenv st s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = st.cs_current_bb /\
  s0.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!ei t. P ei /\ stmt_state_rel ctx func cenv cx ei t ==>
    ?addr. eval_operand (Var arr_ptr) t = SOME addr /\
      mload (w2n addr) t = n2w (LENGTH vs) /\
      (!k. k < LENGTH vs ==>
        val_in_memory tv (EL k vs)
          (w2n addr + 32 + k * type_memory_size tv) t.vs_memory /\
        w2n addr + 32 + k * type_memory_size tv < dimword (:256))) ==>
  ?st1 bc lv p idx dv ov tot ep nv cond bod incr exit sa sb0 sb1 sj ainst sd
   base dst cc.
    dynarray_for_code func cenv bc ty stmts id et tv
      (type_memory_bytes cenv et) (Var arr_ptr) p (type_memory_bytes cenv et)
      ainst idx dv ov tot ep nv lv cond exit bod incr
      (st.cs_next_id + 8) (st.cs_next_id + 9) (st.cs_next_id + 10)
      (st.cs_next_id + 11) (st.cs_next_id + 12)
      sj.cs_next_id (sj.cs_next_id + 1) (sj.cs_next_id + 2) sa sb0 sb1 sj /\
    st'.cs_current_bb = exit /\ st'.cs_current_insts = [] /\
    declare_local cenv id et st1 = (bc,sd) /\
    (!x. not_fresh_at st x ==> not_fresh_at st1 x) /\
    (!x. not_fresh_at st1 x ==>
      not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> tot /\ x <> ep) /\
    (!x. not_fresh_at st1 x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
    not_fresh_at st1 lv /\
    not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
    (!x. Var arr_ptr = Var x ==> not_fresh_at sb0 x) /\
    (!k. k < LENGTH vs ==>
      w2n base + 32 + k * type_memory_bytes cenv et < dimword (:256)) /\
    array_loop_inv ctx func cenv cx P vs id idx (Var arr_ptr) base p dst
      (type_memory_bytes cenv et) ainst cond st 0 es cc /\
    lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
    array_caller_frame st s0 cc /\ gas_marked_path F ctx func s0 0 (OK cc)
Proof
  strip_tac >> drule_all compile_for_dynarray_code_ready >> strip_tac >>
  qpat_assum `!ei t. _` drule_all >> strip_tac >>
  `type_memory_bytes cenv et < dimword (:256)` by simp[] >>
  `ainst.inst_operands = [Lit (n2w (type_memory_bytes cenv et))] /\
   ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p]` by
    simp[mk_inst_def] >>
  `MEM ainst (fn_insts func)` by
    (irule lookup_block_fn_insts >>
     qpat_assum `lookup_block st.cs_current_bb _ = _` (irule_at (Pos hd)) >>
     simp[]) >>
  `not_local_ptr cenv es.scopes p` by
    (`bc.ce_imm_alloca = cenv.ce_imm_alloca /\ local_ptrs_reserved bc sa /\
      FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv et)) /\
      (!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name)` by
       fs[dynarray_for_code_def, compile_env_component_equality] >>
     drule_all array_allocation_safe >> simp[]) >>
  `?dst cc. array_loop_inv ctx func cenv cx P vs id idx (Var arr_ptr) addr p dst
      (type_memory_bytes cenv et) ainst cond st 0 es cc /\
      lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
      array_caller_frame st s0 cc /\ gas_marked_path F ctx func s0 0 (OK cc)` by
    (irule dynarray_loop_initialize >> simp[] >>
     qpat_assum `lookup_block entry _ = _` (irule_at Any) >> simp[] >>
     qexistsl_tac [`st.cs_next_id`, `st.cs_next_id + 2`] >>
     simp[] >> fs[ALL_DISTINCT] >> metis_tac[]) >>
  qexistsl_tac [`st1`, `bc`, `lv`, `p`, `idx`, `dv`, `ov`, `tot`, `ep`, `nv`,
    `cond`, `bod`, `incr`, `exit`, `sa`, `sb0`, `sb1`, `sj`, `ainst`, `sd`,
    `addr`, `dst`, `cc`] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!k. k < LENGTH vs ==> val_in_memory _ _ _ _ /\ _` drule >>
  simp[]
QED

Theorem dynarray_code_loop_counted[local]:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond exit bod incr
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  cs_extends sb0 sb1 /\ LENGTH vs < dimword (:256) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  (!x. not_fresh_at st x ==> not_fresh_at st1 x) /\
  (!x. not_fresh_at st1 x ==>
    not_fresh_at sa x /\ x <> dv /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x. not_fresh_at st1 x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv) /\
  not_fresh_at st1 lv /\ lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
  not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. saved_base = Var x ==> not_fresh_at sb0 x) /\
  (!l. saved_base <> Label l) /\ ret_pc_ok cenv st s0 /\
  (!k. k < LENGTH vs ==> value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)) /\
  (!ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s ==>
    ?addr. eval_operand saved_base s = SOME addr /\
      (!k. k < LENGTH vs ==>
        val_in_memory tv (EL k vs) (w2n addr + 32 + k * stride) s.vs_memory)) /\
  (!k. k < LENGTH vs ==> w2n arr_base + 32 + k * stride < dimword (:256)) /\
  (!ei k. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag ctx func cx (InLoop exit incr) RetQ bc
      (stmts_env bc (InLoop exit incr) ty stmts) (eval_stmts cx stmts)
      (ei with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes)) /\
  (!ei k gs r es2. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
      gas_obs := gs|>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond st 0 es cc /\ array_caller_frame st s0 cc /\
  gas_admissible (eval_for cx tv id stmts vs) (stmt_res_ok lctx) es ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_for cx tv id stmts vs) (es,cc)
    (\res ee t. res = INL () /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
      ~t.vs_halted /\ stmt_state_rel ctx func cenv cx ee t /\
      array_caller_frame st s0 t)
    (\res ee r. ?ex. res = INR ex /\
      !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)
Proof
  strip_tac >>
  `bc.ce_return_pc = cenv.ce_return_pc` by
    fs[dynarray_for_code_def, compile_env_component_equality] >>
  `(!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) ==>
      not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
   (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
      not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
   (!s. ret_pc_ok cenv st s ==> ret_pc_ok bc sb0 s)` by
    (fs[ret_pc_ok_def] >> metis_tac[]) >>
  `?bb. lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX sb0.cs_current_insts bb.bb_instructions` by
    (irule fn_has_code_start >> qexists_tac `sb1` >> fs[dynarray_for_code_def]) >>
  `!j ei s. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst bod st j ei s /\ j < LENGTH vs ==>
      val_in_memory tv (EL j vs) (w2n arr_base + 32 + j * stride) s.vs_memory /\
      ret_pc_ok bc sb0 s` by
    (rpt gen_tac >> simp[array_loop_inv_def] >> strip_tac >>
     qpat_assum `!ei s. P ei /\ _ ==> _` (qspecl_then [`ei`, `s`] mp_tac) >>
     simp[] >> strip_tac >>
     qpat_x_assum `!k. _ ==> val_in_memory _ _ _ _` (qspec_then `j` mp_tac) >>
     gvs[]) >>
  `!ei j. P ei /\ lookup_scopes id ei.scopes = NONE /\ j < LENGTH vs ==>
    w2n arr_base + 32 + j * stride < dimword (:256) /\
    not_local_ptr bc (FEMPTY :: ei.scopes) p /\
    stmt_frag ctx func cx (InLoop exit incr) RetQ bc
      (stmts_env bc (InLoop exit incr) ty stmts) (eval_stmts cx stmts)
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
        gas_obs := []|>) /\
    (!gs r es2. eval_stmts cx stmts
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
        gas_obs := gs|>) = (r,es2) ==>
      stmt_res_ok (InLoop exit incr) r /\
      ?sc rest. es2.scopes = sc :: rest /\
        (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
        ((r = INL () \/ r = INR ContinueException) ==>
          P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE))` by
    suspend "callback" >>
  `array_caller_frame st1 cc cc` by simp[] >>
  drule_all (SRULE [DROP_0] (Q.INST [`k` |-> `0`] dynarray_for_loop_counted)) >>
  strip_tac >>
  irule gas_outcome_post_mono >>
  qpat_assum `gas_outcome _ _ _ _ _ _ _` (irule_at (Pos last)) >>
  simp[] >> rpt strip_tac >> irule dynarray_frame_weaken >> metis_tac[]
QED

Resume dynarray_code_loop_counted[callback]:
  rpt strip_tac
  >- metis_tac[]
  >- (irule array_unbound_body_ptr >> fs[dynarray_for_code_def] >> metis_tac[])
  >- (qpat_assum `!ei k. _` drule_all >>
      disch_then (qspec_then `[]` mp_tac o MATCH_MP stmt_frag_start_gas_obs) >>
      simp[]) >>
  qpat_assum `!ei k gs r es2. _` drule_all >> simp[]
QED
Finalise dynarray_code_loop_counted

Theorem compile_for_dynarray_frag_zero[local]:
  !ctx func cx cenv lctx RetQ ty id et c n name arr_ptr arr_sz stmts tv vs es P.
  (!gs. eval_iterator cx (Array (Name (ArrayT et (Dynamic c)) name))
          (es with gas_obs := gs) = (INL vs, es with gas_obs := gs)) /\
  LENGTH vs <= c /\ c <= n /\ c < dimword (:256) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) /\ cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var arr_ptr) arr_sz) /\
  name <> id /\ lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  P (es with gas_obs := []) /\
  (!k. k < LENGTH vs ==> value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)) /\
  (!ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s ==>
    ?base. eval_operand (Var arr_ptr) s = SOME base /\
      mload (w2n base) s = n2w (LENGTH vs) /\
      (!k. k < LENGTH vs ==>
        val_in_memory tv (EL k vs)
          (w2n base + 32 + k * type_memory_size tv) s.vs_memory /\
        w2n base + 32 + k * type_memory_size tv < dimword (:256))) /\
  (!st0 bc sd ex inc ei k.
    declare_local cenv id et st0 = (bc,sd) /\
    P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
          :: ei.scopes)) /\
  (!ei k gs r es2.
    P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with <| scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
        :: ei.scopes; gas_obs := gs |>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty
      (For id et (Array (Name (ArrayT et (Dynamic c)) name)) n stmts))
    (eval_stmt cx (For id et (Array (Name (ArrayT et (Dynamic c)) name)) n stmts)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >>
  map_every qx_gen_tac [`st`, `st'`, `s0`, `cenv'`] >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def, NoAsms] >>
     strip_tac >> asm_rewrite_tac[]) >>
  `lookup_scopes id (es with gas_obs := []).scopes = NONE` by simp[] >>
  `type_memory_bytes cenv et + 64 < dimword (:256)` by simp[] >>
  mp_tac (Q.INST [`es` |-> `es with gas_obs := []`, `st'` |-> `cs'`]
    dynarray_public_entry_ready) >>
  impl_tac >- (simp[] >> conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `LENGTH vs <= n /\ LENGTH vs < dimword (:256)` by decide_tac >>
  `gas_admissible (eval_for cx tv id stmts vs) (stmt_res_ok lctx)
     (es with gas_obs := [])` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def, Once evaluate_def, lift_option_type_def,
       lift_option_def, bind_return, bind_def, compatible_bound_def,
       check_def, vyperStateTheory.assert_def, ignore_bind_def, return_def]) >>
  `cs_extends sb0 sb1` by (fs[dynarray_for_code_def] >> metis_tac[]) >>
  `!ei k. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag ctx func cx (InLoop exit incr) RetQ bc
      (stmts_env bc (InLoop exit incr) ty stmts) (eval_stmts cx stmts)
      (ei with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes)` by
    (rpt strip_tac >> qpat_assum `!st0 bc sd ex inc ei k. _` drule_all >> simp[]) >>
  `!l. Var arr_ptr <> Label l` by simp[] >>
  `!ei t. P ei /\ stmt_state_rel ctx func cenv cx ei t ==>
    ?addr. eval_operand (Var arr_ptr) t = SOME addr /\
      (!k. k < LENGTH vs ==>
        val_in_memory tv (EL k vs)
          (w2n addr + 32 + k * type_memory_bytes cenv et) t.vs_memory)` by
    (rpt strip_tac >> qpat_assum `!ei s. _` drule_all >> strip_tac >>
     qpat_assum `eval_operand (Var arr_ptr) t = SOME _` (irule_at Any) >>
     simp[]) >>
  drule_all dynarray_code_loop_counted >> strip_tac >>
  drule_all gas_outcome_zero_prefix >> strip_tac >>
  drule_all for_source_prefix_bounded >> strip_tac >>
  irule array_outcome_stmt_post >> simp[] >> goal_assum (drule_at Any)
QED

Theorem compile_for_dynarray_frag:
  !ctx func cx cenv lctx RetQ ty id et c n name arr_ptr arr_sz stmts tv vs es P.
  (!gs. eval_iterator cx (Array (Name (ArrayT et (Dynamic c)) name))
          (es with gas_obs := gs) = (INL vs, es with gas_obs := gs)) /\
  LENGTH vs <= c /\ c <= n /\ c < dimword (:256) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) /\ cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var arr_ptr) arr_sz) /\
  name <> id /\ lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  P es /\
  (!k. k < LENGTH vs ==> value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)) /\
  (!ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s ==>
    ?base. eval_operand (Var arr_ptr) s = SOME base /\
      mload (w2n base) s = n2w (LENGTH vs) /\
      (!k. k < LENGTH vs ==>
        val_in_memory tv (EL k vs)
          (w2n base + 32 + k * type_memory_size tv) s.vs_memory /\
        w2n base + 32 + k * type_memory_size tv < dimword (:256))) /\
  (!st0 bc sd ex inc ei k.
    declare_local cenv id et st0 = (bc,sd) /\
    P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
          :: ei.scopes)) /\
  (!ei k gs r es2.
    P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with <| scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
        :: ei.scopes; gas_obs := gs |>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty
      (For id et (Array (Name (ArrayT et (Dynamic c)) name)) n stmts))
    (eval_stmt cx (For id et (Array (Name (ArrayT et (Dynamic c)) name)) n stmts)) es
Proof
  rpt gen_tac >> strip_tac >>
  irule (Q.SPEC `\ei. ?gs. P (ei with gas_obs := gs)`
           (Q.GEN `P` (SPEC_ALL compile_for_dynarray_frag_zero))) >>
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists `P` >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >> rename1 `P (ei with gas_obs := g0)` >>
      first_x_assum (qspecl_then [`st0`, `bc`, `sd`, `ex`, `inc`,
        `ei with gas_obs := g0`, `k`] mp_tac) >> simp[] >>
      disch_then (qspec_then `ei.gas_obs` mp_tac o
        MATCH_MP stmt_frag_start_gas_obs) >> simp[])
  >- (rpt gen_tac >> strip_tac >> rename1 `P (ei with gas_obs := g0)` >>
      first_x_assum (qspecl_then [`ei with gas_obs := g0`, `k`, `gs`, `r`, `es2`]
        mp_tac) >> simp[] >> strip_tac >> simp[] >>
      strip_tac >> gvs[] >> qexists `es2.gas_obs` >> simp[])
  >- (rpt strip_tac >> rename1 `P (ei with gas_obs := g0)` >>
      first_x_assum (qspecl_then [`ei with gas_obs := g0`, `s`] mp_tac) >>
      simp[] >> disch_then irule >>
      qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
      simp[stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def, NoAsms] >>
      strip_tac >> asm_rewrite_tac[])
  >> qexists `es.gas_obs` >> simp[]
QED
