(* Fixed-array compiler boundary: dynamic length/check code is absent. *)
Theory stmtSimForArrayParts
Ancestors
  loweringPosts stmtSimDefs stmtSimProps stmtSimDeclCompose
  stmtSimForArray stmtSimForParts stmtLowering exprLowering compileEnv
  emitHelper finite_map vyperAST fragExec venomExecSemantics
  venomExecProofs venomInst venomState context  loweringSlice
  exprLoweringProps emitHelperProps list rich_list
Libs
  monadsyntax

(* Address temporaries do not change the allocation frame of live locals. *)
Theorem alloca_frame_update_var:
  not_local_ptr cenv es.scopes x ==>
  alloca_frame cenv es sa s cenv es (update_var x w s)
Proof
  rw[alloca_frame_def, update_var_def] >>
  first_x_assum irule >>
  fs[local_region_def, not_local_ptr_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem compile_for_fixed_array:
  !cenv lctx ty id et n name stmts.
  compile_stmt cenv lctx ty
    (For id et (Array (Name (ArrayT et (Fixed n)) name)) n stmts) =
  do av <- compile_expr cenv (ArrayT et (Fixed n))
             (Name (ArrayT et (Fixed n)) name);
     loc <- return (case vv_location av of SOME l => l | NONE => LocMemory);
     bc <- declare_local cenv id et;
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
     emit_inst JMP [Label cond] [];
     new_block cond;
     done <- emit_op EQ [Var idx; Lit (n2w n)];
     emit_inst JNZ [done; Label exit; Label bod] [];
     new_block bod;
     off <- emit_op MUL [Var idx;
                        Lit (n2w (elem_size_in_location cenv loc et))];
     ep <- emit_op ADD [vv_operand av; off];
     (case FLOOKUP bc.ce_vars id of
        SOME (MemLoc dst _) =>
          compile_iter_elem_copy cenv ep (Lit (n2w dst))
            (elem_size_in_location cenv loc et)
            loc (is_slot_addressed loc) et et
      | SOME (PtrVar ptr_op _) =>
          compile_iter_elem_copy cenv ep ptr_op
            (elem_size_in_location cenv loc et)
            loc (is_slot_addressed loc) et et
      | _ => emit_void INVALID []);
     compile_stmts bc (InLoop exit incr) ty stmts;
     emit_jmp_if_not_terminated incr;
     new_block incr;
     next <- emit_op ADD [Var idx; Lit 1w];
     emit_inst ASSIGN [next] [idx];
     emit_inst JMP [Label cond] [];
     new_block exit;
     return ()
  od
Proof
  rpt gen_tac >>
  simp[Once compile_stmt_def, expr_type_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, FUN_EQ_THM]
QED

(* Fixed arrays need only initialize the index before the condition block. *)
Theorem for_array_entry_block:
  !ctx func ee idx lbl cond_lbl i1 i2.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl;
              bb_instructions := [mk_inst i1 ASSIGN [Lit 0w] [idx];
                                  mk_inst i2 JMP [Label cond_lbl] []] |> /\
    ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted ==>
    !fuel rr.
      run_from fuel ctx func (jump_to cond_lbl (update_var idx 0w ee)) = rr /\
      (!e. rr <> Error e) ==>
      ?fuel'. run_from fuel' ctx func ee = rr
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bb = <| bb_label := lbl;
              bb_instructions := [mk_inst i1 ASSIGN [Lit 0w] [idx];
                                  mk_inst i2 JMP [Label cond_lbl] []] |>` >>
  `!fu. run_from fu ctx func ee =
        run_from fu ctx func (update_var idx 0w ee with vs_inst_idx := 1)` by
    (gen_tac >>
     qspecl_then [`fu`, `ctx`, `func`, `ee`, `bb`,
                  `mk_inst i1 ASSIGN [Lit 0w] [idx]`, `update_var idx 0w ee`]
       mp_tac run_from_step >>
     impl_tac
     >- simp[Abbr `bb`, get_instruction_def, venomInstTheory.mk_inst_def,
             is_terminator_def, step_inst_base_def, eval_operand_def] >>
     simp[]) >>
  qabbrev_tac `d1 = update_var idx 0w ee with vs_inst_idx := 1` >>
  `jump_to cond_lbl d1 = jump_to cond_lbl (update_var idx 0w ee)` by
    simp[Abbr `d1`, jump_to_def, update_var_def] >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  `run_from (SUC fuel) ctx func d1 = rr` by
    (qspecl_then [`fuel`, `ctx`, `func`, `d1`, `bb`,
                  `mk_inst i2 JMP [Label cond_lbl] []`, `cond_lbl`, `rr`]
       mp_tac run_from_jump_result >>
     impl_tac >- (fs[Abbr `bb`, Abbr `d1`, get_instruction_def,
                     venomInstTheory.mk_inst_def, is_terminator_def,
                     update_var_def, step_jmp_behavior]) >>
     simp[]) >>
  fs[]
QED

(* Evaluating a memory-local iterable emits no instructions. *)
Theorem compile_array_name:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar arr_op sz) ==>
  compile_expr cenv (ArrayT et (Fixed n))
    (Name (ArrayT et (Fixed n)) name) st =
  (LocatedValue (ArrayT et (Fixed n)) (mk_ptr arr_op LocMemory), st)
Proof
  strip_tac >>
  simp[Once compile_expr_def, compile_name_vv_def, comp_return_def,
       expr_type_def]
QED

(* The optional back-edge does not allocate registers or change blocks. *)
Theorem array_body_backedge:
  emit_jmp_if_not_terminated incr sb1 = ((),sj) ==>
  sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
  sj.cs_next_var = sb1.cs_next_var /\ cs_extends sb1 sj /\
  (~block_is_terminated sb1 ==>
   sj.cs_current_insts = sb1.cs_current_insts ++
     [mk_inst sb1.cs_next_id JMP [Label incr] []])
Proof
  simp[emit_jmp_if_not_terminated_def, comp_get_def, comp_bind_def] >>
  Cases_on `block_is_terminated sb1`
  >- simp[comp_return_def, cs_extends_refl] >>
  simp[emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
       comp_return_def, LET_THM] >> strip_tac >> gvs[] >>
  irule cs_extends_same_block >> simp[]
QED

(* Cut the actual compiler at copy entry, body entry and the back edge.
   Primitive emission remains opaque here; later static lemmas own it. *)
Theorem compile_for_array_stages:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar arr_op arr_sz) /\
  compile_stmt cenv lctx ty
    (For id et (Array (Name (ArrayT et (Fixed n)) name)) n stmts) st =
    ((),st') ==>
  ?bc entry cond bod incr exit idx off ep sa sb0 sb1 sj.
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
        emit_inst JMP [Label cond] [];
        new_block cond;
        done <- emit_op EQ [Var idx; Lit (n2w n)];
        emit_inst JNZ [done; Label exit; Label bod] [];
        new_block bod;
        off <- emit_op MUL [Var idx;
                   Lit (n2w (elem_size_in_location cenv LocMemory et))];
        ep <- emit_op ADD [arr_op; off];
        return (bc,entry,cond,bod,incr,exit,idx,off,ep)
     od) st = ((bc,entry,cond,bod,incr,exit,idx,off,ep),sa) /\
    (case FLOOKUP bc.ce_vars id of
       SOME (MemLoc dst _) =>
         compile_iter_elem_copy cenv ep (Lit (n2w dst))
           (elem_size_in_location cenv LocMemory et) LocMemory F et et
     | SOME (PtrVar ptr_op _) =>
         compile_iter_elem_copy cenv ep ptr_op
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
  strip_tac >> drule compile_array_name >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[compile_for_fixed_array, vv_location_def,
       vv_operand_def, mk_ptr_def, is_slot_addressed_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  metis_tac[]
QED

Theorem compile_for_array_prefix:
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
      emit_inst JMP [Label cond] [];
      new_block cond;
      done <- emit_op EQ [Var idx; Lit (n2w n)];
      emit_inst JNZ [done; Label exit; Label bod] [];
      new_block bod;
      off <- emit_op MUL [Var idx;
                 Lit (n2w (elem_size_in_location cenv LocMemory et))];
      ep <- emit_op ADD [arr_op; off];
      return (bc,entry,cond,bod,incr,exit,idx,off,ep)
   od) st = ((bc,entry,cond,bod,incr,exit,idx,off,ep),sa) ==>
  ?p dv ov epv.
    p = STRING #"%" (toString st.cs_next_var) /\
    idx = STRING #"%" (toString (st.cs_next_var + 1)) /\
    dv = STRING #"%" (toString (st.cs_next_var + 2)) /\
    ov = STRING #"%" (toString (st.cs_next_var + 3)) /\
    epv = STRING #"%" (toString (st.cs_next_var + 4)) /\
    off = Var ov /\ ep = Var epv /\
    entry = fresh_label_output "iter_entry" st.cs_next_label /\
    cond = fresh_label_output "iter_cond" (st.cs_next_label + 1) /\
    bod = fresh_label_output "iter_body" (st.cs_next_label + 2) /\
    incr = fresh_label_output "iter_incr" (st.cs_next_label + 3) /\
    exit = fresh_label_output "iter_exit" (st.cs_next_label + 4) /\
    declare_local cenv id et st =
      (bc, st with cs_next_var := st.cs_next_var + 1) /\
    FLOOKUP bc.ce_vars id =
      SOME (PtrVar (Var p) (type_memory_bytes cenv et)) /\
    sa.cs_current_bb = bod /\
    sa.cs_current_insts =
      [mk_inst (st.cs_next_id + 6) MUL
         [Var idx; Lit (n2w (elem_size_in_location cenv LocMemory et))] [ov];
       mk_inst (st.cs_next_id + 7) ADD [arr_op; Var ov] [epv]] /\
    sa.cs_next_var = st.cs_next_var + 5 /\
    sa.cs_next_id = st.cs_next_id + 8 /\
    sa.cs_next_label = st.cs_next_label + 5 /\
    sa.cs_blocks =
      [<|bb_label := cond;
         bb_instructions :=
           [mk_inst (st.cs_next_id + 4) EQ [Var idx; Lit (n2w n)] [dv];
            mk_inst (st.cs_next_id + 5) JNZ [Var dv; Label exit; Label bod] []]|>;
       <|bb_label := entry;
         bb_instructions :=
           [mk_inst (st.cs_next_id + 2) ASSIGN [Lit 0w] [idx];
            mk_inst (st.cs_next_id + 3) JMP [Label cond] []]|>;
       <|bb_label := st.cs_current_bb;
         bb_instructions := st.cs_current_insts ++
           [mk_inst st.cs_next_id ALLOCA
              [Lit (n2w (type_memory_bytes cenv et))] [p];
            mk_inst (st.cs_next_id + 1) JMP [Label entry] []]|>] ++ st.cs_blocks
Proof
  strip_tac >>
  qpat_x_assum `_ st = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `declare_local cenv id et st` >>
  rename1 `declare_local cenv id et st = (bc0,st1)` >>
  drule_all declare_local_ptr >> strip_tac >> gvs[] >>
  simp[emit_local_alloca_def, fresh_label_def, emit_inst_def, emit_op_def,
       fresh_id_def, emit_def, new_block_def, fresh_var_def,
       comp_get_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       LET_THM] >> strip_tac >> gvs[] >>
  simp[GSYM arithmeticTheory.ADD_ASSOC] >> metis_tac[]
QED

Theorem compile_for_array_suffix:
  (do new_block incr;
      next <- emit_op ADD [Var idx; Lit 1w];
      emit_inst ASSIGN [next] [idx];
      emit_inst JMP [Label cond] [];
      new_block exit;
      return ()
   od) sj = ((),st') ==>
  ?nv.
    nv = STRING #"%" (toString sj.cs_next_var) /\
    st'.cs_current_bb = exit /\ st'.cs_current_insts = [] /\
    st'.cs_next_var = sj.cs_next_var + 1 /\
    st'.cs_next_id = sj.cs_next_id + 3 /\
    st'.cs_next_label = sj.cs_next_label /\
    st'.cs_blocks =
      [<|bb_label := incr;
         bb_instructions :=
           [mk_inst sj.cs_next_id ADD [Var idx; Lit 1w] [nv];
            mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [idx];
            mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|>;
       <|bb_label := sj.cs_current_bb;
         bb_instructions := sj.cs_current_insts|>] ++ sj.cs_blocks /\
    cs_extends sj st'
Proof
  simp[new_block_def, emit_op_def, emit_inst_def, fresh_var_def,
       fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >> strip_tac >> gvs[] >>
  simp[GSYM arithmeticTheory.ADD_ASSOC, cs_extends_def] >>
  qexists_tac `[_; _]` >> simp[]
QED

(* Memory element copies are straight-line, including composite elements. *)
Theorem array_iter_copy_static:
  ~block_is_terminated sa /\
  compile_iter_elem_copy cenv src dst stride LocMemory F et et sa = ((),sb) ==>
  same_blocks sa sb /\ cs_extends sa sb /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  ~block_is_terminated sb
Proof
  strip_tac >> Cases_on `is_word_type et` >>
  Cases_on `is_bytestring_type et` >>
  gvs[compile_iter_elem_copy_def, compile_store_memory_def,
      compile_store_bytestring_def, compile_bytestring_copy_len_def,
      compile_copy_memory_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_id_def,
      fresh_var_def, emit_def] >>
  simp[same_blocks_def, cs_extends_same_block, emitted_insts_def,
       rich_listTheory.DROP_APPEND1, block_is_terminated_def,
       LAST_APPEND, mk_inst_def, is_terminator_def] >>
  Cases_on `type_memory_bytes cenv et` >>
  gvs[compile_copy_memory_def, comp_return_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, fresh_id_def, emit_def,
      same_blocks_def, cs_extends_same_block, emitted_insts_def,
      rich_listTheory.DROP_APPEND1, block_is_terminated_def,
      LAST_APPEND, mk_inst_def, is_terminator_def] >>
  Cases_on `sa.cs_current_insts` >>
  gvs[LAST_CONS_cond, LAST_APPEND, is_terminator_def, cs_extends_def,
      rich_listTheory.IS_PREFIX_APPEND]
QED

(* Recover block lookups without exposing the final function's block list. *)
Theorem array_emitted_block_lookup[local]:
  fn_has_code sa sb func /\ sb.cs_blocks = blocks ++ sa.cs_blocks /\
  MEM bb blocks /\ bb.bb_label = lbl ==>
  lookup_block lbl func.fn_blocks = SOME bb
Proof
  strip_tac >>
  `emitted_blocks sa sb = blocks` by
    (irule emitted_blocks_append >> simp[]) >>
  fs[fn_has_code_def] >> metis_tac[]
QED

Theorem array_prefix_extends[local]:
  sa.cs_blocks =
    [cond_bb; entry_bb;
     <|bb_label := st.cs_current_bb;
       bb_instructions := st.cs_current_insts ++ insts|>] ++ st.cs_blocks ==>
  cs_extends st sa
Proof
  strip_tac >> simp[cs_extends_def] >> qexists_tac `[_;_;_]` >>
  simp[IS_PREFIX_APPEND]
QED

(* Code ownership for the four opaque compiler segments. *)
Theorem array_stages_code[local]:
  cs_extends st sa /\ cs_extends sa sb0 /\ cs_extends sb0 sb1 /\
  cs_extends sb1 sj /\ cs_extends sj st' /\ fn_has_code st st' func ==>
  fn_has_code st sa func /\ fn_has_code sa sb0 func /\
  fn_has_code sb0 sb1 func /\ fn_has_code sb1 sj func /\
  fn_has_code sj st' func
Proof
  strip_tac >>
  `cs_extends sb1 st' /\ cs_extends sb0 st' /\ cs_extends sa st'` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code st sa func /\ fn_has_code sa st' func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code sa sb0 func /\ fn_has_code sb0 st' func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code sb0 sb1 func /\ fn_has_code sb1 st' func` by
    metis_tac[fn_has_code_split] >>
  drule_all fn_has_code_split >> simp[]
QED

(* Static producer: the body remains opaque and the entry's old instructions
   are retained. Layout/type and runtime facts belong to the consumer. *)
Theorem compile_for_array_parts:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar arr_op arr_sz) /\
  compile_stmt cenv lctx ty
    (For id et (Array (Name (ArrayT et (Fixed n)) name)) n stmts) st =
    ((),st') /\ cenv.ce_alloca_locals /\ fn_has_code st st' func /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
                cs_extends sa sb) ==>
  ?bc p idx dv ov ep nv entry cond bod incr exit sa sb0 sb1 sj.
    p = STRING #"%" (toString st.cs_next_var) /\
    idx = STRING #"%" (toString (st.cs_next_var + 1)) /\
    dv = STRING #"%" (toString (st.cs_next_var + 2)) /\
    ov = STRING #"%" (toString (st.cs_next_var + 3)) /\
    ep = STRING #"%" (toString (st.cs_next_var + 4)) /\
    nv = STRING #"%" (toString sj.cs_next_var) /\
    declare_local cenv id et st =
      (bc, st with cs_next_var := st.cs_next_var + 1) /\
    FLOOKUP bc.ce_vars id =
      SOME (PtrVar (Var p) (type_memory_bytes cenv et)) /\
    sa.cs_current_bb = bod /\
    sa.cs_current_insts =
      [mk_inst (st.cs_next_id + 6) MUL
         [Var idx; Lit (n2w (elem_size_in_location cenv LocMemory et))] [ov];
       mk_inst (st.cs_next_id + 7) ADD [arr_op; Var ov] [ep]] /\
    sa.cs_next_var = st.cs_next_var + 5 /\
    sa.cs_next_id = st.cs_next_id + 8 /\ sa.cs_next_id <= sb0.cs_next_id /\
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
               [mk_inst st.cs_next_id ALLOCA
                  [Lit (n2w (type_memory_bytes cenv et))] [p];
                mk_inst (st.cs_next_id + 1) JMP [Label entry] []]|> /\
    lookup_block entry func.fn_blocks =
      SOME <|bb_label := entry; bb_instructions :=
        [mk_inst (st.cs_next_id + 2) ASSIGN [Lit 0w] [idx];
         mk_inst (st.cs_next_id + 3) JMP [Label cond] []]|> /\
    lookup_block cond func.fn_blocks =
      SOME <|bb_label := cond; bb_instructions :=
        [mk_inst (st.cs_next_id + 4) EQ [Var idx; Lit (n2w n)] [dv];
         mk_inst (st.cs_next_id + 5) JNZ [Var dv; Label exit; Label bod] []]|> /\
    lookup_block incr func.fn_blocks =
      SOME <|bb_label := incr; bb_instructions :=
        [mk_inst sj.cs_next_id ADD [Var idx; Lit 1w] [nv];
         mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [idx];
         mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|> /\
    st'.cs_current_bb = exit /\ st'.cs_current_insts = []
Proof
  strip_tac >> drule_all compile_for_array_stages >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` kall_tac >>
  dxrule_all compile_for_array_prefix >> strip_tac >>
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
  qexistsl_tac [`entry`, `cond`, `incr`, `sa`, `sb0`, `sb1`, `sj`] >>
  fs[] >>
  rpt conj_tac
  >- fs[same_blocks_def]
  >- (irule array_emitted_block_lookup >>
      simp[] >> qexistsl_tac [`TAKE 3 sa.cs_blocks`, `st`, `sa`] >> simp[])
  >- (irule array_emitted_block_lookup >>
      simp[] >> qexistsl_tac [`TAKE 3 sa.cs_blocks`, `st`, `sa`] >> simp[])
  >- (irule array_emitted_block_lookup >>
      simp[] >> qexistsl_tac [`TAKE 3 sa.cs_blocks`, `st`, `sa`] >> simp[])
  >> irule array_emitted_block_lookup >>
  simp[] >> qexistsl_tac [`TAKE 2 st'.cs_blocks`, `sj`, `st'`] >> simp[]
QED
