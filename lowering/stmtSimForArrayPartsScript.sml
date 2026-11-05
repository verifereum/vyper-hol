(* Fixed-array compiler boundary: dynamic length/check code is absent. *)
Theory stmtSimForArrayParts
Ancestors
  loweringPosts stmtSimDefs stmtSimProps
  stmtSimForArray stmtSimForParts stmtLowering exprLowering compileEnv
  emitHelper finite_map vyperAST fragExec venomExecSemantics
  venomExecProofs venomInst venomState context  loweringSlice
  exprLoweringProps emitHelperProps list rich_list
Libs
  monadsyntax

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
  cheat
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
  cheat
QED

(* Evaluating a memory-local iterable emits no instructions. *)
Theorem compile_array_name:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar arr_op sz) ==>
  compile_expr cenv (ArrayT et (Fixed n))
    (Name (ArrayT et (Fixed n)) name) st =
  (LocatedValue (ArrayT et (Fixed n)) (mk_ptr arr_op LocMemory), st)
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

(* Memory element copies are straight-line, including composite elements. *)
Theorem array_iter_copy_static:
  ~block_is_terminated sa /\
  compile_iter_elem_copy cenv src dst stride LocMemory F et et sa = ((),sb) ==>
  same_blocks sa sb /\ cs_extends sa sb /\
  sa.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  ~block_is_terminated sb
Proof
  cheat
QED

(* Recover block lookups without exposing the final function's block list. *)
Theorem array_emitted_block_lookup[local]:
  fn_has_code sa sb func /\ sb.cs_blocks = blocks ++ sa.cs_blocks /\
  MEM bb blocks /\ bb.bb_label = lbl ==>
  lookup_block lbl func.fn_blocks = SOME bb
Proof
  cheat
QED

Theorem array_prefix_extends[local]:
  sa.cs_blocks =
    [cond_bb; entry_bb;
     <|bb_label := st.cs_current_bb;
       bb_instructions := st.cs_current_insts ++ insts|>] ++ st.cs_blocks ==>
  cs_extends st sa
Proof
  cheat
QED

(* Code ownership for the four opaque compiler segments. *)
Theorem array_stages_code[local]:
  cs_extends st sa /\ cs_extends sa sb0 /\ cs_extends sb0 sb1 /\
  cs_extends sb1 sj /\ cs_extends sj st' /\ fn_has_code st st' func ==>
  fn_has_code st sa func /\ fn_has_code sa sb0 func /\
  fn_has_code sb0 sb1 func /\ fn_has_code sb1 sj func /\
  fn_has_code sj st' func
Proof
  cheat
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
  cheat
QED
