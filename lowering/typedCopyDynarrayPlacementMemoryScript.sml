(* Concrete compiler placement for runtime-length typed-copy loops. *)
Theory typedCopyDynarrayPlacementMemory
Ancestors typedCopyLoopLayoutPtr typedCopyLoopPlacementMemory typedMemoryCopy exprLoweringProps
  exprOperandVar compileEnv emitHelper ASCIInumbers arithmetic list

Theorem typed_copy_dynarray_entry_shape[local]:
  fresh_label "typed_dyn_cond" sa = (hdr,l1) /\
  fresh_label "typed_dyn_body" l1 = (blabel,l2) /\
  fresh_label "typed_dyn_exit" l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
  new_block hdr st1 = (u1,sth) ==>
  counter = "%" ++ toString sa.cs_next_var /\
  sth.cs_next_var = sa.cs_next_var + 1 /\
  sth.cs_next_id = sa.cs_next_id + 2 /\
  sth.cs_current_bb = hdr /\ sth.cs_current_insts = [] /\
  sth.cs_blocks = <|bb_label := sa.cs_current_bb;
    bb_instructions := sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [counter];
       mk_inst (sa.cs_next_id+1) JMP [Label hdr] []]|> :: sa.cs_blocks
Proof
  simp[fresh_label_def, fresh_var_def, emit_inst_def, emit_def,
    fresh_id_def, comp_bind_def, comp_return_def, new_block_def] >>
  strip_tac >> gvs[APPEND_ASSOC]
QED

Theorem typed_copy_dynarray_test_shape[local]:
  emit_op LT [Var counter; length] sth = (lt,h1) /\
  emit_op ISZERO [lt] h1 = (done,stj) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2) /\
  new_block blabel st2 = (u2,stb) /\ sth.cs_current_insts = [] ==>
  ?ln dn.
    lt = Var ln /\ done = Var dn /\
    ln = "%" ++ toString sth.cs_next_var /\
    dn = "%" ++ toString (sth.cs_next_var + 1) /\
    stb.cs_next_var = sth.cs_next_var + 2 /\
    stb.cs_next_id = sth.cs_next_id + 3 /\
    stb.cs_current_bb = blabel /\ stb.cs_current_insts = [] /\
    stb.cs_blocks = <|bb_label := sth.cs_current_bb; bb_instructions :=
      [mk_inst sth.cs_next_id LT [Var counter; length] [ln];
       mk_inst (sth.cs_next_id+1) ISZERO [Var ln] [dn];
       mk_inst (sth.cs_next_id+2) JNZ [Var dn; Label exit; Label blabel] []]|>
      :: sth.cs_blocks
Proof
  simp[emit_op_def, emit_inst_def, emit_def, fresh_id_def, fresh_var_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, new_block_def] >>
  strip_tac >> gvs[APPEND_ASSOC]
QED

Theorem typed_copy_dynarray_address_shape[local]:
  emit_op MUL [Var counter; Lit ss] stb = (so,b1) /\
  emit_op MUL [Var counter; Lit ds] b1 = (doff,b2) /\
  emit_op ADD [src;so] b2 = (sp,b3) /\
  emit_op ADD [dst;doff] b3 = (dp,b4) /\ stb.cs_current_insts = [] ==>
  ?sn dn pn qn.
    so = Var sn /\ doff = Var dn /\ sp = Var pn /\ dp = Var qn /\
    sn = "%" ++ toString stb.cs_next_var /\
    dn = "%" ++ toString (stb.cs_next_var+1) /\
    pn = "%" ++ toString (stb.cs_next_var+2) /\
    qn = "%" ++ toString (stb.cs_next_var+3) /\
    b4.cs_next_var = stb.cs_next_var + 4 /\
    b4.cs_next_id = stb.cs_next_id + 4 /\
    b4.cs_current_bb = stb.cs_current_bb /\ b4.cs_blocks = stb.cs_blocks /\
    b4.cs_current_insts =
      [mk_inst stb.cs_next_id MUL [Var counter; Lit ss] [sn];
       mk_inst (stb.cs_next_id+1) MUL [Var counter; Lit ds] [dn];
       mk_inst (stb.cs_next_id+2) ADD [src; Var sn] [pn];
       mk_inst (stb.cs_next_id+3) ADD [dst; Var dn] [qn]]
Proof
  simp[emit_op_def, emit_inst_def, emit_def, fresh_id_def, fresh_var_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[APPEND_ASSOC]
QED

Theorem typed_copy_dynarray_tail_shape[local]:
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,stx) ==>
  stx.cs_current_bb = exit /\ stx.cs_current_insts = [] /\
  stx.cs_blocks = <|bb_label := b5.cs_current_bb;
    bb_instructions := b5.cs_current_insts ++
      [mk_inst b5.cs_next_id ADD [Var counter; Lit 1w]
         ["%" ++ toString b5.cs_next_var];
       mk_inst (b5.cs_next_id+1) ASSIGN
         [Var ("%" ++ toString b5.cs_next_var)] [counter];
       mk_inst (b5.cs_next_id+2) JMP [Label hdr] []]|> :: b5.cs_blocks
Proof
  simp[emit_op_def, emit_inst_def, emit_def, fresh_id_def, fresh_var_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, new_block_def] >>
  strip_tac >> gvs[APPEND_ASSOC]
QED

Theorem typed_copy_dynarray_loop_placement:
  fresh_label "typed_dyn_cond" sa = (hdr,l1) /\
  fresh_label "typed_dyn_body" l1 = (blabel,l2) /\
  fresh_label "typed_dyn_exit" l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
  new_block hdr st1 = (u1,sth) /\
  emit_op LT [Var counter; length] sth = (lt,h1) /\
  emit_op ISZERO [lt] h1 = (done,stj) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2) /\
  new_block blabel st2 = (u2,stb) /\
  emit_op MUL [Var counter; Lit ss] stb = (so,b1) /\
  emit_op MUL [Var counter; Lit ds] b1 = (doff,b2) /\
  emit_op ADD [src;so] b2 = (sp,b3) /\
  emit_op ADD [dst;doff] b3 = (dp,b4) /\
  compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5) /\
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,stx) /\ fn_has_code sa stx func /\
  (!x. src = Var x \/ dst = Var x \/ length = Var x ==> not_fresh_at sa x) ==>
  ?ln dn sn offn pn qn entry test bb back.
    lt = Var ln /\ done = Var dn /\ so = Var sn /\ doff = Var offn /\
    sp = Var pn /\ dp = Var qn /\
    fn_has_code b4 b5 func /\ not_fresh_at b4 pn /\ not_fresh_at b4 qn /\
    ci_mono sa sth /\ ci_mono sth b4 /\
    not_fresh_at sth counter /\ ~not_fresh_at sa counter /\
    ~not_fresh_at sa ("%" ++ toString b5.cs_next_var) /\
    counter <> "%" ++ toString b5.cs_next_var /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sth x) /\
    (!x. MEM x [ln;dn;sn;offn;pn;qn] ==> ~not_fresh_at sth x) /\
    ALL_DISTINCT [counter;sn;offn;pn;qn] /\
    lookup_block sa.cs_current_bb func.fn_blocks = SOME entry /\
    entry.bb_instructions = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [counter];
       mk_inst (sa.cs_next_id+1) JMP [Label hdr] []] /\
    lookup_block hdr func.fn_blocks = SOME test /\
    test.bb_instructions =
      [mk_inst sth.cs_next_id LT [Var counter; length] [ln];
       mk_inst (sth.cs_next_id+1) ISZERO [Var ln] [dn];
       mk_inst (sth.cs_next_id+2) JNZ [Var dn; Label exit; Label blabel] []] /\
    lookup_block blabel func.fn_blocks = SOME bb /\
    isPREFIX
      [mk_inst (sth.cs_next_id+3) MUL [Var counter; Lit ss] [sn];
       mk_inst (sth.cs_next_id+4) MUL [Var counter; Lit ds] [offn];
       mk_inst (sth.cs_next_id+5) ADD [src; Var sn] [pn];
       mk_inst (sth.cs_next_id+6) ADD [dst; Var offn] [qn]] bb.bb_instructions /\
    b4.cs_current_bb = blabel /\ LENGTH b4.cs_current_insts = 4 /\
    lookup_block b5.cs_current_bb func.fn_blocks = SOME back /\
    back.bb_instructions = b5.cs_current_insts ++
      [mk_inst b5.cs_next_id ADD [Var counter; Lit 1w] ["%" ++ toString b5.cs_next_var];
       mk_inst (b5.cs_next_id+1) ASSIGN [Var ("%" ++ toString b5.cs_next_var)] [counter];
       mk_inst (b5.cs_next_id+2) JMP [Label hdr] []] /\
    stx.cs_current_bb = exit /\ stx.cs_current_insts = []
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all typed_copy_dynarray_entry_shape >> strip_tac >>
  drule_all typed_copy_dynarray_test_shape >> strip_tac >>
  drule_all typed_copy_dynarray_address_shape >> strip_tac >>
  drule_all typed_copy_dynarray_tail_shape >> strip_tac >>
  drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)
    typed_copy_loop_slice_locations >>
  disch_then (qspecl_then [`sa`, `stx`, `HD sth.cs_blocks`,
    `HD stb.cs_blocks`, `HD stx.cs_blocks`, `func`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  suspend "finish"
QED

Resume typed_copy_dynarray_loop_placement[finish]:
  `ci_mono b4 b5` by
    (qspec_then `cenv` mp_tac (cj 1 ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`dp`, `dty`, `sp`, `sty`, `b4`] mp_tac) >>
     asm_rewrite_tac[] >> simp[]) >>
  `ci_mono sa sth` by
    (simp[ci_mono_def, cs_extends_def] >>
     qexists_tac `[HD sth.cs_blocks]` >> simp[]) >>
  `ci_mono sth b4` by
    (qpat_x_assum `sth.cs_blocks = _` kall_tac >>
     simp[ci_mono_def, cs_extends_def] >>
     qexists_tac `[HD stb.cs_blocks]` >> simp[]) >>
  `sa.cs_next_var + 7 <= b5.cs_next_var` by
    (qpat_x_assum `ci_mono b4 b5` mp_tac >> simp[ci_mono_def]) >>
  `not_fresh_at b4 pn /\ not_fresh_at b4 qn` by
    simp[not_fresh_at_def, toString_inj] >>
  `not_fresh_at sth counter /\ ~not_fresh_at sa counter /\
   ~not_fresh_at sa ("%" ++ toString b5.cs_next_var) /\
   counter <> "%" ++ toString b5.cs_next_var /\
   (!x. MEM x [ln;dn;sn;dn';pn;qn] ==> ~not_fresh_at sth x) /\
   ALL_DISTINCT [counter;sn;dn';pn;qn]` by
    (irule typed_copy_loop_register_freshness >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`ln`, `dn`, `sn`, `dn'`, `pn`, `qn`,
    `HD sth.cs_blocks`, `HD stb.cs_blocks`, `bb`, `HD stx.cs_blocks`] >>
  rpt conj_tac >> simp[]
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[] >> metis_tac[])
  >- (qpat_x_assum `lookup_block (HD sth.cs_blocks).bb_label _ = _` mp_tac >> simp[])
  >- (qpat_x_assum `lookup_block (HD stb.cs_blocks).bb_label _ = _` mp_tac >> simp[])
  >- (qpat_x_assum `lookup_block b4.cs_current_bb _ = _` mp_tac >> simp[])
  >- (qpat_x_assum `isPREFIX b4.cs_current_insts _` mp_tac >> simp[]) >>
  qpat_x_assum `lookup_block (HD stx.cs_blocks).bb_label _ = _` mp_tac >> simp[]
QED

Finalise typed_copy_dynarray_loop_placement
