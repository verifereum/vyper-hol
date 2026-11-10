(* Compiler and resource boundaries for the pointer Concat proof. *)
Theory bodyPtrBytestringBuiltinsConcatCompile
Ancestors
  bodyPtrBytestringBuiltinsConcatPrefix bodyPtrBytestringBuiltinsConcatArgs
  exprSimConcatResult exprLoweringProps exprLowering compileEnv
  fragExec context emitHelper emitHelperProps loweringPosts words list pair arithmetic
  venomInst bodyPtrDefs

Theorem concat_ptr_compile_cuts:
  compile_expr cenv ty (Builtin ann (Concat n) args) sa = (vv,sb) /\
  fn_has_code sa sb fn ==>
  ?buf s1 data s2 ob s3 s4 s5 fo s6.
    compile_alloc_buffer (concat_alloc_size (MAP expr_type args)) sa = (buf,s1) /\
    emit_op ADD [buf.buf_operand; Lit 32w] s1 = (data,s2) /\
    compile_alloc_buffer 64 s2 = (ob,s3) /\
    emit_void MSTORE [ob.buf_operand; Lit 0w] s3 = ((),s4) /\
    compile_concat compile_expr cenv args data
      (MAP (\e. if is_bytestring_type (expr_type e) then (T,0:num)
         else case expr_type e of BaseT (BytesT (Fixed m)) => (F,m)
              | _ => (F,32:num)) args) ob.buf_operand s4 = ((),s5) /\
    emit_op MLOAD [ob.buf_operand] s5 = (fo,s6) /\
    emit_void MSTORE [buf.buf_operand; fo] s6 = ((),sb) /\
    vv = LocatedValue ann (base_ptr buf) /\
    fn_has_code sa s4 fn /\ fn_has_code s4 s5 fn /\
    fn_has_code s5 s6 fn /\ fn_has_code s6 sb fn /\
    ci_mono sa s4 /\ ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 sb
Proof
  strip_tac >> drule concat_compile_shape >> strip_tac >>
  Cases_on `u` >> Cases_on `u'` >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
   ci_mono s5 s6 /\ ci_mono s6 sb` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_emit_op, ci_mono_emit_void, SND] >>
  `!ce ty e st. ci_mono st (SND (compile_expr ce ty e st))` by
    simp[compile_expr_ci_mono] >>
  `ci_mono s4 s5` by
    (qpat_assum `compile_concat _ _ _ _ _ _ _ = _` mp_tac >>
     simp[] >> metis_tac[ci_mono_compile_concat_cfn, SND]) >>
  `ci_mono sa s4` by (fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `cs_extends s4 sb /\ cs_extends s5 sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s4 fn /\ fn_has_code s4 sb fn` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `fn_has_code s4 s5 fn /\ fn_has_code s5 sb fn` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `fn_has_code s5 s6 fn /\ fn_has_code s6 sb fn` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  qexistsl_tac [`buf`,`s1`,`d`,`s2`,`ob`,`s3`,`s4`,`s5`,`fo`,`s6`] >>
  fs[]
QED

Theorem concat_prefix_args_ready:
  compile_alloc_buffer bsz sa = (buf,s1) /\
  emit_op ADD [buf.buf_operand; Lit 32w] s1 = (data,s2) /\
  compile_alloc_buffer 64 s2 = (ob,s3) /\
  emit_void MSTORE [ob.buf_operand; Lit 0w] s3 = ((),s4) /\
  fn_has_code sa s4 fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ 32 <= bsz /\ bsz < dimword (:256) /\
  stmt_state_rel ctx fn ce cx es s /\ ghost_inv d ce cx es G tn s /\
  (!x k. ce.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r p off a ow Gf tnf t binst oinst.
    buf.buf_operand = Var r /\ data = Var p /\ ob.buf_operand = Var off /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
    stmt_state_rel ctx fn ce cx es t /\ ghost_inv d ce cx es Gf tnf t /\
    ghost_kept ce es sa G tn s Gf tnf /\
    ptr_covers Gf tnf r t bsz /\ ptr_covers Gf tnf p t (bsz-32) /\
    ptr_covers Gf tnf off t 32 /\
    lookup_var r t = SOME a /\ lookup_var p t = SOME (n2w (w2n a+32)) /\
    lookup_var off t = SOME ow /\ mload (w2n ow) t = 0w /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tnf.t_mem) /\
    ~t.vs_halted /\ t.vs_current_bb = s4.cs_current_bb /\
    t.vs_inst_idx = LENGTH s4.cs_current_insts /\
    MEM binst (fn_insts fn) /\ binst.inst_opcode = ALLOCA /\
    binst.inst_id = sa.cs_next_id /\ binst.inst_id < s4.cs_next_id /\
    FLOOKUP t.vs_allocas binst.inst_id = SOME (w2n a,bsz) /\
    MEM oinst (fn_insts fn) /\ oinst.inst_opcode = ALLOCA /\
    oinst.inst_id < s4.cs_next_id /\
    FLOOKUP t.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
    w2n a+bsz < dimword (:256) /\ w2n ow+64 < dimword (:256) /\
    (w2n a+bsz <= w2n ow \/ w2n ow+64 <= w2n a) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
      regions_disjoint (w2n a) bsz b k /\ regions_disjoint (w2n ow) 64 b k) /\
    (!name b k. local_region ce es.scopes t name b k ==>
      (w2n a+bsz <= b \/ b+k <= w2n a) /\
      (w2n ow+64 <= b \/ b+k <= w2n ow)) /\
    (!name b k. local_region ce es.scopes s name b k <=>
      local_region ce es.scopes t name b k) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    not_fresh_at s4 r /\ not_fresh_at s4 p /\ not_fresh_at s4 off /\
    local_ptrs_reserved ce s4 /\
    (!x k. ce.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at s4 x) /\
    (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at s4 x) /\
    (!b k. b+k <= w2n ow \/ w2n ow+64 <= b ==>
      mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory)
Proof
  strip_tac >> drule_all concat_prefix_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all concat_prefix_code >> strip_tac >>
  suspend "resources"
QED

Resume concat_prefix_args_ready[resources]:
  `!i. MEM i (emitted_insts sa s4) ==> MEM i (fn_insts fn)` by
    (rpt strip_tac >> irule concat_code_mem >>
     qexistsl_tac [`sa`,`s4`] >> simp[]) >>
  qabbrev_tac `binst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w bsz)]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  qabbrev_tac `oinst = mk_inst (sa.cs_next_id+2) ALLOCA [Lit 64w]
    [STRING #"%" (toString (sa.cs_next_var+2))]` >>
  `MEM binst (fn_insts fn) /\ MEM oinst (fn_insts fn)` by
    (conj_tac >> first_x_assum irule >> simp[Abbr `binst`, Abbr `oinst`]) >>
  `binst.inst_opcode = ALLOCA /\ binst.inst_id = sa.cs_next_id /\
   oinst.inst_opcode = ALLOCA /\ oinst.inst_id = sa.cs_next_id+2` by
    simp[Abbr `binst`, Abbr `oinst`, mk_inst_def] >>
  `ptr_covers Gf tnf off t 32` by
    (qpat_x_assum `ptr_covers _ _ off _ 64` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ptr_covers_def] >> rpt strip_tac >>
     qexistsl_tac [`w`,`b`,`sz'`] >> simp[] >> decide_tac) >>
  `a+32w = n2w (w2n a+32)` by simp[GSYM word_add_n2w, n2w_w2n] >>
  suspend "finish"
QED

Resume concat_prefix_args_ready[finish]:
  `local_ptrs_reserved ce s4` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s4 x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  qexistsl_tac [`r`,`p`,`off`,`a`,`ow`,`Gf`,`tnf`,`t`,`binst`,`oinst`] >>
  simp[] >>
  conj_tac >- (fs[regions_disjoint_def] >> metis_tac[]) >>
  conj_tac >- (fs[regions_disjoint_def]) >>
  suspend "fresh"
QED

Resume concat_prefix_args_ready[fresh]:
  `r = STRING #"%" (toString sa.cs_next_var) /\
   p = STRING #"%" (toString (sa.cs_next_var+1)) /\
   off = STRING #"%" (toString (sa.cs_next_var+2))` by fs[] >>
  fs[] >>
  `bsz+w2n a <= w2n ow \/ w2n ow+64 <= w2n a` by
    (qpat_x_assum `regions_disjoint (w2n ow) _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[regions_disjoint_def] >> decide_tac) >>
  fs[regions_disjoint_def] >>
  simp[not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise concat_prefix_args_ready
