(* The target-independent expression, snapshot and load prefix. *)
Theory tupleAssignPrefix
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  tupleStageProps tupleTypedLoad  exprOperandVar exprLoweringProps
   localPtrsProps compileEnv loweringStateRelDefs loweringSlice fragExec valueEncoding valueEncodingDefs
  vyperValue vyperTyping vyperInterpreter freshWrites list rich_list finite_map
  exprLowering vyperTypeABI stmtSimAssignTuple stmtSimReturn
  stmtSimDeclPath exprSimBufferStore fragGasMode fragGasSeq fragGasPath venomMemDefs
  venomInstProofs venomInst venomState venomExecSemantics emitHelper
  valueEncodingProofs valueEncodingProps valueCopy loweringHalt
  stmtLowering context
Libs
  monadsyntax

Theorem mcopy_alloca_framed_path[local]:
  !ctx func cenv cx es sa sb s inst p dw sw src sz tv v.
    emit_void MCOPY [Var p; src; Lit (n2w sz)] sa = ((), sb) /\
    lookup_var p s = SOME dw /\ eval_operand src s = SOME sw /\
    sz < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    not_local_ptr cenv es.scopes p /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw, sz) /\
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= sz /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (!q. lookup_var q t = lookup_var q s) /\ t.vs_allocas = s.vs_allocas /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt strip_tac >>
  `stmt_state_rel ctx func cenv cx es (mcopy (w2n dw) (w2n sw) sz s)` by
    (irule stmt_state_rel_mcopy_alloca >> simp[] >>
     qexistsl [`sz`, `inst`, `p`] >> simp[]) >>
  `val_in_memory tv v (w2n dw) (mcopy (w2n dw) (w2n sw) sz s).vs_memory` by
    (irule mcopy_val_in_memory >> simp[]) >>
  `gas_marked_path F ctx func s 0
     (OK (mcopy (w2n dw) (w2n sw) sz s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule emit_inst_zero_marked_path >> simp[] >>
     qexistsl [`[Var p; src; Lit (n2w sz)]`, `MCOPY`, `[]`, `sa`, `sb`] >>
     gvs[emit_void_def, emit_inst_def, is_terminator_def] >>
     simp[stepInstBaseLib.simp_opcode_clause ``MCOPY``, mk_inst_def,
          eval_operand_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[emit_void_def, emit_inst_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qexists `mcopy (w2n dw) (w2n sw) sz s with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[stmt_state_rel_inst_idx] >>
  simp[mcopy_def, write_memory_with_expansion_def, LET_THM, lookup_var_def]
QED

Theorem tuple_stage_copy_path[local]:
  !ctx func cenv cx es sa sb staged op s sw sz tv v.
    (do buf <- compile_alloc_buffer sz;
        emit_void MCOPY [buf.buf_operand; op; Lit (n2w sz)];
        comp_return buf.buf_operand od) sa = (staged,sb) /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    eval_operand op s = SOME sw /\
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= sz /\ sz < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t w. eval_operand staged t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      val_in_memory tv v (w2n w) t.vs_memory /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!x. staged = Var x ==> not_fresh_at sb x) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt strip_tac >> drule_all tuple_stage_copy_parts >>
  disch_then (qx_choosel_then [`sx`, `sm`, `p`] strip_assume_tac) >>
  `MEM (mk_inst sx.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func)` by
    (irule emit_inst_fn_member >> qexists `sm` >> simp[]) >>
  `not_local_ptr cenv es.scopes p` by
    (gvs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
  `op <> Var p` by metis_tac[] >>
  `s.vs_current_bb = sx.cs_current_bb /\
   s.vs_inst_idx = LENGTH sx.cs_current_insts` by simp[] >>
  drule_all annassign_alloca_operand_framed_path >>
  disch_then (qx_choosel_then [`s1`, `w`] strip_assume_tac) >>
  `eval_operand op s1 = SOME sw` by metis_tac[] >>
  `val_in_memory tv v (w2n sw) s1.vs_memory` by simp[] >>
  `?t. stmt_state_rel ctx func cenv cx es t /\
      val_in_memory tv v (w2n w) t.vs_memory /\
      (!q. lookup_var q t = lookup_var q s1) /\ t.vs_allocas = s1.vs_allocas /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      gas_marked_path F ctx func s1 0 (OK t)` by
    (irule mcopy_alloca_framed_path >> simp[] >>
     qexists `mk_inst sx.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
     goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >> gvs[mk_inst_def]) >>
  `gas_marked_path F ctx func s (0 + 0) (OK t)` by
    (irule gas_marked_path_then >> qexists `s1` >> simp[]) >>
  qexistsl [`t`, `w`] >> simp[eval_operand_def] >>
  conj_tac >- gvs[] >>
  conj_tac >- (rpt strip_tac >> `x <> p` by metis_tac[] >> simp[]) >>
  gvs[]
QED

Theorem optional_tuple_stage_path:
  !ctx func cenv cx es flag tys tvs vs se sa sb staged op s sw.
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op) sa = (staged,sb) /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op s /\
    expr_val_at cenv cx (TupleT tys) se sa es (ArrayV (TupleV vs)) op s /\
    eval_operand op s = SOME sw /\
    0 < type_memory_size_list tvs /\
    type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs /\
    (flag ==> type_memory_size_list tvs < dimword (:256)) /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    tuple_val_wf vs tvs /\ values_have_types tvs vs /\
    ?t w. eval_operand staged t = SOME w /\
      tuple_in_memory vs tvs (w2n w) t.vs_memory /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!x. staged = Var x ==> not_fresh_at sb x) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (?b sz. b <= w2n w /\
        w2n w + type_memory_size_list tvs <= b + sz /\
        ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
         (?name. local_region cenv es.scopes t name b sz))) /\
      gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all expr_tuple_memory_owned >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `values_have_types tvs vs` by gvs[value_has_type_def] >> simp[] >>
  Cases_on `flag`
  >- (qpat_x_assum `?b sz. _` kall_tac >> gvs[] >>
      `val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n sw) s.vs_memory /\
       val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
       val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) <=
         type_memory_size_list tvs` by
        simp[val_in_memory_def, val_wf_def, val_footprint_def, type_memory_size_def] >>
      drule_all tuple_stage_copy_path >>
      disch_then (qx_choosel_then [`t`, `w`] strip_assume_tac) >>
      qexistsl [`t`, `w`] >> simp[] >>
      conj_tac >- gvs[val_in_memory_def] >>
      qexistsl [`w2n w`, `type_memory_size_list tvs`] >> simp[] >> metis_tac[]) >>
  gvs[comp_return_def] >> qexistsl [`s`, `sw`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  simp[gas_marked_path_def, cj 1 fragGasPathTheory.gas_path_rules] >>
  qexistsl [`b`, `sz`] >> simp[] >> metis_tac[]
QED

Theorem compile_tuple_load_all_no_gas[local]:
  !tys cenv bop off sa elems sb.
    compile_tuple_load_all cenv bop tys off sa = (elems,sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb) /\
    sb.cs_current_bb = sa.cs_current_bb
Proof
  Induct
  >- simp[compile_tuple_load_all_def, comp_return_def, emitted_insts_def] >>
  rpt gen_tac >>
  simp[compile_tuple_load_all_def, comp_bind_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD _ sa = (pv,sm)` >>
  rename1 `compile_load_memory _ _ sm = (v,sh)` >>
  rename1 `compile_tuple_load_all _ _ _ _ sh = (rest_ops,sb)` >>
  `sh.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sh /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sh) /\
   sh.cs_current_bb = sa.cs_current_bb` by
    (Cases_on `is_word_type h` >>
     gvs[compile_load_memory_def, comp_return_def, emit_op_def, fresh_var_def,
         emit_inst_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
         emit_def, emitted_insts_def, mk_inst_def, APPEND_ASSOC,
         DROP_LENGTH_APPEND, DROP_APPEND] >>
     `LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + 1) = 0` by decide_tac >>
     simp[]) >>
  `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb` by
    metis_tac[emitted_insts_append] >>
  simp[] >> metis_tac[APPEND_ASSOC]
QED

Theorem compile_tuple_load_all_typed_path:
  !tys tvs vals tenv cenv bop sa elems sb s w ctx func cx es.
    compile_tuple_load_all cenv bop tys 0 sa = (elems,sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    values_have_types tvs vals /\ tuple_in_memory vals tvs (w2n w) s.vs_memory /\
    w2n w + type_memory_size_list tvs < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
    (!x. MEM (Var x) elems ==> not_fresh_at sb x) /\
    local_ptrs_reserved cenv sb /\
    ?t. stmt_state_rel ctx func cenv cx es t /\
      gas_marked_path F ctx func s 0 (OK t) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t.vs_halted = s.vs_halted /\ t.vs_memory = s.vs_memory /\
      t.vs_allocas = s.vs_allocas /\
      tuple_in_memory vals tvs (w2n w) t.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!name b sz. local_region cenv es.scopes t name b sz =
                   local_region cenv es.scopes s name b sz) /\
      (!i. i < LENGTH tys ==> ?v. eval_operand (EL i elems) t = SOME v /\
        if is_word_type (EL i tys) then
          v = typed_val_to_w256 (EL i tvs) (EL i vals)
        else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_tuple_load_all_typed_run >> strip_tac >>
  drule_all tuple_load_run_lift >> strip_tac >>
  drule compile_tuple_load_all_no_gas >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
         isPREFIX (emitted_insts sa sb)
           (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     qexists_tac `l` >> REFL_TAC) >>
  drule_all tuple_run_inst_seq_gas_path >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    simp[FILTER_EQ_NIL, EVERY_MEM] >>
  `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts +
      LENGTH (emitted_insts sa sb)` by metis_tac[LENGTH_APPEND] >>
  simp[gas_marked_path_def] >> strip_tac >>
  qexists `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  asm_rewrite_tac[] >> simp[same_blocks_def] >>
  conj_tac >- (rpt strip_tac >> gvs[lookup_var_def]) >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH tys ==> _`
    (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  qexists `v` >> Cases_on `EL i elems` >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem tuple_assignment_prefix_path:
  !ctx func cenv cx es1 tys tvs vs sa su sl ss op staged elems sv flag.
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    0 < type_memory_size_list tvs /\
    expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op sv /\
    expr_val_at cenv cx (TupleT tys) sa su es1 (ArrayV (TupleV vs)) op sv /\
    (!x. op = Var x ==> not_fresh_at su x) /\
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op) su = (staged,sl) /\
    (flag ==> type_memory_size_list tvs < dimword (:256)) /\
    compile_tuple_load_all cenv staged tys 0 sl = (elems,ss) /\
    cs_extends su sl /\ cs_extends sl ss /\
    fn_has_code su sl func /\ fn_has_code sl ss func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv su /\
    stmt_state_rel ctx func cenv cx es1 sv /\ ~sv.vs_halted /\
    sv.vs_current_bb = su.cs_current_bb /\
    sv.vs_inst_idx = LENGTH su.cs_current_insts ==>
    LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at ss x) elems /\
    local_ptrs_reserved cenv ss /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
    ?t (w:256 word) b sz. stmt_state_rel ctx func cenv cx es1 t /\ ~t.vs_halted /\
      t.vs_current_bb = ss.cs_current_bb /\
      t.vs_inst_idx = LENGTH ss.cs_current_insts /\
      tuple_in_memory vs tvs (w2n w) t.vs_memory /\ b <= w2n w /\
      w2n w + type_memory_size_list tvs <= b + sz /\
      ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
       (?name. local_region cenv es1.scopes t name b sz)) /\
      w2n w + type_memory_size_list tvs < dimword (:256) /\
      (!i. i < LENGTH tys ==> ?v. eval_operand (EL i elems) t = SOME v /\
        if is_word_type (EL i tys) then
          v = typed_val_to_w256 (EL i tvs) (EL i vs)
        else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs))) /\
      (!x v. not_fresh_at su x /\ lookup_var x sv = SOME v ==>
         lookup_var x t = SOME v) /\
      (!aid entry. FLOOKUP sv.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry) /\
      gas_marked_path F ctx func sv 0 (OK t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) tys tvs` by
    (irule evaluate_types_LIST_REL >>
     qpat_assum `evaluate_type _ (TupleT tys) = _` mp_tac >>
     simp_tac (srw_ss()) [evaluate_type_def, LET_THM, AllCaseEqs()] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  `type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs` by
    (irule type_memory_bytes_tuple_list >> first_assum ACCEPT_TAC) >>
  `?sw. eval_operand op sv = SOME sw` by metis_tac[expr_val_rel_def] >>
  drule_all optional_tuple_stage_path >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t w. _`
    (qx_choosel_then [`st`, `w`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?b sz. _`
    (qx_choosel_then [`b`, `sz`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `(if flag then _ else _) su = _`
    (assume_tac o REWRITE_RULE [GSYM optional_tuple_stage_code]) >>
  drule tuple_stage_grows >> strip_tac >>
  `local_ptrs_reserved cenv sl` by
    (irule local_ptrs_reserved_next_var >> qexists `su` >> simp[]) >>
  `w2n w + type_memory_size_list tvs < dimword (:256)` by
    (drule_all tuple_container_bound >> decide_tac) >>
  drule_all compile_tuple_load_all_typed_path >> strip_tac >>
  `EVERY (\op. !x. op = Var x ==> not_fresh_at ss x) elems` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  asm_rewrite_tac[] >> qexistsl [`t`, `w`, `b`, `sz`] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sl x` by
        (irule not_fresh_at_mono >> qexists `su` >> fs[cs_extends_def]) >>
      simp[]) >>
  `gas_marked_path F ctx func sv (0 + 0) (OK t)` by
    (irule gas_marked_path_then >> qexists `st` >> simp[]) >> gvs[]
QED
