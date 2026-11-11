(* Pointer-safe internal return suffixes. *)
Theory internalReturnStackPtr
Ancestors
  stmtSimReturn fragExecPtr bodyPtrDefs ptrSafeRun ptrDiscipline
  fragExec venomInst venomState venomExecSemantics
  emitHelper emitHelperProps finite_map list rich_list memLocDefs contextCodegenRel codegenRel
  assignTuplePtrLoadStep logAbiPrefixPtr fragGasPathPtr stateFrame
  stmtLowering exprLoweringProps freshWrites words arithmetic compileEnv

Theorem ret_values_frag_ptr:
  !cx ctx PG sa sb id ops rpc vals pc P Q R.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id RET (ops ++ [Var rpc]) []] /\
    (!G tn s. P G tn s ==>
      eval_operands ops s = SOME vals /\ lookup_var rpc s = SOME pc /\
      EVERY (\op. op_taint tn op = {}) (ops ++ [Var rpc]) /\
      stor_taint_ok cx tn s /\
      R (G,tn) (IntRet <| iret_values := vals; iret_adopt_fmp := NONE |> s)) ==>
    frag_exec_ptr cx ctx PG sa sb P Q R
Proof
  rpt gen_tac >> strip_tac >> simp[frag_exec_ptr_def] >> rpt strip_tac >>
  disj2_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id RET (ops ++ [Var rpc]) [])` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum drule >> strip_tac >>
  `step_inst_base (mk_inst id RET (ops ++ [Var rpc]) []) s =
    IntRet <| iret_values := vals; iret_adopt_fmp := NONE |> s` by
    (irule step_ret_values >> simp[]) >>
  `step_inst 0 ctx (mk_inst id RET (ops ++ [Var rpc]) []) s =
    IntRet <| iret_values := vals; iret_adopt_fmp := NONE |> s` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  qexists_tac `0` >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => fs[GSYM th]) >>
  simp[run_from_def, Once exec_block_def, ghost_run_def,
       Once ghost_block_def, exit_result_def] >>
  conj_tac >- simp[Once exec_block_def] >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def, ptr_safe_step_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       allocas_from_def, mk_inst_def, EVERY_MEM] >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem compile_load_tuple_elements_path_ptr:
  !tys cenv src off sa elems sb s w G tn D ctx func PG.
    compile_load_tuple_elements cenv (Var src) tys off sa = (elems,sb) /\
    fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    not_fresh_at sa src /\ lookup_var src s = SOME w /\
    (!i. i < LENGTH tys ==>
      ptr_covers G tn src s
        (off + SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) + 32) /\
      w2n w + off + SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) + 32 <=
        dimword (:256) /\
      (!j. w2n w + off + SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) <= j /\
           j < w2n w + off + SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) + 32
           ==> j NOTIN tn.t_mem)) ==>
    ?t G' tn'.
      gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      eval_operands elems t = SOME (tuple_words cenv w tys off s.vs_memory) /\
      EVERY (\op. op_taint tn' op = {}) elems /\
      (!x. MEM (Var x) elems ==> not_fresh_at sb x) /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_call_ctx = s.vs_call_ctx /\
      state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!p. not_fresh_at sa p ==>
        lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
        op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  Induct
  >- (rpt strip_tac >> gvs[compile_load_tuple_elements_def, comp_return_def] >>
      qexistsl_tac [`s`, `G`, `tn`] >>
      simp[tuple_words_def, eval_operands_def] >>
      irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_load_tuple_elements _ _ _ _ _ = _` mp_tac >>
  simp[compile_load_tuple_elements_def, comp_bind_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD _ sa = (pv,sm)` >>
  rename1 `emit_op MLOAD _ sm = (v,sh)` >>
  rename1 `compile_load_tuple_elements _ _ _ _ sh = (rest,sf)` >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `cs_extends sm sh /\ sm.cs_next_var <= sh.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `cs_extends sh sf` by metis_tac[compile_load_tuple_elements_extends] >>
  `fn_has_code sa sm func /\ fn_has_code sm sh func /\ fn_has_code sh sf func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  qpat_assum `!i. i < SUC _ ==> _` (qspec_then `0` mp_tac) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  `op_taint tn (Var src) = {} /\ ?site. FLOOKUP G src = SOME site` by
    fs[ptr_covers_def] >>
  drule_all emit_add_member_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `lookup_var out t = SOME (w + n2w off)` >>
  `ptr_covers G' tn' out t 32` by
    (irule ptr_covers_offset_transport >>
     conj_tac >- simp[] >>
     qexistsl_tac [`G`, `off`, `src`, `s`, `tn`, `w`] >> simp[] >> decide_tac) >>
  `w2n (w + n2w off) = w2n w + off` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  `!j. w2n (w + n2w off) <= j /\ j < w2n (w + n2w off) + 32
       ==> j NOTIN tn'.t_mem` by (simp[] >> metis_tac[ADD_COMM]) >>
  qpat_x_assum `pv = Var out` SUBST_ALL_TAC >>
  drule_all emit_mload_member_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `lookup_var loaded u = SOME (mload _ t)` >>
  `not_fresh_at sm src /\ not_fresh_at sh src` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `lookup_var src u = SOME w /\ FLOOKUP G'' src = FLOOKUP G src /\
   op_taint tn'' (Var src) = op_taint tn (Var src)` by metis_tac[] >>
  `!i. i < LENGTH tys ==>
     ptr_covers G'' tn'' src u
       (off + type_memory_bytes cenv h + SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) + 32) /\
     w2n w + off + type_memory_bytes cenv h + SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) + 32 <= dimword (:256) /\
     (!j. w2n w + off + type_memory_bytes cenv h + SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) <= j /\
          j < w2n w + off + type_memory_bytes cenv h + SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) + 32
          ==> j NOTIN tn''.t_mem)` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `SUC i` mp_tac) >>
     simp_tac (srw_ss()) [TAKE_def, ADD_ASSOC] >>
     (impl_tac >- simp[]) >> strip_tac >>
     conj_tac >-
       (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
        qexistsl_tac [`G`, `s`, `tn`] >> simp[ADD_ASSOC]) >> simp[]) >>
  qpat_x_assum `!cenv src off sa elems sb s w G tn D ctx func PG. _`
    (drule_at_then (Pat `compile_load_tuple_elements _ _ _ _ _ = _`) mp_tac) >>
  disch_then (qspecl_then [`u`, `w`, `G''`, `tn''`, `D`, `ctx`, `func`, `PG`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac [] >>
     qpat_x_assum `!i. i < LENGTH tys ==> _` mp_tac >>
     qpat_x_assum `tn''.t_mem = _` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `tn'.t_mem = _` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [AC ADD_ASSOC ADD_COMM] >> metis_tac[])) >>
  strip_tac >>
  rename1 `gas_path_ptr D 0 ctx func PG G'' tn'' u 0 Gf tnf (OK fin)` >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK fin)` by
    metis_tac[gas_path_ptr_then, ADD_0] >>
  `lookup_var loaded fin = lookup_var loaded u /\
   op_taint tnf (Var loaded) = {}` by metis_tac[] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p /\ not_fresh_at sh p` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `!p. not_fresh_at sa p ==>
    lookup_var p fin = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p)` by metis_tac[] >>
  qexistsl_tac [`fin`, `Gf`, `tnf`] >>
  simp[] >>
  fs[state_frame_def, venom_state_component_equality] >>
  conj_tac >-
    (simp[eval_operands_def, eval_operand_def, tuple_words_def,
          mload_def, valueEncodingTheory.mem_word_at_def]) >>
  `sh.cs_next_var <= sf.cs_next_var` by
    (drule compile_load_tuple_elements_run >>
     disch_then (qspecl_then [`u`, `w`] mp_tac) >>
     simp[eval_operand_def] >> metis_tac[]) >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED
