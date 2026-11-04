(* The target-independent expression, snapshot and load prefix. *)
Theory tupleAssignPrefix
Ancestors
  tupleStageProps tupleTypedLoad exprSim exprOperandVar exprLoweringProps
  stmtSim localPtrsProps compileEnv loweringSlice fragExec valueEncoding
  vyperValue vyperTyping vyperInterpreter freshWrites list rich_list finite_map
  exprLowering vyperTypeABI stmtSimAssignTuple stmtSimReturn
Libs
  monadsyntax

Theorem tuple_assignment_prefix_run:
  !ctx func cenv cx e es es1 tys tvs vs sa su sl ss op staged elems s0 flag.
    expr_type e = TupleT tys /\
    (do result <- eval_expr cx e; read_result cx result od) es =
      (INL (ArrayV (TupleV vs)),es1) /\
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    0 < type_memory_size_list tvs /\
    expr_sim ctx func cenv cx (TupleT tys) e es /\
    lower_value compile_expr cenv (TupleT tys) e sa = (op,su) /\
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op) su = (staged,sl) /\
    (flag ==> type_memory_size_list tvs < dimword (:256)) /\
    compile_tuple_load_all cenv staged tys 0 sl = (elems,ss) /\
    cs_extends sa su /\ cs_extends su sl /\ cs_extends sl ss /\
    fn_has_code sa su func /\ fn_has_code su sl func /\ fn_has_code sl ss func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
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
      (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
         lookup_var x t = SOME v) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!fuel r. run_from fuel ctx func t = r /\ (!err. r <> Error err) ==>
         ?fuel'. run_from fuel' ctx func s0 = r)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_res_ok (INL (ArrayV (TupleV vs)))` by simp[expr_res_ok_def] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then drule_all >> disch_then (qspec_then `s0` mp_tac) >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `expr_post ctx _ _ _ _ _ _ _ _ _ _ _ sv` >>
  qpat_x_assum `expr_post ctx _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qpat_x_assum `expr_type e = TupleT tys`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  suspend "stage"
QED

Resume tuple_assignment_prefix_run[stage]:
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  qpat_assum `(if flag then _ else _) su = _`
    (assume_tac o REWRITE_RULE [GSYM optional_tuple_stage_code]) >>
  drule tuple_stage_grows >> strip_tac >>
  `!x. op = Var x ==> not_fresh_at su x` by
    metis_tac[compile_lower_value_var] >>
  `LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) tys tvs` by
    (irule evaluate_types_LIST_REL >>
     qpat_assum `evaluate_type _ (TupleT tys) = _` mp_tac >>
     simp_tac (srw_ss()) [evaluate_type_def, LET_THM, AllCaseEqs()] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  `type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs` by
    (irule type_memory_bytes_tuple_list >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved cenv su` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `?sw. eval_operand op sv = SOME sw` by metis_tac[expr_val_rel_def] >>
  drule_all optional_tuple_stage_run >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t w. _`
    (qx_choosel_then [`st`, `w`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?b sz. _`
    (qx_choosel_then [`b`, `sz`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "load"
QED

Resume tuple_assignment_prefix_run[load]:
  `local_ptrs_reserved cenv sl` by
    (irule local_ptrs_reserved_next_var >> qexists `su` >> simp[]) >>
  `w2n w + type_memory_size_list tvs < dimword (:256)` by
    (drule_all tuple_container_bound >> decide_tac) >>
  drule_all compile_tuple_load_all_typed_frag >> strip_tac >>
  suspend "compose"
QED

Resume tuple_assignment_prefix_run[compose]:
  qpat_x_assum `frag_exec _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [frag_exec_def]) >>
  disch_then (qspec_then `func` mp_tac) >> simp[] >> strip_tac >>
  `EVERY (\op. !x. op = Var x ==> not_fresh_at ss x) elems` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  asm_rewrite_tac [] >> qexistsl [`t`, `w`, `b`, `sz`] >>
  asm_rewrite_tac [] >>
  suspend "frames"
QED

Resume tuple_assignment_prefix_run[frames]:
  conj_tac >- decide_tac >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (qpat_x_assum `!i. i < LENGTH tys ==> ?v. _` mp_tac >>
      simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM]) >>
  conj_tac >- suspend "vars" >>
  conj_tac
  >- (qpat_x_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _` mp_tac >>
      qpat_x_assum `!aid entry. FLOOKUP sv.vs_allocas aid = SOME entry ==> _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  ntac 2 (qpat_x_assum
    `!fuel. _ ==> ?fuel'. run_from fuel' ctx func _ = _` mp_tac) >>
  qpat_x_assum `!fuel r. _ ==> ?fuel'. run_from fuel' ctx func _ = r` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]
QED

Resume tuple_assignment_prefix_run[vars]:
  rpt strip_tac >>
  `not_fresh_at su x` by
    (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `not_fresh_at sl x` by
    (irule not_fresh_at_mono >> qexists `su` >> simp[]) >>
  simp[]
QED

Finalise tuple_assignment_prefix_run
