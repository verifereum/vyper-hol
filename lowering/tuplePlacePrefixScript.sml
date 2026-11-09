(* Optional staging and loading share their execution and certificate endpoint. *)
Theory tuplePlacePrefix
Ancestors
  tuplePlaceRhsCert tuplePlaceStage tuplePlaceLoad tupleTypedLoad tupleStageProps
  tupleAssignPrefix stmtSimAssignTuple exprLoweringProps compileEnv loweringPosts
  valueEncoding valueEncodingProofs vyperValue stmtLowering fragGasPath fragGasSeq
  fragGasMode vyperTyping vyperTypeABI emitHelper
Libs monadsyntax

Theorem tuple_place_optional_stage_path[local]:
  !ctx func cenv cx es flag tys ltys ltvs vs sa su sl staged op s sw.
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_size_list ltvs);
          emit_void MCOPY [buf.buf_operand; op; Lit (n2w (type_memory_size_list ltvs))];
          comp_return buf.buf_operand od
     else comp_return op) su = (staged,sl) /\
    tuple_in_memory vs ltvs (w2n sw) s.vs_memory /\ tuple_val_wf vs ltvs /\
    w2n sw + type_memory_size_list ltvs < dimword (:256) /\
    tuple_place_snapshot cenv cx es sa.cs_next_id su.cs_next_id tys ltys ltvs sw s /\
    sa.cs_next_id <= su.cs_next_id /\
    fn_has_code su sl func /\ local_ptrs_reserved cenv su /\
    (!x. op = Var x ==> not_fresh_at su x) /\
    eval_operand op s = SOME sw /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
    s.vs_inst_idx = LENGTH su.cs_current_insts ==>
    ?t w. eval_operand staged t = SOME w /\
      tuple_in_memory vs ltvs (w2n w) t.vs_memory /\
      w2n w + type_memory_size_list ltvs < dimword (:256) /\
      tuple_place_snapshot cenv cx es sa.cs_next_id sl.cs_next_id tys ltys ltvs w t /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!x. staged = Var x ==> not_fresh_at sl x) /\
      ~t.vs_halted /\ t.vs_current_bb = sl.cs_current_bb /\
      t.vs_inst_idx = LENGTH sl.cs_current_insts /\
      gas_marked_path F ctx func s 0 (OK t)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `flag`
  >- (gvs[] >>
      `val_in_memory (TupleTV ltvs) (ArrayV (TupleV vs)) (w2n sw) s.vs_memory /\
       val_wf (TupleTV ltvs) (ArrayV (TupleV vs)) /\
       val_footprint (TupleTV ltvs) (ArrayV (TupleV vs)) <= type_memory_size_list ltvs` by
        simp[val_in_memory_def, val_wf_def, val_footprint_def, type_memory_size_def] >>
      `type_memory_size_list ltvs < dimword (:256)` by decide_tac >>
      drule_all tuple_place_stage_snapshot_path >>
      disch_then (qspecl_then [`tys`, `ltys`]
        (qx_choosel_then [`t`, `w`] strip_assume_tac)) >>
      `w2n w + type_memory_size_list ltvs < dimword (:256)` by
        (irule tuple_container_bound >>
         goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
         disj1_tac >> qexists `su.cs_next_id` >> simp[]) >>
      qexistsl [`t`, `w`] >> gvs[val_in_memory_def]) >>
  gvs[comp_return_def] >> qexistsl [`s`, `sw`] >> simp[] >>
  simp[gas_marked_path_def, cj 1 fragGasPathTheory.gas_path_rules]
QED

Theorem tuple_place_assignment_prefix_path:
  !ctx func cenv cx es es1 tys ltys ltvs vs sa su sl ss op staged elems sv s0 e.
    expr_type e = TupleT tys /\ lowered_value_type cenv e = TupleT ltys /\
    value_has_type (TupleTV ltvs) (ArrayV (TupleV vs)) /\
    evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) ltys ltvs /\
    expr_post ctx func cenv cx e es sa su s0 es1 (ArrayV (TupleV vs)) op sv /\
    (!x. op = Var x ==> not_fresh_at su x) /\ sa.cs_next_id <= su.cs_next_id /\
    (if is_memory_view e /\ EXISTS (\t. ~is_word_type t) ltys /\
        0 < type_memory_size_list ltvs then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT ltys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT ltys)))];
          comp_return buf.buf_operand od
     else comp_return op) su = (staged,sl) /\
    compile_tuple_load_all cenv staged ltys 0 sl = (elems,ss) /\
    cs_extends sl ss /\ fn_has_code su sl func /\ fn_has_code sl ss func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv su /\
    ~sv.vs_halted /\ sv.vs_current_bb = su.cs_current_bb /\
    sv.vs_inst_idx = LENGTH su.cs_current_insts ==>
    LENGTH elems = LENGTH ltys /\ EVERY (\op. ?x. op = Var x) elems /\
    (!x. MEM (Var x) elems ==> not_fresh_at ss x) /\
    local_ptrs_reserved cenv ss /\ values_have_types ltvs vs /\ tuple_val_wf vs ltvs /\
    ?t w. stmt_state_rel ctx func cenv cx es1 t /\ ~t.vs_halted /\
      t.vs_current_bb = ss.cs_current_bb /\
      t.vs_inst_idx = LENGTH ss.cs_current_insts /\
      tuple_place_snapshot cenv cx es1 sa.cs_next_id ss.cs_next_id tys ltys ltvs w t /\
      tuple_in_memory vs ltvs (w2n w) t.vs_memory /\
      (!i. i < LENGTH ltys ==> ?v. eval_operand (EL i elems) t = SOME v /\
        if is_word_type (EL i ltys) then
          v = typed_val_to_w256 (EL i ltvs) (EL i vs)
        else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i ltvs))) /\
      (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x sv) /\
      (!aid entry. FLOOKUP sv.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      gas_marked_path F ctx func sv 0 (OK t)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all tuple_place_rhs_certificate >> strip_tac >>
  `values_have_types ltvs vs` by gvs[value_has_type_def] >>
  `LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) ltys ltvs` by
    (irule evaluate_types_LIST_REL >>
     qpat_assum `evaluate_type _ (TupleT ltys) = _` mp_tac >>
     simp_tac (srw_ss()) [evaluate_type_def, LET_THM, AllCaseEqs()] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  `type_memory_bytes cenv (TupleT ltys) = type_memory_size_list ltvs` by
    (irule type_memory_bytes_tuple_list >> first_assum ACCEPT_TAC) >>
  `w2n w + type_memory_size_list ltvs < dimword (:256)` by
    (Cases_on `type_memory_size_list ltvs = 0`
     >- simp[wordsTheory.w2n_lt] >>
     `0 < type_memory_size_list ltvs` by decide_tac >>
     drule_all expr_tuple_memory_owned >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_x_assum `?b sz. _` (qx_choosel_then [`b`, `sz`]
       (map_every assume_tac o CONJUNCTS)) >>
     drule_all tuple_container_bound >> decide_tac) >>
  qmatch_asmsub_abbrev_tac `if flag then _ else _` >>
  `cs_extends su sl /\ su.cs_next_var <= sl.cs_next_var` by
    (irule tuple_stage_grows >>
     qexistsl [`flag`, `op`, `staged`, `type_memory_size_list ltvs`] >>
     Cases_on `flag` >>
     gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  `local_ptrs_reserved cenv sl` by
    (irule local_ptrs_reserved_next_var >> qexists `su` >> simp[]) >>
  fs[] >> drule tuple_place_optional_stage_path >>
  disch_then (drule_at (Pat `tuple_place_snapshot _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> disch_then (qspec_then `vs` mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`st`, `sw`] strip_assume_tac) >>
  drule tuple_place_load_snapshot_path >>
  disch_then (drule_at (Pat `tuple_place_snapshot _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> disch_then (qspecl_then [`vs`, `get_tenv cx`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[] >> qexistsl [`t`, `sw`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sl x` by gvs[not_fresh_at_def] >> simp[]) >>
  `gas_marked_path F ctx func sv (0 + 0) (OK t)` suffices_by simp[] >>
  irule gas_marked_path_then >> qexists `st` >> simp[]
QED
