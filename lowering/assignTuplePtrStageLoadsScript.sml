(* Staging-to-load composition. This is separate from assignTuplePtrPrefix,
   whose instruction boundaries are already ancestors of Stage. *)
Theory assignTuplePtrStageLoads
Ancestors
  assignTuplePtrStage assignTuplePtrLoads tupleTypedLoad tupleStageProps stmtSimAssignTuple
  exprSimProps exprLoweringProps compileEnv bodyPtrDefs venomState stmtFragPtr fragGasPathPtr
  valueEncoding vyperTyping vyperTypeABI vyperValue loweringPosts list words arithmetic
Libs
  monadsyntax

Theorem staged_tuple_load_resources_ptr:
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  lowered_value_type cenv e = TupleT tys /\
  type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs /\
  0 < type_memory_size_list tvs /\ eval_operand staged st = SOME w /\
  ptr_val_ok cx (TupleT tys) (ArrayV (TupleV vs)) staged G tn st /\
  ptr_buf_ok cenv e staged G st ==>
  (?p base cap. staged = Var p /\ op_taint tn staged = {} /\
    FLOOKUP G p = SOME (base,cap) /\ base <= w2n w /\
    w2n w + type_memory_size_list tvs <= base+cap) /\
  (!m. mem_agree_outside tn.t_mem st.vs_memory m ==>
       tuple_in_memory vs tvs (w2n w) m)
Proof
  strip_tac >>
  `op_taint tn staged = {} /\
   ptr_mem_ok cx (TupleT tys) (ArrayV (TupleV vs)) staged G tn st` by
    fs[ptr_val_ok_def, is_word_type_def] >>
  conj_tac
  >- (qpat_x_assum `ptr_buf_ok _ _ _ _ _` mp_tac >>
      simp[ptr_buf_ok_def] >> strip_tac >>
      `type_memory_bytes cenv (lowered_value_type cenv e) <> 0` by simp[] >>
      first_x_assum drule_all >> simp[ADD_COMM]) >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_mem_ok_def] >>
  strip_tac >> fs[val_in_memory_def]
QED

Theorem tuple_assignment_prefix_path_ptr:
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs /\
  0 < type_memory_size_list tvs /\
  expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op sv /\
  expr_val_at cenv cx (TupleT tys) sa su es (ArrayV (TupleV vs)) op sv /\
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
  stmt_state_rel ctx func cenv cx es sv /\ ~sv.vs_halted /\
  sv.vs_current_bb = su.cs_current_bb /\
  sv.vs_inst_idx = LENGTH su.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ expr_type e = TupleT tys /\
  lowered_value_type cenv e = TupleT tys /\
  ptr_val_ok cx (TupleT tys) (ArrayV (TupleV vs)) op G tn sv /\
  ptr_buf_ok cenv e op G sv /\ ghost_inv d cenv cx es G tn sv /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) ==>
  LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at ss x) elems /\
  local_ptrs_reserved cenv ss /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
  ?t (w:256 word) b sz p base cap G' tn'.
    stmt_state_rel ctx func cenv cx es t /\ ghost_inv d cenv cx es G' tn' t /\
    ~t.vs_halted /\ t.vs_current_bb = ss.cs_current_bb /\
    t.vs_inst_idx = LENGTH ss.cs_current_insts /\
    eval_operand staged t = SOME w /\ staged = Var p /\
    FLOOKUP G' p = SOME (base,cap) /\ op_taint tn' staged = {} /\
    base <= w2n w /\ w2n w + type_memory_size_list tvs <= base + cap /\
    tuple_in_memory vs tvs (w2n w) t.vs_memory /\
    (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
         tuple_in_memory vs tvs (w2n w) m) /\
    b <= w2n w /\ w2n w + type_memory_size_list tvs <= b + sz /\
    ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region cenv es.scopes t name b sz)) /\
    w2n w + type_memory_size_list tvs < dimword (:256) /\
    (!i. i < LENGTH tys ==>
      ptr_val_ok cx (EL i tys) (EL i vs) (EL i elems) G' tn' t /\
      (?u. eval_operand (EL i elems) t = SOME u /\
        (if is_word_type (EL i tys) then u = typed_val_to_w256 (EL i tvs) (EL i vs)
         else w2n u = w2n w + SUM (MAP type_memory_size (TAKE i tvs)))) /\
      (~is_word_type (EL i tys) ==>
        ?q. EL i elems = Var q /\ FLOOKUP G' q = SOME (base,cap))) /\
    (!x. not_fresh_at su x ==>
      lookup_var x t = lookup_var x sv /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!aid entry. FLOOKUP sv.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    gas_path_ptr D 0 ctx func PG G tn sv 0 G' tn' (OK t) /\
    (flag ==> ?freshbase.
      FLOOKUP t.vs_allocas su.cs_next_id = SOME (freshbase,type_memory_size_list tvs) /\
      w2n w = freshbase /\
      !name entry q size u. lookup_scopes name es.scopes = SOME entry /\
        FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) size) /\
        lookup_var q t = SOME u ==>
        w2n u + val_footprint entry.type entry.value <= freshbase \/
        freshbase + type_memory_size_list tvs <= w2n u)
Proof
  strip_tac >>
  `LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs` by
    (irule evaluate_types_LIST_REL >>
     qpat_assum `evaluate_type _ (TupleT tys) = _` mp_tac >>
     simp_tac (srw_ss()) [evaluate_type_def, LET_THM, AllCaseEqs()] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  `type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs` by
    metis_tac[type_memory_bytes_tuple_list] >>
  `?sw. eval_operand op sv = SOME sw` by metis_tac[expr_val_rel_def] >>
  drule_all optional_tuple_stage_run_ptr >>
  disch_then (qspecl_then [`D`, `PG`]
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`st`, `w`, `G1`, `tn1`]
        (map_every assume_tac o CONJUNCTS))))) >>
  qpat_x_assum `?b sz. _` (qx_choosel_then [`b`, `sz`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `value_has_type _ _` kall_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` kall_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `(if flag then _ else _) su = _`
    (assume_tac o REWRITE_RULE [GSYM optional_tuple_stage_code]) >>
  drule tuple_stage_grows >> strip_tac >>
  qpat_x_assum `ptr_val_ok _ _ _ op _ _ _` kall_tac >>
  qpat_x_assum `ptr_buf_ok _ _ op _ _` kall_tac >>
  qpat_x_assum `ghost_inv _ _ _ _ G tn sv` kall_tac >>
  suspend "loads"
QED

Resume tuple_assignment_prefix_path_ptr[loads]:
  `local_ptrs_reserved cenv sl` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `su` >> fs[cs_extends_def]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sl x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sl x)` by
    (conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `su` >> fs[cs_extends_def] >> metis_tac[]) >>
  `w2n w + type_memory_size_list tvs < dimword (:256)` by
    (drule_all tuple_container_bound >> decide_tac) >>
  drule_all staged_tuple_load_resources_ptr >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_tuple_load_all_typed_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "transport"
QED

Resume tuple_assignment_prefix_path_ptr[transport]:
  qpat_x_assum `?p base cap. _` strip_assume_tac >>
  gnvs[] >>
  qpat_x_assum `evaluate_type _ _ = _` kall_tac >>
  qpat_x_assum `LIST_REL (\ty tv. type_memory_bytes _ ty = _) _ _` kall_tac >>
  qpat_x_assum `LIST_REL (\ty tv. evaluate_type _ ty = _) _ _` kall_tac >>
  qpat_x_assum `compile_tuple_load_all _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `(if flag then _ else _) su = _` kall_tac >>
  qpat_x_assum `ptr_val_ok _ _ _ _ _ _ st` kall_tac >>
  qpat_x_assum `ptr_buf_ok _ _ _ _ st` kall_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ sv` kall_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ st` kall_tac >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ st` kall_tac >>
  `!x. not_fresh_at su x ==> not_fresh_at sl x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `su` >> simp[]) >>
  `gas_path_ptr D 0 ctx func PG G tn sv 0 G' tn' (OK t)` by
    metis_tac[gas_path_ptr_then, ADD] >>
  simp[] >> qexistsl_tac [`t`, `w`, `b`, `sz`, `b'`, `cap`, `G'`, `tn'`] >>
  simp[] >> suspend "finish"
QED

Resume tuple_assignment_prefix_path_ptr[finish]:
  conj_tac
  >- (fs[eval_operand_def]) >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `not_fresh_at sl q` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `lookup_var q st = SOME u` by metis_tac[] >>
  metis_tac[]
QED

Finalise tuple_assignment_prefix_path_ptr
