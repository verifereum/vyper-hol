(* Load the physical tuple before evaluating any destination.  A widened
   call owns this buffer, so every pending element stays clear of locals. *)
Theory tupleWidenedPrefixPtr
Ancestors
  assignTuplePtrStageLoads assignTuplePtrLoadedCoverage assignTuplePtrLoads
  tupleTypedLoad tupleStageProps stmtLoweringMono exprLoweringProps
  loweringPosts bodyPtrDefs valueEncoding valueEncodingDefs valueEncodingTyping
  vyperTyping vyperTypeABI vyperValue stmtSimDefs stmtSimProps compileEnv
  venomState list finite_map words arithmetic

Theorem tuple_widened_owned_prefix_ptr:
  expr_post ctx func cenv cx e es sa su s0 ee
    (ArrayV (TupleV vs)) op sv /\
  lowered_value_type cenv e = TupleT tys /\
  post_value_type cenv e = TupleT tys /\
  post_value_type cenv e <> expr_type e /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs /\
  0 < type_memory_size_list tvs /\
  compile_tuple_load_all cenv op tys 0 su = (elems,ss) /\
  (!p. op = Var p ==> not_fresh_at su p) /\
  local_ptrs_reserved cenv su /\ fn_has_code su ss func /\ ~ctx_has_dalloca ctx /\
  ~sv.vs_halted /\ sv.vs_current_bb = su.cs_current_bb /\
  sv.vs_inst_idx = LENGTH su.cs_current_insts /\
  ptr_val_ok cx (TupleT tys) (ArrayV (TupleV vs)) op G tn sv /\
  ptr_buf_ok cenv e op G sv /\ ghost_inv d cenv cx ee G tn sv /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) ==>
  LENGTH elems = LENGTH tys /\
  EVERY (\op. ?p. op = Var p /\ not_fresh_at ss p) elems /\
  local_ptrs_reserved cenv ss /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
  ?t G' tn' w aid b sz.
    gas_path_ptr D 0 ctx func PG G tn sv 0 G' tn' (OK t) /\
    stmt_state_rel ctx func cenv cx ee t /\ ghost_inv d cenv cx ee G' tn' t /\
    ~t.vs_halted /\ t.vs_current_bb = ss.cs_current_bb /\
    t.vs_inst_idx = LENGTH ss.cs_current_insts /\
    eval_operand op t = SOME w /\
    FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ aid < ss.cs_next_id /\
    b <= w2n w /\ w2n w + type_memory_size_list tvs <= b+sz /\
    (!name lb len. local_region cenv ee.scopes t name lb len ==>
      b+sz <= lb \/ lb+len <= b) /\
    (!i. i < LENGTH tys ==>
      ptr_val_ok cx (EL i tys) (EL i vs) (EL i elems) G' tn' t /\
      ?u. eval_operand (EL i elems) t = SOME u /\
        (if is_word_type (EL i tys) then u = typed_val_to_w256 (EL i tvs) (EL i vs)
         else w2n u = w2n w + SUM (MAP type_memory_size (TAKE i tvs))) /\
        (!p. ~is_word_type (EL i tys) /\ EL i elems = Var p ==>
          ptr_covers G' tn' p t (type_memory_size (EL i tvs)))) /\
    (!p. not_fresh_at su p ==>
      lookup_var p t = lookup_var p sv /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    t.vs_memory = sv.vs_memory /\ t.vs_allocas = sv.vs_allocas /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx ee sv /\
   expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op sv /\
   expr_val_own cenv cx (TupleT tys) sa su ee (ArrayV (TupleV vs)) op sv` by
    fs[expr_post_def] >>
  `?w. eval_operand op sv = SOME w` by metis_tac[expr_val_rel_def] >>
  `values_have_types tvs vs /\ tuple_val_wf vs tvs` by
    (imp_res_tac value_has_type_val_wf >> fs[value_has_type_def, val_wf_def]) >>
  `LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs` by
    (irule evaluate_types_LIST_REL >>
     qpat_assum `evaluate_type _ (TupleT tys) = _` mp_tac >>
     simp_tac (srw_ss()) [evaluate_type_def, LET_THM, AllCaseEqs()] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  `type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs` by
    metis_tac[type_memory_bytes_tuple_list] >>
  drule_all staged_tuple_load_resources_ptr >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?own_aid own_base own_size.
    FLOOKUP sv.vs_allocas own_aid = SOME (own_base,own_size) /\
    own_aid < su.cs_next_id /\ own_base <= w2n w /\
    w2n w + type_memory_size_list tvs <= own_base+own_size /\
    (!name lb len. local_region cenv ee.scopes sv name lb len ==>
      own_base+own_size <= lb \/ lb+len <= own_base)` by
    (qpat_x_assum `expr_val_own _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_val_own_def]) >>
     disch_then (qspec_then `TupleTV tvs` mp_tac) >>
     simp[is_word_type_def, val_footprint_def, type_memory_size_def, eval_operand_def] >>
     metis_tac[]) >>
  `own_base+own_size < dimword (:256)` by
    (irule tuple_container_bound >>
     qexistsl_tac [`cenv`, `ctx`, `cx`, `ee`, `func`, `sv`] >> simp[] >> metis_tac[]) >>
  `w2n w + type_memory_size_list tvs < dimword (:256)` by decide_tac >>
  drule_all compile_tuple_load_all_typed_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?p b cap t G' tn'. _`
    (qx_choosel_then [`load_root`, `load_base`, `load_cap`, `t`, `H`, `un`]
      (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?p b cap. _` strip_assume_tac >> gnvs[] >>
  `ci_mono su ss` by metis_tac[cj 4 ci_mono_list_helpers, pairTheory.SND] >>
  `own_aid < ss.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  `LENGTH tys = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  `!i p. i < LENGTH tys /\ ~is_word_type (EL i tys) /\
      EL i elems = Var p ==>
      ptr_covers H un p t (type_memory_size (EL i tvs))` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i. i < _ ==> ptr_val_ok _ _ _ _ _ _ _ /\ _`
       (qspec_then `i` mp_tac) >>
     (impl_tac >- fs[]) >> strip_tac >>
     qpat_x_assum `!i. i < _ ==> ptr_val_ok _ _ _ _ _ _ _ /\ _` kall_tac >>
     rename1 `eval_operand (EL i elems) t = SOME member_word` >>
     `w2n member_word = w2n w + SUM (MAP type_memory_size (TAKE i tvs))` by
       (qpat_x_assum `~is_word_type _` (fn neg =>
          qpat_x_assum `if is_word_type _ then _ else _`
            (mp_tac o SIMP_RULE std_ss [neg])) >> decide_tac) >>
     qpat_x_assum `if is_word_type _ then _ else _` kall_tac >>
     `FLOOKUP H p = SOME (load_base,load_cap)` by
       (qpat_x_assum `~is_word_type _` (fn neg =>
          qpat_x_assum `EL i elems = Var p` (fn veq =>
            qpat_x_assum `~is_word_type _ ==> ?q. _`
              (mp_tac o SIMP_RULE (srw_ss()) [neg,veq]))) >>
        simp_tac std_ss []) >>
     `w2n w + type_memory_size_list tvs <= load_base+load_cap` by decide_tac >>
     drule_all tuple_loaded_member_coverage_ptr >> disch_then ACCEPT_TAC) >>
  `EVERY (\op. ?p. op = Var p /\ not_fresh_at ss p) elems` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  simp[] >> qexistsl_tac [`t`, `H`, `un`, `w`, `own_aid`, `own_base`, `own_size`] >>
  fs[eval_operand_def] >> metis_tac[]
QED
