(* Successful staged-memory continuation for compatible local destinations. *)
Theory assignTuplePtrLocalSuffix
Ancestors
  assignTuplePtrLocalOpen assignTuplePtrLocalSequence assignTuplePtrLoadedCoverage assignTuplePtrStageLoads
  assignTuplePtrSourceGas tupleAssignPrefix tupleStageProps tupleTargetStoreProps
  exprOperandVar exprSimProps exprLoweringProps compileEnv bodyPtrDefs stmtFragPtr
  fragGasPathPtr loweringPosts stmtSimDefs stmtSimProps tupleAssignParts
  vyperInterpreter vyperState vyperValue vyperTyping vyperTypeDefaults valueEncoding
  stmtLowering stmtSimReturn vyperTypeABI list rich_list finite_map words arithmetic
Libs
  monadsyntax

Theorem assign_tuple_locals_suffix_open_ptr:
  expr_post ctx func cenv cx e es sa su s0 ee v op sv /\
  sv.vs_current_bb = su.cs_current_bb /\
  sv.vs_inst_idx = LENGTH su.cs_current_insts /\ ~sv.vs_halted /\
  ee.gas_obs = [] /\ value_has_type (TupleTV tvs) v /\
  gs <> [] /\ LENGTH gs = LENGTH tys /\ expr_type e = TupleT tys /\
  lowered_value_type cenv e = TupleT tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  (!i. i < LENGTH tys ==>
    evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
    type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
    0 < type_memory_size (EL i tvs)) /\
  (!i. i < LENGTH gs ==>
    ?id p sz vt entry. EL i gs = BaseTarget (NameTarget id) /\
      lookup_scopes id ee.scopes = SOME entry /\ entry.assignable /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ cenv.ce_var_type id = SOME vt /\
      (is_word_type vt = is_word_type (EL i tys)) /\
      (if is_word_type (EL i tys) then
         store_lays_out (EL i tvs) entry.type
           (EL i (case v of ArrayV (TupleV vs) => vs | _ => [])) else
        (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
        evaluate_type (get_tenv cx) vt = SOME entry.type /\
        value_has_type entry.type (EL i (case v of ArrayV (TupleV vs) => vs | _ => [])) /\
        type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
        type_memory_bytes cenv vt = type_memory_size entry.type /\
        0 < type_memory_size entry.type /\ type_memory_size entry.type + 64 < dimword(:256))) /\
  lower_value compile_expr cenv (TupleT tys) e sa = (op,su) /\
  (if flag then
     do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
        emit_void MCOPY [buf.buf_operand; op;
          Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
        comp_return buf.buf_operand od
   else comp_return op) su = (staged,sl) /\
  (flag ==> type_memory_size_list tvs < dimword (:256)) /\
  compile_tuple_load_all cenv staged tys 0 sl = (elems,ss) /\
  compile_tuple_store_all cenv tys gs elems ss = ((),sf) /\
  ~block_is_terminated sf /\
  cs_extends sa su /\ cs_extends su sl /\ cs_extends sl ss /\
  sa.cs_next_var <= su.cs_next_var /\ su.cs_next_var <= sl.cs_next_var /\
  sl.cs_next_var <= ss.cs_next_var /\
  fn_has_code su sl func /\ fn_has_code sl ss func /\ fn_has_code ss sf func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ ptr_val_ok cx (TupleT tys) v op G tn sv /\
  ptr_buf_ok cenv e op G sv /\ ghost_inv d cenv cx ee G tn sv /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?ee' t G' tn'.
    (!tail. assign_tuple_targets cx (TupleTarget gs) v (ee with gas_obs := tail) =
      (INL (),ee' with gas_obs := tail)) /\
    gas_path_ptr D 0 ctx func PG G tn sv 0 G' tn' (OK t) /\
    stmt_post ctx func cx lctx cenv cenv sa sf s0 (INL ())
      (ee' with gas_obs := []) t /\
    ghost_inv d cenv cx ee' G' tn' t /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all tuple_type_value >> strip_tac >> gvs[] >>
  `LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs` by
    (gvs[evaluate_type_def, AllCaseEqs()] >>
     metis_tac[LIST_REL_LENGTH, values_have_types_length]) >>
  `LIST_REL (tuple_source_target cx ee.scopes) gs tvs` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     simp[tuple_source_target_def] >>
     first_x_assum (qspec_then `n` mp_tac) >> simp[] >> metis_tac[]) >>
  `LIST_REL value_has_type tvs vs` by simp[GSYM values_have_types_LIST_REL] >>
  `~cx.txn.is_static` by fs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
  drule_all assign_tuple_targets_safe >> strip_tac >>
  rename1 `assign_tuple_targets _ _ _ ee = (INL (),ee')` >>
  qpat_assum `assign_tuple_targets _ _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def]) >> strip_tac >>
  suspend "prefix"
QED

Resume assign_tuple_locals_suffix_open_ptr[prefix]:
  `LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs` by
    simp[LIST_REL_EL_EQN] >>
  `tys <> []` by (Cases_on `tys` >> gvs[]) >>
  `0 < type_memory_size_list tvs` by
    (irule tuple_memory_size_positive >> qexistsl_tac [`get_tenv cx`, `tys`] >>
     simp[] >> rpt strip_tac >> disj2_tac >>
     qexistsl_tac [`EL i tys`, `EL i tvs`] >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at su x` by metis_tac[compile_lower_value_var] >>
  `local_ptrs_reserved cenv su` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[cs_extends_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at su x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x)` by
    metis_tac[] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `post_value_type cenv e = expr_type e` by simp[post_value_type_lowered] >>
  `expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op sv /\
   expr_val_at cenv cx (TupleT tys) sa su ee (ArrayV (TupleV vs)) op sv` by
    metis_tac[] >>
  drule_all tuple_assignment_prefix_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?t w b sz p base cap G' tn'. _`
    (qx_choosel_then [`st`, `w`, `b`, `sz`, `p`, `sitebase`, `cap`, `G1`, `tn1`]
      (map_every assume_tac o CONJUNCTS)) >>
  suspend "stores"
QED

Resume assign_tuple_locals_suffix_open_ptr[stores]:
  qpat_assum `!i. i < LENGTH tys ==> ptr_val_ok _ _ _ _ _ _ _ /\ _`
    (mp_then Any mp_tac tuple_loaded_operands_coverage_ptr) >>
  simp[] >> disch_tac >>
  `EVERY (\op. ?x. op = Var x /\ not_fresh_at ss x) elems` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x)` by
    (conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `sl` >> simp[] >> irule not_fresh_at_mono >>
     qexists_tac `su` >> simp[] >> metis_tac[]) >>
  `!i. i < LENGTH gs ==>
    ptr_val_ok cx (EL i tys) (EL i vs) (EL i elems) G1 tn1 st /\
    ?u. eval_operand (EL i elems) st = SOME u /\
      (if is_word_type (EL i tys) then u = typed_val_to_w256 (EL i tvs) (EL i vs)
       else w2n u = w2n w + SUM (MAP type_memory_size (TAKE i tvs))) /\
      (!q. ~is_word_type (EL i tys) /\ EL i elems = Var q ==>
        ptr_covers G1 tn1 q st (type_memory_size (EL i tvs)))` by simp[] >>
  `!i. i < LENGTH tys ==> evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by simp[] >>
  `LENGTH elems = LENGTH vs` by simp[] >>
  `!i. i < LENGTH gs ==>
    ?id p sz vt entry. EL i gs = BaseTarget (NameTarget id) /\
      lookup_scopes id ee.scopes = SOME entry /\ entry.assignable /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ cenv.ce_var_type id = SOME vt /\
      (is_word_type vt = is_word_type (EL i tys)) /\
      (if is_word_type (EL i tys) then store_lays_out (EL i tvs) entry.type (EL i vs) else
        (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
        evaluate_type (get_tenv cx) vt = SOME entry.type /\ value_has_type entry.type (EL i vs) /\
        type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
        type_memory_bytes cenv vt = type_memory_size entry.type /\
        0 < type_memory_size entry.type /\ type_memory_size entry.type + 64 < dimword(:256))` by simp[] >>
  drule_all tuple_local_store_sequence_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?t G' tn'. _`
    (qx_choosel_then [`t`, `G2`, `tn2`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`ee'`, `t`, `G2`, `tn2`] >> conj_tac
  >- (drule_all assign_tuple_targets_success_gas_tail_ptr >> simp[]) >>
  conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  suspend "post"
QED

Resume assign_tuple_locals_suffix_open_ptr[post]:
  `!x. not_fresh_at sa x ==> not_fresh_at ss x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sl` >> simp[] >>
     irule not_fresh_at_mono >> qexists_tac `su` >> simp[]) >>
  reverse conj_tac >- metis_tac[] >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl]
QED

Finalise assign_tuple_locals_suffix_open_ptr

Theorem tuple_load_all_arity_ptr[local]:
  !tys cenv base off sa elems sb.
    compile_tuple_load_all cenv base tys off sa = (elems,sb) ==>
    LENGTH elems = LENGTH tys
Proof
  Induct >- simp[compile_tuple_load_all_def, comp_return_def] >>
  rpt gen_tac >>
  simp[compile_tuple_load_all_def, comp_bind_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >>
  first_x_assum drule >> gvs[]
QED

Theorem assign_tuple_locals_suffix_ptr:
  expr_post ctx func cenv cx e es sa su s0 ee v op sv /\
  sv.vs_current_bb = su.cs_current_bb /\
  sv.vs_inst_idx = LENGTH su.cs_current_insts /\ ~sv.vs_halted /\
  ee.gas_obs = [] /\ value_has_type (TupleTV tvs) v /\
  gs <> [] /\ LENGTH gs = LENGTH tys /\ expr_type e = TupleT tys /\
  lowered_value_type cenv e = TupleT tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  (!i. i < LENGTH tys ==>
    evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
    type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
    0 < type_memory_size (EL i tvs)) /\
  (!i. i < LENGTH gs ==>
    ?id p sz vt entry. EL i gs = BaseTarget (NameTarget id) /\
      lookup_scopes id ee.scopes = SOME entry /\ entry.assignable /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ cenv.ce_var_type id = SOME vt /\
      (is_word_type vt = is_word_type (EL i tys)) /\
      (if is_word_type (EL i tys) then
         store_lays_out (EL i tvs) entry.type
           (EL i (case v of ArrayV (TupleV vs) => vs | _ => [])) else
        (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
        evaluate_type (get_tenv cx) vt = SOME entry.type /\
        value_has_type entry.type (EL i (case v of ArrayV (TupleV vs) => vs | _ => [])) /\
        type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
        type_memory_bytes cenv vt = type_memory_size entry.type /\
        0 < type_memory_size entry.type /\ type_memory_size entry.type + 64 < dimword(:256))) /\
  lower_value compile_expr cenv (TupleT tys) e sa = (op,su) /\
  (if flag then
     do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
        emit_void MCOPY [buf.buf_operand; op;
          Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
        comp_return buf.buf_operand od
   else comp_return op) su = (staged,sl) /\
  (flag ==> type_memory_size_list tvs < dimword (:256)) /\
  compile_tuple_load_all cenv staged tys 0 sl = (elems,ss) /\
  compile_tuple_store_all cenv tys gs elems ss = ((),sf) /\
  cs_extends sa su /\ cs_extends su sl /\ cs_extends sl ss /\
  sa.cs_next_var <= su.cs_next_var /\ su.cs_next_var <= sl.cs_next_var /\
  sl.cs_next_var <= ss.cs_next_var /\
  fn_has_code su sl func /\ fn_has_code sl ss func /\ fn_has_code ss sf func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ ptr_val_ok cx (TupleT tys) v op G tn sv /\
  ptr_buf_ok cenv e op G sv /\ ghost_inv d cenv cx ee G tn sv /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?ee' t G' tn'.
    (!tail. assign_tuple_targets cx (TupleTarget gs) v (ee with gas_obs := tail) =
      (INL (),ee' with gas_obs := tail)) /\
    gas_path_ptr D 0 ctx func PG G tn sv 0 G' tn' (OK t) /\
    stmt_post ctx func cx lctx cenv cenv sa sf s0 (INL ())
      (ee' with gas_obs := []) t /\
    ghost_inv d cenv cx ee' G' tn' t /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH elems = LENGTH tys` by metis_tac[tuple_load_all_arity_ptr] >>
  `~block_is_terminated sf` by
    (irule compatible_local_tuple_store_open_ptr >>
     qexistsl_tac [`cenv`, `gs`, `elems`, `ss`, `tys`] >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!i. i < LENGTH gs ==> ?id p sz vt entry. _`
       (qspec_then `i` mp_tac) >> simp[] >>
     strip_tac >> Cases_on `is_word_type (EL i tys)` >> gvs[] >> metis_tac[]) >>
  drule_all assign_tuple_locals_suffix_open_ptr >> simp[]
QED
