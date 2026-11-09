Theory bodyPtrIfExpWordMemory
Ancestors
  bodyPtrDefs representationCleanPtr exprSimProps loweringPosts
  valueEncoding vyperAST vyperTyping vyperValue compileEnv
  exprSimPtrProps exprSimUnwrapProps exprLoweringProps context emitHelper
  appendStorageGhostPtr fragGasPathPtr venomState finite_map freshWrites

(* Runtime type evaluation alone does not type the returned value.  NoneV
   has a vacuous robust memory representation even at a word type.  This
   probe is not a counterexample to the frozen IfExp statement: its actual
   expression precondition may supply the missing value_has_type fact. *)
Theorem word_memory_untyped_none_probe[local]:
  is_word_type (BaseT BoolT) /\ val_wf (BaseTV BoolT) NoneV /\
  (!mem. val_in_memory (BaseTV BoolT) NoneV 0 mem) /\
  ~value_has_type (BaseTV BoolT) NoneV /\
  (!mem. mem_agree_outside {0} m mem ==>
         val_in_memory (BaseTV BoolT) NoneV 0 mem) /\
  ~(!i. 0 <= i /\ i < 32 ==> i NOTIN ({0}:num set))
Proof
  EVAL_TAC >> simp[]
QED

Theorem ifexp_typed_word_memory_clean:
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tv /\
  value_has_type tv v /\ ptr_mem_ok cx t v op G tn s /\
  eval_operand op s = SOME w ==>
  !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at (w2n w) mem = typed_val_to_w256 tv v` by
    (rpt strip_tac >> irule val_in_memory_word_type >>
     gvs[ptr_mem_ok_def] >> metis_tac[]) >>
  drule robust_mem_word_at_clean >> simp[]
QED

Theorem ifexp_typed_word_layout:
  is_word_type t /\ evaluate_type tenv t = SOME tv /\
  value_has_type tv v ==>
  val_footprint tv v = 32 /\ val_store_size tv v = 32
Proof
  strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT BoolT \/ t = BaseT AddressT \/ t = BaseT DecimalT \/
   (?m. t = BaseT (BytesT (Fixed m)) /\ m <= 32) \/ (?n. t = FlagT n)` by
    (Cases_on `t` >> fs[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_word_type_def]) >>
  gvs[evaluate_type_def, AllCaseEqs()] >> Cases_on `v` >>
  gvs[value_has_type_def, val_footprint_def, val_store_size_def,
      type_memory_size_def]
QED

Theorem ifexp_typed_word_memory_coverage:
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tv /\
  value_has_type tv v /\ ptr_mem_ok cx t v op G tn s /\
  eval_operand op s = SOME w ==>
  ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
           b <= w2n w /\ w2n w + 32 <= b + sz
Proof
  strip_tac >> drule_all ifexp_typed_word_layout >> strip_tac >>
  gvs[ptr_mem_ok_def] >> metis_tac[]
QED

Theorem ifexp_located_word_memory_clean:
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tv /\
  value_has_type tv v /\
  ptr_vv_ok cx t raw (LocatedValue t' p) es G tn s /\
  p.ptr_location = LocMemory /\ read_result cx raw es = (INL v,es) /\
  eval_operand p.ptr_operand s = SOME w ==>
  !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem
Proof
  strip_tac >> gvs[ptr_vv_ok_def] >>
  metis_tac[ifexp_typed_word_memory_clean]
QED

Theorem ifexp_located_word_memory_coverage:
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tv /\
  value_has_type tv v /\
  ptr_vv_ok cx t raw (LocatedValue t' p) es G tn s /\
  p.ptr_location = LocMemory /\ read_result cx raw es = (INL v,es) /\
  eval_operand p.ptr_operand s = SOME w ==>
  ?x b sz. p.ptr_operand = Var x /\ FLOOKUP G x = SOME (b,sz) /\
           b <= w2n w /\ w2n w + 32 <= b + sz
Proof
  strip_tac >> gvs[ptr_vv_ok_def] >>
  irule ifexp_typed_word_memory_coverage >> metis_tac[]
QED

Theorem ifexp_memory_word_suffix:
  is_word_type (expr_type e) /\
  compile_ptr_load F cenv.ce_imm_alloca p.ptr_location p.ptr_operand sm = (op,sb) /\
  vv_post ctx fn cenv cx e es sa sm s0 ee raw
    (LocatedValue (expr_type e) p) s /\
  read_result cx raw ee = (INL v,ee) /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue (expr_type e) p) ee G tn s /\
  ghost_inv d cenv cx ee G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\ value_has_type tvt v /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ p.ptr_location = LocMemory ==>
  ?u G1 tn1. gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK u) /\
    expr_post ctx fn cenv cx e es sa sb s0 ee v op u /\
    ptr_val_ok cx (expr_type e) v op G1 tn1 u /\
    ghost_inv d cenv cx ee G1 tn1 u /\
    ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `?w. eval_operand p.ptr_operand s = SOME w` by
    (gvs[vv_post_def, vv_at_def]) >>
  drule_all ifexp_located_word_memory_coverage >> strip_tac >>
  `!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem` by
    metis_tac[ifexp_located_word_memory_clean] >>
  `ptr_covers G tn x s 32` by
    (gvs[ptr_covers_def, ptr_vv_ok_def, eval_operand_def]) >>
  `emit_op MLOAD [Var x] sm = (op,sb)` by
    gvs[compile_ptr_load_def] >>
  `lookup_var x s = SOME w` by gvs[eval_operand_def] >>
  drule_all emit_mload_ptr_path >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK u)` >>
  qexistsl [`u`,`G'`,`tn'`] >> simp[] >>
  conj_tac >- suspend "post" >>
  conj_tac >- (gvs[] >> simp[ptr_val_ok_def]) >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "kept" >>
  gvs[Abbr `u`, update_var_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def, comp_return_def]
QED

Resume ifexp_memory_word_suffix[post]:
  `!z. not_fresh_at sa z ==> not_fresh_at sm z` by
    metis_tac[not_fresh_at_mono] >>
  `not_local_ptr cenv ee.scopes out` by
    (gvs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  `stmt_state_rel ctx fn cenv cx ee u` by
    (simp[Abbr `u`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> gvs[vv_post_def]) >>
  `vv_post ctx fn cenv cx e es sa sm s0 ee (Value v)
     (LocatedValue (expr_type e) p) s` by
    (drule vv_post_read_result >> disch_then (fn th => fs[th])) >>
  irule expr_post_of_vv_post_load >>
  goal_assum (drule_at Any) >>
  simp[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE] >>
  conj_tac
  >- (`ptr_mem_ok cx (expr_type e) v p.ptr_operand G tn s` by
        gvs[ptr_vv_ok_def] >>
      `val_in_memory tvt v (w2n w) s.vs_memory` by
        (gvs[ptr_mem_ok_def] >>
         first_x_assum irule >> simp[mem_agree_outside_def]) >>
      drule_all val_in_memory_word_type >>
      simp[mload_def, mem_word_at_def]) >>
  qexistsl [`p`,`s`,`sm`,`expr_type e`] >> simp[] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Resume ifexp_memory_word_suffix[ghost]:
  irule ghost_inv_fresh_frame >> goal_assum (drule_at Any) >>
  qexistsl [`G`,`ee`,`s`,`sa`] >>
  simp[Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[not_fresh_at_mono]
QED

Resume ifexp_memory_word_suffix[kept]:
  irule ghost_kept_suffix_compose >>
  goal_assum (drule_at Any) >>
  qexistsl [`G`,`tn`] >> simp[] >> metis_tac[]
QED

Finalise ifexp_memory_word_suffix
