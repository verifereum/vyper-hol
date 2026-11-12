(* Compound internal returns at their physical expression endpoint. *)
Theory internalReturnCompoundEndpointMem
Ancestors
  internalReturnValueEndpointMem externalReturnNormalizedMem
  internalReturnBytestringMem intCallReturnWidenMem incompatibleReturnLayout
  valueEncodingTyping exprOperandVar exprSimProps stmtSimReturn
  loweringPosts exprLoweringProps fragExecMem typedMemoryCopy
  loweringStateRelDefs venomExecSemantics venomState vyperState

Theorem compound_return_post_type:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  type_widens_to (get_tenv cx) (expr_type e) ty /\
  ~is_word_type ty /\ ~is_bytestring_type ty ==>
  post_value_type ce e = lowered_value_type ce e
Proof
  strip_tac >>
  Cases_on `lowered_value_type ce e = expr_type e`
  >- metis_tac[post_value_type_lowered] >>
  `~is_bytestring_type (expr_type e)` by
    metis_tac[type_widens_from_bytestring] >>
  `well_typed_expr env e` by fs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >>
  drule incompatible_return_layout_intcall >>
  disch_then (qspec_then `e` mp_tac) >> simp[] >> strip_tac >>
  gvs[post_value_type_def, vyperASTTheory.expr_type_def]
QED

Theorem internal_return_compound_suffix_mem:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (INL v, ee') /\
  type_widens_to (get_tenv cx) (expr_type e) ty /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  lower_value compile_expr ce ty e sa = (op,sm) /\
  local_ptrs_reserved ce sa /\
  compile_internal_return ce (SOME op) (Var rpc) 0 ty
    (lowered_value_type ce e) elems (SOME (Var bp)) sm = ((),sb) /\
  ce.ce_imm_alloca = NONE /\
  ce.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  ce.ce_return_buf = SOME (PtrVar (Var bp) bsz) /\
  ret_pc_ok ce sm t /\ return_buf_frame (SOME (bw,type_memory_size tv)) ce sm t /\
  expr_post ctx func ce cx e es sa sm s0 ee v op t /\
  (!sty stv. post_value_type ce e = sty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    value_has_type stv v /\ ~is_bytestring_type sty ==>
    expr_store_bound cx sty v op t /\
    (~is_word_type sty ==> ?sw. eval_operand op t = SOME sw /\
      (type_memory_size stv = 0 \/
       w2n sw + type_memory_size stv <= t.vs_alloca_next) /\
      w2n sw + type_memory_size stv < dimword (:256))) /\
  (!stv sw. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    eval_operand op t = SOME sw ==>
    regions_disjoint (w2n sw) (type_memory_size stv) (w2n bw) (type_memory_size tv)) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  type_memory_bytes ce ty = type_memory_size tv /\
  w2n bw + type_memory_size tv + 64 < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)) ==>
  frag_exec_mem ctx sm sb (\s. s = t) (\s. F)
    (intret_mem_q func ce cx tv bw v (ee with scopes := []))
Proof
  strip_tac >>
  `post_value_type ce e = lowered_value_type ce e` by
    (irule compound_return_post_type >> metis_tac[]) >>
  drule_all return_value_physical_typed >> strip_tac >>
  `value_has_type tv v` by
    (drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> simp[]) >>
  `~is_bytestring_type (lowered_value_type ce e)` by
    metis_tac[type_widens_from_bytestring] >>
  `!x. op = Var x ==> not_fresh_at sm x` by
    metis_tac[compile_lower_value_var] >>
  `not_fresh_at sm rpc /\ not_fresh_at sm bp /\
   (?pc. eval_operand (Var rpc) t = SOME pc) /\
   eval_operand (Var bp) t = SOME bw /\
   w2n bw + type_memory_size tv <= t.vs_alloca_next` by
    gvs[ret_pc_ok_def, return_buf_frame_def, eval_operand_def] >>
  `val_wf stv v /\ val_wf tv v` by metis_tac[value_has_type_val_wf] >>
  drule_at (Pat `compile_internal_return _ _ _ _ _ _ _ _ _ = _`)
    compile_internal_return_memory_widen_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `ee`, `tv`, `stv`, `v`, `bw`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then (irule o MATCH_MP frag_exec_mem_weaken) >> simp[] >>
  conj_tac >- (
    fs[expr_post_def, stmt_state_rel_def] >>
    conj_tac >- (irule state_rel_scopes_nil >> first_assum ACCEPT_TAC) >>
    reverse conj_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
    irule immutable_alloca_sep_fields >> qexistsl_tac [`t`, `ee`] >>
    simp[local_region_def, lookup_scopes_def]) >>
  conj_tac >- fs[expr_post_def] >>
  qpat_x_assum `!sty stv. _`
    (qspecl_then [`lowered_value_type ce e`, `stv`] mp_tac) >>
  simp[] >> strip_tac >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]) >>
  strip_tac >>
  `~is_word_type (lowered_value_type ce e)` by
    metis_tac[externalNormalizePremisesTheory.normalize_return_source_kinds] >>
  qpat_x_assum `~is_word_type _ ==> _` mp_tac >> simp[] >> strip_tac >>
  qexists_tac `sw` >> simp[] >>
  first_x_assum drule_all >> simp[regions_disjoint_def]
QED
