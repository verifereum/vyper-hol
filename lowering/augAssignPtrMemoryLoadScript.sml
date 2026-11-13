(* A clean scalar load at an arbitrary live local path. *)
Theory augAssignPtrMemoryLoad
Ancestors
  bodyPtrPopNestedLiveHandoff bodyPtrPopTargetSimCurrentLocal
  bodyPtrPopTargetDefs bodyPtrDefs bodySimAugPlaceLoad
  assignTuplePtrLoadStep augAssignPtrLoad exprSimSource stmtSimAugAssign
  exprSimHypsDefs exprSimProps exprLoweringProps loweringStateRelDefs
  vyperTypeInvariants vyperState vyperInterpreter ptrDiscipline
  emitHelper emitHelperProps compileEnv stmtFragPtr venomState finite_map
  valueEncoding valueEncodingProps words loweringPosts vyperTypeEnv

Theorem target_memory_word_inputs_ptr:
  target_post ctx func cenv cx es sa sb s0 mid
    (PlaceR (MemoryPlace id path)) (Type ty) (hdr,loc,pt) s /\
  ghost_inv d cenv cx mid G tn s /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) (hdr,loc,pt) G tn s /\
  expr_sim_inv cenv cx env mid /\ FLOOKUP env.var_types id = SOME root_ty /\
  lookup_scopes id mid.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL cur /\
  word_value_type ty ==>
  ?out a tv.
    hdr = Var out /\ not_fresh_at sb out /\
    lookup_var out s = SOME a /\ ptr_covers G tn out s 32 /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv cur /\
    mload (w2n a) s = typed_val_to_w256 tv cur /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  drule_all stmtSimAugAssignTheory.expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME root_ty` by
    (gvs[expr_sim_inv_def] >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) root_ty = SOME entry.type` by metis_tac[] >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (irule vyperTypeEnvTheory.scope_well_typed_lookup_scopes >>
     fs[expr_sim_inv_def, state_well_typed_def] >> metis_tac[]) >>
  drule_all pop_memory_target_ptr_handoff >> strip_tac >> gvs[] >>
  `ISL (evaluate_subscripts entry.type entry.value path)` by simp[] >>
  drule_all target_current_local_path_ptr >> strip_tac >> gvs[] >>
  `type_memory_size tv = 32` by metis_tac[word_value_type_memory_size] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `(!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv cur (w2n (b + n2w k)) mem)` by metis_tac[] >>
  drule_all robust_typed_word_clean >> strip_tac >>
  gvs[] >>
  `mem_agree_outside tn.t_mem s.vs_memory s.vs_memory` by
    simp[mem_agree_outside_def] >>
  metis_tac[mem_word_at_eq_mload]
QED

Theorem augassign_memory_load_clean_frame_ptr:
  target_post ctx func cenv cx es sa sm s0 mid
    (PlaceR (MemoryPlace id path)) (Type ty) (hdr,loc,pt) s /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) (hdr,loc,pt) G tn s /\
  expr_sim_inv cenv cx env mid /\ FLOOKUP env.var_types id = SOME root_ty /\
  read_place cx (MemoryPlace id path) mid = (INL cur,mid) /\
  (!entry. lookup_scopes id mid.scopes = SOME entry ==>
     ISL (evaluate_subscripts entry.type entry.value path)) /\
  word_value_type ty /\ ghost_inv d cenv cx mid G tn s /\
  emit_op MLOAD [hdr] sm = (Var out,sb) /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sm /\ ret_pc_ok cenv sm s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?H tm t tv.
    t.vs_allocas = s.vs_allocas /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK t) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv cur /\
    lookup_var out t = SOME (typed_val_to_w256 tv cur) /\
    op_taint tm (Var out) = {} /\ op_prov H (Var out) = NONE /\
    stmt_state_rel ctx func cenv cx mid t /\ ghost_inv d cenv cx mid H tm t /\
    ghost_kept cenv mid sm G tn s H tm /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ not_fresh_at sb out /\
    (!rp. not_fresh_at sm rp ==>
      lookup_var rp t = lookup_var rp s /\ FLOOKUP H rp = FLOOKUP G rp /\
      op_taint tm (Var rp) = op_taint tn (Var rp))
Proof
  strip_tac >>
  drule_all stmtSimAugAssignTheory.expr_sim_inv_local >> strip_tac >>
  `evaluate_subscripts entry.type entry.value path = INL cur` by
    (`ISL (evaluate_subscripts entry.type entry.value path)` by metis_tac[] >>
     Cases_on `evaluate_subscripts entry.type entry.value path` >>
     gvs[read_place_def, get_scopes_def, bind_def, lift_option_type_def,
         lift_sum_def, return_def, read_memory_path_def]) >>
  drule_all target_memory_word_inputs_ptr >> strip_tac >> gvs[] >>
  drule_all emit_mload_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx mid s` by
    (gvs[target_post_def] >> metis_tac[]) >>
  `sb.cs_next_var = sm.cs_next_var + 1 /\
   out = STRCAT "%" (toString sm.cs_next_var)` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[]) >>
  `sf.vs_allocas = s.vs_allocas` by simp[venomStateTheory.update_var_def] >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[IgnAsm `sf = _`] >>
  conj_tac
  >- (gvs[] >> simp[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_update_var >> simp[stmt_state_rel_inst_idx] >>
      irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
  conj_tac
  >- (irule ghost_inv_load_frame >>
      qexistsl_tac [`G`, `s`, `sm`, `tn`] >> simp[] >> gvs[ret_pc_ok_def]) >>
  conj_tac >- simp[ghost_kept_def] >>
  conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  simp[not_fresh_at_def]
QED

Theorem augassign_memory_load_clean_ptr:
  target_post ctx func cenv cx es sa sm s0 mid
    (PlaceR (MemoryPlace id path)) (Type ty) (hdr,loc,pt) s /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) (hdr,loc,pt) G tn s /\
  expr_sim_inv cenv cx env mid /\ FLOOKUP env.var_types id = SOME root_ty /\
  read_place cx (MemoryPlace id path) mid = (INL cur,mid) /\
  (!entry. lookup_scopes id mid.scopes = SOME entry ==>
     ISL (evaluate_subscripts entry.type entry.value path)) /\
  word_value_type ty /\ ghost_inv d cenv cx mid G tn s /\
  emit_op MLOAD [hdr] sm = (Var out,sb) /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sm /\ ret_pc_ok cenv sm s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?H tm t tv.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK t) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv cur /\
    lookup_var out t = SOME (typed_val_to_w256 tv cur) /\
    op_taint tm (Var out) = {} /\ op_prov H (Var out) = NONE /\
    stmt_state_rel ctx func cenv cx mid t /\ ghost_inv d cenv cx mid H tm t /\
    ghost_kept cenv mid sm G tn s H tm /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ not_fresh_at sb out /\
    (!rp. not_fresh_at sm rp ==>
      lookup_var rp t = lookup_var rp s /\ FLOOKUP H rp = FLOOKUP G rp /\
      op_taint tm (Var rp) = op_taint tn (Var rp))
Proof
  strip_tac >> drule_all augassign_memory_load_clean_frame_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`H`, `tm`, `t`, `tv`] >> simp[]
QED
