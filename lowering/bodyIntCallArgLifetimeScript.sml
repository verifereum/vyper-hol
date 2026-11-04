(* Deferred internal-call argument interface probes. *)
Theory bodyIntCallArgLifetime
Ancestors
  exprSimAggregateChildren exprSimAggregateSource exprLowering compileEnv vyperEvalPureExpr vyperPureExpr supportedExprs supportedExprForms
  exprReasonOperand exprSimHyps exprOperandVar exprSafeOperand context venomState exprSim
  vyperValue valueEncoding valueEncodingProps valueEncodingProofs vyperTypeEnv vyperTypeInvariants vyperTyping

Theorem compile_multi_vvs_empty:
  compile_multi_vvs cfn cenv [] st = ([],st)
Proof
  simp[compile_multi_vvs_def, comp_return_def]
QED

Theorem compile_stage_intcall_args_empty:
  compile_stage_intcall_args cenv [] flags tys st = ([],st)
Proof
  simp[compile_stage_intcall_args_def, comp_return_def]
QED

Theorem supported_purity_semantic:
  (!tops e. supported_pure_expr tops e ==> pure_expr e) /\
  (!tops es. supported_pure_exprs tops es ==> EVERY pure_expr es) /\
  (!tops fields. supported_pure_fields tops fields ==>
     EVERY pure_expr (MAP SND fields)) /\
  (!tops e. supported_place_expr tops e ==> pure_expr e)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  simp[supported_pure_expr_def, pure_expr_def, SF ETA_ss] >>
  rpt conj_tac >> rpt gen_tac >>
  Cases_on `es` >> simp[supported_builtin_form_def]
QED

Theorem supported_pure_eval_expr_state:
  supported_pure_expr tops e /\ eval_expr cx e es = (res,es') ==>
  es' = es
Proof
  metis_tac[supported_purity_semantic, eval_expr_preserves_state]
QED

(* A compiled operand is already reserved at the next compile boundary.
   The semantic invariant rules out label-valued local pointers. *)
Theorem compile_expr_operand_safe:
  expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
  local_ptrs_reserved cenv sa /\ compile_expr cenv ty e sa = (vv,sb) ==>
  safe_operand sb (vv_operand vv)
Proof
  strip_tac >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_inv_def] >>
  drule_all compile_expr_operand_not_label >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    metis_tac[CONJUNCT1 compiler_compile_var] >>
  Cases_on `vv` >> simp[safe_operand_def, vv_operand_def]
QED

Theorem safe_operand_value_preserved:
  safe_operand sa op /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s = SOME w) /\
  eval_operand op s0 = SOME w ==>
  eval_operand op s = SOME w
Proof
  Cases_on `op` >> simp[safe_operand_def, eval_operand_def] >>
  metis_tac[]
QED

Theorem vv_post_preserves_compiled_operand:
  expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
  local_ptrs_reserved cenv sa /\ compile_expr cenv ty e sa = (vv,sm) /\
  vv_post ctx func cenv cx e' es0 sm sb s0 es' tv vv' s /\
  eval_operand (vv_operand vv) s0 = SOME w ==>
  eval_operand (vv_operand vv) s = SOME w
Proof
  strip_tac >> irule safe_operand_value_preserved >>
  qexists_tac `s0` >> qexists_tac `sm` >> simp[] >>
  conj_tac >- gvs[vv_post_def] >>
  irule compile_expr_operand_safe >> metis_tac[]
QED

(* Word encodings use a full word even when their numeric width is small. *)
Theorem word_type_val_footprint:
  is_word_type t /\ evaluate_type tenv t = SOME tv ==>
  val_footprint tv v = 32
Proof
  Cases_on `t` >> simp[is_word_type_def]
  >- (rename1 `BaseT bt` >> Cases_on `bt`
      >~ [`BytesT bound`] >-
        (Cases_on `bound` >> simp[is_word_type_def, evaluate_type_def] >>
         rpt strip_tac >> gvs[] >> Cases_on `v` >>
         simp[val_footprint_def, type_memory_size_def]) >>
      simp[is_word_type_def, evaluate_type_def] >>
      rpt strip_tac >> gvs[] >> Cases_on `v` >>
      simp[val_footprint_def, type_memory_size_def]) >>
  simp[evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> Cases_on `v` >> simp[val_footprint_def, type_memory_size_def]
QED

Theorem vv_post_old_allocation_window:
  vv_post ctx func cenv cx e es sm sn s0 es' tv vv s /\
  FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sm.cs_next_id /\
  (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
              b + sz <= lb \/ lb + lsz <= b) /\
  b <= off /\ off + len <= b + sz ==>
  mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at b sz s0.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (gvs[vv_post_def] >> metis_tac[]) >>
  drule mem_bytes_at_agree_window >> simp[]
QED

Theorem local_ptrs_rel_dynarray_header:
  local_ptrs_rel func cenv scopes s /\
  local_region cenv scopes s name b sz /\
  lookup_scopes name scopes = SOME entry /\
  entry.value = ArrayV (DynArrayV vs) ==>
  mem_word_at b s.vs_memory = n2w (LENGTH vs)
Proof
  simp[local_region_def] >> rpt strip_tac >>
  gvs[local_ptrs_rel_def] >>
  first_x_assum drule_all >> simp[val_in_memory_def]
QED

Theorem vv_holds_nonmemory_frame:
  vv_holds cenv cx t raw (LocatedValue t' p) es s0 /\
  p.ptr_location <> LocMemory /\
  (!w. eval_operand p.ptr_operand s0 = SOME w ==>
       eval_operand p.ptr_operand s = SOME w) ==>
  vv_holds cenv cx t raw (LocatedValue t' p) es s
Proof
  Cases_on `p.ptr_location` >> simp[vv_holds_def] >> metis_tac[]
QED

Theorem vv_holds_memory_footprint_frame:
  vv_holds cenv cx t raw (LocatedValue t' p) es s0 /\
  p.ptr_location = LocMemory /\
  (!w. eval_operand p.ptr_operand s0 = SOME w ==>
       eval_operand p.ptr_operand s = SOME w) /\
  (!v tv w. read_result cx raw es = (INL v,es) /\
       evaluate_type (get_tenv cx) t = SOME tv /\
       eval_operand p.ptr_operand s0 = SOME w ==>
       val_wf tv v /\
       mem_bytes_at (w2n w) (val_footprint tv v) s0.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory) ==>
  vv_holds cenv cx t raw (LocatedValue t' p) es s
Proof
  strip_tac >> gvs[vv_holds_def] >> gen_tac >> disch_tac >>
  `val_wf tvt v /\
   mem_bytes_at (w2n w) (val_footprint tvt v) s0.vs_memory =
   mem_bytes_at (w2n w) (val_footprint tvt v) s.vs_memory` by metis_tac[] >>
  conj_tac
  >- (irule val_in_memory_footprint_agree >> metis_tac[]) >>
  strip_tac >>
  `val_footprint tvt v = 32` by metis_tac[word_type_val_footprint] >>
  gvs[] >> drule mem_bytes_at_agree_window >> simp[]
QED

Theorem expr_sim_inv_dynarray_entry:
  expr_sim_inv cenv cx env es /\ dynarray_local cenv n /\
  lookup_scopes n es.scopes = SOME entry ==>
  ?vs. entry.value = ArrayV (DynArrayV vs)
Proof
  strip_tac >>
  `env_scopes_consistent env cx es /\ state_well_typed es /\
   (!id ty. FLOOKUP env.var_types id = SOME ty ==>
            cenv.ce_var_type id = SOME ty)` by
    gvs[expr_sim_inv_def, env_consistent_def] >>
  `IS_SOME (FLOOKUP env.var_types n)` by
    (gvs[env_scopes_consistent_def] >> metis_tac[]) >>
  fs[optionTheory.IS_SOME_EXISTS] >>
  `?t m. FLOOKUP env.var_types n = SOME (ArrayT t (Dynamic m)) /\
          evaluate_type (get_tenv cx) (ArrayT t (Dynamic m)) = SOME entry.type` by
    (gvs[dynarray_local_def, dynarray_type_def, env_scopes_consistent_def] >>
     metis_tac[optionTheory.SOME_11]) >>
  `value_has_type entry.type entry.value` by
    (irule (cj 1 scope_well_typed_lookup_scopes) >>
     gvs[state_well_typed_def] >> metis_tac[]) >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  qpat_x_assum `ArrayTV _ _ = entry.type` (fn th => fs[GSYM th]) >>
  Cases_on `entry.value` >> gvs[value_has_type_def] >>
  rename1 `entry.value = ArrayV av` >>
  Cases_on `av` >> gvs[value_has_type_def]
QED

(* Only pointer variables belonging to compiler locals must remain stable. *)
Theorem local_ptrs_rel_same_scopes_dynarray_header:
  expr_sim_inv cenv cx env es /\ dynarray_local cenv n /\
  local_ptrs_rel func cenv es.scopes s0 /\
  local_ptrs_rel func cenv es.scopes s /\
  local_region cenv es.scopes s0 n b sz /\
  (!name p size w.
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) size) /\
     lookup_var p s0 = SOME w ==> lookup_var p s = SOME w) ==>
  mem_word_at b s.vs_memory = mem_word_at b s0.vs_memory
Proof
  strip_tac >>
  `?entry. lookup_scopes n es.scopes = SOME entry` by
    metis_tac[local_region_def] >>
  drule_all expr_sim_inv_dynarray_entry >> strip_tac >>
  `local_region cenv es.scopes s n b sz` by
    (gvs[local_region_def] >> metis_tac[]) >>
  metis_tac[local_ptrs_rel_dynarray_header]
QED

Theorem locals_kept_typed_full_window:
  expr_sim_inv cenv cx env es /\
  local_ptrs_rel func cenv es.scopes s0 /\
  local_ptrs_rel func cenv es.scopes s /\
  locals_kept cenv es s0 s /\
  (!name p size w.
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) size) /\
     lookup_var p s0 = SOME w ==> lookup_var p s = SOME w) /\
  local_region cenv es.scopes s0 n b sz /\
  b <= off /\ off + len <= b + sz ==>
  mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory
Proof
  strip_tac >> Cases_on `dynarray_local cenv n`
  >- (
    `mem_word_at b s.vs_memory = mem_word_at b s0.vs_memory` by
      (irule local_ptrs_rel_same_scopes_dynarray_header >> metis_tac[]) >>
    `mem_bytes_at b 32 s.vs_memory = mem_bytes_at b 32 s0.vs_memory` by
      (irule mload_eq_mem_bytes_at_eq >> gvs[GSYM mem_word_at_eq_mload]) >>
    `mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory` by
      (Cases_on `sz <= 32`
       >- (drule mem_bytes_at_agree_window >> simp[]) >>
       `sz = 32 + (sz - 32)` by decide_tac >>
       `mem_bytes_at (b + 32) (sz - 32) s.vs_memory =
        mem_bytes_at (b + 32) (sz - 32) s0.vs_memory` by
         (gvs[locals_kept_def] >> first_x_assum irule >>
          qexistsl_tac [`b`, `n`, `sz`] >> simp[]) >>
       qpat_x_assum `sz = 32 + (sz - 32)`
         (fn th => once_rewrite_tac[th]) >>
       simp[mem_bytes_at_split_padded]) >>
    drule mem_bytes_at_agree_window >> simp[]) >>
  gvs[locals_kept_def] >> metis_tac[]
QED
