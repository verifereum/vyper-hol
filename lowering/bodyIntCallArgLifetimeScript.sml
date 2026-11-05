(* Deferred internal-call argument interface probes. *)
Theory bodyIntCallArgLifetime
Ancestors
  exprSimAggregateChildren exprSimAggregateSource exprLowering compileEnv vyperEvalPureExpr vyperPureExpr supportedExprs supportedExprForms
  bodyIntCallStorageFrame loweringPosts bodyIntCallSourceFrame exprReasonOperand exprSimHyps exprOperandVar exprSafeOperand context venomState exprSim exprLoweringProps fragExec
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
  (p.ptr_location = LocStorage ==> contract_storage s = contract_storage s0) /\
  (p.ptr_location = LocTransient ==> contract_transient s = contract_transient s0) /\
  (!w. eval_operand p.ptr_operand s0 = SOME w ==>
       eval_operand p.ptr_operand s = SOME w) ==>
  vv_holds cenv cx t raw (LocatedValue t' p) es s
Proof
  Cases_on `p.ptr_location` >>
  simp[vv_holds_def, storage_holds_def] >> metis_tac[]
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

(* A covered footprint survives a later successful expression. *)
Theorem vv_post_covered_window:
  expr_sim_inv cenv cx env es /\
  local_ptrs_rel func cenv es.scopes s0 /\
  local_ptrs_rel func cenv es.scopes s /\
  local_ptrs_reserved cenv sm /\
  vv_post ctx func cenv cx e es sm sn s0 es' tv vv s /\
  ((?aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
      aid < sm.cs_next_id /\ b <= off /\ off + len <= b + sz /\
      (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
                  b + sz <= lb \/ lb + lsz <= b)) \/
   (?n b sz. local_region cenv es.scopes s0 n b sz /\
      b <= off /\ off + len <= b + sz) \/ len = 0) ==>
  mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory
Proof
  strip_tac
  >- (irule vv_post_old_allocation_window >> metis_tac[])
  >- (`!name p size w.
         FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) size) /\
         lookup_var p s0 = SOME w ==> lookup_var p s = SOME w` by
        (gvs[vv_post_def, local_ptrs_reserved_def] >> metis_tac[]) >>
      `locals_kept cenv es s0 s` by gvs[vv_post_def] >>
      metis_tac[locals_kept_typed_full_window]) >>
  simp[mem_bytes_at_def]
QED

Theorem vv_post_preserves_located_memory:
  expr_sim_inv cenv cx env es /\
  local_ptrs_rel func cenv es.scopes s0 /\
  local_ptrs_rel func cenv es.scopes s /\
  local_ptrs_reserved cenv sm /\
  vv_post ctx func cenv cx e es sm sn s0 es' tv vv s /\
  vv_holds cenv cx t raw (LocatedValue t' p) es s0 /\
  vv_at cenv cx t sa sm es raw (LocatedValue t' p) s0 /\
  p.ptr_location = LocMemory /\
  (!w. eval_operand p.ptr_operand s0 = SOME w ==>
       eval_operand p.ptr_operand s = SOME w) ==>
  vv_holds cenv cx t raw (LocatedValue t' p) es s
Proof
  strip_tac >> irule vv_holds_memory_footprint_frame >>
  conj_tac >- simp[] >>
  qexists_tac `s0` >> simp[] >>
  map_every qx_gen_tac [`v`, `tvt`, `w`] >> strip_tac >>
  gvs[vv_at_def] >> sym_tac >>
  irule vv_post_covered_window >> metis_tac[]
QED

Theorem vv_post_preserves_stack_value:
  expr_sim_inv cenv cx env es /\
  local_ptrs_rel func cenv es.scopes s0 /\
  local_ptrs_rel func cenv es.scopes s /\
  local_ptrs_reserved cenv sm /\
  vv_post ctx func cenv cx e es sm sn s0 es' tv vv s /\
  vv_holds cenv cx t raw (StackValue t' op) es s0 /\
  vv_at cenv cx t sa sm es raw (StackValue t' op) s0 /\
  (!w. eval_operand op s0 = SOME w ==> eval_operand op s = SOME w) ==>
  vv_holds cenv cx t raw (StackValue t' op) es s
Proof
  strip_tac >> gvs[vv_holds_def, expr_val_rel_def] >>
  gen_tac >> strip_tac >> Cases_on `is_word_type t`
  >- gvs[] >>
  gvs[vv_at_def, expr_val_at_def] >>
  (irule val_in_memory_footprint_agree >>
   conj_tac >- simp[] >>
   qexists_tac `s0.vs_memory` >> simp[] >>
   sym_tac >> irule vv_post_covered_window >> metis_tac[])
QED

Theorem vv_post_preserves_held_value:
  expr_sim_inv cenv cx env es /\
  local_ptrs_rel func cenv es.scopes s0 /\
  local_ptrs_rel func cenv es.scopes s /\
  local_ptrs_reserved cenv sm /\
  vv_post ctx func cenv cx e es sm sn s0 es' tv vv s /\
  contract_storage s = contract_storage s0 /\
  contract_transient s = contract_transient s0 /\
  vv_holds cenv cx t raw held es s0 /\
  vv_at cenv cx t sa sm es raw held s0 /\
  (!w. eval_operand (vv_operand held) s0 = SOME w ==>
       eval_operand (vv_operand held) s = SOME w) ==>
  vv_holds cenv cx t raw held es s
Proof
  Cases_on `held` >> simp[vv_operand_def] >> strip_tac
  >- (irule vv_post_preserves_stack_value >> metis_tac[]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (irule vv_post_preserves_located_memory >> metis_tac[]) >>
  irule vv_holds_nonmemory_frame >> metis_tac[]
QED

(* The first raw result is still held only after the second expression has
   succeeded; no read_results or materialisation is inserted between them. *)
Theorem two_vv_posts_deferred_holds:
  expr_sim_inv cenv cx env es /\ well_typed_expr env e1 /\
  supported_pure_expr tops e2 /\
  eval_expr cx e2 es = (INL raw2,es2) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  compile_expr cenv ty1 e1 sa = (vv1,sm) /\
  vv_post ctx func cenv cx e1 es0 sa sm start es raw1 vv1 s0 /\
  vv_post ctx func cenv cx e2 es sm sn s0 es2 raw2 vv2 s /\
  contract_storage s = contract_storage s0 /\
  contract_transient s = contract_transient s0 ==>
  vv_holds cenv cx (expr_type e1) raw1 vv1 es2 s
Proof
  strip_tac >>
  `es2 = es with outcomes := es2.outcomes` by
    metis_tac[supported_eval_expr_outcomes] >>
  `es2.scopes = es.scopes` by
    fs[vyperStateTheory.evaluation_state_component_equality] >>
  `!w. eval_operand (vv_operand vv1) s0 = SOME w ==>
       eval_operand (vv_operand vv1) s = SOME w` by
    (rpt strip_tac >> irule vv_post_preserves_compiled_operand >> metis_tac[]) >>
  `local_ptrs_rel func cenv es.scopes s0 /\
   local_ptrs_rel func cenv es.scopes s /\
   vv_holds cenv cx (expr_type e1) raw1 vv1 es s0 /\
   vv_at cenv cx (expr_type e1) sa sm es raw1 vv1 s0` by
    gvs[vv_post_def, stmt_state_rel_def, state_rel_def] >>
  `vv_holds cenv cx (expr_type e1) raw1 vv1 es s` by
    (irule vv_post_preserves_held_value >> metis_tac[]) >>
  metis_tac[vv_holds_outcomes]
QED

Theorem expr_vv_sim_success_frag:
  expr_vv_sim ctx func cenv cx ty e es /\
  compile_expr cenv ty e sa = (vv,sb) /\
  eval_expr cx e es = (INL raw,es') /\ expr_vv_res_ok (INL raw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = start /\ stmt_state_rel ctx func cenv cx es s)
    (vv_post ctx func cenv cx e es sa sb start es' raw vv)
    (\r. F)
Proof
  strip_tac >> gvs[expr_vv_sim_def] >>
  first_x_assum drule_all >>
  disch_then (qspec_then `start` mp_tac) >>
  `expr_exit (INL raw) = (\r. F)` by simp[FUN_EQ_THM] >>
  simp[SF ETA_ss]
QED

Theorem two_expr_vv_success_deferred:
  expr_sim_inv cenv cx env es1 /\ well_typed_expr env e1 /\
  supported_pure_expr tops e2 /\
  expr_vv_sim ctx func cenv cx (expr_type e1) e1 es /\
  expr_vv_sim ctx func cenv cx (expr_type e2) e2 es1 /\
  eval_expr cx e1 es = (INL raw1,es1) /\
  eval_expr cx e2 es1 = (INL raw2,es2) /\
  expr_vv_res_ok (INL raw1) /\ expr_vv_res_ok (INL raw2) /\
  compile_expr cenv (expr_type e1) e1 sa = (vv1,sm) /\
  compile_expr cenv (expr_type e2) e2 sm = (vv2,sn) /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  (!mid s. vv_post ctx func cenv cx e2 es1 sm sn mid es2 raw2 vv2 s ==>
     contract_storage s = contract_storage mid /\
     contract_transient s = contract_transient mid) ==>
  frag_exec ctx sa sn
    (\s. s = start /\ stmt_state_rel ctx func cenv cx es s)
    (\s. ?mid.
       vv_post ctx func cenv cx e1 es sa sm start es1 raw1 vv1 mid /\
       vv_post ctx func cenv cx e2 es1 sm sn mid es2 raw2 vv2 s /\
       vv_holds cenv cx (expr_type e1) raw1 vv1 es2 s)
    (\r. F)
Proof
  strip_tac >>
  `frag_exec ctx sa sm
     (\s. s = start /\ stmt_state_rel ctx func cenv cx es s)
     (vv_post ctx func cenv cx e1 es sa sm start es1 raw1 vv1)
     (\r. F)` by (irule expr_vv_sim_success_frag >> metis_tac[]) >>
  drule frag_exec_then >> disch_then irule >>
  conj_tac
  >- (rpt strip_tac >>
      `frag_exec ctx sm sn
         (\s. s = t /\ stmt_state_rel ctx func cenv cx es1 s)
         (vv_post ctx func cenv cx e2 es1 sm sn t es2 raw2 vv2)
         (\r. F)` by (irule expr_vv_sim_success_frag >> metis_tac[]) >>
      irule frag_exec_conseq >> first_assum (irule_at Any) >> simp[] >>
      conj_tac >- gvs[vv_post_def] >>
      rpt strip_tac >> qexists_tac `t` >> simp[] >>
      irule two_vv_posts_deferred_holds >> metis_tac[]) >>
  metis_tac[cj 1 exprLoweringPropsTheory.compile_expr_grows]
QED

Theorem expr_vv_sim_exception_frag:
  expr_vv_sim ctx func cenv cx ty e es /\
  compile_expr cenv ty e sa = (vv,sb) /\
  eval_expr cx e es = (INR exc,es') /\ expr_vv_res_ok (INR exc) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb
    (\s. s = start /\ stmt_state_rel ctx func cenv cx es s)
    (\s. F) (expr_exit (INR exc : eval_result + exception))
Proof
  strip_tac >> gvs[expr_vv_sim_def] >>
  first_x_assum drule_all >>
  disch_then (qspec_then `start` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem two_expr_vv_second_exception:
  expr_vv_sim ctx func cenv cx (expr_type e1) e1 es /\
  expr_vv_sim ctx func cenv cx (expr_type e2) e2 es1 /\
  eval_expr cx e1 es = (INL raw1,es1) /\
  eval_expr cx e2 es1 = (INR exc,es2) /\
  expr_vv_res_ok (INL raw1) /\ expr_vv_res_ok (INR exc) /\
  compile_expr cenv (expr_type e1) e1 sa = (vv1,sm) /\
  compile_expr cenv (expr_type e2) e2 sm = (vv2,sn) /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm ==>
  frag_exec ctx sa sn
    (\s. s = start /\ stmt_state_rel ctx func cenv cx es s)
    (\s. F) (expr_exit (INR exc : eval_result + exception))
Proof
  strip_tac >>
  `frag_exec ctx sa sm
     (\s. s = start /\ stmt_state_rel ctx func cenv cx es s)
     (vv_post ctx func cenv cx e1 es sa sm start es1 raw1 vv1)
     (\r. F)` by (irule expr_vv_sim_success_frag >> metis_tac[]) >>
  `frag_exec ctx sa sm
     (\s. s = start /\ stmt_state_rel ctx func cenv cx es s)
     (vv_post ctx func cenv cx e1 es sa sm start es1 raw1 vv1)
     (expr_exit (INR exc : eval_result + exception))` by
    (irule frag_exec_conseq >> first_assum (irule_at Any) >> simp[]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ (\r. F)` kall_tac >>
  drule frag_exec_then >>
  disch_then irule >> conj_tac
  >- (rpt strip_tac >>
      `frag_exec ctx sm sn
         (\s. s = t /\ stmt_state_rel ctx func cenv cx es1 s)
         (\s. F) (expr_exit (INR exc : eval_result + exception))` by
        (irule expr_vv_sim_exception_frag >> metis_tac[]) >>
      irule frag_exec_conseq >> first_assum (irule_at Any) >>
      gvs[vv_post_def]) >>
  metis_tac[cj 1 exprLoweringPropsTheory.compile_expr_grows]
QED

Theorem compile_multi_vvs_singleton:
  cfn cenv (expr_type e) e sa = (vv,sb) ==>
  compile_multi_vvs cfn cenv [e] sa = ([vv],sb)
Proof
  simp[compile_multi_vvs_def, comp_bind_def, comp_return_def]
QED

Theorem compile_multi_vvs_pair:
  cfn cenv (expr_type e1) e1 sa = (vv1,sm) /\
  cfn cenv (expr_type e2) e2 sm = (vv2,sn) ==>
  compile_multi_vvs cfn cenv [e1;e2] sa = ([vv1;vv2],sn)
Proof
  simp[compile_multi_vvs_def, comp_bind_def, comp_return_def]
QED

Theorem local_region_pointer_frame:
  (!name p size.
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) size) ==>
     lookup_var p s = lookup_var p s0) ==>
  (local_region cenv scopes s name b sz <=>
   local_region cenv scopes s0 name b sz)
Proof
  strip_tac >> simp[local_region_def] >> metis_tac[]
QED

Theorem vv_at_region_frame:
  vv_at cenv cx ty ca cb es raw held s0 /\
  cb.cs_next_id <= cc.cs_next_id /\
  (!aid region. FLOOKUP s0.vs_allocas aid = SOME region ==>
     FLOOKUP s.vs_allocas aid = SOME region) /\
  (!name b sz. local_region cenv es.scopes s name b sz <=>
               local_region cenv es.scopes s0 name b sz) /\
  (!w. eval_operand (vv_operand held) s0 = SOME w ==>
       eval_operand (vv_operand held) s = SOME w) ==>
  vv_at cenv cx ty ca cc es raw held s
Proof
  strip_tac >> Cases_on `held` >>
  gvs[vv_at_def, expr_val_at_def, vv_operand_def] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qexists_tac `w` >> simp[]
  >>~- ([`FLOOKUP s0.vs_allocas aid = SOME (b,sz)`],
    disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >>
    `aid < cc.cs_next_id` by decide_tac >> asm_rewrite_tac[] >>
    metis_tac[]) >>
  disj2_tac >> disj1_tac >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem vv_at_frame:
  vv_at cenv cx ty ca cb es raw held s0 /\
  cb.cs_next_id <= cc.cs_next_id /\
  (!aid region. FLOOKUP s0.vs_allocas aid = SOME region ==>
     FLOOKUP s.vs_allocas aid = SOME region) /\
  (!name p size.
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) size) ==>
     lookup_var p s = lookup_var p s0) /\
  (!w. eval_operand (vv_operand held) s0 = SOME w ==>
     eval_operand (vv_operand held) s = SOME w) ==>
  vv_at cenv cx ty ca cc es raw held s
Proof
  strip_tac >> irule vv_at_region_frame >>
  qexistsl_tac [`cb`, `s0`] >> simp[] >>
  metis_tac[local_region_pointer_frame]
QED

(* Only live locals are relevant to location witnesses.  Uninitialised,
   non-live pointer variables need not have equal lookups at both endpoints. *)
Theorem vv_post_local_regions:
  local_ptrs_rel func cenv es.scopes s0 /\
  local_ptrs_reserved cenv sm /\
  vv_post ctx func cenv cx e es sm sn s0 es' raw vv s ==>
  (!name b sz. local_region cenv es.scopes s name b sz <=>
               local_region cenv es.scopes s0 name b sz)
Proof
  strip_tac >>
  `!name entry p size. lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) size) ==>
     lookup_var p s = lookup_var p s0` by
    (rpt strip_tac >>
     `?w. lookup_var p s0 = SOME w` by
       (gvs[local_ptrs_rel_def] >> metis_tac[]) >>
     `not_fresh_at sm p` by
       (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
     gvs[vv_post_def] >> metis_tac[]) >>
  simp[local_region_def] >> metis_tac[]
QED

Theorem vv_post_held_location:
  local_ptrs_rel func cenv es.scopes s0 /\
  local_ptrs_reserved cenv sm /\
  vv_post ctx func cenv cx e es sm sn s0 es' raw_new vv_new s /\
  vv_at cenv cx ty lo sm es raw held s0 /\
  sm.cs_next_id <= sn.cs_next_id /\
  (!w. eval_operand (vv_operand held) s0 = SOME w ==>
       eval_operand (vv_operand held) s = SOME w) ==>
  vv_at cenv cx ty lo sn es raw held s
Proof
  strip_tac >> irule vv_at_region_frame >>
  qexistsl_tac [`sm`, `s0`] >> simp[] >> conj_tac
  >- metis_tac[vv_post_local_regions] >>
  gvs[vv_post_def]
QED

Theorem vv_post_deferred_entry:
  expr_sim_inv cenv cx env es /\
  local_ptrs_rel func cenv es.scopes s0 /\ local_ptrs_reserved cenv sm /\
  compile_expr cenv (expr_type e) e sm = (vv_new,sn) /\
  vv_post ctx func cenv cx e es sm sn s0 es' raw_new vv_new s /\
  contract_storage s = contract_storage s0 /\
  contract_transient s = contract_transient s0 /\
  es' = es with outcomes := es'.outcomes /\
  vv_holds cenv cx ty raw held es s0 /\
  vv_at cenv cx ty lo sm es raw held s0 /\
  safe_operand sm (vv_operand held) ==>
  vv_holds cenv cx ty raw held es' s /\
  vv_at cenv cx ty lo sn es' raw held s /\
  safe_operand sn (vv_operand held)
Proof
  strip_tac >> drule (cj 1 compile_expr_grows) >> strip_tac >>
  `!w. eval_operand (vv_operand held) s0 = SOME w ==>
       eval_operand (vv_operand held) s = SOME w` by
    (rpt strip_tac >> irule safe_operand_value_preserved >>
     qexistsl_tac [`s0`, `sm`] >> simp[] >> gvs[vv_post_def]) >>
  `local_ptrs_rel func cenv es.scopes s` by
    gvs[vv_post_def, stmt_state_rel_def, state_rel_def] >>
  `vv_holds cenv cx ty raw held es s` by
    (irule vv_post_preserves_held_value >> metis_tac[]) >>
  `vv_at cenv cx ty lo sn es raw held s` by
    (irule vv_post_held_location >> metis_tac[]) >>
  metis_tac[vv_holds_outcomes, vv_at_outcomes, safe_operand_mono]
QED

Theorem vv_post_deferred_prefix:
  expr_sim_inv cenv cx env es /\
  local_ptrs_rel func cenv es.scopes s0 /\ local_ptrs_reserved cenv sm /\
  compile_expr cenv (expr_type e) e sm = (vv_new,sn) /\
  vv_post ctx func cenv cx e es sm sn s0 es' raw_new vv_new s /\
  contract_storage s = contract_storage s0 /\
  contract_transient s = contract_transient s0 /\
  es' = es with outcomes := es'.outcomes /\
  EVERY (\(ty,raw,held,lo).
    vv_holds cenv cx ty raw held es s0 /\
    vv_at cenv cx ty lo sm es raw held s0 /\
    safe_operand sm (vv_operand held)) hs ==>
  EVERY (\(ty,raw,held,lo).
    vv_holds cenv cx ty raw held es' s /\
    vv_at cenv cx ty lo sn es' raw held s /\
    safe_operand sn (vv_operand held)) hs
Proof
  simp[listTheory.EVERY_MEM] >> strip_tac >> gen_tac >> disch_tac >>
  rename1 `MEM item hs` >> PairCases_on `item` >>
  first_x_assum drule >> simp[] >> strip_tac >>
  irule vv_post_deferred_entry >> metis_tac[]
QED

(* The frame belongs to the supplied execution, not to arbitrary vv_post states. *)
Theorem expr_vv_framed_deferred_prefix:
  expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
  compile_expr cenv (expr_type e) e sm = (vv_new,sn) /\
  local_ptrs_reserved cenv sm /\
  es' = es with outcomes := es'.outcomes /\
  frag_exec ctx sm sn
    (\s. s = start /\ stmt_state_rel ctx func cenv cx es s)
    (\s. vv_post ctx func cenv cx e es sm sn start es' raw_new vv_new s /\
         contract_storage s = contract_storage start /\
         contract_transient s = contract_transient start)
    (\r. F) ==>
  frag_exec ctx sm sn
    (\s. s = start /\ stmt_state_rel ctx func cenv cx es s /\
      EVERY (\(ty,raw,held,lo).
        vv_holds cenv cx ty raw held es s /\
        vv_at cenv cx ty lo sm es raw held s /\
        safe_operand sm (vv_operand held)) hs)
    (\s. vv_post ctx func cenv cx e es sm sn start es' raw_new vv_new s /\
      EVERY (\(ty,raw,held,lo).
        vv_holds cenv cx ty raw held es' s /\
        vv_at cenv cx ty lo sn es' raw held s /\
        safe_operand sn (vv_operand held)) hs /\
      safe_operand sn (vv_operand vv_new))
    (\r. F)
Proof
  strip_tac >> irule frag_exec_pointwise >>
  qx_gen_tac `s0` >> strip_tac >> fs[] >>
  qpat_x_assum `s0 = start` SUBST_ALL_TAC >>
  irule frag_exec_conseq >> first_assum (irule_at Any) >> simp[] >>
  gen_tac >> strip_tac >> simp[] >> conj_tac
  >- (irule vv_post_deferred_prefix >>
      `local_ptrs_rel func cenv es.scopes start` by
        gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  irule compile_expr_operand_safe >> metis_tac[]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag expr_vv_framed_deferred_prefix)
  in
    if null axioms andalso null (Thm.hyp expr_vv_framed_deferred_prefix) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Framed deferred prefix has unproved dependencies"
  end;

Theorem expr_vv_success_deferred_prefix:
  expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
  expr_vv_sim ctx func cenv cx (expr_type e) e es /\
  compile_expr cenv (expr_type e) e sm = (vv_new,sn) /\
  eval_expr cx e es = (INL raw_new,es') /\ expr_vv_res_ok (INL raw_new) /\
  es' = es with outcomes := es'.outcomes /\
  (!s. vv_post ctx func cenv cx e es sm sn start es' raw_new vv_new s ==>
     contract_storage s = contract_storage start /\
     contract_transient s = contract_transient start) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm ==>
  frag_exec ctx sm sn
    (\s. s = start /\ stmt_state_rel ctx func cenv cx es s /\
      EVERY (\(ty,raw,held,lo).
        vv_holds cenv cx ty raw held es s /\
        vv_at cenv cx ty lo sm es raw held s /\
        safe_operand sm (vv_operand held)) hs)
    (\s. vv_post ctx func cenv cx e es sm sn start es' raw_new vv_new s /\
      EVERY (\(ty,raw,held,lo).
        vv_holds cenv cx ty raw held es' s /\
        vv_at cenv cx ty lo sn es' raw held s /\
        safe_operand sn (vv_operand held)) hs /\
      safe_operand sn (vv_operand vv_new))
    (\r. F)
Proof
  strip_tac >> irule frag_exec_pointwise >>
  qx_gen_tac `s0` >> strip_tac >> fs[] >>
  qpat_x_assum `s0 = start` SUBST_ALL_TAC >>
  `frag_exec ctx sm sn
     (\s. s = start /\ stmt_state_rel ctx func cenv cx es s)
     (vv_post ctx func cenv cx e es sm sn start es' raw_new vv_new)
     (\r. F)` by (irule expr_vv_sim_success_frag >> metis_tac[]) >>
  irule frag_exec_conseq >> first_assum (irule_at Any) >> simp[] >>
  gen_tac >> disch_tac >> simp[] >> conj_tac
  >- (irule vv_post_deferred_prefix >>
      `local_ptrs_rel func cenv es.scopes start` by
        gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  irule compile_expr_operand_safe >> metis_tac[]
QED

Theorem expr_vv_exception_deferred_prefix:
  expr_vv_sim ctx func cenv cx (expr_type e) e es /\
  compile_expr cenv (expr_type e) e sm = (vv_new,sn) /\
  eval_expr cx e es = (INR exc,es') /\ expr_vv_res_ok (INR exc) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm ==>
  frag_exec ctx sm sn
    (\s. s = start /\ stmt_state_rel ctx func cenv cx es s /\
      EVERY (\(ty,raw,held,lo).
        vv_holds cenv cx ty raw held es s /\
        vv_at cenv cx ty lo sm es raw held s /\
        safe_operand sm (vv_operand held)) hs)
    (\s. F) (expr_exit (INR exc : eval_result + exception))
Proof
  strip_tac >>
  `frag_exec ctx sm sn
     (\s. s = start /\ stmt_state_rel ctx func cenv cx es s)
     (\s. F) (expr_exit (INR exc : eval_result + exception))` by
    (irule expr_vv_sim_exception_frag >> metis_tac[]) >>
  irule frag_exec_conseq >> first_assum (irule_at Any) >> simp[]
QED
