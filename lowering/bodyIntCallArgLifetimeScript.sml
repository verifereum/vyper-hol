(* Deferred internal-call argument interface probes. *)
Theory bodyIntCallArgLifetime
Ancestors
  exprSimAggregateChildren exprSimAggregateSource exprLowering compileEnv vyperEvalPureExpr vyperPureExpr supportedExprs supportedExprForms
  bodyIntCallStorageFrame loweringPosts bodyIntCallSourceFrame bodyIntCallArgPath exprReasonOperand exprSimHyps exprSimHypsDefs exprOperandVar exprSafeOperand context venomState exprSimDefs exprSimProps exprLoweringProps fragExec
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


(* Variables are reserved statically; labels are framed by the actual path. *)
Theorem compile_expr_operand_reserved:
  compile_expr cenv ty e sa = (vv,sb) /\ local_ptrs_reserved cenv sa ==>
  !x. vv_operand vv = Var x ==> not_fresh_at sb x
Proof
  metis_tac[CONJUNCT1 compiler_compile_var]
QED

Theorem reserved_operand_value_preserved:
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s = SOME w) /\
  s.vs_labels = s0.vs_labels /\ eval_operand op s0 = SOME w ==>
  eval_operand op s = SOME w
Proof
  Cases_on `op` >> simp[eval_operand_def] >> metis_tac[]
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
  s.vs_labels = s0.vs_labels /\
  eval_operand (vv_operand vv) s0 = SOME w ==>
  eval_operand (vv_operand vv) s = SOME w
Proof
  strip_tac >> irule reserved_operand_value_preserved >>
  qexistsl_tac [`s0`, `sm`] >> simp[] >>
  conj_tac >- gvs[vv_post_def] >>
  metis_tac[compile_expr_operand_reserved]
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
  b <= off /\ len + off <= b + sz ==>
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
  (!w. immutable_holds cenv cx t raw w es s0 ==>
       immutable_holds cenv cx t raw w es s) /\
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

(* A covered footprint survives a later successful expression. *)
Theorem vv_post_covered_window:
  expr_sim_inv cenv cx env es /\
  local_ptrs_rel func cenv es.scopes s0 /\
  local_ptrs_rel func cenv es.scopes s /\
  local_ptrs_reserved cenv sm /\
  (!n b sz off len. local_region cenv es.scopes s0 n b sz /\
     b <= off /\ len + off <= b + sz ==>
     mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory) /\
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
  >- (irule vv_post_old_allocation_window >>
      fs[arithmeticTheory.ADD_COMM] >> metis_tac[])
  >- (fs[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  simp[mem_bytes_at_def]
QED

Theorem vv_post_preserves_located_memory:
  expr_sim_inv cenv cx env es /\
  local_ptrs_rel func cenv es.scopes s0 /\
  local_ptrs_rel func cenv es.scopes s /\
  local_ptrs_reserved cenv sm /\
  (!n b sz off len. local_region cenv es.scopes s0 n b sz /\
     b <= off /\ len + off <= b + sz ==>
     mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory) /\
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
  irule vv_post_covered_window >>
  fs[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

Theorem vv_post_preserves_stack_value:
  expr_sim_inv cenv cx env es /\
  local_ptrs_rel func cenv es.scopes s0 /\
  local_ptrs_rel func cenv es.scopes s /\
  local_ptrs_reserved cenv sm /\
  (!n b sz off len. local_region cenv es.scopes s0 n b sz /\
     b <= off /\ len + off <= b + sz ==>
     mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory) /\
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
   sym_tac >> irule vv_post_covered_window >>
  fs[arithmeticTheory.ADD_COMM] >> metis_tac[])
QED

Theorem vv_post_preserves_held_value:
  expr_sim_inv cenv cx env es /\
  local_ptrs_rel func cenv es.scopes s0 /\
  local_ptrs_rel func cenv es.scopes s /\
  local_ptrs_reserved cenv sm /\
  (!n b sz off len. local_region cenv es.scopes s0 n b sz /\
     b <= off /\ len + off <= b + sz ==>
     mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory) /\
  vv_post ctx func cenv cx e es sm sn s0 es' tv vv s /\
  contract_storage s = contract_storage s0 /\
  contract_transient s = contract_transient s0 /\
  vv_holds cenv cx t raw held es s0 /\
  (!w. immutable_holds cenv cx t raw w es s0 ==>
       immutable_holds cenv cx t raw w es s) /\
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
  (!n b sz off len. local_region cenv es.scopes s0 n b sz /\
     b <= off /\ len + off <= b + sz ==>
     mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory) /\
  vv_post ctx func cenv cx e2 es sm sn s0 es2 raw2 vv2 s /\
  contract_storage s = contract_storage s0 /\
  contract_transient s = contract_transient s0 /\
  s.vs_labels = s0.vs_labels /\
  (!w. immutable_holds cenv cx (expr_type e1) raw1 w es s0 ==>
       immutable_holds cenv cx (expr_type e1) raw1 w es s) ==>
  vv_holds cenv cx (expr_type e1) raw1 vv1 es2 s
Proof
  strip_tac >>
  `es2 = es with <|outcomes := es2.outcomes; gas_obs := es2.gas_obs|>` by
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

(* Fixed-source-run frag_exec eliminators are intentionally omitted:
   expression judgments retain counted paths and exempt alternatives. *)

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
  (!n b sz off len. local_region cenv es.scopes s0 n b sz /\
     b <= off /\ len + off <= b + sz ==>
     mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory) /\
  vv_post ctx func cenv cx e es sm sn s0 es' raw_new vv_new s /\
  contract_storage s = contract_storage s0 /\
  contract_transient s = contract_transient s0 /\
  es' = es with <|outcomes := es'.outcomes; gas_obs := es'.gas_obs|> /\
  vv_holds cenv cx ty raw held es s0 /\
  (!w. immutable_holds cenv cx ty raw w es s0 ==>
       immutable_holds cenv cx ty raw w es s) /\
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
  `es'.scopes = es.scopes` by
    fs[vyperStateTheory.evaluation_state_component_equality] >>
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
  (!n b sz off len. local_region cenv es.scopes s0 n b sz /\
     b <= off /\ len + off <= b + sz ==>
     mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory) /\
  vv_post ctx func cenv cx e es sm sn s0 es' raw_new vv_new s /\
  contract_storage s = contract_storage s0 /\
  contract_transient s = contract_transient s0 /\
  es' = es with <|outcomes := es'.outcomes; gas_obs := es'.gas_obs|> /\
  (!ty raw held lo w. MEM (ty,raw,held,lo) hs /\
    immutable_holds cenv cx ty raw w es s0 ==>
    immutable_holds cenv cx ty raw w es s) /\
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

