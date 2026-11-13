(* A ternary at the joint judgments, on finite horizons: the condition's
   value, the JNZ into the selected arm's block, the arm (no copy, a
   bytestring widening copy, or a widened internal call's typed copy), the
   ASSIGN and the JMP.  The value judgment follows from the vv judgment by
   the shared joint unwrap_value lemma (bodyFullUnwrap).

   The helper lemmas the arm steps take as premises are discharged here:
   the generic ALLOCA/bytestring ones from bodyFullAllocGeneric, the joint
   typed copy from typedCopyOriginPtr.

   DRAFT: statements only; the proofs are not written yet.
 *
 * TOP-LEVEL:
 *   expr_sim_full_of_vv -- the value judgment from the vv judgment
 *   ifexp_vv_full_root -- the ternary's vv judgment from its parts
 *   ifexp_expr_full_ok -- bodyFullCases' IfExp case (body_ifexp_case_full)
 *)
Theory bodyFullIfExp
Ancestors
  bodyFullIfExpArm bodyFullIfExpWiden bodyFullIfExpWidenCall
  bodyFullIfExpFinish bodyFullIfExpShadow bodyFullAllocGeneric typedCopyOriginPtr
  bodyFullUnwrap bodyFullPreds
  bodySimFull gasOutcomeFullCompose gasOutcomeFull gasShadowCompile
  gasShadowCompileHelpers exprSimMemorySource exprSimIfExp exprSimDefs
  exprSimMemDefs bodyPtrDefs loweringPosts exprLowering exprLoweringProps
  typedCopyDomain vyperTypeSystem compileEnv context vyperAST
  vyperInterpreter vyperState venomState

val _ = Parse.hide "body";

(* An owned physical value never needs the local-place alternative. *)
Theorem ifexp_nocopy_physical_owned_vv[local]:
  ~is_word_type src /\ ~is_word_type dst /\
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\ val_wf dv v /\
  val_footprint sv v = val_footprint dv v /\
  expr_val_own ce cx src sa sb ee v op s /\
  read_result cx tv ee = (INL v,ee) ==>
  vv_at ce cx dst sa sb ee tv (LocatedValue dst (mk_ptr op LocMemory)) s
Proof
  simp[vv_at_def, mk_ptr_def, expr_val_own_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `sv` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem ifexp_nocopy_physical_post[local]:
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  same_memory_layout ce (post_value_type ce e) (expr_type e) /\
  arg_type_fits (post_value_type ce e) (expr_type e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME sv /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME dv /\
  ~is_word_type (expr_type e) /\ value_has_type dv v /\
  (~expr_has_effect (IfExp (expr_type e) c a b) ==> ~expr_has_effect e) /\
  expr_post H ctx func ce cx e es sa sb s0 ee v op s ==>
  expr_post H ctx func ce cx (IfExp (expr_type e) c a b) es sa sb s0 ee v op s
Proof
  strip_tac >> Cases_on `post_value_type ce e = expr_type e`
  >- (gvs[expr_post_def, expr_type_def] >> metis_tac[]) >>
  qpat_assum `expr_post H _ _ _ _ e _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE[expr_post_def]) >>
  `expr_val_rel cx (expr_type e) v op s` by
    (irule exprSimLayoutTransportTheory.expr_val_rel_layout_transport >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `expr_val_at ce cx (expr_type e) sa sb ee v op s` by
    (irule exprSimLayoutTransportTheory.expr_val_at_layout_transport >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[expr_post_def, expr_type_def] >> metis_tac[]
QED

Theorem ifexp_nocopy_physical_endpoint_vv[local]:
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  same_memory_layout ce (post_value_type ce e) (expr_type e) /\
  arg_type_fits (post_value_type ce e) (expr_type e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME sv /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME dv /\
  ~is_word_type (expr_type e) /\ value_has_type dv v /\
  post_value_type ce e <> expr_type e /\
  expr_post H ctx fn ce cx e es sa sb s0 ee v op s /\
  read_result cx raw ee = (INL v,ee) ==>
  vv_at ce cx (expr_type e) sa sb ee raw
    (LocatedValue (expr_type e) (mk_ptr op LocMemory)) s
Proof
  strip_tac >> irule ifexp_nocopy_physical_owned_vv >>
  simp[] >> qexistsl_tac [`post_value_type ce e`, `sv`] >>
  simp[] >> rpt conj_tac
  >- metis_tac[exprSimLayoutTransportTheory.compatible_word_type]
  >- (fs[same_memory_layout_def] >>
      metis_tac[exprSimLayoutTransportTheory.compatible_footprint])
  >- metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]
  >> fs[expr_post_def]
QED

Theorem ifexp_nocopy_physical_store_size[local]:
  ~is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
  val_store_size tv v = type_memory_size tv
Proof
  rpt strip_tac >> Cases_on `v` >> simp[exprSimPropsTheory.val_store_size_def] >>
  Cases_on `tv` >> simp[] >>
  rename1 `BaseTV b` >> Cases_on `b` >> simp[] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[]) >>
  Cases_on `ty` >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def]
QED

Theorem ifexp_nocopy_physical_buffer[local]:
  same_memory_layout ce (lowered_value_type ce e) t /\
  ptr_buf_ok ce e op G s ==>
  !e'. lowered_value_type ce e' = t ==> ptr_buf_ok ce e' op G s
Proof
  simp[same_memory_layout_def, ptr_buf_ok_def] >> metis_tac[]
QED

Theorem ifexp_nocopy_physical_bound[local]:
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  same_memory_layout ce src dst /\
  evaluate_type (get_tenv cx) dst = SOME dv /\ type_memory_size dv < 2 ** 64 ==>
  !sv. evaluate_type (get_tenv cx) src = SOME sv ==>
    type_memory_bytes ce src = type_memory_size sv /\ type_memory_size sv < 2 ** 64
Proof
  simp[same_memory_layout_def] >> metis_tac[]
QED

Theorem ifexp_nocopy_physical_ptr[local]:
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  same_memory_layout ce src dst /\ arg_type_fits src dst /\
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\
  ~is_word_type dst /\ ~is_bytestring_type src /\ ~is_bytestring_type dst /\
  ptr_val_ok cx src v op G tn s ==>
  ptr_val_ok cx dst v op G tn s
Proof
  strip_tac >>
  `~is_word_type src` by
    metis_tac[exprSimLayoutTransportTheory.compatible_word_type] >>
  `type_memory_size sv = type_memory_size dv` by
    (fs[same_memory_layout_def] >> metis_tac[]) >>
  `val_footprint sv v = val_footprint dv v` by
    metis_tac[exprSimLayoutTransportTheory.compatible_footprint] >>
  `val_store_size sv v = val_store_size dv v` by
    metis_tac[ifexp_nocopy_physical_store_size] >>
  `!b mem. val_in_memory sv v b mem <=> val_in_memory dv v b mem` by
    (drule exprSimLayoutTransportTheory.compatible_layout_memory >>
     strip_tac >> first_x_assum irule >>
     qexistsl_tac [`dst`, `src`] >> fs[same_memory_layout_def]) >>
  gvs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]
QED

(* Retyping keeps the one physical unwrap endpoint outside the horizon guard. *)
Theorem ifexp_nocopy_physical_family[local]:
  expr_type e = t /\ post_value_type ce e <> t /\
  post_value_type ce e = lowered_value_type ce e /\
  same_memory_layout ce (lowered_value_type ce e) t /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) t /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME sv /\
  evaluate_type (get_tenv cx) t = SOME dv /\
  value_has_type dv v /\ ~is_word_type t /\
  (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  read_result cx raw ee = (INL v,ee) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK z,Gz,tf) /\
    expr_post H ctx func ce cx e es sa sb u ee v op z /\
    ghost_inv_at (DF H) lo d ce cx ee Gz tf z) /\
  expr_store_bound cx t v op z /\
  ptr_val_ok cx (post_value_type ce e) v op Gz tf z /\
  ptr_buf_ok ce e op Gz z /\
  (!rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
    eval_operand op z = SOME w ==>
    type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) ==>
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK z,Gz,tf) /\
    expr_post H ctx func ce cx (IfExp t c a b) es sa sb u ee v op z /\
    ghost_inv_at (DF H) lo d ce cx ee Gz tf z) /\
  vv_at ce cx t sa sb ee raw (LocatedValue t (mk_ptr op LocMemory)) z /\
  expr_store_bound cx t v op z /\
  ptr_val_ok cx t v op Gz tf z /\
  (!e'. lowered_value_type ce e' = t ==> ptr_buf_ok ce e' op Gz z) /\
  (!rt w. evaluate_type (get_tenv cx) t = SOME rt /\
    eval_operand op z = SOME w ==>
    type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next)
Proof
  strip_tac >>
  `arg_type_fits (post_value_type ce e) t` by
    fs[type_widens_to_def] >>
  `~is_bytestring_type t` by metis_tac[post_value_type_bytestring] >>
  `~is_bytestring_type (post_value_type ce e)` by
    metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_x_assum `expr_type e = t` (SUBST_ALL_TAC o SYM) >>
  rpt conj_tac
  >- (rpt strip_tac >> res_tac >> simp[] >>
      irule ifexp_nocopy_physical_post >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[])
  >- (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      irule (INST_TYPE [``:'a`` |-> ``:256``] ifexp_nocopy_physical_endpoint_vv) >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`storage_trace_horizon ee.storage_trace`, `ctx`, `es`, `func`, `u`] >>
      first_assum ACCEPT_TAC)
  >- first_assum ACCEPT_TAC
  >- (irule ifexp_nocopy_physical_ptr >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >- (rpt strip_tac >> drule_all ifexp_nocopy_physical_buffer >> simp[])
  >> fs[same_memory_layout_def] >> metis_tac[]
QED

(* The value judgment from the vv judgment: lower_value is compile_expr
   then unwrap_value, whose code reads no GAS (unwrap_value_origin_ptr). *)
Theorem expr_sim_full_of_vv:
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        ~is_word_type (post_value_type cenv e) ==>
        type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
        type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
     read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty e es ==>
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty e es
Proof
  cheat
QED

(* The ternary's root from the condition's value judgment and the arms'
   vv judgments.  Each arm is one of the three arm steps' kinds. *)
Theorem ifexp_vv_full_root:
  expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
  (!e. (e = a \/ e = b) ==>
       (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
       (post_value_type cenv e = t /\
        (is_word_type t \/
         same_memory_layout cenv (lowered_value_type cenv e) t /\
         (?rtp. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rtp) \/
         ~same_memory_layout cenv (lowered_value_type cenv e) t /\
         is_bytestring_type t /\ is_bytestring_type (lowered_value_type cenv e) /\
         arg_type_fits (lowered_value_type cenv e) t) \/
        ~is_word_type t /\ ~same_memory_layout cenv (lowered_value_type cenv e) t /\
        post_value_type cenv e = lowered_value_type cenv e /\
        type_widens_to (get_tenv cx) (lowered_value_type cenv e) t /\
        (?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv))) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields.
     FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv)
       fields) /\
  (!ty' tvt. evaluate_type (get_tenv cx) ty' = SOME tvt ==>
     type_memory_bytes cenv ty' = type_memory_size tvt) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
     type_memory_size tvt < 2 ** 64) /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx (BaseT BoolT) c es /\
  (!gs v es1.
     bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) =
       (INL v,es1) ==>
     expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty a es1 /\
     expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty b es1 /\
     !e gs' v' es2.
       (e = a \/ e = b) /\
       bind (eval_expr cx e) (read_result cx) (es1 with gas_obs := gs') =
         (INL v',es2) ==>
       value_has_type rty v' /\
       !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
             value_has_type ptv v') ==>
  expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty (IfExp t c a b) es
Proof
  cheat
QED

(* bodyFullCases' IfExp case: the side facts the root takes come from
   body_inv and expr_body_pre, the word agreement by the contrapositive of
   post_value_type_nonword. *)
Theorem ifexp_expr_full_ok:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e3) /\
    body_expr_full_ok cx e1 ==>
    body_expr_full_ok cx (IfExp v5 e1 e2 e3)
Proof
  cheat
QED
