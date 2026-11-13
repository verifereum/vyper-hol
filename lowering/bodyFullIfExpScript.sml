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
