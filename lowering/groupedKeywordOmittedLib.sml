(* Shared omitted-row interfaces for the ordinary and confined clients. *)
structure groupedKeywordOmittedLib =
struct
open HolKernel boolLib bossLib
open runtimeDefaultExpressionTheory exprSimFullBundlePropsTheory
open loweringPostsTheory loweringStateRelDefsTheory bodyPtrDefsTheory
open ptrDisciplineTheory valueEncodingTheory vyperTypeExprResultTheory
open vyperTypeExprSoundnessTheory typedMemoryCopyTheory finite_mapTheory

fun omitted_expr_inputs () = ``
  runtime_constant_expr mods e /\ expr_type e = ty /\
  body_inv tops ctx (ce with ce_vars := FEMPTY) cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre (ce with ce_vars := FEMPTY) cx env e es /\
  expr_sim_full_hypotheses
    ((DF:(bool # 256 word # type_value) list # num list -> dead),
     0,NONE,ctx,shadow_ctx,(PG:(num # num) option list),fn,shadow_fn)
    (ce with ce_vars := FEMPTY) cx ty e es (st0,sa,mid,sha,shmid,src,s,G,tn) /\
  (if is_word_type ty then emit_void MSTORE [Var dst;src]
   else if is_bytestring_type ty then compile_store_bytestring src (Var dst)
   else emit_void MCOPY [Var dst;src;Lit (n2w (type_memory_bytes ce ty))])
    mid = ((),last) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ env.type_defs = get_tenv cx /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  fn_has_code mid last fn /\
  ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\ ce.ce_return_pc = NONE /\
  not_fresh_at sa dst /\ lookup_var dst s = SOME b /\
  FLOOKUP s.vs_allocas oid = SOME (w2n b,type_memory_size tv) /\
  ptr_covers G tn dst s (type_memory_size tv)``;

fun omitted_expr_store_post () = ``\H (res:value + vyperState$exception) ee J tz u.
      ?v. res = INL v /\ value_has_type tv v /\ val_wf tv v /\
          (!mem. mem_agree_outside tz.t_mem u.vs_memory mem ==>
            val_in_memory tv v (w2n b) mem) /\
          lookup_var dst u = SOME b /\ FLOOKUP u.vs_allocas oid =
            SOME (w2n b,type_memory_size tv) /\
          ptr_covers J tz dst u (type_memory_size tv) /\
          (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
            FLOOKUP u.vs_allocas aid = SOME entry) /\
          (!p w. not_fresh_at sa p /\ lookup_var p s = SOME w ==>
            lookup_var p u = SOME w /\ FLOOKUP J p = FLOOKUP G p /\
            op_taint tz (Var p) = op_taint tn (Var p)) /\
          (!aid p old_base n otv x. aid <> oid /\ aid < sa.cs_next_id /\
            FLOOKUP s.vs_allocas aid = SOME (old_base,n) /\
            not_fresh_at sa p /\ lookup_var p s = SOME (n2w old_base) /\
            ptr_covers G tn p s n /\ val_wf otv x /\ val_footprint otv x <= n /\
            (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
              val_in_memory otv x old_base mem) ==>
            !mem. mem_agree_outside tz.t_mem u.vs_memory mem ==>
              val_in_memory otv x old_base mem) /\
          stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx ee u /\
          storage_well_formed_on cx ee (FST H) /\
          ghost_inv_at ((DF:(bool # 256 word # type_value) list # num list -> dead) H)
            0 NONE (ce with ce_vars := FEMPTY) cx ee J tz u /\
          ee.scopes = es.scopes /\ expr_sim_inv (ce with ce_vars := FEMPTY) cx env ee /\
          alloca_history fn u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          u.vs_current_bb = last.cs_current_bb /\
          u.vs_inst_idx = LENGTH last.cs_current_insts /\ ~u.vs_halted``;

fun omitted_expr_normal_post () = ``\H (res:value + vyperState$exception) ee G1 tn1 t.
  expr_sim_full_post
    ((DF:(bool # 256 word # type_value) list # num list -> dead),0,NONE,ctx,fn)
    (ce with ce_vars := FEMPTY) cx e (es,sa,mid,s,src,G,tn) H res ee G1 tn1 t /\
  ~t.vs_halted /\ ee.scopes = es.scopes /\
  expr_sim_inv (ce with ce_vars := FEMPTY) cx env ee /\
  !v. res = INL v ==> expr_result_typed env e (Value v)``;
end
