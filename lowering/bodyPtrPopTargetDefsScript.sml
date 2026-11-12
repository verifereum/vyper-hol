(*
 * The pointer twins of S1's target fragment judgments, for a pop on a
 * nested target: target_sim_ptr (of targetPlaceSimDefs' target_sim, over
 * eval_base_place) and pop_target_frag_ptr (of exprSimPopNestedBase's
 * pop_target_frag, over eval_target_place), with the ghost threaded as
 * bodyPtrDefs' expr_vv_sim_ptr threads it.
 *
 * TOP-LEVEL:
 *   target_ptr_ok -- the target's pointer is untainted, and carries its
 *     place's provenance: a local's site for a memory place, none for
 *     storage
 *   target_sim_ptr, pop_target_frag_ptr -- the judgments
 *   local_target_live -- each index of a local-rooted target leaves the
 *     base's path inside the local's current value
 *)
Theory bodyPtrPopTargetDefs
Ancestors
  bodyPtrDefs targetPlaceSimDefs targetPlaceSimCases fragGasPathPtr
  loweringPosts exprLowering compileEnv ptrDiscipline vyperInterpreter
  vyperState venomState

(* New definition: target_post (with ghost_inv) says what the target's
   pointer holds, not where it may point, and a fresh pointer derived
   from a local's (an attribute's or an element's) needs the local's site
   for the pop's MLOAD and MSTORE access checks.  The site is the one the
   local's pointer has (ghost_inv's ptr_covers covers the local inside
   it). *)
Definition target_ptr_ok_def:
  target_ptr_ok cenv (pv : eval_result)
    (r : operand # data_location option # place_ty option) G tn
    (s : venom_state) <=>
    op_taint tn (FST r) = {} /\
    (!id path p sz.
       pv = PlaceR (MemoryPlace id path) /\
       FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
       op_prov G (FST r) = FLOOKUP G p) /\
    (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
                  op_prov G (FST r) = NONE) /\
    (!tr slot kt vt. pv = HashMapRef tr slot kt vt ==>
                     op_prov G (FST r) = NONE)
End

(* New definition: targetPlaceSimDefs' target_sim with the ghost, as
   expr_vv_sim_ptr has expr_vv_sim's. *)
Definition target_sim_ptr_def:
  target_sim_ptr d ctx PG func cenv cx env bt es <=>
    !vt sa sb op s0 G0 tn0.
      type_place_target env bt = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (op, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
      ~cenv.ce_is_ctor /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_base_place cx bt) target_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx, func) PG
        (eval_base_place cx bt) (es, s0, G0, tn0)
        (\res ee G tn t. ?pv. res = INL pv /\
          target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          ghost_inv d cenv cx ee G tn t /\
          target_ptr_ok cenv pv op G tn t /\
          ghost_kept cenv es sa G0 tn0 s0 G tn)
        (\res ee gt r. expr_exit res r)
End

(* New definition: exprSimPopNestedBase's pop_target_frag with the ghost. *)
Definition pop_target_frag_ptr_def:
  pop_target_frag_ptr d ctx PG func cenv cx env bt es <=>
    !ty sa sb r s0 G0 tn0.
      type_place_target env bt = SOME (Type ty) /\
      compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
      ~cenv.ce_is_ctor /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx, func) PG
        (eval_target_place cx bt) (es, s0, G0, tn0)
        (\res ee G tn t. ?p. res = INL p /\
          target_post ctx func cenv cx es sa sb s0 ee (PlaceR p) (Type ty)
            r t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          ghost_inv d cenv cx ee G tn t /\
          target_ptr_ok cenv (PlaceR p) r G tn t /\
          ghost_kept cenv es sa G0 tn0 s0 G tn)
        (\res ee gt r. expr_exit res r)
End

(* New definition: an index of a target rooted at the local id, once
   evaluated, leaves the base's path inside the local's value.
   extend_place reads the base through read_memory_path, which does not
   consult the popped history when the path resolves, so an index that
   pops the local can leave the base's path (and the length words on it)
   dead while the source carries on; this rules that out at each index. *)
Definition local_target_live_def:
  local_target_live cx id (NameTarget nm) = T /\
  local_target_live cx id (TopLevelNameTarget nsid) = T /\
  local_target_live cx id (AttributeTarget t fld) = local_target_live cx id t /\
  local_target_live cx id (SubscriptTarget t e) =
    (local_target_live cx id t /\
     !s path s1 v s2 entry.
       eval_base_place cx t s = (INL (PlaceR (MemoryPlace id path)), s1) /\
       bind (eval_expr cx e) (read_result cx) s1 = (INL v, s2) /\
       lookup_scopes id s2.scopes = SOME entry ==>
       ISL (evaluate_subscripts entry.type entry.value path))
End
