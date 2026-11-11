(*
 * The judgment of an expression naming a mapping (a mapping variable, or a
 * mapping inside one).  Its source result is a HashMapRef, which neither
 * expr_vv_res_ok nor well_typed_expr covers, so expr_vv_case says nothing
 * of it; the mapping subscript case (exprSimSubscriptMap) takes this
 * judgment of its base instead.
 *)
Theory exprSimMapDefs
Ancestors
  exprSimHypsDefs exprSimDefs loweringPosts gasOutcome gasContext
  vyperStoragePlaceProvenance exprLowering vyperInterpreter vyperState
  vyperTypeCallGraph vyperTypeSystem

(* The results the mapping judgment speaks of: any result, and the errors
   expr_res_ok allows. *)
Definition expr_map_res_ok_def:
  expr_map_res_ok (res : eval_result + exception) <=>
    (?tv. res = INL tv) \/ (?m. res = INR (Error (RuntimeError m))) \/
    (?d. res = INR (Error (RevertData d))) \/
    (?str. res = INR (AssertException str))
End

(* expr_vv_sim for an expression naming a mapping: compile_expr's fragment
   ends with the pointer's operand holding the mapping's slot, at its
   location, the slot that of a declared mapping (storage_mapping_region),
   and with vv_post's frame. *)
Definition expr_map_sim_def:
  expr_map_sim ctx func cenv cx ty e es <=>
    !sa sb vv s0.
      compile_expr cenv ty e sa = (vv, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      gas_admissible (eval_expr cx e) expr_map_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx, func) (eval_expr cx e) (es, s0)
        (\res ee t. ?tr slot kt vt tp p.
          res = INL (HashMapRef tr slot kt vt) /\
          storage_mapping_region cx tr slot (HashMapT kt vt) /\
          vv = LocatedValue tp p /\ p.ptr_location = slot_loc tr /\
          eval_operand p.ptr_operand t = SOME slot /\
          stmt_state_rel ctx func cenv cx ee t /\
          (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                 lookup_var x t = SOME w) /\
          (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                   FLOOKUP t.vs_allocas aid = SOME b) /\
          (!aid off sz.
             FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\
             aid < sa.cs_next_id /\
             (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                        off + sz <= b \/ b + sz' <= off) ==>
             mem_bytes_at off sz t.vs_memory =
               mem_bytes_at off sz s0.vs_memory) /\
          locals_kept cenv es ee s0 t /\
          (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts)
        (\res ee r. expr_exit res r)
End

(* expr_body_pre for an expression naming a mapping, which
   well_typed_expr does not type: type_place_expr gives it a mapping's
   type. *)
Definition expr_map_pre_def:
  expr_map_pre cenv cx env e es <=>
    expr_sim_inv cenv cx env es /\
    (?kt vt. type_place_expr env e = SOME (HashMapT kt vt)) /\
    byte_widths_expr e /\ alloc_limits_expr cenv e /\
    call_evaluation_safe cx (int_calls_expr e) /\ ~expr_has_evm_run e /\
    ~supported_expr_exists call_operands_effect_root e /\
    EVERY (\c. FST c = NONE /\
               ?tops. supported_program tops /\
                      get_module_code cx NONE = SOME tops /\
                      IS_SOME (supported_function_decl tops c Internal))
          (int_calls_expr e) /\
    (!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
              occurs_abi_decode_target target (cx_tops cx)) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
              is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target))
End

(* expr_vv_case for an expression naming a mapping. *)
Definition expr_map_case_def:
  expr_map_case nocalls ctx func cenv cx e <=>
    !env ty es.
      expr_map_pre cenv cx env e es /\ (nocalls ==> int_calls_expr e = []) ==>
      expr_map_sim ctx func cenv cx ty e es
End

(* No form but a top-level name and a subscript names a mapping. *)
Theorem expr_map_case_other:
  !nocalls ctx func cenv cx e.
    (!ty id. e <> TopLevelName ty id) /\
    (!ty e1 e2. e <> Subscript ty e1 e2) ==>
    expr_map_case nocalls ctx func cenv cx e
Proof
  rw[expr_map_case_def, expr_map_pre_def] >>
  Cases_on `e` >> gvs[well_typed_expr_def]
QED
