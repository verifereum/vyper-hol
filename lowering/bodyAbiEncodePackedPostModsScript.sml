(* Saved ABI encoder operands at a common linked observation state. *)
Theory bodyAbiEncodePackedPostMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv
  exprLowering compileEnv exprSimHypsDefs exprSimMemDefs loweringPosts bodyPtrDefs
  vyperInterpreter vyperState vyperTypeSystem allocaHistory venomState
  finite_map list pair

(* The compile and snapshot witnesses stay fixed when the row is transported.
   The source value stays fixed too, but its raw read witness need not. *)
Definition abi_encode_saved_row_mods_def[nocompute]:
  abi_encode_saved_row_mods lo cenv cx sa sb e sv v si sm ss vv copy H ee G tn t <=>
    compile_expr cenv (expr_type e) e si = (vv,sm) /\
    compile_snapshot_vv cenv copy
      (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
    (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
      ?p w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var p /\
        eval_operand (vv_operand sv) t = SOME w /\
        evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
        val_wf tv v /\ FLOOKUP t.vs_allocas sm.cs_next_id =
          SOME (w2n w,type_memory_size tv) /\
        sm.cs_next_id < ss.cs_next_id /\
        (!n b sz. local_region cenv ee.scopes t n b sz ==>
          regions_disjoint (w2n w) (type_memory_size tv) b sz)) /\
    sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id /\
    sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
    ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id /\
    local_ptrs_reserved cenv si /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    ((?tag op0. sv = StackValue tag op0) \/
     (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
       ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
     (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
       ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
       lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
    (?raw. read_result cx raw ee = (INL v,ee) /\
      vv_holds_mods cenv cx (lowered_value_type cenv e) raw sv ee t /\
      vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv t /\
      ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
      vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e)
        ee raw sv t) /\
    vv_storage_live H cx sv ee t /\
    (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
      ptr_buf_ok cenv e op G t) /\
    (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand G t) /\
    (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
      !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
        eval_operand (vv_operand sv) t = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem))
End

(* Positional only: the cons compilation equation selects its copy flag
   using the remaining positional expressions and no keyword arguments. *)
Definition abi_encode_packed_post_mods_def[nocompute]:
  abi_encode_packed_post_mods mods DF lo d ctx func cenv cx env
    xs svs sa sb es s0 G0 tn0 H res ee G tn t <=>
    ?vs. res = INL vs /\ LENGTH svs = LENGTH xs /\
      LIST_REL (\(e,sv) v.
        ?si sm ss vv copy.
          abi_encode_saved_row_mods lo cenv cx sa sb e sv v si sm ss vv copy
            H ee G tn t) (ZIP (xs,svs)) vs /\
      EVERY (\sv. !x. vv_operand sv = Var x ==> not_fresh_at sb x) svs /\
      stmt_state_rel H ctx func cenv cx ee t /\
      immutable_frame_mods func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\
      (~EXISTS expr_has_effect xs ==> pure_frame cenv func es sa s0 t) /\
      MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      expr_sim_inv_mods mods cenv cx env ee /\
      body_const_cells_agree_mods mods cx env ee /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
End
