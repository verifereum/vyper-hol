(* A saved positional operand at the common exit of an ExtCall slice. *)
Theory bodyExtPosSavedRowMods
Ancestors
  bodyFullPostsMods exprSimMemDefs

Definition ext_pos_saved_row_mods_def[nocompute]:
  ext_pos_saved_row_mods lo cenv cx kw_es sa sb H e sv v ee G tn t <=>
    (?si sm ss vv raw copy.
      compile_expr cenv (expr_type e) e si = (vv,sm) /\
      compile_snapshot_vv cenv copy
        (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
      (~copy ==> ~exprs_can_mutate cenv kw_es) /\
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
      read_result cx raw ee = (INL v,ee) /\
      vv_holds_mods cenv cx (lowered_value_type cenv e) raw sv ee t /\
      vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv t /\
      ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
      vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
    vv_storage_live H cx sv ee t /\
    (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
      ptr_buf_ok cenv e op G t) /\
    (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand G t) /\
    (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
      !tv w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
        eval_operand (vv_operand sv) t = SOME w ==>
        w2n w + type_memory_size tv <= lo /\
        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
          val_in_memory tv v (w2n w) mem))
End

Theorem ext_pos_saved_row_ctor:
  ext_pos_saved_row_mods lo cenv cx kw_es sa sb H e sv v ee G tn t /\
  cenv.ce_is_ctor /\ vv_location sv = SOME LocCode /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
  eval_operand (vv_operand sv) t = SOME w ==>
  w2n w + type_memory_size tv <= lo /\
  (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS o
    PURE_REWRITE_RULE [ext_pos_saved_row_mods_def]) >>
  qpat_assum `cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==> _` mp_tac >>
  simp[]
QED
