(* Specialization of the storage-leaf selector at a linked Subscript cut. *)
Theory bodyMapSelectLeafAdapterMods
Ancestors
  bodyMapSelectLeafMods bodyFullPostsMods gasOutcomeFullMods gasOutcomeFullPostMods
  gasContext fragGasOriginPtr gasOutcomeFull loweringPosts vyperAST arithmetic

Definition mapping_leaf_select_post_mods_def:
  mapping_leaf_select_post_mods DF lo d ctx func cenv cx ann obj idx
      es sa sb s0 vv G0 tn0 = \H res ee G tn t.
    ?tv. res = INL tv /\
      vv_post_mods H ctx func cenv cx (Subscript ann obj idx) es sa sb s0 ee tv vv t /\
      vv_store_bound cx (post_value_type cenv (Subscript ann obj idx))
        (lowered_value_type cenv (Subscript ann obj idx)) ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv (Subscript ann obj idx)) tv vv ee G tn t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv (Subscript ann obj idx)) /\
           ~is_bytestring_type (post_value_type cenv (Subscript ann obj idx)) ==>
           vv_own cenv cx (post_value_type cenv (Subscript ann obj idx)) sa sb ee tv vv t /\
           (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val,ee) /\
             !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Subscript ann obj idx)) =
                    SOME rt /\ eval_operand (vv_operand vv) t = SOME w ==>
                    w2n w + type_memory_size rt <= lo /\
                    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                           val_in_memory rt val (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv (Subscript ann obj idx)) ==>
               ptr_buf_ok cenv (Subscript ann obj idx) op G t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok cenv (Subscript ann obj idx) p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
End

Definition mapping_select_exit_mods_def:
  mapping_select_exit_mods ctx cx =
    \H res ee (gt : (string |-> num # num) # taint) q.
    expr_exit res q /\ halt_exit H cx ee res q /\
    (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s)
End

Theorem mapping_select_leaf_adapter_mods:
  evaluate_type (get_tenv cx) ann = SOME rt /\
  fin.gas_obs = [] /\ ~it.vs_halted /\
  vv = LocatedValue ann (mk_ptr outop (slot_loc tr)) /\
  eval_operand outop u = SOME (hashmap_slot slot (encode_hashmap_key (expr_type idx) v)) /\
  op_taint tnu outop = {} /\
  wb_frame cenv es fin sa s0 u /\
  (~expr_has_effect (Subscript ann obj idx) ==> pure_frame cenv func es sa s0 u) /\
  u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tnu /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (it,Gi,tni) [] (OK u,Gu,tnu) /\
    stmt_state_rel H ctx func cenv cx fin u /\
    immutable_frame_mods func cenv cx fin u /\
    storage_well_formed_on cx fin (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx fin Gu tnu u) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0
    (select_result cx (expr_type obj) (HashMapRef tr slot (expr_type idx) (Type ann))
      (ValueSubscript v)) (fin,it,Gi,tni)
    (mapping_leaf_select_post_mods DF lo d ctx func cenv cx ann obj idx es sa sb s0 vv G0 tn0)
    (mapping_select_exit_mods ctx cx)
Proof
  pure_rewrite_tac [mapping_leaf_select_post_mods_def, mapping_select_exit_mods_def] >>
  ACCEPT_TAC (Q.INST [`kt` |-> `expr_type idx`,
     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
     `R` |-> `\H res ee gt q. expr_exit res q /\ halt_exit H cx ee res q /\
          (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s)`]
    mapping_select_leaf_mods)
QED
