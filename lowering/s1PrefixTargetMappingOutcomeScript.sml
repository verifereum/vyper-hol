(* Request-prefix companion to bodyFullTargetMappingOutcome. *)
Theory s1PrefixTargetMappingOutcome
Ancestors
  s1PrefixPreds bodyFullTargetMappingOutcome s1PrefixDefs s1PrefixFrame
  vyperState vyperStorageTrace list

Theorem mapping_extension_prefix_outcome:
  extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript v) mid2 = (res,ee) /\
  gas_admissible (extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript v))
    target_res_ok mid2 /\
  storage_trace_domain cx st0 mid2.storage_trace /\
  mid2.gas_obs = [] /\
  ~t2.vs_halted /\
  eval_operand slot t = SOME (hashmap_slot base_slot (encode_hashmap_key kt v)) /\
  op_taint tn slot = {} /\
  op_prov G slot = NONE /\
  (!x. slot = Var x ==> not_fresh_at sb x) /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  wb_frame cenv es mid2 sa s0 t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid2 t /\
    storage_well_formed_on cx mid2 (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid2 G tn t /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (t2,G2,tn2) [] (OK t,G,tn)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG)
      cx st0 (extend_place cx (HashMapRef tr base_slot kt vt) (ValueSubscript v))
      (mid2,t2,G2,tn2)
Proof
  strip_tac >> irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_extend_place] >>
  Cases_on `vt` >> simp[extend_place_nested_mapping] >>
  rename1 `HashMapRef _ _ _ (Type typ)` >>
  Cases_on `evaluate_type (get_tenv cx) typ` >>
  simp[extend_place_mapping_leaf, DROP_APPEND1,
       extend_place_def, lift_option_type_def, bind_def, ignore_bind_def,
       raise_def, record_storage_event_def, return_def]
QED
