(* The linked frame at the zero-instruction external return. *)
Theory bodyExtReturnMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv exprBodyPreProps exprSimExtCallCase
  fragGasOriginPtr bodyPtrDefs exprSimMemDefs loweringPosts exprLowering
  compileEnv context vyperInterpreter vyperAST vyperState vyperABI
  venomState valueEncoding valueEncodingDefs vyperTypeSystem
Libs monadsyntax

Theorem extcall_return_void_mods[local]:
  expr_body_pre_mods mods cenv cx env
    (Call ann (ExtCall stat skip (fname,arg_types,NoneT) opts) args dflt) es /\
  extcall_returned st0 ctx func cenv cx NoneT es sa s0 sr addr buf cap target
    has_default default_op default_ty default_opt bs ee t /\
  immutable_frame_mods func cenv cx ee t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t) ==>
  (!tail. (case (if bs = [] then default_opt else NONE) of
     SOME v => do accounts' <- get_accounts;
                  check (skip \/ ext_call_has_code target accounts')
                    "ExtCall target has no code";
                  return (Value v) od
   | NONE => do v <- lift_sum_runtime
                      (evaluate_abi_decode_return (get_tenv cx) NoneT bs);
                return (Value v) od) (ee with gas_obs := tail) =
     (INL (Value NoneV),ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK t,G,tn) /\
    vv_post_mods H ctx func cenv cx
      (Call ann (ExtCall stat skip (fname,arg_types,NoneT) opts) args dflt)
      es sa sr s0 ee (Value NoneV) (StackValue NoneT (Lit 0w)) t /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t)
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  `ann = NoneT` by fs[Once well_typed_expr_def] >>
  qpat_x_assum `ann = NoneT` SUBST_ALL_TAC >>
  fs[extcall_returned_def,extcall_default_ready_def] >>
  `default_opt = NONE` by (Cases_on `default_opt` >> fs[]) >>
  conj_tac
  >- simp[evaluate_abi_decode_return_def,needs_external_call_wrap_def,
          evaluate_abi_decode_returndata_def,vyper_abi_size_bound_def,
          vyper_valid_enc_returndata_def,decode_abi_value_def,vyper_is_dynamic_def,
          vyper_decode_valid_enc_def,bind_def,return_def,lift_sum_runtime_def] >>
  rpt gen_tac >> strip_tac >>
  simp[gas_origin_ptr_path_rules,vv_post_mods_def,vv_holds_mods_def,
       vv_place_ptr_mods_def,vv_place_ptr_def,vv_holds_def,vv_at_def,
       post_value_type_def,expr_type_def] >>
  fs[wb_frame_def, read_result_def, return_def, expr_val_rel_def,
     expr_val_at_def, eval_operand_def, is_word_type_def, val_in_memory_def,
     val_footprint_def, type_memory_size_def, val_wf_def] >>
  first_assum ACCEPT_TAC
QED
