(* A reached default MsgGas head consumes the very word observed by the source. *)
Theory s1PrefixBoolChainDefaultMsgGasStep
Ancestors
  s1PrefixBoolChainDefaultMsgGasConcreteStep

Theorem bool_chain_default_msggas_step:
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  gas_shadow_function func shadow_func /\
  ~s.vs_halted /\ s.vs_gas_readings = w::readings /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id GAS [] [out]) /\
  lookup_block shadow_lbl shadow_func.fn_blocks = SOME shadow_bb /\
  get_instruction shadow_bb shadow_idx = SOME (mk_inst id GASPRICE [] [out]) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       ptr_inst_ok (DF H) lo 0 ctx func G tn (mk_inst id GAS [] [out]) s) ==>
  ?t G1 tn1.
    (!tail. bind (eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) []))
      (read_result cx)
      (es with gas_obs := gas_explicit [T] s.vs_gas_readings ++ tail) =
      (INL (IntV (&w2n w)), es with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s,G,tn) [T] (OK t,G1,tn1)) /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = SUC s.vs_inst_idx /\ t.vs_gas_readings = readings /\
    eval_operand (Var out) t = SOME w /\
    G1 = step_prov PG G (mk_inst id GAS [] [out])
           (update_var out w (s with vs_gas_readings := readings)) /\
    tn1 = step_taint (mk_inst id GAS [] [out]) s
            (update_var out w (s with vs_gas_readings := readings)) tn
Proof
  strip_tac >> drule_all bool_chain_default_msggas_step_concrete >>
  disch_then (qspec_then `PG` (qx_choosel_then [`t`,`G1`,`tn1`] strip_assume_tac)) >>
  qexistsl_tac [`t`,`G1`,`tn1`] >> simp[]
QED
