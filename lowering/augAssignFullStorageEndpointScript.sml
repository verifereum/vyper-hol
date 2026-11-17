(* A normal storage write has one path endpoint and its all-horizon ghosts. *)
Theory augAssignFullStorageEndpoint
Ancestors
  augAssignFullStore augAssignFullStoreGhost vyperStorageFootprint

Theorem augassign_storage_endpoint_joint:
  emit_void (if tr then TSTORE else SSTORE) [addr;op] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_call_ctx.cc_static /\
  eval_operand addr s = SOME slot /\ eval_operand op s = SOME w /\
  op_taint tn addr = {} /\ op_taint tn op = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  es'.scopes = es.scopes /\ s.vs_call_ctx.cc_address = cx.txn.target /\
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G tn /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
    dead_lo_ok H (DF H) lo cenv cx /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s /\
    (!k b. storage_dead H tr
      (update_storage slot w (if tr then contract_transient s else contract_storage s)) k b =
      storage_dead H tr (if tr then contract_transient s else contract_storage s) k b)) /\
  u = ((if tr then tstore slot w s else sstore slot w s)
        with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  un = (if tr then tn with t_trans := key_update tn.t_trans slot {}
        else tn with t_stor := key_update tn.t_stor slot {}) ==>
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G un /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G,un) /\
    ghost_inv_at (DF H) lo d cenv cx es' G un u)
Proof
  strip_tac >> gvs[] >> conj_tac
  >- (irule ghost_kept_at_storage_word_store >> simp[]) >>
  qx_gen_tac `H` >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >> conj_tac
  >- (irule storage_word_store_origin_ptr >> simp[] >>
      qexistsl [`addr`, `op`, `sa`] >> simp[]) >>
  irule (INST_TYPE [Type.alpha |-> ``:256``] ghost_inv_at_storage_word_store) >>
  simp[] >> conj_tac
  >- (qexists_tac `H` >> simp[]) >>
  qexists_tac `es` >> simp[]
QED
