Theory bodyPtrPopScalarAppendEmitted
Ancestors
  bodyPtrPopScalarAppendOrigin bodyPtrPopSynchronizedStore
  bodyPtrPopRegionInvariant compileEnv vyperValue words ptrDiscipline
  venomState venomExecSemantics venomInst emitHelperProps fragExec vfmState

(* These are the payload and header cuts of scalar storage/transient append,
   not the intervening arithmetic, control flow, or a complete append trace. *)
Theorem pop_emitted_scalar_append:
  emit_void (if tr then TSTORE else SSTORE) [a;v] sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  eval_operand a s = SOME (n2w (bs+1+l)) /\ eval_operand v s = SOME value /\
  emit_void (if tr then TSTORE else SSTORE) [h;len] sc = ((),sd) /\
  run_inst_seq (emitted_insts sc sd) t = OK u /\
  eval_operand h t = SOME (n2w bs) /\ eval_operand len t = SOME (n2w (l+1)) /\
  bs+1+n <= dimword (:256) /\ l<n /\
  lookup_storage (n2w bs) (if tr then contract_transient s else contract_storage s) = n2w l /\
  pop_region_taint_ok (if tr then contract_transient s else contract_storage s)
    bs (ArrayTV (BaseTV (UintT 256)) (Dynamic n)) X ==>
  pop_region_taint_ok (if tr then contract_transient u else contract_storage u)
    bs (ArrayTV (BaseTV (UintT 256)) (Dynamic n))
    (key_update (key_update X (n2w (bs+1+l)) {}) (n2w bs) {})
Proof
  strip_tac >>
  drule_all pop_emitted_storage_store_backend >> strip_tac >>
  qpat_x_assum `run_inst_seq _ t = OK u` kall_tac >>
  drule_all pop_emitted_storage_store_backend >> strip_tac >>
  drule_all pop_region_taint_scalar_append >> simp[]
QED

Theorem pop_emitted_scalar_append_ghost:
  emit_void (if tr then TSTORE else SSTORE) [a;v] sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  eval_operand a s = SOME (n2w (bs+1+l)) /\ eval_operand v s = SOME value /\
  emit_void (if tr then TSTORE else SSTORE) [h;len] sc = ((),sd) /\
  run_inst_seq (emitted_insts sc sd) t = OK u /\
  eval_operand h t = SOME (n2w bs) /\ eval_operand len t = SOME (n2w (l+1)) /\
  tn1 = step_taint (mk_inst iid (if tr then TSTORE else SSTORE) [a;v] []) s t tn /\
  tn2 = step_taint (mk_inst iid (if tr then TSTORE else SSTORE) [h;len] []) t u tn1 /\
  op_taint tn v = {} /\ op_taint tn1 len = {} /\
  bs+1+n <= dimword (:256) /\ l<n /\
  lookup_storage (n2w bs) (if tr then contract_transient s else contract_storage s) = n2w l /\
  pop_region_taint_ok (if tr then contract_transient s else contract_storage s)
    bs (ArrayTV (BaseTV (UintT 256)) (Dynamic n))
    (if tr then tn.t_trans else tn.t_stor) ==>
  pop_region_taint_ok (if tr then contract_transient u else contract_storage u)
    bs (ArrayTV (BaseTV (UintT 256)) (Dynamic n))
    (if tr then tn2.t_trans else tn2.t_stor)
Proof
  strip_tac >> drule_all pop_emitted_scalar_append >>
  Cases_on `tr` >>
  gvs[step_taint_def, store_taint_def, adopt_reset_def, mk_inst_def]
QED
