(* The source oracle transition paired with its counted, checked CALL edge.
   The remaining local-memory frame is kept explicit at this boundary. *)
Theory rawCallOracleProofPtr
Ancestors
  oracleCallStepPtr extCallOracleStep rawCallAllocationProofPtr
  appendStorageGhostPtr decoderGhostFramePtr ptrDiscipline
  venomExecSemantics venomState venomCallOracleDefs bodyPtrDefs

Theorem oracle_call_checked_step:
  state_rel func cenv cx es s /\ inst.inst_outputs = [out] /\
  ((~stat /\ inst.inst_opcode = CALL /\
      inst.inst_operands = [gas_op;addr_op;value_op;ao_op;az_op;ro_op;rz_op]) \/
   (stat /\ inst.inst_opcode = STATICCALL /\
      inst.inst_operands = [gas_op;addr_op;ao_op;az_op;ro_op;rz_op])) /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr_op s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand ao_op s = SOME ao /\ eval_operand az_op s = SOME az /\
  eval_operand ro_op s = SOME ro /\ eval_operand rz_op s = SOME rz /\
  w2w aw = target /\ w2n (if stat then 0w else vw) =
    (case value_opt of NONE => 0 | SOME n => n) /\ stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\
  access_ok 0 G func inst s /\ taint_ok func tn inst s /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok cx tn s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  ?s'.
    exec_ext_call inst s gas aw (if stat then 0w else vw) ao az ro rz stat =
      OK (update_var out (if outcome.co_success then 1w else 0w) s') /\
    s' = s with <| vs_outcomes := s'.vs_outcomes; vs_requests := s'.vs_requests;
      vs_accounts := s'.vs_accounts; vs_transient := s'.vs_transient;
      vs_logs := s'.vs_logs; vs_pending_deletions := s'.vs_pending_deletions;
      vs_returndata := s'.vs_returndata; vs_memory := s'.vs_memory |> /\
    s'.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE (w2n rz) outcome.co_returnData) s).vs_memory /\
    s'.vs_returndata = outcome.co_returnData /\
    (local_ptrs_rel func cenv es.scopes s' /\
      immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s' ==>
      state_rel func cenv cx (SND (adopt_call_outcome rq outcome es1)) s') /\
    gas_path_ptr_edge (cx_dead cx) 0 ctx func PG G tn s 0
      (step_prov PG G inst (update_var out (if outcome.co_success then 1w else 0w) s'))
      (step_taint inst s (update_var out (if outcome.co_success then 1w else 0w) s') tn)
      (OK ((update_var out (if outcome.co_success then 1w else 0w) s')
        with vs_inst_idx := SUC s.vs_inst_idx)) /\
    stor_taint_ok cx
      (step_taint inst s (update_var out (if outcome.co_success then 1w else 0w) s') tn)
      (update_var out (if outcome.co_success then 1w else 0w) s') /\
    op_taint
      (step_taint inst s (update_var out (if outcome.co_success then 1w else 0w) s') tn)
      (Var out) = {} /\
    op_prov
      (step_prov PG G inst (update_var out (if outcome.co_success then 1w else 0w) s'))
      (Var out) = NONE
Proof
  strip_tac >> (
  `~s.vs_call_ctx.cc_static` by fs[compileEnvTheory.state_rel_def] >>
  drule_all exec_ext_call_oracle_step >>
  disch_then (strip_assume_tac o Q.ISPECL [`gas:bytes32`, `ro:bytes32`, `rz:bytes32`]) >>
  qexists_tac `s'` >> gvs[] >>
  `step_inst_base inst s =
    OK (update_var out (if outcome.co_success then 1w else 0w) s')` by
    (gvs[step_inst_base_def]) >>
  conj_tac
  >- (irule call_gas_path_ptr_edge >> simp[] >> metis_tac[]) >>
  conj_tac
  >- metis_tac[exec_ext_call_stor_taint_ok] >>
  simp[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
    step_prov_def, set_prov_def, out_prov_def, op_prov_def,
    finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE])
QED

