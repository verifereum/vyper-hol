Theory entryCreateAbiRowsScope
Ancestors
  bodyFullCreateHeld bodyFullExtCallDirectState abiEncodeValuesRun
  entryCreatePathScope createSizePrefixReplay abiEncoderProps exprLoweringProps
  fragGasOriginPtr fragExec loweringPosts venomInst venomState

Theorem abi_create_prefix_observer[local]:
  (!bb inst. lookup_block fin.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH fin.cs_current_insts) = SOME inst ==>
    fin.cs_next_id <= inst.inst_id) ==>
  abi_encode_values_observer st fin
    (\a c u v. create_expr_prefix a c explicit ctx func u [] v)
    (\u v. create_expr_prefix st fin explicit ctx func u [] v)
Proof
  strip_tac >> simp[abi_encode_values_observer_def] >> conj_tac
  >- (rpt strip_tac >> drule_all create_expr_prefix_append >> simp[]) >>
  rpt strip_tac >> irule create_expr_prefix_lift >>
  first_assum (irule_at Any) >> fs[ci_mono_def, frag_ids_def] >>
  rpt strip_tac >> res_tac >> decide_tac
QED

(* The caller supplies the phase laws, not a second run of the encoder.
   In the fixed-band fold, the exit fetch is outside every local segment. *)
Theorem create_encoded_rows_window_of_confined_steps:
  LENGTH args = LENGTH vals /\ LENGTH args = LENGTH vs /\
  EVERY (\e. expr_body_pre ce cx env e ee) args /\
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env ee /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!i. i < LENGTH args ==>
    ?e saved v raw si sm ss vv copy tv.
      e = EL i args /\ saved = EL i vals /\ v = EL i vs /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
      type_memory_size tv < 2**64 /\ value_has_type tv v /\
      compile_expr ce (expr_type e) e si = (vv,sm) /\
      compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) sm = (saved,ss) /\
      ((?tag op0. saved = StackValue tag op0) \/
       (?p. saved = LocatedValue (lowered_value_type ce e) p /\
            ~is_word_type (lowered_value_type ce e) /\ p.ptr_location = LocMemory) \/
       (?p. saved = LocatedValue (lowered_value_type ce e) p /\
            ~is_word_type (lowered_value_type ce e) /\ p.ptr_location <> LocMemory /\
            lowered_value_type ce e = expr_type e /\ saved = vv)) /\
      local_ptrs_reserved ce si /\ sm.cs_next_var <= se.cs_next_var /\ sm.cs_next_id <= se.cs_next_id /\
      ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id /\
      (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!l. vv_operand saved <> Label l) /\ read_result cx raw ee = (INL v,ee) /\
      vv_holds ce cx (lowered_value_type ce e) raw saved ee s /\
      vv_at ce cx (lowered_value_type ce e) si ss ee raw saved s /\
      ptr_vv_ok cx (lowered_value_type ce e) raw saved ee G tn s /\
      vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee raw saved s /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==> vv_storage_live H cx saved ee s) /\
      ((case saved of StackValue tag op0 => ~is_word_type (lowered_value_type ce e)
        | LocatedValue tag p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok ce e (vv_operand saved) G s)) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  LENGTH prefix + abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) <= capacity /\
  compile_abi_encode_values_to_buf ce (Var payload_var) (ZIP (vals,MAP (lowered_value_type ce) args)) st =
    (alen,fin) /\ fn_has_code st fin func /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
    shared pbase capacity root payload_var (LENGTH prefix) prefix st initial Gi ti /\
  abi_encode_values_init_observes ctx func lo explicit PG
    (\a c u v. create_expr_prefix a c explicit ctx func u [] v) /\
  abi_encode_values_finish_observes ctx func lo explicit PG
    (\a c u v. create_expr_prefix a c explicit ctx func u [] v) /\
  create_saved_row_observes ctx func lo explicit PG
    (\a c u v. create_expr_prefix a c explicit ctx func u [] v) /\
  (!bb inst. lookup_block fin.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH fin.cs_current_insts) = SOME inst ==>
    fin.cs_next_id <= inst.inst_id) ==>
  ?bytes z Gz tz.
    encode_create_ctor_args (get_tenv cx) (MAP expr_type args) vs = SOME bytes /\
    pure_frame ce func ee se initial z /\ wb_frame ce ee ee se initial z /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
      shared pbase capacity root payload_var (LENGTH prefix) prefix fin z Gz tz /\
    eval_operand alen z = SOME (n2w (LENGTH bytes)) /\ op_taint tz alen = {} /\
    (!x. alen = Var x ==> not_fresh_at fin x) /\
    LENGTH prefix + LENGTH bytes <= capacity /\ pbase + capacity <= z.vs_alloca_next /\
    read_memory pbase (LENGTH (prefix ++ bytes)) z = prefix ++ bytes /\
    (!j. pbase <= j /\ j < pbase + LENGTH (prefix ++ bytes) ==> j NOTIN tz.t_mem) /\
    create_expr_prefix st fin explicit ctx func initial [] z /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (initial,Gi,ti) [] (OK z,Gz,tz)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (BETA_RULE (Q.INST
    [`Obs` |-> `\a c u v. create_expr_prefix a c explicit ctx func u [] v`,
     `R` |-> `\u v. create_expr_prefix st fin explicit ctx func u [] v`]
    create_encoded_rows_window_observed)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                irule abi_create_prefix_observer >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED
