(* Published custom-error store loop and successful encoder endpoint. *)
Theory stmtSimCustomErrorStore
Ancestors
  stmtSimCustomErrorStoreHead stmtSimCustomErrorStoreLoop bodyCustomErrorHandoff
  abiEncoderAdmissible bodyCustomErrorWindowBounds valueEncoding valueEncodingDefs venomState

Theorem custom_error_store_args_sim:
  !args ce cx env off sa sb es tvs func inst x b asz s0 ctx tys.
  tys = MAP expr_type args /\
  compile_custom_error_store_args ce args tys (Var x) off sa = ((),sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  (!e ee. MEM e args /\ expr_sim_inv ce cx env ee ==>
    expr_body_pre ce cx env e ee) /\
  exprs_case F ctx func ce cx args /\
  (!e. MEM e args ==> (int_calls_expr e <> [] /\
    lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields)) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!ee. expr_sim_inv ce cx env ee ==> not_local_ptr ce ee.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list tvs <= asz /\ b+asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size_list tvs)) /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
    (\res ee r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env ee /\
      stmt_state_rel ctx func ce cx ee r /\
      tuple_in_memory vs tvs (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size_list tvs <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es ee s0 r /\
      (EVERY ($~ o expr_has_effect) args ==>
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          mem_bytes_at lo sz r.vs_memory = mem_bytes_at lo sz s0.vs_memory) /\
        (!p n. (p+n <= b \/ b+asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
            sa.cs_next_id <= i.inst_id /\
            FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
            regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory)))
    (\res ee exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  match_mp_tac custom_error_store_args_sim_using_head >>
  MATCH_ACCEPT_TAC custom_error_store_head_path
QED

(* The loop's zero-offset successful postcondition supplies tuple storage and
   the two preservation premises. Source value typing and conversion are
   deliberately explicit: tuple storage alone does not establish them. *)
Theorem custom_error_store_encoder_endpoint:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env ee /\
  evaluate_type (get_tenv cx) (TupleT (MAP SND params)) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  vyper_to_abi (get_tenv cx) (TupleT (MAP SND params)) (ArrayV (TupleV vs)) = SOME av /\
  tuple_in_memory vs tvs b r.vs_memory /\
  type_memory_size_list tvs <= asz /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas aid = SOME (b,asz) /\
  (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
    lookup_var z r = SOME w) /\
  (!i a. FLOOKUP s0.vs_allocas i = SOME a ==>
    FLOOKUP r.vs_allocas i = SOME a) ==>
  ?at rv.
    abi_encoder_admissible
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND params))) /\
    eval_operand (Var x) r = SOME (n2w b) /\
    FLOOKUP r.vs_allocas aid = SOME (b,asz) /\
    type_memory_bytes ce (TupleT (MAP SND params)) <= asz /\
    abi_encoder_window_input
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND params)))
      at rv b (type_memory_bytes ce (TupleT (MAP SND params))) r.vs_memory /\
    enc at rv = enc (vyper_to_abi_type (get_tenv cx) (TupleT (MAP SND params))) av /\
    LENGTH (enc at rv) <= abi_size_bound ce.ce_struct_fields (TupleT (MAP SND params))
Proof
  strip_tac >>
  `val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) b r.vs_memory` by
    simp[val_in_memory_def] >>
  drule_all custom_error_tuple_encoder_handoff >> strip_tac >>
  drule_all custom_error_expr_inv_memory_size >> strip_tac >>
  qexistsl_tac [`at`, `rv`] >>
  simp[abi_encoder_translation_admissible, type_memory_size_def,
       eval_operand_def]
QED
