(* Conditional caller probe, not a real-call resource initialization theorem.
   s denotes the state AFTER the recovered ALLOCA.  The caller obligation
   below deliberately exposes what allocation/prelude integration must supply. *)
Theory entryReachBodyRegistrationBoundaryProbe
Ancestors
  entryReachBodySourceInstalledDecoder entryReachBodyPreludeFrame
  calldataRegistration calldataRegistrationExec finite_map compileEnv moduleLowering

Theorem entry_source_singleton_shell_probe:
  compile_register_positional_args ce
    [(name,prim,dyn,sz,type_to_abi_dec_info ce.ce_struct_fields ce ty)] off st = (cef,final) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME n /\
  (prim ==> ?c. type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord c) /\
  compile_register_positional_args body_ce tail next_off final = (body_env,registered) /\
  compile_guarded_body body_env F key ut iv fbody rt registered = ((),z) /\
  fn_has_code final z fn /\
  (* Exact canonical address; not merely an existential operand value. *)
  n2w sb = (if dyn /\ ~prim then n2w 4 + abi_decode_load CALLDATALOAD
    (n2w 4 + n2w (off-4):bytes32) s else n2w 4 + n2w (off-4)) /\
  (* Remaining allocation/prelude resource contract, intentionally conditional. *)
  (!buf allocated src first ready.
    compile_alloc_buffer n st = (buf,allocated) /\
    compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) first = ((),final) /\
    entry_prelude_frame s ready /\
    eval_operand src ready = SOME (n2w sb) /\
    abi_decoder_operand_live first.cs_next_var src ==>
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    entry_source_metadata ce env ce.ce_struct_fields ty tv
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
    mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
      (abi_decode_source CALLDATALOAD ready) = enc (vyper_to_abi_type env ty) av /\
    sb+LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
    cell+type_memory_size tv < dimword (:256) /\
    eval_operand buf.buf_operand ready = SOME (n2w cell) /\
    abi_decoder_operand_live first.cs_next_var buf.buf_operand /\
    final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st ready /\
    fn_has_code first final fn /\ abi_decoder_code first final /\
    fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
    oid NOTIN abi_decoder_ids first.cs_next_id final.cs_next_id /\
    window_alloca_sites fn (abi_decoder_ids first.cs_next_id final.cs_next_id) SUBSET ambient /\
    oid NOTIN ambient /\ entry_scratch_ready ambient b cap ready /\ alloca_inv ready /\
    abi_alloca_history (fn_insts fn) ready /\ alloca_frontier_inv ctx fn site ready /\
    entry_owned_region oid root extent cell (type_memory_size tv) ready /\
    ~ready.vs_halted /\ ready.vs_current_bb = first.cs_current_bb /\
    ready.vs_inst_idx = LENGTH first.cs_current_insts) ==>
  ?buf allocated head after_head src first ready t.
    compile_alloc_buffer n st = (buf,allocated) /\
    FLOOKUP cef.ce_vars name = SOME (PtrVar buf.buf_operand n) /\
    emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] allocated = (head,after_head) /\
    (if dyn /\ ~prim then
       ?offset after_load.
         emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
         emit_op ADD [Lit (n2w 4); offset] after_load = (src,first)
     else src = head /\ first = after_head) /\
    compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) first = ((),final) /\
    frag_exec_mem ctx allocated first (\u. u = s) (\u. u = ready) (\r. F) /\
    eval_operand src ready = SOME (n2w sb) /\
    abi_decoder_operand_live first.cs_next_var src /\
    (!op. abi_decoder_operand_live allocated.cs_next_var op ==>
      eval_operand op ready = eval_operand op s) /\
    entry_prelude_frame s ready /\
    array_child_result ctx fn oid root extent ambient
      (window_alloca_sites fn (abi_decoder_ids first.cs_next_id final.cs_next_id))
      b cap site limit_st first final cell tv v ready t
Proof
  strip_tac >> drule_all register_singleton_allocated_boundary >> strip_tac >>
  `FLOOKUP cef.ce_vars name = SOME (PtrVar buf.buf_operand n)` by
    simp[FLOOKUP_UPDATE] >>
  `var_location_decode_operand (PtrVar buf.buf_operand n) = SOME buf.buf_operand` by
    simp[var_location_decode_operand_def] >>
  drule_all registration_decoder_prelude >> strip_tac >>
  drule_all entry_registration_address_prelude_framed >>
  disch_then (qspecl_then [`s`,`ctx`] strip_assume_tac) >>
  `eval_operand src t = SOME (n2w sb)` by metis_tac[] >>
  first_x_assum (drule_at Any) >> simp[] >>
  disch_then (qspec_then `first` mp_tac) >> simp[] >> strip_tac >>
  `?out. array_child_result ctx fn oid root extent ambient
    (window_alloca_sites fn (abi_decoder_ids first.cs_next_id final.cs_next_id))
    b cap site limit_st first final cell tv v t out` by
    (irule entry_source_registration_decoder_endpoint >>
     qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `entry_source_metadata _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `compile_register_positional_args body_ce _ _ _ = _` (irule_at Any) >>
     simp[] >> qexists_tac `sb` >> simp[]) >>
  qexistsl_tac [`src`,`first`,`t`,`out`] >> simp[]
QED
