(* Diagnostic only: these ML terms are NOT asserted theorems or new predicates.
   The receipt in docs/proof-progress/calldata-exact-interface.md records gaps. *)
Theory calldataExactInterfaceProbe
Ancestors
  calldataFiniteTyped calldataBulkUniformPtr calldataClampPtr
  calldataRecursiveExecution calldataRegistrationExec
  abiDecoderCoherence abiDecoderPhi abiDecoderContract abiDecoderReentry
  fragGasOriginPtr compileEnv loweringStateRelDefs venomState venomExecSemantics
  vyperCalldata exprLowering valueEncoding words finite_map list arithmetic

(* Free ce/env/sf/ty/tv are precisely the induction parameters. Every varying
   compiler interval, ambient limit, state, allocation and ghost is quantified.
   This is a candidate interface, not a claim that its premises suffice. *)
val exact_decoder_contract = ``
  !st last limit ctx fn site src child initial p d oid base_addr cap G tn lower PG.
  abi_decoder_coherent ce env sf ty tv /\
  compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),last) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  last.cs_next_var <= limit.cs_next_var /\
  unit_alloca_budget ctx < dimword (:256) /\
  (last.cs_current_insts = [] ==> !bb.
    lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  eval_operand src initial = SOME p /\
  eval_operand (Var child) initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var child) /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  (!id q k. st.cs_next_id <= id /\ id < last.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d /\ d+type_memory_size tv <= base_addr+cap /\
  d+type_memory_size tv < dimword (:256) /\
  ptr_covers G tn child initial (type_memory_size tv) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  fresh_vars_wrt limit initial /\ allocas_from lower initial /\
  lower <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = NONE /\
   ?z H u. z.vs_returndata = [] /\
     (?fuel. run_from fuel ctx fn initial = Abort Revert_abort z /\
       mem_safe_run fuel ctx fn initial) /\
     (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
       (initial,G,tn) [] (Abort Revert_abort z,H,u))) \/
  ?v x sc H u.
    cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x /\
    ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\ value_has_type tv x /\
    val_wf tv x /\ val_in_memory tv x d v.vs_memory /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial)) /\
    v.vs_call_ctx = initial.vs_call_ctx /\
    v.vs_data_section = initial.vs_data_section /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    (!id q k. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= v.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ last.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,type_memory_size tv)::sc) initial v /\
    (!q k. MEM (q,k) sc ==> ?id. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    fresh_vars_wrt limit v /\ ptr_covers H u child v (type_memory_size tv) /\
    (!name. not_fresh_at st name ==> FLOOKUP H name = FLOOKUP G name /\
      FLOOKUP u.t_var name = FLOOKUP tn.t_var name) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (initial,G,tn) [] (OK v,H,u))``;

(* All child contracts use the identical expanded schema. The struct child
   MUST substitute both descending maps; ce remains the full layout map. *)
val schema_term = Parse.parse_in_context (free_vars exact_decoder_contract);
val array_child_contract = exact_decoder_contract;
val struct_child_contract = Term.subst
  [schema_term `env` |-> schema_term `env \\ nsid`,
   schema_term `sf` |-> schema_term `sf \\ nsid_to_string nsid`] exact_decoder_contract;
val positional_child_contract = Term.subst
  [schema_term `sf` |-> schema_term `ce.ce_struct_fields`] exact_decoder_contract;
val _ = List.app (fn t =>
  if type_of t = bool then () else raise Fail "non-boolean decoder interface")
  [exact_decoder_contract, array_child_contract, struct_child_contract,
   positional_child_contract];
val _ = print "Exact decoder and three expanded child contracts typechecked (not proved).\n";

(* Catch accidental free parser variables, in addition to checking boolean type. *)
val _ = let val vs = free_vars exact_decoder_contract in
  if length vs = 5 andalso List.all
    (fn v => List.exists (fn n => fst (dest_var v) = n)
      ["ce","env","sf","ty","tv"]) vs
  then List.app (fn v => print (term_to_string v ^ "\n")) vs
  else raise Fail "unintended free variable in exact decoder schema"
end;

(* Bounded interface tests inspect existing kernel theorem statements. They do
   not use theorem constructors and do not assert the unproved exact schema. *)
local
  fun has_const name tm =
    can (find_term (fn t => is_const t andalso
      #Name (dest_thy_const t) = name)) tm;
  fun check msg b = if b then print (msg ^ "\n") else raise Fail msg;
  fun parts th = dest_imp (#2 (strip_forall (concl th)));
  val (clamp_in,clamp_out) = parts
    calldata_clamp_overwrite_prefix_uniform_origin;
  val (bulk_in,bulk_out) = parts
    calldata_bulk_decoder_endpoint_ptr_uniform_origin;
  val (_,recursive_out) = parts calldata_coherent_owned_run;
  val (_,positional_out) = parts registration_positional_owned_run;
in
  val _ = check "Scalar residual: successful run_inst_seq is an INPUT, not constructed."
    (has_const "run_inst_seq" clamp_in andalso
     not (has_const "cd_decode" clamp_out));
  val _ = check "Bulk residual: successful run_inst_seq is an INPUT; no source exactness."
    (has_const "run_inst_seq" bulk_in andalso
     has_const "gas_origin_ptr_path" bulk_out andalso
     not (has_const "cd_decode" bulk_out));
  val _ = check "Recursive owned result: typed memory, but no source or pointer observation."
    (has_const "val_in_memory" recursive_out andalso
     not (has_const "cd_decode" recursive_out) andalso
     not (has_const "gas_origin_ptr_path" recursive_out));
  val _ = check "Struct child: both env and sf descend; ambient limit remains quantified."
    (not (aconv struct_child_contract exact_decoder_contract) andalso
     has_const "fresh_vars_wrt" struct_child_contract);
  val _ = check "Positional owned result: outputs allocated, but no decode-list rejection observation."
    (has_const "FLOOKUP" positional_out andalso
     has_const "val_in_memory" positional_out andalso
     not (has_const "calldata_decode_args" positional_out) andalso
     not (has_const "gas_origin_ptr_path" positional_out));
end;

(* Universal closure is the proposed higher-order child hypothesis. No logical
   constant or named theorem is introduced by forming these ML terms. *)
val universal_array_child = list_mk_forall
  (free_vars array_child_contract, array_child_contract);
val universal_struct_child = list_mk_forall
  (free_vars struct_child_contract, struct_child_contract);
val universal_positional_child = list_mk_forall
  (free_vars positional_child_contract, positional_child_contract);
val _ = List.app (fn t =>
  if null (free_vars t) then () else raise Fail "open child hypothesis")
  [universal_array_child,universal_struct_child,universal_positional_child];
