(* Bounded interface diagnostic. ML quotations below are terms, NOT theorems.
   No assertion of a complete array decoder or new semantic predicate is made. *)
Theory calldataArrayIterationProbe
Ancestors
  calldataArrayRawCallsite calldataExactInterfaceProbe calldataDynOwned
  robustCopyTransportPtr exprSimProps abiDecoderFrame allocaFrontierBound
  allocaBudgetProps allocaHistory vyperCalldata abiDecoderPhi
  abiDecoderCoherence abiDecoderContract abiDecoderReentry
  loweringStateRelDefs compileEnv fragGasOriginPtr bodyPtrDefs ptrDiscipline
  valueEncodingProps valueEncodingDefs valueEncoding venomState
  venomExecSemantics words finite_map pred_set list arithmetic

(* Fixed ce/env/sf/ty/tv only: all execution parameters are universally bound.
   This repeats the baseline diagnostic schema, retaining EVERY clause, and
   spells out the additional robustness/world frame required by C1.9. *)
val fixed_element_contract = ``
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
      (initial,G,tn) [] (OK v,H,u)) /\
    (!mem. mem_agree_outside u.t_mem v.vs_memory mem ==>
      val_in_memory tv x d mem) /\
    v.vs_accounts = initial.vs_accounts /\
    v.vs_transient = initial.vs_transient /\
    v.vs_logs = initial.vs_logs /\
    v.vs_outcomes = initial.vs_outcomes /\
    v.vs_requests = initial.vs_requests /\
    v.vs_pending_deletions = initial.vs_pending_deletions /\
    v.vs_tx_ctx = initial.vs_tx_ctx /\
    v.vs_block_ctx = initial.vs_block_ctx /\
    v.vs_fmp = initial.vs_fmp /\
    v.vs_gas_readings = initial.vs_gas_readings``;

(* The nonwrapping premise of the convenience wrapper is NOT valid for every
   source word. This is not a counterexample to any frozen family target. *)
Theorem array_iteration_wrapping_header[local]:
  w2n (n2w (dimword (:256)-16):bytes32) = dimword (:256)-16 /\
  cd_at F (dimword (:256)-16) 32 = 16 /\
  ~(dimword (:256)-16+32 < dimword (:256))
Proof
  simp[cd_at_def, dimword_def, w2n_n2w]
QED

Theorem array_iteration_modular_header[local]:
  !p:bytes32. cd_at F (w2n p) 32 = w2n (p+32w)
Proof
  simp[cd_at_def, word_add_def, w2n_n2w]
QED

Theorem array_iteration_normalized_member[local]:
  cd_member_ptr F cd tv (sb+32) ofs =
  cd_member_ptr F cd tv ((sb+32) MOD dimword (:256)) ofs
Proof
  simp[cd_member_ptr_def, cd_at_def, LET_THM, MOD_PLUS]
QED

Theorem array_iteration_cursor_frontier[local]:
  alloca_frontier_inv ctx fn site (s with vs_inst_idx := n) <=>
  alloca_frontier_inv ctx fn site s
Proof
  simp[alloca_frontier_inv_def, remaining_alloca_budget_def]
QED

(* Use the return-frame window AND shrinking dirty set, not the physical
   memory frame alone. A child may clean extra bytes outside its own cell. *)
Theorem array_iteration_robust_prefix[local]:
  stride = type_memory_size tv /\ EVERY (val_wf tv) xs /\ LENGTH xs = j /\
  mem_bytes_at dst (32+j*stride) t.vs_memory =
    mem_bytes_at dst (32+j*stride) s.vs_memory /\ dirty' SUBSET dirty /\
  (!k. k < j ==> !mem. mem_agree_outside dirty s.vs_memory mem ==>
    val_in_memory tv (EL k xs) (dst+32+k*stride) mem) ==>
  !k. k < j ==> !mem. mem_agree_outside dirty' t.vs_memory mem ==>
    val_in_memory tv (EL k xs) (dst+32+k*stride) mem
Proof
  strip_tac >> qx_gen_tac `k` >> strip_tac >>
  `val_wf tv (EL k xs)` by metis_tac[EVERY_EL] >>
  `val_footprint tv (EL k xs) <= stride` by metis_tac[val_footprint_le] >>
  rpt strip_tac >> irule calldata_member_robust_window_frame >>
  simp[] >>
  qexistsl_tac [`t.vs_memory`, `dirty'`, `s.vs_memory`, `dirty`] >> simp[] >>
  `SUC k * stride <= j * stride` by simp[] >>
  `32+k*stride+val_footprint tv (EL k xs) <= 32+j*stride` by
    (qpat_x_assum `SUC k * stride <= j * stride` mp_tac >>
     pure_rewrite_tac [MULT_CLAUSES] >> decide_tac) >>
  drule mem_bytes_at_translated_window >>
  disch_then (qspecl_then [`32+k*stride`, `val_footprint tv (EL k xs)`] mp_tac) >>
  gvs[]
QED

Theorem array_iteration_index_edges[local]:
  !count j.
  ((0:num) < count /\ count < dimword (:256) ==>
    w2n (n2w (0:num):bytes32) = 0 /\ SUC 0 <= count) /\
  (j < count /\ count < dimword (:256) /\ j+1 = count ==>
    (n2w j:bytes32)+1w = n2w count /\ SUC j = count) /\
  ~((0:num) < 0) /\
  (!tv dst dirty mem. !k. k < LENGTH ([]:value list) ==>
    !m. mem_agree_outside dirty mem m ==>
      val_in_memory tv (EL k []) (dst+32+k*type_memory_size tv) m)
Proof
  simp[word_add_n2w]
QED

(* Application probes are ML terms only. Instantiating a schema is NOT proving
   it or assuming its universally closed all-types version. *)
local
  fun check msg b = if b then print (msg ^ "\n") else raise Fail msg;
  fun has_const name tm = can (find_term (fn t => is_const t andalso
    (#Name (dest_thy_const t) = name orelse
     String.isSuffix ("." ^ name) (#Name (dest_thy_const t))))) tm;
  fun parts th = dest_imp (#2 (strip_forall (concl th)));
  val (params,body) = strip_forall fixed_element_contract;
  val parse = Parse.parse_in_context (params @ free_vars body);
  fun parameter name = valOf (List.find (fn v => fst (dest_var v) = name) params);
  fun specialize sub = Term.subst (map (fn {redex,residue} =>
    {redex=redex, residue=Term.inst (match_type (type_of residue) (type_of redex)) residue}) sub);
  val instance = specialize
    [parameter "st" |-> parse `ready`,
     parameter "last" |-> parse `child_end`,
     parameter "initial" |-> parse `a`,
     parameter "src" |-> parse `FST (SND ops)`,
     parameter "child" |-> parse `child_name`,
     parameter "p" |-> parse `n2w (cd_member_ptr F a.vs_call_ctx.cc_calldata tv
       (cd_at F sb 32) (j*tv_abi_size tv))`,
     parameter "d" |-> parse `dst+32+j*type_memory_size tv`] body;
  val (child_in,child_out) = dest_imp instance;
  val loop_prefix = ``
    !j count.
    j < count /\ count <= bound /\ count < dimword (:256) /\
    LENGTH xs = j /\ EVERY (val_wf tv) xs /\
    (!k. k < j ==> cd_decode F initial.vs_call_ctx.cc_calldata tv
      (cd_member_ptr F initial.vs_call_ctx.cc_calldata tv
        (cd_at F sb 32) (k*tv_abi_size tv)) = SOME (EL k xs)) /\
    (!k. k < j ==> !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv (EL k xs) (dst+32+k*type_memory_size tv) mem) /\
    lookup_var q s = SOME (n2w slot) /\ mload slot s = n2w j /\
    FLOOKUP s.vs_allocas counter_id = SOME (slot,32) /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
    ptr_covers G tn q s 32 /\ ptr_covers G tn root s cap /\
    (!a. slot <= a /\ a < slot+32 ==> a NOTIN tn.t_mem) /\
    eval_operand src s = SOME (n2w sb) /\ lookup_var root s = SOME (n2w dst) /\
    base_addr <= dst /\ dst+32+bound*type_memory_size tv <= base_addr+cap /\
    dst+32+bound*type_memory_size tv < dimword (:256) /\
    alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
    fresh_vars_wrt limit s /\ allocas_from lower s /\
    lower <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    (!id off sz. lo <= id /\ id < hi /\
      FLOOKUP s.vs_allocas id = SOME (off,sz) ==>
      sz = 32 /\ off < dimword (:256) /\ off+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    (?scratch. abi_decode_footprint_frame
      ((dst,32+bound*type_memory_size tv)::scratch) initial s /\
      !off sz. MEM (off,sz) scratch ==>
        ?id. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (off,sz))``;
  val (raw_in,_) = parts calldata_array_raw_child_callsite;
  val (setup_in,setup_out) = parts calldataDynStepTheory.calldata_element_setup_reentry;
  val (ptr_in,ptr_out) = parts decoderArraySetupPtrTheory.calldata_array_element_setup_endpoint_ptr_origin_core;
  val (return_in,return_out) = parts calldata_array_raw_child_return_frame;
  val (_,step_out) = parts calldata_owned_header_step_observed;
  (* Explicit term applications at this same iteration. These carry the
     supplier antecedents; none is discharged by merely forming the term. *)
  fun instantiate th substitutions = let
    val tm = #2 (strip_forall (concl th));
    val vs = free_vars tm;
    val p = Parse.parse_in_context vs;
    fun one (name,q) = let
      val v = valOf (List.find (fn v => fst (dest_var v) = name) vs)
    in v |-> p q end
  in specialize (map one substitutions) tm end;
  val setup_instance = instantiate calldataDynStepTheory.calldata_element_setup_reentry
    [("ip",`Var q`),("dst",`Var root`),("abi_sz",`tv_abi_size tv`),
     ("mem_sz",`type_memory_size tv`)];
  val return_instance = instantiate calldata_array_raw_child_return_frame
    [("stride",`type_memory_size tv`),("s",`a`),("t",`v`),
     ("scratch",`sc`),("lo",`ready.cs_next_id`),("hi",`child_end.cs_next_id`)];
  val backedge_instance = instantiate calldata_owned_header_step_observed
    [("st0",`body_st`),("middle",`ready`),("st1",`child_end`),
     ("abi_sz",`tv_abi_size tv`)];
  val scratch_instance = instantiate calldata_footprint_accumulate
    [("d",`dst`),("sz",`32+bound*type_memory_size tv`),
     ("e",`dst+32+j*type_memory_size tv`),("stride",`type_memory_size tv`),
     ("new",`sc`),("u",`a`)];
  val (_,accepted) = dest_disj child_out;
  val (_,accepted_body) = strip_exists accepted;
  val (return_need,_) = dest_imp return_instance;
  val child_frame = hd (List.filter (has_const "abi_decode_footprint_frame")
    (strip_conj accepted_body));
  val return_frame = hd (List.filter (has_const "abi_decode_footprint_frame")
    (strip_conj return_need));
  val scratch_frames = List.filter (has_const "abi_decode_footprint_frame")
    (strip_conj (fst (dest_imp scratch_instance)));
in
  val _ = check "Setup, accepted-return and observed-backedge instances typecheck (antecedents remain obligations)."
    (List.all (fn t => type_of t = bool)
      [setup_instance,return_instance,backedge_instance]);
  val _ = check "Accepted child's footprint matches return-frame premise at this exact cell."
    (aconv child_frame return_frame);
  val _ = check "Accepted child's footprint also matches scratch accumulation's second frame."
    (aconv child_frame (List.nth (scratch_frames,1)));
  val _ = check "Fixed child: baseline resource and execution premise names retained."
    (List.all (fn n => if has_const n child_in then true else
      (print ("Missing constant name: " ^ n ^ "\n");
       List.app (fn t => print (#Name (dest_thy_const t) ^ " "))
         (find_terms is_const child_in); print "\n"; false))
      ["abi_decoder_coherent","fn_has_code","fn_inst_ids_distinct",
       "unit_alloca_budget","phi_prefix_length","eval_operand",
       "alloca_inv","alloca_frontier_inv","FLOOKUP","ptr_covers",
       "op_taint","op_prov","fresh_vars_wrt","allocas_from",
       "ctx_has_dalloca","vs_halted","vs_current_bb","vs_inst_idx"]);
  val _ = check "Fixed child: only ce/env/sf/ty/tv free before specialization."
    (length (free_vars fixed_element_contract) = 5);
  val _ = check "Child instance: setup operands, modular source and current cell typecheck."
    (type_of instance = bool andalso has_const "cd_member_ptr" child_in);
  val _ = check "Loop prefix: exact source values, robust old cells, local ownership and ambient freshness typecheck."
    (type_of loop_prefix = bool andalso has_const "cd_decode" loop_prefix andalso
     has_const "mem_agree_outside" loop_prefix andalso
     has_const "fresh_vars_wrt" loop_prefix);
  val _ = check "Child instance retains rejection, common ghosts, robust result and all world fields."
    (List.all (fn n => has_const n child_out)
      ["cd_decode","gas_origin_ptr_path","mem_agree_outside",
       "vs_accounts","vs_transient","vs_logs","vs_outcomes","vs_requests",
       "vs_pending_deletions","vs_tx_ctx","vs_block_ctx","vs_fmp","vs_gas_readings"]);
  val _ = check "Residual: raw wrapper requires global history; loop schema does not provide it."
    (has_const "alloca_history" raw_in andalso not (has_const "alloca_history" child_in));
  val _ = check "Lower setup and pointer core avoid global history and accept arbitrary sb."
    (not (has_const "alloca_history" setup_in) andalso
     not (has_const "alloca_history" ptr_in) andalso
     has_const "run_inst_seq" setup_out andalso
     has_const "run_inst_seq" ptr_in andalso has_const "gas_origin_ptr_path" ptr_out);
  val _ = check "Return applies to accepted child's footprint/local allocations; outputs counter and prefix window."
    (has_const "abi_decode_footprint_frame" return_in andalso
     has_const "FLOOKUP" return_in andalso has_const "mload" return_out andalso
     has_const "mem_bytes_at" return_out);
  val _ = check "Scratch accumulation has an explicit containment antecedent, not an assumption of clean capacity."
    (has_const "abi_decode_footprint_frame" (concl calldata_footprint_accumulate));
  val _ = check "Observed backedge preserves physical prefix, but lacks robust values and origin-pointer paths."
    (has_const "mem_bytes_at" step_out andalso
     not (has_const "mem_agree_outside" step_out) andalso
     not (has_const "gas_origin_ptr_path" step_out));
  val _ = print "Residual application obligations: interval restriction/code shape, modular setup join, ambient freshness, counter write ghost frame, zero-event backedge and robust new cell after counter write. No full loop theorem asserted.\n";
end;
