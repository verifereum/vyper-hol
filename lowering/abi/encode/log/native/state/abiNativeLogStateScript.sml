(* TOP-LEVEL: arbitrary typed recursive ABI encoding and LOG preserve the
   complete source state and live local backing outside their real output
   buffer. Actual compiler provenance derives scratch write privacy.
   Helper: native_log_source_state_frame composes execution frames. *)
Theory abiNativeLogState
Ancestors
  abiNativeLogPrivacy abiNativeLogPath abiNativeEncodingDefs sourceAllocationPrivacy
  sourceAbiFrames sourceMemoryFrames allocationPathGrowth allocationGrowth abiPathAllocInv
  abiMemoryFrame abiAllocationWindows abiAllocationTrace abiStateFrame abiFieldOperands
  compileAllocaProvenance compileEnv fragExec fragBlockPath valueEncoding memoryValueDefs
  vyperTypeInvariants vyperState vyperABI contractABI venomState list words

Theorem native_log_source_state_frame:
  !ctx func cenv cx es dst src info topic_ops topics cs cs' bound before after dst_addr payload.
    state_well_typed es /\ state_rel cenv cx es before /\ local_ptrs_rel func cenv es.scopes before /\
    alloca_inv before /\ fn_inst_ids_distinct func /\
    compile_log_abi_emit dst src info topic_ops cs = ((),cs') /\ fn_has_code cs cs' func /\
    source_alloca_floor cenv es.scopes (compiler_alloca_ids cs cs') before /\
    source_memory_separated cenv es.scopes before (w2n dst_addr) (LENGTH payload) /\
    bound <= cs.cs_next_var /\
    (!name entry p capacity. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) capacity) ==> abi_operand_before bound (Var p)) /\
    fragment_path ctx func before after /\
    abi_memory_frame ((w2n dst_addr,LENGTH payload)::abi_allocation_windows (compiler_alloca_ids cs cs') after) before after /\
    after.vs_logs = before.vs_logs ++ [<|logger := w2w before.vs_call_ctx.cc_address; topics := topics; data := payload|>] /\
    (!arg_op. abi_operand_before bound arg_op ==> eval_operand arg_op after = eval_operand arg_op before) /\
    abi_state_frame before (after with vs_logs := before.vs_logs) ==>
    allocation_growth before after /\
    state_rel cenv cx (es with logs := es.logs ++
      [<|logger := w2w before.vs_call_ctx.cc_address; topics := topics; data := payload|>]) after /\
    local_ptrs_rel func cenv es.scopes after
Proof
  rpt gen_tac >> strip_tac >>
  `allocation_growth before after` by (drule_all fragment_path_allocation_growth >> simp[]) >>
  `alloca_inv after` by (drule_all fragment_path_alloca_inv >> simp[]) >>
  `!name entry p capacity. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) capacity) ==> abi_operand_before cs.cs_next_var (Var p)` by
    (qspecl_then [`cenv`, `es.scopes`, `bound`, `cs.cs_next_var`] mp_tac source_pointer_lifetimes_mono >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >> first_assum MATCH_ACCEPT_TAC) >>
  qspecl_then [`dst`, `src`, `info`, `topic_ops`, `cs`, `cs'`, `func`, `cenv`, `es.scopes`, `before`, `after`]
    mp_tac compile_log_scratch_writes_private >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `source_writes_separated cenv es.scopes before
    ((w2n dst_addr,LENGTH payload)::abi_allocation_windows (compiler_alloca_ids cs cs') after)` by
    (qpat_x_assum `source_writes_separated _ _ _ _` mp_tac >>
     simp[source_writes_separated_def]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `before`, `after`,
    `(w2n dst_addr,LENGTH payload)::abi_allocation_windows (compiler_alloca_ids cs cs') after`,
    `[<|logger := w2w before.vs_call_ctx.cc_address; topics := topics; data := payload|>]`, `bound`]
    mp_tac source_relations_native_log_frame >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem compile_abi_typed_tuple_log_state:
  !env sfields cenv tys tvs values avs ctx func cx es dst src topic_ops topics cs cs' ss
    dst_addr src_addr span source_id target_id.
    state_well_typed es /\ state_rel cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
    abi_memory_env_rel env cenv /\ abi_struct_env_rel env sfields /\
    LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
    memory_tuple_rel tvs values (w2n src_addr) ss.vs_memory /\ values_have_types tvs values /\
    vyper_to_abi_list env tys values = SOME avs /\ type_memory_size_list tvs <= span /\
    compile_log_abi_emit dst src (type_to_abi_enc_info sfields cenv (TupleT tys)) topic_ops cs = ((),cs') /\
    fn_has_code cs cs' func /\
    abi_native_memory_ready func cs cs' source_id target_id src_addr span dst_addr
      (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) ss /\
    source_alloca_floor cenv es.scopes (compiler_alloca_ids cs cs') ss /\
    source_memory_separated cenv es.scopes ss (w2n dst_addr)
      (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs))) /\
    (!name entry p capacity. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) capacity) ==> abi_operand_before cs.cs_next_var (Var p)) /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    EVERY (abi_operand_before cs.cs_next_var) topic_ops /\
    eval_operands topic_ops ss = SOME topics /\ LENGTH topic_ops < dimword (:256) ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      out.vs_logs = ss.vs_logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address; topics := topics;
        data := enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)|>] /\
      state_rel cenv cx (es with logs := es.logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address; topics := topics;
        data := enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)|>]) out /\
      local_ptrs_rel func cenv es.scopes out /\ allocation_growth ss out /\
      read_memory (w2n dst_addr) (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs))) out =
        enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
      abi_memory_frame ((w2n dst_addr,LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))::
        abi_allocation_windows (compiler_alloca_ids cs cs') out) ss out /\
      abi_allocation_trace 32 (compiler_alloca_ids cs cs') ss out /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_state_frame ss (out with vs_logs := ss.vs_logs)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`env`, `sfields`, `cenv`, `tys`, `tvs`, `values`, `avs`, `ctx`, `func`, `dst`, `src`, `topic_ops`, `topics`,
    `cs`, `cs'`, `ss`, `dst_addr`, `src_addr`, `span`, `source_id`, `target_id`] mp_tac compile_abi_typed_tuple_log_path >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> disch_then (qx_choose_then `out` strip_assume_tac) >>
  `alloca_inv ss /\ fn_inst_ids_distinct func` by fs[abi_native_memory_ready_def] >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `dst`, `src`, `type_to_abi_enc_info sfields cenv (TupleT tys)`,
    `topic_ops`, `topics`, `cs`, `cs'`, `cs.cs_next_var`, `ss`, `out`, `dst_addr`,
    `enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)`] mp_tac native_log_source_state_frame >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >> strip_tac >>
  qexists_tac `out` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive typed Log source state: " ^ name)
  end) (DB.thms "abiNativeLogState")
