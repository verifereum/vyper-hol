(* Counted fixed operations of the external request prefix. *)
Theory exprExtRequestPrefixOps
Ancestors
  exprExtRequestAllocationEndpoint exprExtRequestMaterialize
  exprExtRequestHistory exprExtRequestReadProbe exprExtRequestTupleStore
  exprExtRequestJointUnwrap exprSimHypsDefs
  exprSimMapKey exprSimAlloc exprSimHash stmtSimDeclPath valueEncodingProps
  valueEncodingProofs abiCanonicalHeadSize entryDispatchProps selectorDispatch
  exprLoweringProps exprSimProps exprSafeOperand freshWrites
  emitHelper emitHelperProps compileEnv context fragExec fragGasMode
  venomInst venomState venomExecSemantics list arithmetic

Theorem extrequest_add_endpoint:
  emit_op ADD [lhs;rhs] sa = (dst,sb) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ee t /\
    extrequest_history_frame cenv cx ee sa s ee sb t /\
    eval_operand dst t = SOME (a+b) /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ safe_operand sb dst
Proof
  strip_tac >> drule_all emit_ADD_frame >> strip_tac >>
  `same_blocks sa sb` by metis_tac[emit_op_same_blocks] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `gas_marked_path F ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule extrequest_straight_run_path >> simp[] >> qexists_tac `sa` >>
     simp[mk_inst_def, is_terminator_def]) >>
  `t = update_var (STRING #"%" (toString sa.cs_next_var)) (a+b) s` by
    (qpat_x_assum `run_inst_seq _ _ = OK _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_def, mk_inst_def,
          exec_pure2_def, bind_outputs_def]) >>
  `stmt_state_rel ctx func cenv cx ee t` by
    (simp[] >> irule stmt_state_rel_update_var >> simp[] >>
     irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def] >>
  gvs[extrequest_history_frame_def, extrequest_read_frame_def,
      update_var_def, lookup_var_def, same_blocks_def, safe_operand_def,
      not_fresh_at_def] >>
  simp[venom_state_component_equality] >>
  metis_tac[]
QED

(* The selector store is separated from allocation so its write frame can
   be transported relative to the pre-allocation capture endpoint. *)
Theorem extrequest_mstore_endpoint:
  emit_void MSTORE [Var p; Lit wd] sm = ((),sb) /\
  fn_has_code sm sb func /\ stmt_state_rel ctx func cenv cx ee s /\
  lookup_var p s = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,cap) /\ 32 <= cap /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
     regions_disjoint (w2n w) cap b len) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ee t /\
    (t with <|vs_memory := s.vs_memory; vs_inst_idx := s.vs_inst_idx|>) = s /\
    t.vs_memory = (mstore (w2n w) wd s).vs_memory /\
    (!op. eval_operand op t = eval_operand op s) /\
    (!a k. regions_disjoint (w2n w) cap a k ==>
       mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx ee (mstore (w2n w) wd s)` by
    (irule literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`w2n w`, `inst`, `cap`] >>
     gvs[regions_disjoint_def] >> metis_tac[]) >>
  `gas_marked_path F ctx func s 0
    (OK (mstore (w2n w) wd s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule emit_mstore_marked_path >> simp[eval_operand_def] >>
     qexistsl_tac [`Lit wd`, `p`, `sm`, `sb`] >> simp[eval_operand_def]) >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    metis_tac[emit_void_same_blocks, same_blocks_def] >>
  drule emitted_insts_emit_void >> strip_tac >>
  `!a k. regions_disjoint (w2n w) cap a k ==>
     mem_bytes_at a k (mstore (w2n w) wd s).vs_memory =
       mem_bytes_at a k s.vs_memory` by
    (rpt strip_tac >> irule mstore_region_frame >>
     qexistsl_tac [`w2n w`, `cap`] >> simp[]) >>
  qexists_tac `mstore (w2n w) wd s with vs_inst_idx := SUC s.vs_inst_idx` >>
  asm_rewrite_tac[stmt_state_rel_inst_idx] >>
  gvs[mstore_def, eval_operand_def, lookup_var_def,
      venom_state_component_equality]
QED

Theorem extrequest_alloc_selector_endpoint:
  compile_alloc_buffer sz sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; Lit wd] sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  stmt_state_rel ctx func cenv cx ee s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ 32 <= sz /\ sz < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ee t /\
    extrequest_history_frame cenv cx ee sa s ee sb t /\
    eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\
    mem_bytes_at (w2n w) 32 t.vs_memory = word_to_bytes wd T /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb
Proof
  strip_tac >> drule_all extrequest_allocation_endpoint >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
        [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  `lookup_var p u = SOME w` by gvs[eval_operand_def] >>
  `?t. gas_marked_path F ctx func u 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ee t /\
    (t with <|vs_memory := u.vs_memory; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_memory = (mstore (w2n w) wd u).vs_memory /\
    (!op. eval_operand op t = eval_operand op u) /\
    (!a k. regions_disjoint (w2n w) sz a k ==>
       mem_bytes_at a k t.vs_memory = mem_bytes_at a k u.vs_memory) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule extrequest_mstore_endpoint >> simp[] >>
     conj_tac >- metis_tac[] >> conj_tac
     >- (qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
          [STRING #"%" (toString sa.cs_next_var)]` >> simp[mk_inst_def]) >>
     qexistsl_tac [`p`, `sm`] >> metis_tac[]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  qexistsl_tac [`t`, `w`] >> rpt conj_tac
  >- (qpat_assum `gas_marked_path F ctx func s 0 (OK u)`
        (mp_then Any mp_tac gas_marked_path_then) >>
      disch_then (qspecl_then [`OK t`, `0`] mp_tac) >> simp[])
  >- simp[]
  >- suspend "history"
  >- metis_tac[]
  >- (qpat_x_assum `(t with <|vs_memory := _; vs_inst_idx := _|>) = u`
        mp_tac >> simp[venom_state_component_equality] >> metis_tac[])
  >- simp[]
  >- simp[mem_bytes_at_mstore_same]
  >> simp[]
QED

Resume extrequest_alloc_selector_endpoint[history]:
  `t.vs_allocas = u.vs_allocas` by
    (qpat_x_assum `(t with <|vs_memory := _; vs_inst_idx := _|>) = u`
      mp_tac >> simp[venom_state_component_equality]) >>
  `!x. lookup_var x t = lookup_var x u` by
    (rpt gen_tac >> first_x_assum (qspec_then `Var x` mp_tac) >>
     simp[eval_operand_def]) >>
  irule extrequest_copy_history >> simp[] >>
  qexistsl_tac [`sz`, `w2n w`, `sm`, `u`] >> simp[] >>
  metis_tac[]
QED

Finalise extrequest_alloc_selector_endpoint

Theorem extrequest_selector_word_suffix:
  !bs. LENGTH (bs:byte list) = 4 ==>
    DROP 28 (word_to_bytes (calldata_method_id bs) T) = bs
Proof
  rpt gen_tac >>
  Cases_on `bs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  simp[calldata_method_id_def, byteTheory.word_to_bytes_def,
       byteTheory.word_to_bytes_aux_compute, byteTheory.get_byte_def,
       byteTheory.byte_index_def, wordsTheory.n2w_w2n,
       GSYM wordsTheory.word_add_n2w, GSYM wordsTheory.word_mul_n2w,
       GSYM wordsTheory.w2w_def] >>
  blastLib.BBLAST_TAC
QED

Theorem extrequest_selector_window:
  expr_sim_inv cenv cx env ee /\
  mem_bytes_at baddr 32 mem =
    word_to_bytes (n2w (cenv.ce_method_id fname tys):bytes32) T ==>
  mem_bytes_at (baddr + 28) 4 mem =
    function_selector fname (vyper_to_abi_types (get_tenv cx) tys)
Proof
  strip_tac >>
  `cenv.ce_method_id fname tys =
    w2n (calldata_method_id
      (function_selector fname (vyper_to_abi_types (get_tenv cx) tys)))` by
    gvs[expr_sim_inv_def] >>
  `TAKE 4 (DROP 28 (mem_bytes_at baddr 32 mem)) =
      mem_bytes_at (baddr + 28) 4 mem` by
    (irule mem_bytes_at_window >> simp[]) >>
  gvs[] >>
  gvs[extrequest_selector_word_suffix, function_selector_length] >>
  metis_tac[listTheory.TAKE_LENGTH_ID, function_selector_length]
QED
