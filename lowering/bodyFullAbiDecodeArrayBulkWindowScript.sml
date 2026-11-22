Theory bodyFullAbiDecodeArrayBulkWindow
Ancestors
  bodyFullAbiDecodeLeafCases abiDecodePtrBytesTail
  instSeqPtrLo fragGasOriginPtrDead fragGasOriginPtrLoop fragExecMem
  instMemFrontier emitHelperProps exprLoweringProps stateFrame
  bodyPtrDefs ptrDiscipline words arithmetic list rich_list finite_map pred_set
  venomState venomInst assignTuplePtrStoreWord exprSimProps
  bodyFullAbiDecodeRelativeLoadExact[qualified]

Theorem abi_decode_bulk_clean_elements:
  msz = type_memory_size tv /\
  (!i. d+32 <= i /\ i < d+32+n*msz ==> i NOTIN tnf.t_mem) ==>
  !k. k < n ==> !v.
    val_wf tv v /\ val_in_memory tv v (d+32+k*msz) t.vs_memory ==>
    !mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
          val_in_memory tv v (d+32+k*msz) mem
Proof
  rpt strip_tac >>
  `val_footprint tv v <= msz` by
    metis_tac[val_footprint_le_store_size, val_store_size_le, LESS_EQ_TRANS] >>
  `(k+1)*msz <= n*msz` by (irule LESS_MONO_MULT >> decide_tac) >>
  `!i. d+32+k*msz <= i /\ i < d+32+k*msz+val_footprint tv v ==>
       i NOTIN tnf.t_mem` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. _ ==> i NOTIN tnf.t_mem` (qspec_then `i` mp_tac) >>
     qpat_x_assum `(k+1)*msz <= _`
       (assume_tac o REWRITE_RULE [RIGHT_ADD_DISTRIB, MULT_LEFT_1]) >>
     `d+32 <= i /\ i < d+32+n*msz` by decide_tac >> simp[]) >>
  irule val_in_memory_clean_footprint_ptr >>
  conj_tac >- asm_rewrite_tac[] >>
  qexistsl_tac [`tnf.t_mem`, `t.vs_memory`] >> asm_rewrite_tac[]
QED

(* The same owned state used by the finite scalar frame. *)
val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\
  ptr_covers G tn output s output_cap /\
  output_base + output_cap < dimword (:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
      b+sz <= s.vs_alloca_next) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid,p,b,k,bytes). not_fresh_at st p) live``;

(* Form an address from a covered window, without bounding the entire
   provenance object. Keep the finite supplier's endpoint and ghosts. *)
Theorem abi_decode_bulk_window_add_joint:
  emit_op ADD [Var dst;pos] sa = (Var out,sb) /\
  ptr_covers G tn dst s cap /\ lookup_var dst s = SOME b /\
  eval_operand pos s = SOME (n2w q) /\
  op_taint tn (Var dst) = {} /\ op_taint tn pos = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ q+k <= cap /\ w2n b+cap < dimword (:256) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  allocas_from lo s /\ (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
         (s,G,tn) [] (OK ((update_var out (b+n2w q) s) with vs_inst_idx := LENGTH
           sb.cs_current_insts),(step_prov PG G (mk_inst sa.cs_next_id ADD [Var dst;pos] [out])
           (update_var out (b+n2w q) s)),(step_taint (mk_inst sa.cs_next_id ADD [Var dst;pos] [out]) s
           (update_var out (b+n2w q) s) tn))) /\
  ~((update_var out (b+n2w q) s) with vs_inst_idx := LENGTH sb.cs_current_insts).vs_halted /\
    ((update_var out (b+n2w q) s) with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb =
    sb.cs_current_bb /\
  ((update_var out (b+n2w q) s) with vs_inst_idx := LENGTH sb.cs_current_insts).vs_inst_idx = LENGTH
    sb.cs_current_insts /\
  (^owned_decoder_state) sb ((update_var out (b+n2w q) s) with vs_inst_idx := LENGTH sb.cs_current_insts)
    (step_prov PG G (mk_inst sa.cs_next_id ADD [Var dst;pos] [out]) (update_var out (b+n2w q) s))
    (step_taint (mk_inst sa.cs_next_id ADD [Var dst;pos] [out]) s (update_var out (b+n2w q) s) tn) /\
  ptr_covers (step_prov PG G (mk_inst sa.cs_next_id ADD [Var dst;pos] [out]) (update_var out (b+n2w q)
    s)) (step_taint (mk_inst sa.cs_next_id ADD [Var dst;pos] [out]) s (update_var out (b+n2w q) s) tn)
    out ((update_var out (b+n2w q) s) with vs_inst_idx := LENGTH sb.cs_current_insts) k /\ lookup_var out
    ((update_var out (b+n2w q) s) with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME (b+n2w q) /\
  ((update_var out (b+n2w q) s) with vs_inst_idx := LENGTH sb.cs_current_insts).vs_memory = s.vs_memory
    /\ ((update_var out (b+n2w q) s) with vs_inst_idx := LENGTH sb.cs_current_insts).vs_allocas =
    s.vs_allocas /\
  ((update_var out (b+n2w q) s) with vs_inst_idx := LENGTH sb.cs_current_insts).vs_alloca_next =
    s.vs_alloca_next /\ (step_taint (mk_inst sa.cs_next_id ADD [Var dst;pos] [out]) s (update_var out
    (b+n2w q) s) tn).t_mem = tn.t_mem /\
  (!x. not_fresh_at sa x ==>
    lookup_var x ((update_var out (b+n2w q) s) with vs_inst_idx := LENGTH sb.cs_current_insts) =
      lookup_var x s /\ FLOOKUP (step_prov PG G (mk_inst sa.cs_next_id ADD [Var dst;pos] [out])
      (update_var out (b+n2w q) s)) x = FLOOKUP G x /\
    op_taint (step_taint (mk_inst sa.cs_next_id ADD [Var dst;pos] [out]) s (update_var out (b+n2w q) s)
      tn) (Var x) = op_taint tn (Var x))
Proof
  BETA_TAC >> strip_tac >>
  drule_all (abi_decode_ptr_output_address |> Q.INST [
    `D` |-> `<|d_stor := K (K {}); d_trans := K (K {});
              d_imm := K {}; d_ret := K {}|>`]) >>
  disch_then (qspecl_then [`fn`, `PG`] mp_tac) >>
  rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `u = update_var out (b+n2w q) s` >>
  qabbrev_tac `t = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qabbrev_tac `H = step_prov PG G (mk_inst sa.cs_next_id ADD [Var dst;pos] [out]) u` >>
  qabbrev_tac `tm = step_taint (mk_inst sa.cs_next_id ADD [Var dst;pos] [out]) s u tn` >>
  drule emitted_insts_emit_op >> simp[] >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    metis_tac[emit_op_same_blocks, same_blocks_def] >>
  `inst_extends sa sb` by simp[inst_extends_def] >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) (emitted_insts sa sb) /\
   EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (simp[run_inst_seq_mem_ok_last] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `(ctx_has_dalloca ctx ==>
    !pre i post u'. emitted_insts sa sb = pre ++ i::post /\
      run_inst_seq pre s = OK u' ==> dalloca_no_wrap i u')` by
    simp[APPEND_EQ_CONS, mk_inst_def, memSafeRunTheory.dalloca_no_wrap_non_dalloca] >>
  `inst_seq_ptr <|d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {}|> lo ctx fn PG G tn
      (emitted_insts sa sb) s H tm` by
    (irule inst_seq_ptr_zero_to_lo >> asm_rewrite_tac[] >>
     qexists_tac `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>` >> gvs[SUBSET_REFL]) >>
  qpat_x_assum `inst_seq_ptr _ 0 _ _ _ _ _ _ _ _ _` kall_tac >>
  `gas_origin_ptr_path
      (<|d_stor := K (K {}); d_trans := K (K {});
         d_imm := K {}; d_ret := K {}|>,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,H,tm)` by
    (drule_all fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
     disch_then (qspec_then `explicit` mp_tac) >> simp[Abbr `t`]) >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\ t.vs_allocas = s.vs_allocas /\
   t.vs_memory = s.vs_memory /\ t.vs_alloca_next = s.vs_alloca_next /\
   state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx)` by
    simp[Abbr `t`, Abbr `u`, update_var_def, state_frame_def] >>
  `alloca_history fn t` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`, `sa`, `sb`] >> simp[IS_PREFIX_APPEND]) >>
  mp_tac (bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_owned_scalar_frame_with_history_lower |> BETA_RULE |>
          Q.INST [`G'` |-> `H`, `tn'` |-> `tm`]) >>
  impl_tac
  >- (asm_rewrite_tac[] >> qexists_tac `inst` >> asm_rewrite_tac[]) >>
  strip_tac >> conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >> gs[AC ADD_ASSOC ADD_COMM] >>
  qexists_tac `inst` >> asm_rewrite_tac[]
QED
