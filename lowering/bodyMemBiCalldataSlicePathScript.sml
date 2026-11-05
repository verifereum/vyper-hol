(* Located slice results and counted memory paths. *)
Theory bodyMemBiCalldataSlicePath
Ancestors
  bodyMemBiCalldataSliceRun bodyMemBiCalldataSliceFacts
  exprSimCalldataSlice exprSimDefs exprSimMemDefs exprSimProps
  exprSimVVFrame exprSimAlloc loweringPosts instMemFrontier
  valueEncoding valueEncodingProps valueTypingMemoryProps
  venomState venomExecSemantics words list finite_map
  vyperAST vyperState vyperContext vyperValue vyperTypeSystem
  vyperInterpreter exprLoweringProps freshWrites localPtrsProps exprLowering
  valueCopy compileEnv venomMemDefs
  bodyMemBiCalldataSliceSuffixMemory bodyUnopFragMemory
  fragGasSeqMem fragGasMode allocaHistoryFragment fragExec rich_list
  context loweringSlice emitHelper builtinBytes venomInst

(* Original: exprSimCalldataSlice.slice_calldata_vv_post [local]. *)
Theorem slice_calldata_vv_post:
  !func cenv cx e es sa sb s t p a n w ctx.
  expr_type e = BaseT (BytesT (Dynamic n)) /\ p.ptr_location = LocMemory /\
  eval_operand p.ptr_operand t = SOME w /\ a+n <= LENGTH cx.txn.calldata /\
  stmt_state_rel ctx func cenv cx es t /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32 + 32 * word_size n) /\
  sa.cs_next_id < sb.cs_next_id /\
  val_in_memory (BaseTV (BytesT (Dynamic n)))
    (BytesV (TAKE n (DROP a cx.txn.calldata))) (w2n w) t.vs_memory /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
  (!nm lb len. local_region cenv es.scopes t nm lb len ==>
     regions_disjoint (w2n w) (32 + 32 * word_size n) lb len) /\
  locals_kept cenv es s t ==>
  !k. vv_post ctx func cenv cx e es sa sb s es
    (Value (BytesV (TAKE n (DROP a cx.txn.calldata))))
    (LocatedValue (expr_type e) p) (t with vs_inst_idx := k)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  `LENGTH (TAKE n (DROP a cx.txn.calldata)) = n` by simp[LENGTH_TAKE_EQ] >>
  `n <= 32 * word_size n` by simp[word_size_capacity] >>
  `eval_operand p.ptr_operand (t with vs_inst_idx := k) = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def, lookup_var_def]) >>
  simp[vv_post_def, stmt_state_rel_inst_idx, vv_holds_def, vv_at_def,
       read_result_def, return_def, evaluate_type_def, is_word_type_def,
       eval_operand_def, lookup_var_def, val_wf_def, val_footprint_def,
       locals_kept_inst_idx] >>
  conj_tac
  >- (strip_tac >> conj_tac
      >- simp[type_memory_size_def, word_size_capacity] >>
      disj1_tac >> qexistsl_tac [`sa.cs_next_id`,`w2n w`,`32 + 32 * word_size n`] >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!nm lb len. local_region _ _ t _ _ _ ==> _` drule >>
      simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >> first_x_assum irule >> qexists_tac `aid` >> simp[]
QED

Theorem slice_calldata_vv_capacity:
  vv_post ctx func cenv cx e es sa sb s es tv
    (LocatedValue (expr_type e) p) t /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  stmt_state_rel ctx func cenv cx es t /\
  eval_operand p.ptr_operand t = SOME w /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,32 + 32 * word_size n) ==>
  vv_store_bound cx (expr_type e) (expr_type e) es tv
    (LocatedValue (expr_type e) p) t
Proof
  strip_tac >>
  Cases_on `evaluate_type (get_tenv cx) (expr_type e)`
  >- simp[vv_store_bound_def] >>
  drule vv_store_bound_capacity >> simp[] >> disch_then irule >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  simp[type_memory_size_def] >>
  irule alloca_region_below_frontier >> conj_tac
  >- gvs[stmt_state_rel_def, alloca_inv_def] >>
  qexistsl_tac [`aid`, `w2n w`, `32 * word_size n + 32`] >> simp[]
QED

Theorem calldata_slice_no_gas[local]:
  compile_slice_calldata op num_op sz sa = (buf_op,sb) ==>
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  simp[compile_slice_calldata_def, compile_slice_out_buf_def,
       contextTheory.compile_alloc_buffer_def, compile_assert_slice_bounds_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND1, mk_inst_def]
QED

Theorem slice_calldata_path_mem:
  !ctx func cenv cx e es sa sb op p n a s0 bres.
  compile_slice_calldata op (Lit (n2w n)) (32 + 32 * word_size n) sa =
    (p.ptr_operand,sb) /\ p.ptr_location = LocMemory /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ context_well_typed cx /\
  0 < n /\ n < 2 ** 256 /\ a < 2 ** 256 /\
  32 + 32 * word_size n < 2 ** 64 /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  bres = (case evaluate_calldata_slice cx.txn.calldata (IntV &a) n of
           INL v => INL v | INR err => INR (Error err)) /\
  stmt_state_rel ctx func cenv cx es s0 /\ eval_operand op s0 = SOME (n2w a) /\
  alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?m r. gas_marked_path T ctx func s0 m r /\
    ((?u. r = OK u /\
          (?rv. bres = INL rv /\ vv_post ctx func cenv cx e es sa sb s0 es
             (Value rv) (LocatedValue (expr_type e) p) u /\
             vv_store_bound cx (expr_type e) (expr_type e) es (Value rv)
               (LocatedValue (expr_type e) p) u) /\
          alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
          u.vs_current_bb = sb.cs_current_bb /\
          u.vs_inst_idx = LENGTH sb.cs_current_insts) \/
     (exit_result r /\ expr_exit bres r))
Proof
  rpt gen_tac >> strip_tac >>
  drule slice_calldata_shape >> strip_tac >>
  `?bb rest. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s0.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND1]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32 + 32 * word_size n))]
       [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
     simp[MEM_APPEND] >> metis_tac[MEM_APPEND]) >>
  `32 + 32 * word_size n < dimword (:256)` by
    (gvs[wordsTheory.dimword_def] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s0` by
    (irule calldata_slice_seq_mem >> metis_tac[]) >>
  `n < dimword (:256) /\ a < dimword (:256)` by
    fs[wordsTheory.dimword_def] >>
  drule_all slice_calldata_run >>
  Cases_on `dimword (:256) <= a+n \/ LENGTH cx.txn.calldata < a+n` >>
  gns[wordsTheory.dimword_def] >> strip_tac
  >- suspend "abort" >>
  suspend "success"
QED

Resume slice_calldata_path_mem[abort]:
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (drule calldata_slice_no_gas >> fs[EVERY_MEM]) >>
  `?j. gas_marked_path T ctx func s0 0
     (Abort Revert_abort (t with vs_inst_idx := j))` by
    (irule run_inst_seq_abort_zero_path_mem >>
     simp[] >> qexists_tac `emitted_insts sa sb` >>
     simp[IS_PREFIX_APPEND]) >>
  qexistsl_tac [`0`, `Abort Revert_abort (t with vs_inst_idx := j)`] >>
  simp[] >>
  Cases_on `dimword (:256) <= a+n` >>
  fs[wordsTheory.dimword_def] >>
  simp[CONV_RULE numLib.REDUCE_CONV evaluate_calldata_slice_uint,
       expr_exit_def, exit_result_def]
QED

Resume slice_calldata_path_mem[success]:
  `?k. gas_marked_path T ctx func s0 k
     (OK (t with vs_inst_idx := s0.vs_inst_idx + LENGTH (emitted_insts sa sb)))` by
    (irule_at Any gas_marked_path_from_mem >>
     irule_at Any run_inst_seq_gas_path_mem >> simp[] >>
     qexists_tac `emitted_insts sa sb` >> simp[IS_PREFIX_APPEND]) >>
  `alloca_history func
     (t with vs_inst_idx := s0.vs_inst_idx + LENGTH (emitted_insts sa sb))` by
    (irule alloca_history_run_inst_seq >> simp[] >>
     fs[EVERY_MEM, stmt_state_rel_def]) >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by
    (irule calldata_slice_seq_frontier >>
     qexists_tac `emitted_insts sa sb` >> fs[EVERY_MEM]) >>
  `t.vs_current_bb = s0.vs_current_bb` by
    (irule (SRULE [] run_inst_seq_preserves_field) >>
     qexists_tac `emitted_insts sa sb` >> simp[] >> rpt strip_tac >>
     `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
       fs[EVERY_MEM] >>
     `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
     drule venomInstProofsTheory.step_preserves_control_flow >> simp[]) >>
  `a+n <= LENGTH cx.txn.calldata` by decide_tac >>
  `!j. vv_post ctx func cenv cx e es sa sb s0 es
     (Value (BytesV (TAKE n (DROP a cx.txn.calldata))))
     (LocatedValue (expr_type e) p) (t with vs_inst_idx := j)` by
    (irule slice_calldata_vv_post >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`k`, `OK (t with vs_inst_idx := s0.vs_inst_idx +
                                  LENGTH (emitted_insts sa sb))`] >>
  simp[] >> disj1_tac >>
  simp[same_blocks_def, evaluate_calldata_slice_uint] >>
  qpat_x_assum `expr_type e = _` (assume_tac o GSYM) >>
  asm_rewrite_tac[] >>
  `vv_post ctx func cenv cx e es sa sb s0 es
     (Value (BytesV (TAKE n (DROP a cx.txn.calldata))))
     (LocatedValue (expr_type e) p) t` by
    (first_x_assum (qspec_then `t.vs_inst_idx` mp_tac) >>
     simp[venom_state_component_equality]) >>
  simp[] >> reverse conj_tac
  >- (reverse conj_tac >- fs[same_blocks_def] >>
      qpat_x_assum `alloca_history func (t with vs_inst_idx := _)` mp_tac >>
      simp[]) >>
  irule slice_calldata_vv_capacity >>
  simp[stmt_state_rel_inst_idx] >>
  conj_tac
  >- (qexistsl_tac [`sa.cs_next_id`, `n`] >> simp[]) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Finalise slice_calldata_path_mem
