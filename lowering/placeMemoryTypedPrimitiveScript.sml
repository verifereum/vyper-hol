Theory placeMemoryTypedPrimitive
Ancestors
  placeMemoryPrimitiveForward placeMemoryTypedBase valueEncodingProps
  venomExecSemantics context emitHelper valueCopy fragExec compileEnv
  venomExecProofs venomState venomInst list rich_list exprLoweringProps
  valueCopyBytes

Theorem compile_copy_memory_sequence:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb) /\
  run_inst_seq (emitted_insts sa sb) s =
    OK (if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
Proof
  Cases_on `n`
  >- simp[compile_copy_memory_def, comp_return_def, emitted_insts_def,
          same_blocks_def, run_inst_seq_def] >>
  strip_tac >>
  `emit_void MCOPY [dst; src; Lit (n2w (SUC n'))] sa = ((),sb)` by
    gvs[compile_copy_memory_def] >>
  drule_all emit_mcopy_run >> strip_tac >> simp[] >>
  qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
  simp[emit_void_def, comp_bind_def, comp_return_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, DROP_APPEND, mk_inst_def]
QED

Theorem mcopy_memory_length:
  LENGTH s.vs_memory <= LENGTH (mcopy dst src n s).vs_memory
Proof
  simp[mcopy_def, write_memory_with_expansion_def, LET_THM, LENGTH_TAKE,
       LENGTH_DROP] >>
  Cases_on `dst + n > LENGTH s.vs_memory` >> simp[LENGTH_TAKE] >> decide_tac
QED

Theorem compile_copy_memory_forward:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      mem_bytes_at (w2n dw) n t.vs_memory = mem_bytes_at (w2n sw) n s.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      (!a len. a + len <= w2n dw \/ w2n dw + n <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all compile_copy_memory_sequence >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK u` >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  Cases_on `n = 0`
  >- (gvs[Abbr `u`, valueEncodingTheory.mem_bytes_at_def, lookup_var_def] >>
      simp[venom_state_component_equality]) >>
  gvs[Abbr `u`] >>
  simp[mcopy_mem_bytes_at_same, mcopy_memory_length] >>
  conj_tac
  >- simp[mcopy_def, write_memory_with_expansion_def,
          venom_state_component_equality] >>
  conj_tac >- simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  conj_tac
  >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem typed_memory_bytestring_forward:
  is_bytestring_type dty /\ is_bytestring_type sty /\
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type dtv v /\ val_wf dtv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  w2n dw + type_memory_size dtv + 64 < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `~is_word_type dty` by metis_tac[is_bytestring_word_type] >>
  `val_in_memory dtv v (w2n sw) s.vs_memory` by
    (irule bytestring_val_in_memory_transfer >>
     simp[] >> qexistsl_tac [`sty`, `dty`, `tenv`, `stv`] >> simp[]) >>
  `compile_store_memory cenv src dst dty dty sa = ((),sb)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, compile_store_memory_def]) >>
  drule compile_store_memory_same_type_forward >> simp[] >>
  disch_then (qspec_then `v` mp_tac) >>
  disch_then (qspecl_then [`dtv`, `tenv`, `sw`, `s`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`func`, `ctx`] mp_tac) >>
  simp[arithmeticTheory.ADD_ASSOC] >> strip_tac >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (qpat_x_assum `_ = s`
        (mp_tac o Q.AP_TERM
          `\z. z with <|vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb|>`) >>
      simp[]) >>
  qpat_x_assum `_ = s`
    (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[] >> metis_tac[]
QED

Theorem typed_memory_sarray_fast_forward:
  ~is_abi_dynamic cenv.ce_struct_fields det /\
  type_widens_to tenv (ArrayT src_et (Fixed m)) (ArrayT det (Fixed n)) /\
  compile_copy_sarray_typed cenv dst det src src_et n sa = ((),sb) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv (ArrayT src_et (Fixed m)) = SOME stv /\
  evaluate_type tenv (ArrayT det (Fixed n)) = SOME dtv /\
  val_wf dtv v /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_bytes cenv (ArrayT det (Fixed n)) = type_memory_size dtv /\
  w2n dw + type_memory_size dtv + 64 < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `ArrayT src_et (Fixed m) = ArrayT det (Fixed n)` by
    (irule (INST_TYPE [``:'a`` |-> ``:string``, ``:'b`` |-> ``:num``]
              typed_memory_static_widening) >> conj_tac
     >- (qexists_tac `cenv.ce_struct_fields` >> simp[is_abi_dynamic_def]) >>
     qexists_tac `tenv` >> simp[]) >>
  gvs[] >>
  `compile_copy_memory dst src (type_memory_size dtv) sa = ((),sb)` by
    (qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def] >>
     gvs[type_memory_bytes_def]) >>
  `type_memory_size dtv < dimword (:256)` by decide_tac >>
  drule_all compile_copy_memory_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (irule valueEncodingPropsTheory.val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`s.vs_memory`, `type_memory_size dtv`, `w2n sw`] >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `_ = s` mp_tac >> simp[venom_state_component_equality]) >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
