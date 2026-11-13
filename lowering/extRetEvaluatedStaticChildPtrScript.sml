Theory extRetEvaluatedStaticChildPtr
Ancestors
  extRetBytesCopyCountedPtr extRetAbiStaticCountedPtr representationCleanPtr
  abiEncoder exprLowering valueEncoding valueEncodingProps vyperTypeABI
  vyperValue vyperTyping vyperABI compileEnv emitHelper fragExec fragGasPathPtr
  bodyPtrDefs venomState ptrDiscipline words pred_set arithmetic
  fragExecPtr venomInst venomExecSemantics context codegenRel

Theorem ext_ret_evaluated_static_copy_ptr:
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  ~is_dynamic (vyper_to_abi_type env ty) /\ k = type_memory_size tv /\
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiCopy k) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s k /\ ptr_covers G tn dst s k /\ k < dimword(:256) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory tv v (w2n a) mem') ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME (n2w k) /\ op_taint tnf out = {} /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) k s).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+k} /\
    (!i. w2n b <= i /\ i < w2n b+k ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b+k} sf.vs_memory s.vs_memory /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `!i. w2n a <= i /\ i < w2n a+k ==> i NOTIN tn.t_mem` by
    (drule robust_val_in_memory_static_clean >>
     disch_then (qspecl_then [`v`, `tn.t_mem`, `s.vs_memory`, `w2n a`] mp_tac) >>
     simp[]) >>
  `emit_void MCOPY [Var dst; Var src; Lit (n2w k)] sa = ((),sb) /\
   out = Lit (n2w k)` by
    (gvs[Once compile_abi_encode_child_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def] >> pairarg_tac >> gvs[]) >>
  `eval_operand (Lit (n2w k)) s = SOME (n2w k) /\
   op_taint tn (Lit (n2w k)) = {} /\
   ptr_covers G tn src s (w2n (n2w k:bytes32)) /\
   ptr_covers G tn dst s (w2n (n2w k:bytes32))` by
    gvs[eval_operand_def, op_taint_def, w2n_n2w, LESS_MOD] >>
  drule_all emit_mcopy_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `{w2n b+i | i < k /\ w2n a+i IN tn.t_mem} = {}` by
    (simp[EXTENSION] >> rpt strip_tac >>
     Cases_on `i < k` >> simp[] >>
     `w2n a+i NOTIN tn.t_mem` by (first_x_assum irule >> decide_tac) >> simp[]) >>
  qexistsl_tac [`tnf`, `sf`] >>
  gvs[eval_operand_def, op_taint_def, w2n_n2w, LESS_MOD] >>
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  irule mcopy_mem_bytes_at_disjoint >> decide_tac
QED

(* The nested None field contributes no bytes, but the uint sibling does.
   This regression reaches the counted endpoint, without an ABI-plan or
   assignability premise. *)
Theorem ext_ret_nested_none_static_child_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src)
    (type_to_abi_enc_info ce.ce_struct_fields ce
      (TupleT [NoneT; BaseT (UintT 256)])) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  value_has_type (TupleTV [NoneTV; BaseTV (UintT 256)]) v /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory (TupleTV [NoneTV; BaseTV (UintT 256)]) v (w2n a) mem') ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME 32w /\ op_taint tnf out = {} /\
    (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b+32} sf.vs_memory s.vs_memory /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `evaluate_type FEMPTY (TupleT [NoneT; BaseT (UintT 256)]) =
     SOME (TupleTV [NoneTV; BaseTV (UintT 256)]) /\
   type_memory_size (TupleTV [NoneTV; BaseTV (UintT 256)]) = 32 /\
   ~is_dynamic (vyper_to_abi_type FEMPTY (TupleT [NoneT; BaseT (UintT 256)])) /\
   type_to_abi_enc_info ce.ce_struct_fields ce
     (TupleT [NoneT; BaseT (UintT 256)]) = AbiCopy 32 /\
   32 < dimword(:256)` by
    (EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC) >>
  fs[] >>
  mp_tac (ext_ret_evaluated_static_copy_ptr |> SPEC_ALL |>
    Q.INST [`env` |-> `FEMPTY`, `k` |-> `32`,
            `ty` |-> `TupleT [NoneT; BaseT (UintT 256)]`,
            `tv` |-> `TupleTV [NoneTV; BaseTV (UintT 256)]`]) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`tnf`, `sf`] >> gvs[]
QED

(* A zero-sized copy still emits MCOPY. Only clean operand values, not
   provenance or a strict source bound, are needed for this zero read. *)
Theorem ext_ret_zero_copy_child_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiCopy 0) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} ==>
  ?sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) 0 s).vs_memory /\
    sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\ sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME 0w /\ op_taint tn out = {} /\
    (!p. lookup_var p sf = lookup_var p s)
Proof
  strip_tac >>
  `emit_void MCOPY [Var dst; Var src; Lit 0w] sa = ((),sb) /\ out = Lit 0w` by
    (gvs[Once compile_abi_encode_child_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def] >> pairarg_tac >> gvs[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit 0w] []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        fresh_id_def, emit_def, comp_return_def] >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MCOPY [Var dst;Var src;Lit 0w] []` >>
  qabbrev_tac `t = mcopy (w2n b) (w2n a) 0 s` >>
  `step_prov PG G inst t = G /\ step_taint inst s t tn = tn` by
    (simp[Abbr `inst`, Abbr `t`, step_prov_def, set_prov_def,
         step_taint_def, mk_inst_def, set_var_taint_def,
         finite_mapTheory.DRESTRICT_UNIV, store_taint_def, adopt_reset_def,
         imm_taint_def, mem_taint_def, step_writes_def,
         source_memory_write_ranges_def, fixed_source_write_range_def,
         sized_source_write_range_def, written_taint_def, range_bytes_def,
         new_site_bytes_def, eval_operand_def, op_taint_def,
         taint_component_equality, finite_mapTheory.FLOOKUP_DEF, EXTENSION] >>
     metis_tac[]) >>
  qexists_tac `t with vs_inst_idx := SUC s.vs_inst_idx` >>
  conj_tac >-
    (`gas_path_ptr D 0 ctx fn PG G tn s 0 (step_prov PG G inst t)
       (step_taint inst s t tn) (OK (t with vs_inst_idx := SUC s.vs_inst_idx))`
       suffices_by simp[] >>
     irule emitted_step_counted_ptr >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
     conj_tac >-
       (pure_once_rewrite_tac[step_inst_base_def] >>
        simp[Abbr `t`, mk_inst_def, eval_operand_def]) >>
     conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_mcopy_zero) >> simp[eval_operand_def]) >>
  simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def,
       eval_operand_def, op_taint_def, lookup_var_def]
QED
