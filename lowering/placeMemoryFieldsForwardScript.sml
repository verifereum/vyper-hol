Theory placeMemoryFieldsForward
Ancestors
  placeMemoryDynarrayForward placeMemoryTypedBase placeMemoryForwardPath placeMemoryPrimitiveForward
  placeMemoryCopyFrames placeMemoryCopyEffect placeMemoryChildForward
  context compileEnv loweringStateRelDefs exprLoweringProps emitHelper emitHelperProps
  venomState venomInst venomExecSemantics venomExecProofs fragExec
  fragGasMode freshWrites ASCIInumbers list rich_list finite_map

Theorem compile_with_byte_offset_sequence:
  compile_with_byte_offset op off sa = (out_op,sb) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME w ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb) /\
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
      eval_operand out_op u = SOME (w + n2w off) /\
      (u with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> Cases_on `off = 0`
  >- gvs[compile_with_byte_offset_def, comp_return_def,
         emitted_insts_def, same_blocks_def, run_inst_seq_def, wordsTheory.WORD_ADD_0] >>
  `eval_operand op
     (update_var (STRING #"%" (toString sa.cs_next_var)) (w + n2w off) s) =
     eval_operand op s` by
    (irule typed_memory_fresh_operand >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `compile_with_byte_offset _ _ _ = _` mp_tac >>
  simp[compile_with_byte_offset_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >> strip_tac >>
  gvs[] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND, mk_inst_def,
       is_terminator_def, run_inst_seq_def, step_inst_base_opcode_eqs,
       exec_pure2_def, eval_operand_def, lookup_var_update_var] >>
  simp[update_var_def, venom_state_component_equality] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by
    metis_tac[not_fresh_at_def, arithmeticTheory.LESS_EQ_REFL] >> simp[]
QED

Theorem compile_with_byte_offset_forward:
  compile_with_byte_offset op off sa = (out_op,sb) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME w /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand out_op t = SOME (w + n2w off) /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all compile_with_byte_offset_sequence >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(_ with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >> conj_tac
  >- (qpat_x_assum `(_ with vs_vars := _) = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  metis_tac[lookup_var_def]
QED

(* Offset operands remain usable after the recursive child emits more code. *)
Theorem compile_with_byte_offset_fresh:
  compile_with_byte_offset op off sa = (out_op,sb) /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. out_op = Var x ==> not_fresh_at sb x)
Proof
  Cases_on `off = 0`
  >- (strip_tac >> gvs[compile_with_byte_offset_def, comp_return_def]) >>
  simp[compile_with_byte_offset_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >> gvs[] >>
  simp[not_fresh_at_def, toString_inj]
QED

Theorem typed_memory_fields_addresses_sequence:
  (do dp <- compile_with_byte_offset dst doff;
      sp <- compile_with_byte_offset src soff;
      return (dp,sp)
   od) sa = ((dp,sp),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb) /\
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
      eval_operand dp u = SOME (dw + n2w doff) /\
      eval_operand sp u = SOME (sw + n2w soff) /\
      (u with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >>
  `!k w t. sa.cs_next_var <= k ==>
     eval_operand src (update_var (STRING #"%" (toString k)) w t) = eval_operand src t /\
     eval_operand dst (update_var (STRING #"%" (toString k)) w t) = eval_operand dst t` by
    (rpt strip_tac >> irule typed_memory_fresh_operand >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `_ sa = ((_,_),sb)` mp_tac >>
  Cases_on `doff = 0` >> Cases_on `soff = 0` >>
  simp[compile_with_byte_offset_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, same_blocks_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_APPEND, mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
       lookup_var_update_var, toString_inj, wordsTheory.WORD_ADD_0] >>
  simp[update_var_def, venom_state_component_equality] >> rpt strip_tac >>
  `!k. sa.cs_next_var <= k ==> x <> STRING #"%" (toString k)` by
    metis_tac[not_fresh_at_def] >> simp[]
QED

Theorem typed_memory_fields_addresses_forward:
  (do dp <- compile_with_byte_offset dst doff;
      sp <- compile_with_byte_offset src soff;
      return (dp,sp)
   od) sa = ((dp,sp),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand dp t = SOME (dw + n2w doff) /\
      eval_operand sp t = SOME (sw + n2w soff) /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_memory_fields_addresses_sequence >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(_ with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >> conj_tac
  >- (qpat_x_assum `(_ with vs_vars := _) = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  metis_tac[lookup_var_def]
QED

Theorem typed_memory_fields_addresses_fresh:
  (do dp <- compile_with_byte_offset dst doff;
      sp <- compile_with_byte_offset src soff;
      return (dp,sp)
   od) sa = ((dp,sp),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. dp = Var x ==> not_fresh_at sb x) /\
  (!x. sp = Var x ==> not_fresh_at sb x)
Proof
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_with_byte_offset dst doff sa = (dp,mid)` >>
  drule_all compile_with_byte_offset_fresh >> strip_tac >>
  `!x. src = Var x ==> not_fresh_at mid x` by
    metis_tac[not_fresh_at_mono] >>
  drule_all compile_with_byte_offset_fresh >> strip_tac >>
  metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem compile_with_byte_offset_extends:
  compile_with_byte_offset op off sa = (out_op,sb) ==> cs_extends sa sb
Proof
  Cases_on `off = 0`
  >- (simp[compile_with_byte_offset_def, comp_return_def] >>
      rpt strip_tac >> gvs[cs_extends_refl]) >>
  simp[compile_with_byte_offset_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[cs_extends_def] >>
  qexists_tac `[]` >> simp[]
QED

(* Expose the four genuine compiler boundaries once; consumers do not
   instantiate compiler layout conjunctions or unfold monadic plumbing. *)
Theorem typed_memory_fields_cons_compile:
  compile_typed_copy_fields cenv dst src (dt::dts) (st::sts) doff soff sa = ((),sb) ==>
  ?dp sp a b c.
    compile_with_byte_offset dst doff sa = (dp,a) /\
    compile_with_byte_offset src soff a = (sp,b) /\
    compile_store_memory_typed cenv dp dt sp st b = ((),c) /\
    compile_typed_copy_fields cenv dst src dts sts
      (doff + type_memory_bytes cenv dt) (soff + type_memory_bytes cenv st) c = ((),sb) /\
    cs_extends sa a /\ cs_extends a b /\ cs_extends b c /\ cs_extends c sb
Proof
  simp[Once compile_store_memory_typed_def, comp_bind_def,
       comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  rpt conj_tac
  >- metis_tac[compile_with_byte_offset_extends]
  >- metis_tac[compile_with_byte_offset_extends]
  >- (mp_tac (cj 1 ci_mono_typed_memory_family) >>
      simp[ci_mono_def] >> metis_tac[pairTheory.SND]) >>
  mp_tac (cj 2 ci_mono_typed_memory_family) >>
  simp[ci_mono_def] >> metis_tac[pairTheory.SND]
QED

(* Suffix control induction. P may retain the full source, the completed
   destination prefix, the whole-copy frame and the aligned endpoint. *)
Theorem typed_memory_fields_path_induction:
  !dts sts doff soff sa sb s.
  LENGTH dts = LENGTH sts /\
  compile_typed_copy_fields cenv dst src dts sts doff soff sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ P dts sts doff soff sa s /\
  (!dt dr st sr a b u dx sx.
    LENGTH dr = LENGTH sr /\
    (do dp <- compile_with_byte_offset dst dx;
        sp <- compile_with_byte_offset src sx;
        compile_store_memory_typed cenv dp dt sp st
     od) a = ((),b) /\
    fn_has_code a b func /\ ~u.vs_halted /\ P (dt::dr) (st::sr) dx sx a u ==>
    ?v. gas_marked_path F ctx func u 0 (OK v) /\ ~v.vs_halted /\
        P dr sr (dx + type_memory_bytes cenv dt)
          (sx + type_memory_bytes cenv st) b v) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\ ~t.vs_halted /\
      P [] [] (doff + SUM (MAP (type_memory_bytes cenv) dts))
        (soff + SUM (MAP (type_memory_bytes cenv) sts)) sb t
Proof
  Induct
  >- (Cases_on `sts` >> simp[cj 2 compile_store_memory_typed_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[gas_marked_path_def] >>
      irule (cj 1 fragGasPathTheory.gas_path_rules) >> simp[]) >>
  pop_assum (mk_asm "ih") >>
  Cases_on `sts` >> simp[] >> rpt strip_tac >>
  rename1 `compile_typed_copy_fields cenv dst src (dt::dts) (st::sts) doff soff sa = ((),sb)` >>
  drule typed_memory_fields_cons_compile >> strip_tac >>
  `cs_extends sa c` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa c func /\ fn_has_code c sb func` by
    metis_tac[fn_has_code_split] >>
  `?u. gas_marked_path F ctx func s 0 (OK u) /\ ~u.vs_halted /\
       P dts sts (doff + type_memory_bytes cenv dt)
         (soff + type_memory_bytes cenv st) c u` by
    (first_assum irule >> simp[] >> qexists_tac `sa` >>
     simp[comp_bind_def, comp_ignore_bind_def]) >>
  asm_x "ih" drule_all >> strip_tac >>
  rename1 `gas_marked_path F ctx func u 0 (OK result)` >>
  qexists_tac `result` >>
  conj_tac
  >- metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES] >>
  conj_tac >- simp[] >>
  qpat_x_assum `P [] [] _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  `doff + type_memory_bytes cenv dt + SUM (MAP (type_memory_bytes cenv) dts) =
   doff + (SUM (MAP (type_memory_bytes cenv) dts) + type_memory_bytes cenv dt)` by decide_tac >>
  `soff + type_memory_bytes cenv st + SUM (MAP (type_memory_bytes cenv) sts) =
   soff + (SUM (MAP (type_memory_bytes cenv) sts) + type_memory_bytes cenv st)` by decide_tac >>
  pure_asm_rewrite_tac[] >> disch_then ACCEPT_TAC
QED

(* Tuple framing is the aggregate instance of the value byte-frame boundary. *)
Theorem typed_memory_tuple_outside_write:
  tuple_in_memory vs tvs p m /\ tuple_val_wf vs tvs /\
  (p + type_memory_size_list tvs <= d \/ d + n <= p) /\
  (!a len. a + len <= d \/ d + n <= a ==>
           mem_bytes_at a len m' = mem_bytes_at a len m) ==>
  tuple_in_memory vs tvs p m'
Proof
  strip_tac >>
  `val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) p m'` suffices_by
    simp[valueEncodingDefsTheory.val_in_memory_def] >>
  irule val_in_memory_outside_write >>
  simp[valueEncodingDefsTheory.val_in_memory_def, valueEncodingDefsTheory.val_wf_def,
       valueEncodingTheory.type_memory_size_def] >>
  qexistsl_tac [`d`, `m`, `n`] >> metis_tac[]
QED


Theorem typed_memory_fields_forward:
  !dts sts dtvs stvs vs doff soff sa sb s.
  LIST_REL (\dt tv. evaluate_type tenv dt = SOME tv /\
                       type_memory_bytes cenv dt = type_memory_size tv) dts dtvs /\
  LIST_REL (\st tv. evaluate_type tenv st = SOME tv /\
                       type_memory_bytes cenv st = type_memory_size tv) sts stvs /\
  LIST_REL (\dt st. type_widens_to tenv st dt) dts sts /\
  values_have_types dtvs vs /\ tuple_val_wf vs dtvs /\
  values_have_types stvs vs /\ tuple_val_wf vs stvs /\
  tuple_in_memory vs stvs (w2n sw + soff) s.vs_memory /\
  (w2n sw + soff + type_memory_size_list stvs <= w2n dw + doff \/
   w2n dw + doff + type_memory_size_list dtvs <= w2n sw + soff) /\
  w2n sw + soff + type_memory_size_list stvs < dimword (:256) /\
  w2n dw + doff + type_memory_size_list dtvs + 64 < dimword (:256) /\
  compile_typed_copy_fields cenv dst src dts sts doff soff sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!dt. MEM dt dts ==> typed_memory_child_forward cenv tenv ctx func dt) ==>
  ?t. tuple_in_memory vs dtvs (w2n dw + doff) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw + doff) (type_memory_size_list dtvs)
Proof
  Induct
  >- (Cases_on `sts` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
      simp[vyperTypingTheory.value_has_type_def, valueEncodingDefsTheory.val_wf_def,
           valueEncodingDefsTheory.val_in_memory_def, valueEncodingTheory.type_memory_size_def,
           cj 2 compile_store_memory_typed_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      irule typed_copy_effect_identity >> simp[]) >>
  pop_assum (mk_asm "ih") >>
  Cases_on `sts` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
  simp[vyperTypingTheory.value_has_type_def, valueEncodingDefsTheory.val_wf_def,
       valueEncodingTheory.type_memory_size_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `compile_typed_copy_fields cenv dst src (dt::dts) (st::sts) doff soff sa = ((),sb)` >>
  rename1 `tuple_in_memory (v::vs) (stv::stvs) _ s.vs_memory` >>
  rename1 `evaluate_type tenv dt = SOME dtv` >>
  qmatch_goalsub_rename_tac `tuple_in_memory (v::vs) (dtv::dtvs)` >>
  drule typed_memory_fields_cons_compile >> strip_tac >>
  `cs_extends sa b /\ cs_extends sa c` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa b func /\ fn_has_code b c func /\ fn_has_code c sb func` by
    metis_tac[fn_has_code_split] >>
  `(do dp <- compile_with_byte_offset dst doff;
       sp <- compile_with_byte_offset src soff;
       return (dp,sp) od) sa = ((dp,sp),b)` by
    simp[comp_bind_def, comp_return_def] >>
  drule_all typed_memory_fields_addresses_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `eval_operand dp u = SOME (dw + n2w doff)` >>
  drule_all typed_memory_fields_addresses_fresh >> strip_tac >>
  `w2n (dw + n2w doff) = w2n dw + doff /\
   w2n (sw + n2w soff) = w2n sw + soff` by
    (`w2n dw + doff < dimword (:256) /\ w2n sw + soff < dimword (:256)` by decide_tac >>
     `doff < dimword (:256) /\ soff < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    (qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `val_in_memory stv v (w2n (sw + n2w soff)) u.vs_memory /\
   tuple_in_memory vs stvs (w2n sw + soff + type_memory_size stv) u.vs_memory` by
    gvs[valueEncodingDefsTheory.val_in_memory_def] >>
  `typed_memory_child_forward cenv tenv ctx func dt` by metis_tac[] >>
  `(w2n (sw + n2w soff) + type_memory_size stv <= w2n (dw + n2w doff) \/
    w2n (dw + n2w doff) + type_memory_size dtv <= w2n (sw + n2w soff)) /\
   w2n (sw + n2w soff) + type_memory_size stv < dimword (:256) /\
   w2n (dw + n2w doff) + type_memory_size dtv + 64 < dimword (:256)` by
    (simp[] >> decide_tac) >>
  `?z. val_in_memory dtv v (w2n (dw + n2w doff)) z.vs_memory /\
       typed_copy_effect ctx func b c u z (w2n (dw + n2w doff)) (type_memory_size dtv)` by
    (irule typed_memory_child_forward_apply >> simp[] >>
     qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> gvs[] >> decide_tac) >>
  `tuple_in_memory vs stvs (w2n sw + soff + type_memory_size stv) z.vs_memory` by
    (irule typed_memory_tuple_outside_write >> simp[] >>
     qexistsl_tac [`w2n dw + doff`, `u.vs_memory`, `type_memory_size dtv`] >>
     gvs[] >> qx_gen_tac `addr` >> qx_gen_tac `len` >> strip_tac >>
     `mem_bytes_at addr len z.vs_memory = mem_bytes_at addr len u.vs_memory` suffices_by simp[] >>
     irule typed_copy_effect_bytes >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by
    metis_tac[typed_copy_effect_lookup, not_fresh_at_mono] >>
  `z.vs_labels = s.vs_labels` by
    (drule typed_copy_effect_record >>
     qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand dst z = SOME dw /\ eval_operand src z = SOME sw` by
    (conj_tac
     >- (Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
     Cases_on `src` >> gvs[eval_operand_def] >> metis_tac[]) >>
  drule typed_copy_effect_endpoint >> strip_tac >>
  `sa.cs_next_var <= c.cs_next_var` by
    (qspec_then `cenv` (qspecl_then [`dp`,`dt`,`sp`,`st`,`b`] mp_tac)
       (cj 1 ci_mono_typed_memory_family) >>
     simp[ci_mono_def] >> decide_tac) >>
  `?t. tuple_in_memory vs dtvs (w2n dw + (doff + type_memory_size dtv)) t.vs_memory /\
       typed_copy_effect ctx func c sb z t (w2n dw + (doff + type_memory_size dtv))
         (type_memory_size_list dtvs)` by
    (asm "ih" irule >> simp[] >>
     conj_tac >- metis_tac[not_fresh_at_mono] >>
     conj_tac >- metis_tac[not_fresh_at_mono] >>
     qexistsl_tac [`soff + type_memory_size stv`, `sts`, `stvs`] >>
     gvs[] >> decide_tac) >>
  `val_in_memory dtv v (w2n dw + doff) t.vs_memory` by
    (irule val_in_memory_outside_write >> simp[] >>
     qexistsl_tac [`w2n dw + (doff + type_memory_size dtv)`,
                   `z.vs_memory`, `type_memory_size_list dtvs`] >>
     gvs[] >> rpt strip_tac >> irule typed_copy_effect_bytes >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  qexists_tac `t` >> (conj_tac
  >- gvs[valueEncodingDefsTheory.val_in_memory_def] >>
  asm_x "ih" kall_tac >>
  `typed_copy_effect ctx func sa b s u (w2n dw + doff)
     (type_memory_size dtv + type_memory_size_list dtvs)` by
    (simp[typed_copy_effect_def] >>
     qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `typed_copy_effect ctx func b c u z (w2n dw + doff)
     (type_memory_size dtv + type_memory_size_list dtvs)` by
    (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> simp[]) >>
  `typed_copy_effect ctx func c sb z t (w2n dw + doff)
     (type_memory_size dtv + type_memory_size_list dtvs)` by
    (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> decide_tac) >>
  `typed_copy_effect ctx func sa c s z (w2n dw + doff)
     (type_memory_size dtv + type_memory_size_list dtvs)` by
    (match_mp_tac (GEN_ALL placeMemoryCopyEffectTheory.typed_copy_effect_then) >>
     qexistsl_tac [`u`, `b`, `b`] >> simp[] >> metis_tac[not_fresh_at_mono]) >>
  match_mp_tac (GEN_ALL placeMemoryCopyEffectTheory.typed_copy_effect_then) >>
  qexistsl_tac [`z`, `c`, `c`] >> gvs[] >> metis_tac[not_fresh_at_mono])
QED

(* Ordered struct metadata reduces both execution and representation to the
   same tuple suffix; no by-position assumption about source names is needed. *)
Theorem typed_memory_struct_forward:
  ALL_DISTINCT (MAP FST fields) /\
  EVERY (\(name,ty,sz). sz = type_memory_bytes cenv ty) fields /\
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv /\
                        type_memory_bytes cenv ty = type_memory_size tv)
    (MAP (FST o SND) fields) tvs /\
  LENGTH tvs = LENGTH fields /\
  struct_has_type (ZIP (MAP FST fields,tvs)) vals /\
  fields_val_wf vals (ZIP (MAP FST fields,tvs)) /\
  fields_in_memory vals (ZIP (MAP FST fields,tvs)) (w2n sw + soff) s.vs_memory /\
  (w2n sw + soff + type_memory_size_list tvs <= w2n dw + doff \/
   w2n dw + doff + type_memory_size_list tvs <= w2n sw + soff) /\
  w2n sw + soff + type_memory_size_list tvs < dimword (:256) /\
  w2n dw + doff + type_memory_size_list tvs + 64 < dimword (:256) /\
  compile_struct_typed_copy cenv dst src fields fields doff soff sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!dt. MEM dt (MAP (FST o SND) fields) ==>
        typed_memory_child_forward cenv tenv ctx func dt) ==>
  ?t. fields_in_memory vals (ZIP (MAP FST fields,tvs))
        (w2n dw + doff) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw + doff) (type_memory_size_list tvs)
Proof
  strip_tac >>
  `?vs. vals = ZIP (MAP FST fields,vs) /\ LENGTH vs = LENGTH (MAP FST fields) /\
        values_have_types tvs vs /\ tuple_val_wf vs tvs` by
    (irule typed_memory_struct_values >> simp[]) >>
  gvs[] >>
  `compile_struct_typed_copy cenv dst src fields fields doff soff =
   compile_typed_copy_fields cenv dst src
      (MAP (FST o SND) fields) (MAP (FST o SND) fields) doff soff` by
    (irule typed_memory_struct_copy_fields >> simp[EVERY_MEM]) >>
  gvs[typed_memory_fields_tuple_zip] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule typed_memory_fields_forward >> simp[] >>
  goal_assum $ drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`) >>
  qexistsl_tac [`tvs`, `sw`, `tenv`] >>
  simp[LIST_REL_refl, EVERY_MEM] >> decide_tac
QED
