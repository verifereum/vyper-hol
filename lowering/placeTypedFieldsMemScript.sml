(* Memory-safe field addressing and representation reassembly. *)
Theory placeTypedFieldsMem
Ancestors
  placeTypedCopyPrimitiveMem placeMemoryFieldsForward placeMemoryCopyEffect
  placeMemoryCopyFrames
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  venomState venomExecSemantics fragGasPathMem valueEncodingProps
  list finite_map freshWrites

Theorem typed_fields_addresses_path_mem[local]:
  compile_with_byte_offset dst doff sa = (dp,mid) /\
  compile_with_byte_offset src soff mid = (sp,sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  fn_has_code sa mid func /\ fn_has_code mid sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand dp t = SOME (dw + n2w doff) /\
      eval_operand sp t = SOME (sw + n2w soff) /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all compile_with_byte_offset_fresh >> strip_tac >>
  `!x. src = Var x ==> not_fresh_at mid x` by
    metis_tac[not_fresh_at_mono] >>
  drule_all compile_with_byte_offset_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `eval_operand src t = SOME sw` by
    (Cases_on `src` >> gvs[eval_operand_def, venom_state_component_equality] >> metis_tac[]) >>
  `?u. gas_path_mem ctx func t 0 (OK u) /\
       eval_operand sp u = SOME (sw + n2w soff) /\
       (u with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>) = t /\
       (!x. not_fresh_at mid x ==> lookup_var x u = lookup_var x t) /\
       ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule compile_with_byte_offset_path_mem >> rpt (goal_assum (drule_at Any))) >>
  qexists_tac `u` >>
  `eval_operand dp u = eval_operand dp t` by
    (Cases_on `dp` >> gvs[eval_operand_def, venom_state_component_equality] >> metis_tac[]) >>
  conj_tac >- metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  simp[] >> conj_tac
  >- (gvs[venom_state_component_equality]) >>
  metis_tac[not_fresh_at_mono]
QED

Theorem typed_fields_cons_reassemble[local]:
  val_in_memory dtv v d z.vs_memory /\ val_wf dtv v /\
  tuple_in_memory vs dtvs (d + type_memory_size dtv) t.vs_memory /\
  typed_copy_effect ctx func sa sb z t (d + type_memory_size dtv)
    (type_memory_size_list dtvs) ==>
  tuple_in_memory (v::vs) (dtv::dtvs) d t.vs_memory
Proof
  strip_tac >> simp[valueEncodingTheory.val_in_memory_def] >>
  irule val_in_memory_outside_write >> simp[] >>
  qexistsl_tac [`d + type_memory_size dtv`, `z.vs_memory`,
                `type_memory_size_list dtvs`] >>
  simp[] >> rpt strip_tac >> irule typed_copy_effect_bytes >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem typed_fields_child_suffix_memory[local]:
  tuple_in_memory (v::vs) (stv::stvs) p u.vs_memory /\
  tuple_val_wf vs stvs /\
  (p + type_memory_size stv + type_memory_size_list stvs <= d \/
   d + type_memory_size dtv + tail <= p) /\
  typed_copy_effect ctx func sa sb u z d (type_memory_size dtv) ==>
  tuple_in_memory vs stvs (p + type_memory_size stv) z.vs_memory
Proof
  strip_tac >>
  `!a len. a + len <= d \/ d + type_memory_size dtv <= a ==>
     mem_bytes_at a len z.vs_memory = mem_bytes_at a len u.vs_memory` by
    (rpt strip_tac >> irule typed_copy_effect_bytes >>
     goal_assum (drule_at Any) >> simp[]) >>
  irule typed_memory_tuple_outside_write >> simp[] >>
  qexistsl_tac [`d`, `u.vs_memory`, `type_memory_size dtv`] >>
  gvs[valueEncodingTheory.val_in_memory_def] >> gvs[]
QED

Theorem typed_fields_child_suffix_frame[local]:
  tuple_in_memory (v::vs) (stv::stvs) p u.vs_memory /\
  tuple_val_wf vs stvs /\
  (p + type_memory_size stv + type_memory_size_list stvs <= d \/
   d + type_memory_size dtv + tail <= p) /\
  typed_copy_effect ctx func sa sb u z d (type_memory_size dtv) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst u = SOME dw /\ eval_operand src u = SOME sw ==>
  tuple_in_memory vs stvs (p + type_memory_size stv) z.vs_memory /\
  eval_operand dst z = SOME dw /\ eval_operand src z = SOME sw /\
  z.vs_alloca_next = u.vs_alloca_next /\
  ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
  z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `tuple_in_memory vs stvs (p + type_memory_size stv) z.vs_memory` by
    (irule typed_fields_child_suffix_memory >> rpt (goal_assum (drule_at Any)) >>
     metis_tac[]) >>
  drule typed_copy_effect_endpoint >> strip_tac >>
  drule typed_copy_effect_record >> strip_tac >>
  `z.vs_labels = u.vs_labels /\ z.vs_alloca_next = u.vs_alloca_next` by
    gvs[venom_state_component_equality] >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x u` by
    metis_tac[typed_copy_effect_lookup] >>
  `eval_operand dst z = SOME dw` by
    (Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `eval_operand src z = SOME sw` by
    (Cases_on `src` >> gvs[eval_operand_def] >> metis_tac[]) >> simp[]
QED
