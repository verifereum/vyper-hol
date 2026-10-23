Theory abiTupleProps
Ancestors
  exprLowering exprLoweringProps contextProps emitHelperProps
  valueEncoding valueEncodingProps compileEnv context venomExecSemantics words
Libs
  wordsLib

(* Word inputs carry a typed encoding, not the untyped BytesV heuristic. *)
Definition abi_tuple_word_def:
  abi_tuple_word tv v =
    ((?b. v = BoolV b) \/ (?n. v = IntV n) \/
     (?k. v = FlagV k) \/ (?n. v = DecimalV n) \/
     (?bs n. tv = BaseTV (BytesT (Fixed n)) /\ v = BytesV bs) \/
     (?bs. tv = BaseTV AddressT /\ v = BytesV bs))
End

Definition abi_tuple_input_def:
  abi_tuple_input cenv ty tv v op ss =
    (val_wf tv v /\ type_memory_bytes cenv ty = type_memory_size tv /\
     if is_word_type ty then
       type_memory_size tv = 32 /\ abi_tuple_word tv v /\
       eval_operand op ss = SOME (typed_val_to_w256 tv v)
     else
       ?p. eval_operand op ss = SOME p /\
           val_in_memory tv v (w2n p) ss.vs_memory)
End

Theorem abi_tuple_word_mstore:
  abi_tuple_word tv v ==>
  val_in_memory tv v dst (mstore dst (typed_val_to_w256 tv v) ss).vs_memory
Proof
  rw[abi_tuple_word_def] >>
  simp[val_in_memory_def, typed_val_to_w256_def,
       mstore_mem_word_at_same] >>
  Cases_on `tv` >> simp[typed_val_to_w256_def] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> simp[typed_val_to_w256_def]
QED

Theorem compile_copy_memory_extends:
  compile_copy_memory dst src sz st = ((),st') ==>
  st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
  same_blocks st st'
Proof
  Cases_on `sz`
  >- simp[compile_copy_memory_def, comp_return_def, emitted_insts_def, same_blocks_def] >>
  simp[compile_copy_memory_def] >> metis_tac[emit_void_extends]
QED

(* The write half of a slot; ADD is composed separately below. *)
Theorem abi_tuple_write_correct:
  (if is_word_type ty then emit_void MSTORE [dst; op]
   else compile_copy_memory dst op (type_memory_bytes cenv ty)) st = ((),st') /\
  eval_operand dst ss = SOME (n2w d) /\ d < dimword (:256) /\
  type_memory_bytes cenv ty < dimword (:256) /\
  abi_tuple_input cenv ty tv v op ss /\ fresh_vars_wrt st ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    val_in_memory tv v d ss'.vs_memory /\
    same_blocks st st' /\ fresh_vars_wrt st' ss' /\
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
    (!p k. p+k <= d \/ d+type_memory_bytes cenv ty <= p ==>
      mem_bytes_at p k ss'.vs_memory = mem_bytes_at p k ss.vs_memory)
Proof
  strip_tac >>
  Cases_on `is_word_type ty` >> gvs[abi_tuple_input_def]
  >- (drule_all emit_void_MSTORE_correct >> strip_tac >>
      drule emit_void_extends >> strip_tac >>
      qexists_tac `mstore d (typed_val_to_w256 tv v) ss` >>
      gvs[w2n_n2w, abi_tuple_word_mstore] >>
      metis_tac[mstore_mem_bytes_at_disjoint, arithmeticTheory.ADD_COMM]) >>
  Cases_on `type_memory_bytes cenv ty = 0`
  >- (gvs[contextTheory.compile_copy_memory_def, comp_return_def] >>
      qexists_tac `ss` >> simp[emitted_insts_def, run_inst_seq_def, same_blocks_def] >>
      irule val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`ss.vs_memory`, `0`, `w2n p`] >>
      simp[mem_bytes_at_def]) >>
  `type_memory_size tv > 0` by simp[] >>
  drule_all compile_copy_memory_correct >> strip_tac >>
  drule compile_copy_memory_extends >> strip_tac >>
  qexists_tac `mcopy d (w2n p) (type_memory_size tv) ss` >>
  gvs[w2n_n2w, mcopy_establishes_val_in_memory] >>
  metis_tac[mcopy_mem_bytes_at_disjoint, arithmeticTheory.ADD_COMM]
QED

Definition compile_abi_tuple_slot_def:
  compile_abi_tuple_slot cenv buf off op ty =
    do dst <- emit_op ADD [buf; Lit (n2w off)];
       if is_word_type ty then emit_void MSTORE [dst; op]
       else compile_copy_memory dst op (type_memory_bytes cenv ty)
    od
End

Theorem abi_tuple_input_memory_cong:
  ss'.vs_memory = ss.vs_memory /\
  (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
  abi_tuple_input cenv ty tv v op ss ==>
  abi_tuple_input cenv ty tv v op ss'
Proof
  rw[abi_tuple_input_def] >> metis_tac[]
QED

Theorem abi_tuple_add_correct[local]:
  emit_op ADD [buf; Lit (n2w off)] st = (dst,st1) /\
  eval_operand buf ss = SOME (n2w baddr) /\ fresh_vars_wrt st ss ==>
  ?ss1. run_inst_seq (emitted_insts st st1) ss = OK ss1 /\
    eval_operand dst ss1 = SOME (n2w (baddr+off)) /\
    same_blocks st st1 /\ fresh_vars_wrt st1 ss1 /\
    st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 /\
    ss1.vs_memory = ss.vs_memory /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op ss1 = SOME w)
Proof
  strip_tac >>
  `eval_operand (Lit (n2w off)) ss = SOME (n2w off)` by simp[eval_operand_lit] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qexists_tac `ss'` >> simp[word_add_n2w] >>
  simp[listTheory.LIST_EQ] >> metis_tac[]
QED

Theorem compile_abi_tuple_slot_correct:
  compile_abi_tuple_slot cenv buf off op ty st = ((),st') /\
  eval_operand buf ss = SOME (n2w baddr) /\ fresh_vars_wrt st ss /\
  baddr+off < dimword (:256) /\
  baddr+off+type_memory_bytes cenv ty <= dimword (:256) /\
  type_memory_bytes cenv ty < dimword (:256) /\
  abi_tuple_input cenv ty tv v op ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    val_in_memory tv v (baddr+off) ss'.vs_memory /\
    same_blocks st st' /\ fresh_vars_wrt st' ss' /\
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
    (!p k. p+k <= baddr+off \/ baddr+off+type_memory_bytes cenv ty <= p ==>
      mem_bytes_at p k ss'.vs_memory = mem_bytes_at p k ss.vs_memory)
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_tuple_slot _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_abi_tuple_slot_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule_all abi_tuple_add_correct >> strip_tac >>
  `abi_tuple_input cenv ty tv v op ss1` by
    (irule abi_tuple_input_memory_cong >> metis_tac[]) >>
  drule_all abi_tuple_write_correct >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists_tac `ss'` >> gvs[] >>
  metis_tac[same_blocks_def]
QED

(* Check all public boundaries, including their transitive proof dependencies. *)
val _ = List.app (fn name =>
  if null (List.filter (fn x => x <> "DISK_THM")
    (#1 (Tag.dest_tag (Thm.tag (DB.fetch "abiTupleProps" name)))))
  then () else raise Fail ("oracle in " ^ name))
  ["abi_tuple_word_mstore", "compile_copy_memory_extends",
   "abi_tuple_write_correct", "abi_tuple_input_memory_cong",
   "compile_abi_tuple_slot_correct"];
