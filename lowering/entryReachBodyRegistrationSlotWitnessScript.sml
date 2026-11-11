(* Exact original-source witnesses for each processed registration index. *)
Theory entryReachBodyRegistrationSlotWitness
Ancestors
  valueEncodingDefs entryReachBodyRegistrationEndpointAudit
  entryStateRel entryReachBodyCanonicalArrayChild entryReachBodyOwnedRegion
  abiDecoderReentry compileEnv finite_map list words arithmetic

Definition entry_slot_witness_def:
  entry_slot_witness fn env args values j ce st s <=>
    ?tv op oid p vname ins.
      evaluate_type env (SND (EL j args)) = SOME tv /\
      FLOOKUP ce.ce_vars (FST (EL j args)) = SOME (PtrVar op (type_memory_size tv)) /\
      oid < st.cs_next_id /\ abi_decoder_operand_live st.cs_next_var op /\
      FLOOKUP s.vs_allocas oid = SOME (p,type_memory_size tv) /\
      eval_operand op s = SOME (n2w p) /\
      val_in_memory tv (EL j values) p s.vs_memory /\ val_wf tv (EL j values) /\
      op = Var vname /\ MEM ins (fn_insts fn) /\ ins.inst_opcode = ALLOCA /\
      ins.inst_outputs = [vname] /\ ins.inst_id = oid /\ p < dimword (:256)
End

Definition entry_prefix_witness_def:
  entry_prefix_witness fn env args values i ce st s <=>
    i <= LENGTH args /\ LENGTH values = LENGTH args /\
    !j. j < i ==> entry_slot_witness fn env args values j ce st s
End

Theorem entry_slot_old_lookup:
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st = (ce1,last) /\
  FST (EL j args) <> name ==>
  FLOOKUP ce1.ce_vars (FST (EL j args)) = FLOOKUP ce.ce_vars (FST (EL j args))
Proof
  strip_tac >> drule compile_register_positional_args_cenv >> simp[]
QED

Theorem entry_slot_witness_old:
  entry_slot_witness fn env args values j ce st initial /\
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st = (ce1,last) /\
  FST (EL j args) <> name /\
  array_child_result ctx fn st.cs_next_id root extent ambient
    (window_alloca_sites fn (abi_decoder_ids first.cs_next_id last.cs_next_id))
    b cap site limit first last cell tv value ready t /\
  st.cs_next_id < first.cs_next_id /\ first.cs_next_id <= last.cs_next_id /\
  st.cs_next_var <= first.cs_next_var /\ st.cs_next_var <= last.cs_next_var /\
  (!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==>
    FLOOKUP ready.vs_allocas id = SOME entry) /\
  ready.vs_memory = initial.vs_memory /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op ready = eval_operand op initial) ==>
  entry_slot_witness fn env args values j ce1 last t
Proof
  strip_tac >> drule_all entry_slot_old_lookup >> disch_tac >>
  fs[entry_slot_witness_def] >>
  drule_all registration_next_slot_previous_witness >> strip_tac >>
  qexistsl_tac [`p`, `ins`] >> simp[] >>
  irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]
QED

Theorem entry_slot_witness_new:
  evaluate_type env (SND (EL i args)) = SOME tv /\
  FLOOKUP ce1.ce_vars (FST (EL i args)) = SOME (PtrVar op (type_memory_size tv)) /\
  k < last.cs_next_id /\ abi_decoder_operand_live last.cs_next_var op /\
  array_child_result ctx fn k p (type_memory_size tv) ambient ids b cap site limit
    first last p tv (EL i values) ready t /\
  eval_operand op t = SOME (n2w p) /\ val_wf tv (EL i values) /\
  op = Var vname /\ MEM ins (fn_insts fn) /\ ins.inst_opcode = ALLOCA /\
  ins.inst_outputs = [vname] /\ ins.inst_id = k /\ p < dimword (:256) ==>
  entry_slot_witness fn env args values i ce1 last t
Proof
  simp[entry_slot_witness_def, array_child_result_def, entry_owned_region_def] >>
  metis_tac[]
QED

Theorem entry_slot_names_distinct:
  ALL_DISTINCT (MAP FST args) /\ j < i /\ i < LENGTH args ==>
  FST (EL j args) <> FST (EL i args)
Proof
  strip_tac >>
  `j < LENGTH args` by decide_tac >>
  mp_tac (Q.ISPEC `MAP FST args` ALL_DISTINCT_EL_IMP) >>
  disch_then (qspecl_then [`j`, `i`] mp_tac) >> simp[EL_MAP]
QED

Theorem entry_prefix_witness_empty:
  LENGTH values = LENGTH args ==>
  entry_prefix_witness fn env args values 0 ce st s
Proof
  simp[entry_prefix_witness_def]
QED

Theorem entry_prefix_witness_step:
  i < LENGTH args /\ LENGTH values = LENGTH args /\
  (!j. j < i ==> entry_slot_witness fn env args values j ce st s) /\
  entry_slot_witness fn env args values i ce st s ==>
  entry_prefix_witness fn env args values (SUC i) ce st s
Proof
  simp[entry_prefix_witness_def] >> rpt strip_tac >>
  Cases_on `j = i` >> gvs[] >> first_x_assum irule >> decide_tac
QED
