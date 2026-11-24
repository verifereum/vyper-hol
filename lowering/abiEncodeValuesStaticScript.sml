Theory abiEncodeValuesStatic
Ancestors
  abiEncodeValuesSource abiEncodeValuesCode abiEncodeValuesPhases abiEncoder
  abiEncoderWindowPhase abiEncoderWindowContract abiEncoderProps abiEncoderOpenInput
  exprSimAbiEncodeExecFrame fragGasOriginPtr fragExec
  exprLowering context compileEnv ptrDiscipline localPtrsProps
  emitHelperProps compileAllocaProvenance venomInst
  vyperValue vyperTyping vyperABI contractABI valueEncodingDefs valueEncodingProps
  venomState venomMemDefs words finite_map pred_set list arithmetic

(* The source-window hook is called with the actual robust source input.
   A caller can retain additional data on the same normal endpoint. *)
Definition abi_values_source_phase_def:
  abi_values_source_phase ctx func lo explicit PG R <=>
  !st en dst src ei out bs sb cap d s G tn.
    compile_abi_encode_to_buf dst src ei st = (out,en) /\
    abi_encoder_admissible ei /\
    (?ct rv. enc ct rv = bs /\
      !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        abi_encoder_window_input ei ct rv sb cap mem) /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    op_taint tn src = {} /\ op_taint tn dst = {} /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st en func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
        s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
    (0 < cap ==> sb + cap <= s.vs_alloca_next /\
        venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH bs) /\
        ?p. src = Var p /\ ptr_covers G tn p s cap) /\
    d + LENGTH bs <= s.vs_alloca_next /\
    (0 < LENGTH bs ==> ?p. dst = Var p /\ ptr_covers G tn p s (LENGTH bs)) /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
        sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
        venomMemDefs$regions_disjoint (d,LENGTH bs) (b,sz)) /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t G' tn'.
      mem_bytes_at d (LENGTH bs) t.vs_memory = bs /\
      eval_operand out t = SOME (n2w (LENGTH bs)) /\
      window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
        [(d,LENGTH bs)] s t /\ abi_encode_exec_frame func s t /\
      op_taint tn' out = {} /\ (!x. out = Var x ==> not_fresh_at en x) /\
      (!i. d <= i /\ i < d + LENGTH bs ==> i NOTIN tn'.t_mem) /\
      (!x. not_fresh_at st x ==>
        FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
      (!i. (i < d \/ d + LENGTH bs <= i) /\
        (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
          FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b + sz <= i) ==>
        (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
      R st en s t
End

Theorem abi_values_source_phase_trivial:
  abi_values_source_phase ctx func lo explicit PG (\st en s t. T)
Proof
  simp_tac bool_ss [abi_values_source_phase_def] >>
  rpt gen_tac >> ACCEPT_TAC abi_encode_values_source_window_input
QED

(* Static materialized aggregates already have the required ABI bytes.
   MCOPY is the recursive encoder's AbiCopy case; the empty layout emits
   no copy and has no source bytes to check. *)
Theorem abi_encode_values_static_store_phase:
  R st st s s /\ abi_values_source_phase ctx func lo explicit PG R /\
  compile_store_memory ce src dst ty ty st = ((),en) /\
  ~is_word_type ty /\ ~is_abi_dynamic ce.ce_struct_fields ty /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv = static_length (vyper_to_abi_type env ty) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v sb mem) /\
  bs = enc (vyper_to_abi_type env ty) av /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  (0 < LENGTH bs ==> sb + LENGTH bs <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,LENGTH bs) (d,LENGTH bs) /\
    (?p. src = Var p /\ ptr_covers G tn p s (LENGTH bs)) /\
    (?p. dst = Var p /\ ptr_covers G tn p s (LENGTH bs))) /\
  d + LENGTH bs <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    mem_bytes_at d (LENGTH bs) t.vs_memory = bs /\
    window_phase ctx func st en {} [(d,LENGTH bs)] s t /\
    abi_encode_exec_frame func s t /\
    (!i. d <= i /\ i < d + LENGTH bs ==> i NOTIN tn'.t_mem) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < d \/ d + LENGTH bs <= i) ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    R st en s t
Proof
  strip_tac >>
  `LENGTH bs = type_memory_size tv` by
    (`abi_encoder_layout_valid (vyper_to_abi_type env ty) av` by
       (irule abi_encode_values_typed_layout >> metis_tac[]) >>
     fs[abi_encoder_layout_valid_def]) >>
  Cases_on `type_memory_bytes ce ty = 0`
  >- (drule_all abi_encode_static_value_empty >> strip_tac >>
      `en = st` by fs[comp_return_def] >>
      `LENGTH (bs:word8 list) = 0` by decide_tac >>
      `bs = []` by metis_tac[LENGTH_NIL] >>
      qexistsl_tac [`s`,`G`,`tn`] >> gvs[mem_bytes_at_def, window_phase_refl,
        cj 1 gas_origin_ptr_path_rules]) >>
  `0 < type_memory_bytes ce ty` by decide_tac >>
  drule_all abi_encode_static_copy_trace >> strip_tac >>
  `emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes ce ty))] st = ((),en)` by
    (qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
     PURE_REWRITE_TAC [compile_abi_encode_child_def, comp_ignore_bind_def, comp_bind_def] >>
     Cases_on `emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes ce ty))] st` >>
     simp[comp_return_def, oneTheory.one]) >>
  drule_then strip_assume_tac emitted_insts_emit_void >>
  `!inst. MEM inst (fn_insts func) /\ inst.inst_id IN frag_ids st en ==>
     inst.inst_opcode <> ALLOCA` by
    (qx_gen_tac `inst` >> strip_tac >>
     qabbrev_tac `copy = mk_inst st.cs_next_id MCOPY
       [dst;src;Lit (n2w (type_memory_bytes ce ty))] []` >>
     `copy.inst_id = inst.inst_id` by
       (simp[Abbr `copy`, mk_inst_def] >> fs[frag_ids_def] >> decide_tac) >>
     `MEM copy (fn_insts func)` by
       (mp_tac (Q.SPECL [`st`,`en`,`func`,`copy`] fn_has_code_current_member) >>
        qpat_assum `en.cs_current_insts = _` (fn th => simp[th, Abbr `copy`])) >>
     `inst = copy` by metis_tac[fn_inst_ids_distinct_inj] >>
     fs[Abbr `copy`, mk_inst_def]) >>
  `window_alloca_sites func (frag_ids st en) = {}` by
    (simp[window_alloca_sites_def, EXTENSION] >> metis_tac[]) >>
  `abi_enc_plan env ty (AbiCopy (type_memory_bytes ce ty))` by
    metis_tac[abi_enc_plan_rules] >>
  `val_footprint tv v = LENGTH bs` by metis_tac[abi_encode_values_static_footprint] >>
  qpat_assum `abi_values_source_phase _ _ _ _ _ _`
    (mp_tac o Q.SPECL [`st`,`en`,`dst`,`src`,`AbiCopy (type_memory_bytes ce ty)`,
      `Lit (n2w (type_memory_bytes ce ty))`,`bs`,`sb`,`LENGTH (bs:word8 list)`,`d`,`s`,`G`,`tn`] o
      REWRITE_RULE [abi_values_source_phase_def]) >>
  impl_tac >-
    (`abi_encoder_admissible (AbiCopy (type_memory_bytes ce ty)) /\
      ?ct rv. enc ct rv = bs /\
       !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         abi_encoder_window_input (AbiCopy (type_memory_bytes ce ty)) ct rv sb (LENGTH bs) mem` by
       (drule_all abi_encode_values_plan_window_input >>
        qpat_assum `val_footprint tv v = LENGTH bs` (fn th => simp_tac bool_ss [th]) >>
        metis_tac[]) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  disch_then (qx_choose_then `t` (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac))) >>
  qpat_assum `window_alloca_sites func (frag_ids st en) = {}` (fn th =>
    RULE_ASSUM_TAC (REWRITE_RULE [th, NOT_IN_EMPTY])) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> asm_rewrite_tac[] >>
  TRY (conj_tac >- simp[]) >> gen_tac >> disch_tac >>
  qpat_assum `!i. _ /\ _ ==> (i IN tn'.t_mem <=> i IN tn.t_mem)`
    (qspec_then `i` mp_tac) >> simp[]
QED

Theorem abi_encode_values_static_store:
  compile_store_memory ce src dst ty ty st = ((),en) /\
  ~is_word_type ty /\ ~is_abi_dynamic ce.ce_struct_fields ty /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv = static_length (vyper_to_abi_type env ty) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v sb mem) /\
  bs = enc (vyper_to_abi_type env ty) av /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  (0 < LENGTH bs ==> sb + LENGTH bs <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,LENGTH bs) (d,LENGTH bs) /\
    (?p. src = Var p /\ ptr_covers G tn p s (LENGTH bs)) /\
    (?p. dst = Var p /\ ptr_covers G tn p s (LENGTH bs))) /\
  d + LENGTH bs <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    mem_bytes_at d (LENGTH bs) t.vs_memory = bs /\
    window_phase ctx func st en {} [(d,LENGTH bs)] s t /\
    abi_encode_exec_frame func s t /\
    (!i. d <= i /\ i < d + LENGTH bs ==> i NOTIN tn'.t_mem) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < d \/ d + LENGTH bs <= i) ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  mp_tac (Q.INST [`R` |-> `\st en s t. T`] abi_encode_values_static_store_phase) >>
  simp_tac bool_ss [abi_values_source_phase_trivial]
QED
