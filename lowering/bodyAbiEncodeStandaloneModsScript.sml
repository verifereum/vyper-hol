(* Physical payload execution after the standalone saved operand is unwrapped. *)
Theory bodyAbiEncodeStandaloneMods
Ancestors
  abiEncoderWindowJoint abiEncoderWindowPhase abiEncoderWindowContract
  exprLowering compileEnv fragExec bodyPtrDefs fragGasSeqPtr
  freshWrites ptrDiscipline venomMemDefs venomState words list finite_map
  contractABI vyperAST

Theorem abi_encode_nonword_window_mods:
  compile_abi_encode_payload ce T [saved] [ty] dst ready = (out,en) /\
  ~is_word_type ty /\ unwrap_value ce saved ready = (src,st) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce ty /\
  abi_encoder_admissible ei /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input ei at av sb cap mem) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (0 < cap ==> sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (enc at av)) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  d + LENGTH (enc at av) <= s.vs_alloca_next /\
  (0 < LENGTH (enc at av) ==> ?p. dst = Var p /\
    ptr_covers G tn p s (LENGTH (enc at av))) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
      [(d,LENGTH (enc at av))] s t /\
    abi_encode_exec_frame func s t /\
    mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    op_taint tn' out = {} /\ (!x. out = Var x ==> not_fresh_at en x) /\
    (!i. d <= i /\ i < d + LENGTH (enc at av) ==> i NOTIN tn'.t_mem) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < d \/ d + LENGTH (enc at av) <= i) /\
      (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b + sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  `compile_abi_encode_to_buf dst src ei st = (out,en)` by
    (qpat_x_assum `compile_abi_encode_payload _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_abi_encode_payload_def, comp_bind_def]) >>
  drule_all compile_abi_encode_to_buf_window_joint >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule_then assume_tac window_phase_strong_result >>
  drule_then (strip_assume_tac o MATCH_MP abi_encoder_window_result_output)
    window_strong_result_public >>
  qexistsl [`t`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED
