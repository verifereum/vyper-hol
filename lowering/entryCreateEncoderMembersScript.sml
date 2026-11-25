(* Confined ABI complex members, using the same endpoints as the joint window. *)
Theory entryCreateEncoderMembers
Ancestors
  abiEncoderWindowJointComplex entryCreatePathScope entryCreateCompletedCut
  entryCreateAdminSequence abiEncoderChildCode emitHelperProps
  abiEncoderProps abiEncoderWindowContract fragGasOriginPtr fragExec
  emitHelper compileEnv venomInst venomState rich_list list pred_set arithmetic
Libs monadsyntax

(* An enclosing encoder or row may choose its own stop PC. The rebasing
   condition is only about the fetch at that PC, not the execution. *)
Definition encoder_member_segment_def:
  encoder_member_segment ctx func explicit a b s t <=>
    !x y. x.cs_next_id <= a.cs_next_id /\ b.cs_next_id <= y.cs_next_id /\
      (!bb i. lookup_block y.cs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb (LENGTH y.cs_current_insts) = SOME i ==>
        i.inst_id NOTIN frag_ids a b) ==>
      create_expr_prefix x y explicit ctx func s [] t
End

Theorem encoder_member_segment_from_prefix:
  create_expr_prefix a b explicit ctx func s [] t ==>
  encoder_member_segment ctx func explicit a b s t
Proof
  rw[encoder_member_segment_def] >> metis_tac[create_expr_prefix_lift]
QED

Theorem encoder_member_segment_from_scope:
  create_operand_full_scope a b explicit ctx func s [] (OK t) ==>
  encoder_member_segment ctx func explicit a b s t
Proof
  simp[create_operand_full_scope_def] >> metis_tac[encoder_member_segment_from_prefix]
QED

Theorem encoder_member_segment_scope:
  encoder_member_segment ctx func explicit a b s t /\
  (!bb i. lookup_block b.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
    i.inst_id NOTIN frag_ids a b) /\
  window_strong_result ctx func a b out at av d s t ==>
  create_operand_full_scope a b explicit ctx func s [] (OK t)
Proof
  simp[encoder_member_segment_def,create_operand_full_scope_def,
       window_strong_result_def,abi_encoder_window_result_def] >> metis_tac[]
QED

Triviality encoder_member_segment_comp:
  a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id /\
  encoder_member_segment ctx func explicit a m s u /\
  encoder_member_segment ctx func explicit m b u t ==>
  encoder_member_segment ctx func explicit a b s t
Proof
  simp[encoder_member_segment_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  `frag_ids a m SUBSET frag_ids a b /\ frag_ids m b SUBSET frag_ids a b` by
    (simp[frag_ids_def,SUBSET_DEF] >> decide_tac) >>
  `create_expr_prefix x y explicit ctx func s [] u` by
    (qpat_assum `!x y. _ ==> create_expr_prefix x y explicit ctx func s [] u`
       (qspecl_then [`x`,`y`] irule) >> simp[SUBSET_DEF] >> metis_tac[SUBSET_DEF,LESS_EQ_TRANS]) >>
  `create_expr_prefix x y explicit ctx func u [] t` by
    (qpat_assum `!x y. _ ==> create_expr_prefix x y explicit ctx func u [] t`
       (qspecl_then [`x`,`y`] irule) >> simp[SUBSET_DEF] >> metis_tac[SUBSET_DEF,LESS_EQ_TRANS]) >>
  drule_all create_expr_prefix_append >> simp[]
QED

Definition encoder_members_primitive_scope_def:
  encoder_members_primitive_scope <=>
    !ctx func explicit a b s raw.
      abi_members_straight_code a b /\ fn_has_code a b func /\
      ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
      s.vs_inst_idx = LENGTH a.cs_current_insts /\
      run_inst_seq (emitted_insts a b) s = OK raw ==>
      create_expr_prefix a b explicit ctx func s []
        (raw with vs_inst_idx := LENGTH b.cs_current_insts)
End

Triviality encoder_members_straight_layout:
  abi_members_straight_code a b ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts a b)
Proof
  simp_tac bool_ss [abi_members_straight_code_def,abi_encode_child_prefix_def,
    abi_encode_child_suffix_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt strip_tac >>
  gvs[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def, fresh_id_def,
    emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[exprLoweringPropsTheory.emitted_insts_def, DROP_APPEND,
    mk_inst_def, frag_ids_def, is_terminator_def, SUB_PLUS]
QED

Theorem encoder_members_primitive_scope_from_run:
  encoder_members_primitive_scope
Proof
  rw[encoder_members_primitive_scope_def] >>
  drule encoder_members_straight_layout >> strip_tac >>
  drule_all (REWRITE_RULE [entryCreateFocusSpecTheory.create_operand_at_def,
    create_operand_full_scope_def]
     create_admin_sequence_scope) >> simp[]
QED

Triviality encoder_member_segment_laws:
  encoder_members_primitive_scope ==>
  abi_members_path_laws encoder_member_segment
Proof
  simp[encoder_members_primitive_scope_def,abi_members_path_laws_def] >>
  strip_tac >> rpt conj_tac
  >- simp[encoder_member_segment_def]
  >- metis_tac[encoder_member_segment_comp] >>
  metis_tac[encoder_member_segment_from_prefix]
QED

(* Same complete joint contract as the recursive encoder, with the extra
   segment inside the endpoint existential and outside the horizon binder. *)
Definition encoder_member_joint_scoped_def:
  encoder_member_joint_scoped ei <=>
  !dst src st out en ctx func s at av sb cap d G tn lo explicit PG.
    compile_abi_encode_to_buf dst src ei st = (out,en) /\
    abi_encoder_admissible ei /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      abi_encoder_window_input ei at av sb cap mem) /\
    eval_operand src s = SOME (n2w sb) /\
    eval_operand dst s = SOME (n2w d) /\
    op_taint tn src = {} /\ op_taint tn dst = {} /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st en func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_room ctx func s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
      s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    (0 < cap ==>
      sb + cap <= s.vs_alloca_next /\
      venomMemDefs$regions_disjoint
        (sb,cap) (d,LENGTH (contractABI$enc at av)) /\
      ?p. src = Var p /\ ptr_covers G tn p s cap) /\
    d + LENGTH (contractABI$enc at av) <= s.vs_alloca_next /\
    (0 < LENGTH (contractABI$enc at av) ==>
      ?p. dst = Var p /\
        ptr_covers G tn p s (LENGTH (contractABI$enc at av))) /\
    (!inst b sz.
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st en /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\
      (0 < cap ==>
        venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
      venomMemDefs$regions_disjoint
        (d,LENGTH (contractABI$enc at av)) (b,sz)) /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t G' tn'.
      window_strong_result ctx func st en out at av d s t /\
      abi_encode_exec_frame func s t /\
      op_taint tn' out = {} /\
      (!x. out = Var x ==> not_fresh_at en x) /\
      (!i. d <= i /\ i < d + LENGTH (contractABI$enc at av) ==>
        i NOTIN tn'.t_mem) /\
      (!x. not_fresh_at st x ==>
        FLOOKUP G' x = FLOOKUP G x /\
        op_taint tn' (Var x) = op_taint tn (Var x)) /\
      (!i. (i < d \/ d + LENGTH (contractABI$enc at av) <= i) /\
        (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
          FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
          i < b \/ b + sz <= i) ==>
        (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
      tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\
      tn'.t_imm = tn.t_imm /\
      encoder_member_segment ctx func explicit st en s t /\
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,G',tn')
End

Theorem encoder_complex_window_scoped_from_children:
  encoder_members_primitive_scope /\
  (!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==>
    encoder_member_joint_scoped ei) ==>
  encoder_member_joint_scoped (AbiComplex infos)
Proof
  strip_tac >> drule encoder_member_segment_laws >> disch_tac >>
  qpat_assum `abi_members_path_laws _`
    (mp_tac o MATCH_MP (Q.INST [`P` |-> `encoder_member_segment`]
      compile_abi_encode_to_buf_complex_window_joint_payload)) >>
  pure_rewrite_tac[GSYM encoder_member_joint_scoped_def] >>
  disch_then MATCH_MP_TAC >> first_assum ACCEPT_TAC
QED
