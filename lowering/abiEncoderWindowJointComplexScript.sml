(* Joint actual-window complex encoding on each selected member execution. *)
Theory abiEncoderWindowJointComplex
Ancestors
  abiEncoderWindowJointPhases abiEncoderWindowJointLeaves
  abiEncoderWindowComplex abiEncoderWindowStructuralMembers abiEncoderWindowMembers
  abiEncoderWindowChild abiEncoderWindowPhase abiEncoderWindowSequence
  abiEncoderWindowContract abiEncoderWindow abiEncoderRegisteredEffect
  abiEncoderBufferFrame abiEncoderInput abiCanonicalWindows bodyPtrDefs valueEncodingDefs
  abiEncoderComplexCode abiEncoderMemberCode abiEncoderChildCode
  exprSimAbiEncodeExecFrame exprSimAbiEncodeFramedLeaves
  representationCleanPtr robustCopyTransportPtr
  stmtAppendStorageRunPtr exprLoweringProps venomInstProofs ptrSafetyTransport
  fragExecMem ptrSafeRun instIdxIndep ghostPcTransportPtr emitHelper fragExec
  unitTransformDefs memSafeRun decoderGhostFramePtr
  exprSimAbiEncodeFramedArrayBody
  fragGasSeqPtr fragGasOriginPtr fragExecPtr ptrCoverage ptrDiscipline
  loweringStateRelDefs emitHelperProps freshWrites compileEnv
  venomExecSemantics venomState venomMemDefs venomInst
  contractABI valueEncodingProps words list rich_list finite_map pred_set arithmetic

(* The primitive producer supplies the concrete straight-line run. The
   payload law decides which enclosing path geometry to collect from it. *)
Definition abi_members_straight_code_def:
  abi_members_straight_code a b <=>
    (?ops out. emit_op ADD ops a = (out,b)) \/
    (?ops out. emit_op MLOAD ops a = (out,b)) \/
    (?cursor value m. emit_op ALLOCA [Lit 32w] a = (cursor,m) /\
      emit_void MSTORE [cursor;value] m = ((),b)) \/
    (?dst ho dp ops. abi_encode_child_prefix dst ho dp a = (ops,b)) \/
    (?head dp offset len out.
      abi_encode_child_suffix head dp offset len a = (out,b))
End

Definition abi_members_path_laws_def:
  abi_members_path_laws
      (P : venom_context -> ir_function -> (string # num) set ->
           compile_state -> compile_state -> venom_state -> venom_state -> bool) <=>
    (!ctx func explicit a s. P ctx func explicit a a s s) /\
    (!ctx func explicit a m b s u t.
      a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id /\
      P ctx func explicit a m s u /\ P ctx func explicit m b u t ==>
      P ctx func explicit a b s t) /\
    (!ctx func explicit a b s raw.
      abi_members_straight_code a b /\ fn_has_code a b func /\
      ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
      s.vs_inst_idx = LENGTH a.cs_current_insts /\
      run_inst_seq (emitted_insts a b) s = OK raw ==>
      P ctx func explicit a b s
        (raw with vs_inst_idx := LENGTH b.cs_current_insts))
End

Triviality members_payload_refl:
  abi_members_path_laws P ==> P ctx func explicit a a s s
Proof
  simp[abi_members_path_laws_def]
QED

Triviality members_payload_comp:
  abi_members_path_laws P /\
  a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id /\
  P ctx func explicit a m s u /\ P ctx func explicit m b u t ==>
  P ctx func explicit a b s t
Proof
  simp[abi_members_path_laws_def] >> metis_tac[]
QED

Triviality members_payload_pure:
  abi_members_path_laws P /\ abi_members_straight_code a b /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  window_pure_seq a b s raw ==>
  P ctx func explicit a b s
    (raw with vs_inst_idx := LENGTH b.cs_current_insts)
Proof
  simp[abi_members_path_laws_def,window_pure_seq_def,window_seq_def] >>
  metis_tac[]
QED

Triviality members_payload_phase:
  abi_members_path_laws P /\ abi_members_straight_code a b /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  run_inst_seq (emitted_insts a b) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
  t.vs_inst_idx = LENGTH b.cs_current_insts ==>
  P ctx func explicit a b s t
Proof
  simp[abi_members_path_laws_def] >> strip_tac >>
  first_x_assum (qspecl_then [`ctx`,`func`,`explicit`,`a`,`b`,`s`,
    `t with vs_inst_idx := s.vs_inst_idx`] mp_tac) >>
  `(t with vs_inst_idx := LENGTH b.cs_current_insts) = t` by
    simp[venom_state_component_equality] >>
  simp[]
QED

Theorem compile_abi_encode_to_buf_complex_window_joint_payload:
  abi_members_path_laws P ==>
  (!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==>
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
        P ctx func explicit st en s t /\
        !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
          (s,G,tn) [] (OK t,G',tn')) ==>
  !dst src st out en ctx func s at av sb cap d G tn lo explicit PG.
    compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,en) /\
    abi_encoder_admissible (AbiComplex infos) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      abi_encoder_window_input (AbiComplex infos) at av sb cap mem) /\
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
      P ctx func explicit st en s t /\
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `abi_encoder_window_input (AbiComplex infos) at av sb cap s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `?ats avs. av = ListV avs /\ abi_encoder_tuple_type at ats /\
    LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_complex_iff] >> metis_tac[]) >>
  qpat_x_assum `av = ListV avs` SUBST_ALL_TAC >>
  `!i ei az ms dyn.
    i < LENGTH infos /\ EL i infos = (ei,az,ms,dyn) ==>
    az = abi_member_head_size (EL i ats) /\
    dyn = is_dynamic (EL i ats) /\
    !source_memory source_taint.
      (!mem. mem_agree_outside source_taint source_memory mem ==>
        abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb cap mem) ==>
    !mem. mem_agree_outside source_taint source_memory mem ==>
      abi_encoder_window_input ei (EL i ats) (EL i avs)
        (sb + abi_encoder_member_span (TAKE i infos))
        (MIN ms (cap - abi_encoder_member_span (TAKE i infos))) mem` by
    (qpat_x_assum `!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> _` kall_tac >>
     rpt gen_tac >> strip_tac >>
     `az = abi_member_head_size (EL i ats) /\
      dyn = is_dynamic (EL i ats)` by
       (drule_all abi_encoder_window_complex_child >>
        disch_then (qx_choose_then `child_types`
          (qx_choose_then `child_cap` strip_assume_tac)) >>
        `child_types = ats` by
          metis_tac[abiEncoderBufferFrameTheory.abi_encoder_tuple_type_unique] >>
        qpat_assum `child_types = ats` (SUBST1_TAC o SYM) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     `abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb cap mem` by
       metis_tac[] >>
     drule_all abi_encoder_window_complex_child >>
     disch_then (qx_choose_then `child_types`
       (qx_choose_then `child_cap` strip_assume_tac)) >>
     `child_types = ats` by
       metis_tac[abiEncoderBufferFrameTheory.abi_encoder_tuple_type_unique] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`child_types = ats`, `child_cap <= ms`,
        `sb + abi_encoder_member_span (TAKE i infos) + child_cap <= sb + cap`,
        `abi_encoder_window_input ei (EL i child_types) (EL i avs)
          (sb + abi_encoder_member_span (TAKE i infos)) child_cap mem`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     qpat_x_assum `child_types = ats` SUBST_ALL_TAC >>
     irule abi_encoder_window_input_capacity >>
     goal_assum (drule_at Any) >> simp[MIN_DEF] >> decide_tac) >>
  Cases_on `infos = []`
  >- (qpat_x_assum `infos = []` SUBST_ALL_TAC >>
      qpat_x_assum `!ei az ms dyn. MEM (ei,az,ms,dyn) [] ==> _` kall_tac >>
      qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
      simp_tac (srw_ss()) [Once abiEncoderTheory.compile_abi_encode_child_def,
        comp_return_def] >> strip_tac >>
      qpat_x_assum `out = Lit 0w` SUBST_ALL_TAC >>
      qpat_x_assum `st = en` SUBST_ALL_TAC >>
      `enc at (ListV avs) = []` by
        (map_every (fn pat => qpat_assum pat mp_tac)
           [`abi_encoder_tuple_type at ats`, `LENGTH [] = LENGTH ats`,
            `LENGTH ats = LENGTH avs`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         gvs[abi_encoder_tuple_type_def, enc_def,
           head_lengths_def, LET_THM, REV_DEF]) >>
      qexistsl_tac [`s`, `G`, `tn`] >>
      simp[eval_operand_def, op_taint_def] >> conj_tac
      >- (irule window_complex_phase_result >>
          map_every (fn pat => qpat_assum pat mp_tac)
            [`alloca_inv s`, `alloca_room ctx func s`, `~s.vs_halted`,
             `s.vs_current_bb = en.cs_current_bb`,
             `s.vs_inst_idx = LENGTH en.cs_current_insts`,
             `enc at (ListV avs) = []`] >>
          POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
          conj_tac
          >- (rpt strip_tac >>
              qpat_x_assum `i IN window_alloca_sites _ _` mp_tac >>
              simp[window_alloca_sites_def, abiEncoderPropsTheory.frag_ids_def] >>
              decide_tac) >>
          simp[mem_bytes_at_def, eval_operand_def] >>
          irule window_phase_refl >> simp[]) >>
      conj_tac
      >- fs[abi_members_path_laws_def] >>
      gen_tac >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  suspend "members"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[members]:
  drule_all window_complex_structural_members >> strip_tac >>
  drule_all window_complex_head_layout >> strip_tac >>
  `enc at (ListV avs) = enc (Tuple ats) (ListV avs)` by
    (qpat_assum `abi_encoder_tuple_type at ats` mp_tac >>
     qpat_assum `LENGTH ats = LENGTH avs` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rw[abi_encoder_tuple_type_def] >>
     gvs[Once enc_def, LET_THM]) >>
  `!u tu.
    mem_bytes_at sb cap u.vs_memory = mem_bytes_at sb cap s.vs_memory /\
    (!i. i < cap ==> (sb+i IN tu.t_mem <=> sb+i IN tn.t_mem)) ==>
    !mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
      abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb cap mem` by
    (qpat_x_assum `!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> _` kall_tac >>
     rpt strip_tac >>
     qspecl_then [`tn.t_mem`, `tu.t_mem`, `s.vs_memory`, `u.vs_memory`,
       `sb`, `sb`, `cap`, `mem`] mp_tac copied_window_agree_witness >>
     (impl_tac >- asm_rewrite_tac[]) >>
     disch_then (qx_choose_then `mix` strip_assume_tac) >>
     `abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb cap mix` by
       metis_tac[] >>
     drule abi_encoder_window_input_mem_agree >>
     disch_then (qspec_then `mem` mp_tac) >> asm_rewrite_tac[]) >>
  suspend "member_induction"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_induction]:
  qabbrev_tac `encoded_size = LENGTH (enc at (ListV avs))` >>
  qabbrev_tac `sites = window_alloca_sites func (frag_ids st en)` >>
  qabbrev_tac `head_bytes = \k.
    LENGTH (FLAT (abi_tuple_heads (window_member_head_size infos) 0
      (TAKE k ats) (TAKE k avs)))` >>
  qabbrev_tac `tail_bytes = \k.
    LENGTH (FLAT (abi_tuple_tails (TAKE k ats) (TAKE k avs)))` >>
  `!remaining k current end_st result u Gu tu dp site slot.
    remaining = DROP k infos /\ k <= LENGTH infos /\
    compile_abi_encode_complex_elems dst src remaining
      (abi_encoder_member_span (TAKE k infos))
      (SUM (MAP abi_member_head_size (TAKE k ats))) dp current = (result,end_st) /\
    fn_has_code current end_st func /\
    st.cs_next_var <= current.cs_next_var /\
    st.cs_next_id <= current.cs_next_id /\ end_st.cs_next_id <= en.cs_next_id /\
    alloca_inv u /\ alloca_room ctx func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u /\ u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp) /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\
    ~u.vs_halted /\ u.vs_current_bb = current.cs_current_bb /\
    u.vs_inst_idx = LENGTH current.cs_current_insts /\
    eval_operand src u = SOME (n2w sb) /\ eval_operand dst u = SOME (n2w d) /\
    op_taint tu src = {} /\ op_taint tu dst = {} /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at current x) /\
    (0 < cap ==> sb+cap <= u.vs_alloca_next /\
      regions_disjoint (sb,cap) (d,encoded_size) /\
      ?p. src = Var p /\ ptr_covers Gu tu p u cap) /\
    d+encoded_size <= u.vs_alloca_next /\
    (0 < encoded_size ==> ?p. dst = Var p /\ ptr_covers Gu tu p u encoded_size) /\
    (!id b sz. id IN sites /\ FLOOKUP u.vs_allocas id = SOME (b,sz) ==>
      sz = 32 /\ (0 < cap ==> regions_disjoint (sb,cap) (b,sz)) /\
      regions_disjoint (d,encoded_size) (b,sz)) /\
    mem_bytes_at sb cap u.vs_memory = mem_bytes_at sb cap s.vs_memory /\
    (!i. i < cap ==> (sb+i IN tu.t_mem <=> sb+i IN tn.t_mem)) /\
    window_member_prefix infos ats avs k d u.vs_memory /\
    (!i. (d <= i /\ i < d + head_bytes k) \/
      (d + window_member_head_size infos <= i /\
       i < d + window_member_head_size infos + tail_bytes k) ==> i NOTIN tu.t_mem) /\
    (EXISTS (\(_,_,_,dyn). dyn) infos ==>
      site IN sites /\ site < current.cs_next_id /\
      (?p. dp = Var p /\ not_fresh_at current p /\ ptr_covers Gu tu p u 32) /\
      eval_operand dp u = SOME (n2w slot) /\
      FLOOKUP u.vs_allocas site = SOME (slot,32) /\
      slot + 32 <= u.vs_alloca_next /\
      mem_word_at slot u.vs_memory = n2w (window_member_tail infos ats avs k) /\
      (!i. slot <= i /\ i < slot+32 ==> i NOTIN tu.t_mem)) ==>
    ?t Gf tf.
      window_phase ctx func current end_st sites [(d,encoded_size)] u t /\
      abi_encode_exec_frame func u t /\
      window_member_prefix infos ats avs (LENGTH infos) d t.vs_memory /\
      (!i. d <= i /\ i < d+encoded_size ==> i NOTIN tf.t_mem) /\
      allocas_from lo t /\ lo <= t.vs_alloca_next /\
      (!id b sz. id IN sites /\ FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
        sz = 32 /\ (0 < cap ==> regions_disjoint (sb,cap) (b,sz)) /\
        regions_disjoint (d,encoded_size) (b,sz)) /\
      (EXISTS (\(_,_,_,dyn). dyn) infos ==>
        eval_operand dp t = SOME (n2w slot) /\
        FLOOKUP t.vs_allocas site = SOME (slot,32) /\
        mem_word_at slot t.vs_memory = n2w encoded_size /\
        (!i. slot <= i /\ i < slot+32 ==> i NOTIN tf.t_mem) /\
        (?p. dp = Var p /\ not_fresh_at end_st p /\ ptr_covers Gf tf p t 32)) /\
      (!x. not_fresh_at current x ==>
        FLOOKUP Gf x = FLOOKUP Gu x /\ op_taint tf (Var x) = op_taint tu (Var x)) /\
      (!i. (i < d \/ d+encoded_size <= i) /\
        (!id b sz. id IN sites /\ FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
          i < b \/ b+sz <= i) ==> (i IN tf.t_mem <=> i IN tu.t_mem)) /\
      tf.t_stor = tu.t_stor /\ tf.t_trans = tu.t_trans /\ tf.t_imm = tu.t_imm /\
      P ctx func explicit current end_st u t /\
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (u,Gu,tu) [] (OK t,Gf,tf)` by
    (Induct >> rpt gen_tac >> strip_tac
     >- suspend "members_done" >>
     suspend "member_step") >>
  suspend "parent_assembly"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[members_done]:
  `k = LENGTH infos` by
    (qpat_assum `[] = DROP k infos` mp_tac >>
     qpat_assum `k <= LENGTH infos` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     `LENGTH infos <= k` by metis_tac[DROP_EQ_NIL] >> decide_tac) >>
  qpat_x_assum `k = LENGTH infos` SUBST_ALL_TAC >>
  `head_bytes (LENGTH infos) = window_member_head_size infos /\
   window_member_head_size infos + tail_bytes (LENGTH infos) = encoded_size /\
   window_member_tail infos ats avs (LENGTH infos) = encoded_size` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH infos = LENGTH ats`, `LENGTH ats = LENGTH avs`,
        `LIST_REL abi_encoder_structural_valid ats avs`,
        `window_member_head_size infos = head_lengths ats 0`,
        `enc at (ListV avs) = enc (Tuple ats) (ListV avs)`,
        `Abbrev (encoded_size = _)`, `Abbrev (head_bytes = _)`,
        `Abbrev (tail_bytes = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     `TAKE (LENGTH infos) ats = ats /\ TAKE (LENGTH infos) avs = avs` by
       metis_tac[TAKE_LENGTH_ID] >>
     drule window_structural_member_tuple_length >> disch_tac >>
     drule abiEncoderOpenInputTheory.abi_encoder_structural_list_layout >> disch_tac >>
     asm_simp_tac bool_ss [Abbr `head_bytes`, Abbr `tail_bytes`, Abbr `encoded_size`,
       window_member_tail_def, abiEncoderOpenInputTheory.abi_encoder_open_heads_length,
       abiDecodeRangesTheory.head_lengths_acc, ADD_COMM, ADD_CLAUSES]) >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ [] _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once abiEncoderTheory.compile_abi_encode_child_def,
    comp_return_def, pairTheory.PAIR_EQ] >> strip_tac >>
  qpat_x_assum `current = end_st` SUBST_ALL_TAC >>
  `!i. d <= i /\ i < d+encoded_size ==> i NOTIN tu.t_mem` by
    (qpat_assum `!i. (_ /\ _) \/ (_ /\ _) ==> i NOTIN tu.t_mem` mp_tac >>
     qpat_assum `head_bytes (LENGTH infos) = window_member_head_size infos` mp_tac >>
     qpat_assum `window_member_head_size infos + tail_bytes (LENGTH infos) = encoded_size` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     gen_tac >> strip_tac >> first_x_assum irule >>
     asm_rewrite_tac[] >> decide_tac) >>
  `window_phase ctx func end_st end_st sites [(d,encoded_size)] u u` by
    (irule window_phase_refl >> asm_rewrite_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (u,Gu,tu) [] (OK u,Gu,tu)` by
    (gen_tac >> irule (cj 1 gas_origin_ptr_path_rules) >> first_assum ACCEPT_TAC) >>
  `P ctx func explicit end_st end_st u u` by
    (irule members_payload_refl >> first_assum ACCEPT_TAC) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`P ctx func explicit end_st end_st u u`,
     `window_phase ctx func end_st end_st sites [(d,encoded_size)] u u`,
     `window_member_prefix infos ats avs (LENGTH infos) d u.vs_memory`,
     `!i. d <= i /\ i < d+encoded_size ==> i NOTIN tu.t_mem`,
     `allocas_from lo u`, `lo <= u.vs_alloca_next`,
     `!id b sz. id IN sites /\ FLOOKUP u.vs_allocas id = SOME (b,sz) ==> _`,
     `EXISTS (\(_,_,_,dyn). dyn) infos ==> _`,
     `window_member_tail infos ats avs (LENGTH infos) = encoded_size`,
     `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK u,Gu,tu)`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  qexistsl_tac [`u`, `Gu`, `tu`] >>
  asm_simp_tac bool_ss [abi_encode_exec_frame_refl] >> first_assum ACCEPT_TAC
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_step]:
  rename1 `entry::rest = DROP k infos` >> PairCases_on `entry` >>
  rename1 `(ei,az,ms,dyn)::rest = DROP k infos` >>
  `k < LENGTH infos` by
    (qpat_assum `(ei,az,ms,dyn)::rest = DROP k infos`
       (mp_tac o Q.AP_TERM `LENGTH`) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[LENGTH_DROP] >> decide_tac) >>
  `EL k infos = (ei,az,ms,dyn)` by
    (qpat_assum `(ei,az,ms,dyn)::rest = DROP k infos`
       (mp_tac o Q.AP_TERM `HD`) >>
     qpat_assum `k < LENGTH infos` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[HD_DROP]) >>
  `DROP (SUC k) infos = rest` by
    (qpat_assum `(ei,az,ms,dyn)::rest = DROP k infos`
       (fn th => simp_tac (srw_ss()) [NoAsms, DROP_SUC, GSYM th])) >>
  `MEM (ei,az,ms,dyn) infos` by metis_tac[MEM_EL] >>
  `abi_encoder_admissible ei` by
    (qpat_assum `abi_encoder_admissible (AbiComplex infos)` mp_tac >>
     qpat_assum `MEM (ei,az,ms,dyn) infos` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiEncoderAdmissibleTheory.abi_encoder_admissible_def,
       abiEncoderAdmissibleTheory.abi_encoder_members_admissible_every, EVERY_MEM] >>
     rpt strip_tac >> first_x_assum (qspec_then `(ei,az,ms,dyn)` mp_tac) >> simp[]) >>
  `!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
    abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb cap mem` by
    (qpat_assum `!u tu. mem_bytes_at sb cap u.vs_memory = _ /\ _ ==> _`
       (qspecl_then [`u`, `tu`] MATCH_MP_TAC) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!i ei az ms dyn. i < LENGTH infos /\ EL i infos = _ ==> _`
    (qspecl_then [`k`, `ei`, `az`, `ms`, `dyn`]
      (fn th => SUBGOAL_THEN (fst (dest_imp (concl th)))
        (fn pre => strip_assume_tac (MP th pre)))) >-
    (conj_tac >> first_assum ACCEPT_TAC) >>
  `!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
    abi_encoder_window_input ei (EL k ats) (EL k avs)
      (sb + abi_encoder_member_span (TAKE k infos))
      (MIN ms (cap - abi_encoder_member_span (TAKE k infos))) mem` by
    (qpat_assum `!source_memory source_taint. _`
       (qspecl_then [`u.vs_memory`, `tu.t_mem`] MATCH_MP_TAC) >>
     first_assum ACCEPT_TAC) >>
  drule_all abi_encoder_member_cons_context >>
  disch_then (qx_choose_then `elem_src`
    (qx_choose_then `prepared`
      (qx_choose_then `child_len` (qx_choose_then `child_end` strip_assume_tac)))) >>
  suspend "member_source_add"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_source_add]:
  qabbrev_tac `source_offset = abi_encoder_member_span (TAKE k infos)` >>
  qabbrev_tac `source_var = STRING #"%" (toString current.cs_next_var)` >>
  `eval_operand (Lit (n2w source_offset)) u = SOME (n2w source_offset)` by
    simp[eval_operand_def] >>
  drule_all window_emit_add_pure >>
  disch_then (qx_choose_then `source_raw` strip_assume_tac) >>
  `elem_src = Var source_var /\
   emitted_insts current prepared =
     [mk_inst current.cs_next_id ADD [src;Lit (n2w source_offset)] [source_var]]` by
    (qpat_assum `emit_op ADD [src;_] current = _` mp_tac >>
     qpat_assum `Abbrev (source_var = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     drule emitted_insts_emit_op >> simp[Abbr `source_var`]) >>
  `source_raw = update_var source_var (n2w (sb+source_offset)) u` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`window_pure_seq current prepared u source_raw`,
        `emitted_insts current prepared = _`,
        `eval_operand src u = SOME (n2w sb)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     qpat_x_assum `window_pure_seq _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_pure_seq_def, window_seq_def] >> strip_tac >>
     qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     asm_rewrite_tac[] >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, eval_operand_def, word_add_n2w]) >>
  `abi_encode_exec_frame func u source_raw` by
    (irule exprSimAbiEncodeFramedArrayBodyTheory.abi_encode_framed_ordinary_pure_sequence >>
     goal_assum (drule_at Any) >>
     qpat_assum `emitted_insts current prepared = _` (fn th => rewrite_tac[th]) >>
     simp[mk_inst_def, is_terminator_def, is_alloca_op_def, is_ext_call_op_def]) >>
  qabbrev_tac `source_inst =
    mk_inst current.cs_next_id ADD [src;Lit (n2w source_offset)] [source_var]` >>
  qabbrev_tac `Gs = step_prov PG Gu source_inst source_raw` >>
  qabbrev_tac `ts = step_taint source_inst u source_raw tu` >>
  `ts = tu with t_var := tu.t_var |+ (source_var,{})` by
    (simp_tac bool_ss [Abbr `ts`, Abbr `source_inst`] >>
     irule scalar_add_taint >>
     qpat_assum `source_raw = update_var _ _ u` (fn th => rewrite_tac[th]) >>
     simp[NoAsms, update_var_def]) >>
  suspend "member_source_path"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_source_path]:
  `step_inst_base source_inst u = OK source_raw` by
    (qpat_assum `window_pure_seq current prepared u source_raw` mp_tac >>
     qpat_assum `emitted_insts current prepared = _` mp_tac >>
     qpat_assum `Abbrev (source_inst = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[markerTheory.Abbrev_def, window_pure_seq_def, window_seq_def,
       run_inst_seq_def, AllCaseEqs()]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by metis_tac[] >>
  `!D. ptr_inst_ok D lo 0 ctx func Gu tu source_inst u` by
    (gen_tac >>
     irule (Q.INST [`lo0` |-> `0`] ptr_inst_ok_lower_bound_transport) >>
     simp_tac bool_ss [ZERO_LESS_EQ] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`op_taint tu src = {}`, `ctx_has_dalloca ctx ==> allocas_below_fmp u`,
        `step_inst_base source_inst u = OK source_raw`,
        `source_raw = update_var _ _ u`, `Abbrev (source_inst = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     gvs[markerTheory.Abbrev_def] >>
     irule append_scalar_inst_check >>
     asm_simp_tac (srw_ss()) [update_var_def] >>
     rpt strip_tac >> gvs[op_taint_def]) >>
  `!D. inst_seq_ptr D lo ctx func PG Gu tu [source_inst] u Gs ts` by
    (gen_tac >> pure_rewrite_tac[inst_seq_ptr_def] >>
     qpat_assum `step_inst_base source_inst u = OK source_raw`
       (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, Abbr `Gs`, Abbr `ts`,
       step_prov_inst_idx, step_taint_inst_idx_left, step_taint_inst_idx_right] >>
     first_assum MATCH_ACCEPT_TAC) >>
  `prepared.cs_current_insts = current.cs_current_insts ++ [source_inst] /\
   prepared.cs_current_bb = current.cs_current_bb` by
    (qpat_assum `emit_op ADD _ current = _` mp_tac >>
     qpat_assum `Abbrev (source_inst = _)` mp_tac >>
     qpat_assum `Abbrev (source_var = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def, LET_THM] >>
     rpt strip_tac >> gvs[]) >>
  `?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX [source_inst] (DROP u.vs_inst_idx bb.bb_instructions)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`fn_has_code current prepared func`, `prepared.cs_current_insts = _`,
        `prepared.cs_current_bb = _`, `u.vs_current_bb = _`, `u.vs_inst_idx = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rw[fn_has_code_def, IS_PREFIX_APPEND] >>
     qexists_tac `bb` >> qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
     asm_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (u,Gu,tu) []
    (OK (source_raw with vs_inst_idx := LENGTH prepared.cs_current_insts),Gs,ts)` by
    (gen_tac >>
     `u.vs_inst_idx + 1 = LENGTH prepared.cs_current_insts` by
       (qpat_assum `u.vs_inst_idx = LENGTH current.cs_current_insts`
          (fn th => rewrite_tac[th]) >>
        qpat_assum `prepared.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
        simp[NoAsms]) >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
       [source_inst]` by
       simp[NoAsms, Abbr `source_inst`, mk_inst_def, is_terminator_def] >>
     `run_inst_seq_mem_ok [source_inst] u` by
       (simp[NoAsms, fragExecMemTheory.run_inst_seq_mem_ok_def,
         Abbr `source_inst`, mk_inst_def,
         unitTransformDefsTheory.inst_mem_below_frontier_def,
         memSafeRunTheory.inst_dload_in_section_def,
         contextCodegenRelTheory.source_memory_read_ranges_def,
         codegenRelTheory.source_memory_write_ranges_def] >>
        CASE_TAC >> simp[NoAsms]) >>
     `run_inst_seq [source_inst] u = OK source_raw` by
       (qpat_assum `step_inst_base source_inst u = OK source_raw`
          (fn th => simp[NoAsms, run_inst_seq_def, th])) >>
     `inst_seq_ptr D lo ctx func PG Gu tu [source_inst] u Gs ts` by metis_tac[] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`~u.vs_halted`, `lookup_block u.vs_current_bb func.fn_blocks = SOME bb`,
        `isPREFIX [source_inst] (DROP u.vs_inst_idx bb.bb_instructions)`,
        `EVERY _ [source_inst]`, `run_inst_seq_mem_ok [source_inst] u`,
        `inst_seq_ptr D lo ctx func PG Gu tu [source_inst] u Gs ts`,
        `run_inst_seq [source_inst] u = OK source_raw`,
        `u.vs_inst_idx + 1 = LENGTH prepared.cs_current_insts`,
        `Abbrev (source_inst = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     `(ctx_has_dalloca ctx ==>
        !pre i post v. [source_inst] = pre ++ i::post /\
          run_inst_seq pre u = OK v ==> dalloca_no_wrap i v)` by
       simp[NoAsms, Once EQ_SYM_EQ, APPEND_EQ_SING, Abbr `source_inst`, mk_inst_def] >>
     drule_all run_inst_seq_gas_origin_ptr_path >>
     simp_tac (srw_ss()) [Abbr `source_inst`, mk_inst_def] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `window_phase ctx func current prepared sites [(d,encoded_size)] u
    (source_raw with vs_inst_idx := LENGTH prepared.cs_current_insts)` by
    (irule window_pure_seq_phase >> asm_simp_tac bool_ss []) >>
  suspend "member_source_transport"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_source_transport]:
  qabbrev_tac `us = source_raw with vs_inst_idx := LENGTH prepared.cs_current_insts` >>
  `P ctx func explicit current prepared u us` by
    (simp_tac bool_ss [Abbr `us`] >> irule members_payload_pure >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     pure_rewrite_tac[abi_members_straight_code_def] >> disj1_tac >>
     goal_assum (drule_at Any)) >>
  `window_phase ctx func current prepared sites [(d,encoded_size)] u us` by
    (qpat_assum `window_phase ctx func current prepared _ _ u _` mp_tac >>
     simp_tac bool_ss [Abbr `us`]) >>
  drule window_phase_resources >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  `abi_encode_exec_frame func u us` by
    (simp_tac bool_ss [Abbr `us`, abi_encode_exec_frame_inst_idx] >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp us /\
    us.vs_alloca_next + pending_alloca_size func us <= w2n us.vs_initial_fmp` by
    (qpat_assum `abi_encode_exec_frame func u us` (fn frame =>
       qpat_assum `alloca_inv us` (fn inv =>
         qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u /\ u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp` (fn bound =>
           ACCEPT_TAC (MATCH_MP window_exec_frame_alloca_budget
             (LIST_CONJ [frame,inv,bound])))))) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp us` by
    qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp us /\ us.vs_alloca_next + pending_alloca_size func us <= w2n us.vs_initial_fmp`
      (fn th => ACCEPT_TAC (DISCH (fst (dest_imp (concl th)))
        (CONJUNCT1 (UNDISCH th)))) >>
  `eval_operand dst us = SOME (n2w d)` by
    (irule window_phase_operand >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >> metis_tac[]) >>
  `!x. not_fresh_at current x ==> source_var <> x` by
    (simp[NoAsms, Abbr `source_var`, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  `!x. not_fresh_at current x ==>
    lookup_var x us = lookup_var x u /\
    FLOOKUP Gs x = FLOOKUP Gu x /\
    op_taint ts (Var x) = op_taint tu (Var x)` by
    (gen_tac >> strip_tac >>
     `source_var <> x` by metis_tac[] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`source_var <> x`, `source_raw = update_var _ _ u`,
        `Abbrev (us = _)`, `Abbrev (Gs = _)`, `Abbrev (source_inst = _)`,
        `ts = tu with t_var := _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     asm_simp_tac (srw_ss()) [Abbr `us`, Abbr `Gs`, Abbr `source_inst`,
       scalar_step_old_prov, scalar_step_old_taint, update_var_def,
       lookup_var_def, op_taint_def, FLOOKUP_UPDATE]) >>
  `eval_operand elem_src us = SOME (n2w (sb+source_offset)) /\
   op_taint ts elem_src = {}` by
    (qpat_assum `elem_src = Var source_var` (fn th => rewrite_tac[th]) >>
     simp_tac bool_ss [Abbr `us`] >>
     qpat_assum `source_raw = update_var _ _ u` (fn th => rewrite_tac[th]) >>
     qpat_assum `ts = tu with t_var := _` (fn th => rewrite_tac[th]) >>
     simp[NoAsms, eval_operand_def, lookup_var_def,
       update_var_def, op_taint_def, FLOOKUP_UPDATE]) >>
  `us.vs_memory = u.vs_memory /\ us.vs_allocas = u.vs_allocas /\
   us.vs_alloca_next = u.vs_alloca_next /\ ts.t_mem = tu.t_mem /\
   ts.t_stor = tu.t_stor /\ ts.t_trans = tu.t_trans /\ ts.t_imm = tu.t_imm` by
    (simp_tac bool_ss [Abbr `us`] >>
     qpat_assum `source_raw = update_var _ _ u` (fn th => rewrite_tac[th]) >>
     qpat_assum `ts = tu with t_var := _` (fn th => rewrite_tac[th]) >>
     simp[NoAsms, update_var_def]) >>
  `!mem. mem_agree_outside ts.t_mem us.vs_memory mem ==>
    abi_encoder_window_input ei (EL k ats) (EL k avs)
      (sb + abi_encoder_member_span (TAKE k infos))
      (MIN ms (cap - abi_encoder_member_span (TAKE k infos))) mem` by
    (qpat_assum `Abbrev (source_offset = _)`
       (fn th => pure_rewrite_tac
         [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
     asm_rewrite_tac[]) >>
  suspend "member_source_coverage"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_source_coverage]:
  `0 < MIN ms (cap-source_offset) ==>
    sb+source_offset+MIN ms (cap-source_offset) <= us.vs_alloca_next /\
    ?p. elem_src = Var p /\
      ptr_covers Gs ts p us (MIN ms (cap-source_offset))` by
    (strip_tac >>
     `MIN ms (cap-source_offset) <= cap-source_offset` by simp[NoAsms, MIN_LE] >>
     `0 < cap /\ source_offset < cap /\
       source_offset + MIN ms (cap-source_offset) <= cap` by decide_tac >>
     `sb+cap <= u.vs_alloca_next /\
       ?p. src = Var p /\ ptr_covers Gu tu p u cap` by metis_tac[] >>
     `u.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
     `sb < dimword (:256) /\ sb+source_offset < dimword (:256)` by decide_tac >>
     conj_tac >- (asm_rewrite_tac[] >> decide_tac) >>
     qexists_tac `source_var` >> conj_tac >- first_assum ACCEPT_TAC >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers Gu tu p u cap`, `src = Var p`,
        `eval_operand src u = SOME (n2w sb)`,
        `Abbrev (Gs = _)`, `Abbrev (source_inst = _)`,
        `ts = tu with t_var := _`, `Abbrev (us = _)`,
        `source_raw = update_var _ _ u`,
        `sb < dimword (:256)`, `sb+source_offset < dimword (:256)`,
        `source_offset + MIN ms (cap-source_offset) <= cap`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     gvs[markerTheory.Abbrev_def, ptr_covers_def, eval_operand_def,
       step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, update_var_def, lookup_var_def,
       op_taint_def, FLOOKUP_UPDATE, w2n_n2w, LESS_MOD] >>
     decide_tac) >>
  `allocas_from lo us /\ lo <= us.vs_alloca_next` by
    (conj_tac >-
       (qpat_assum `allocas_from lo u` mp_tac >>
        qpat_assum `us.vs_allocas = u.vs_allocas` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[allocas_from_def]) >>
     asm_rewrite_tac[] >> first_assum ACCEPT_TAC) >>
  `d+encoded_size <= us.vs_alloca_next` by
    (qpat_assum `us.vs_alloca_next = u.vs_alloca_next` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `op_taint ts dst = {}` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`op_taint tu dst = {}`,
        `!x. src = Var x \/ dst = Var x ==> not_fresh_at current x`,
        `!x. not_fresh_at current x ==> lookup_var x us = _ /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `dst` >> simp[op_taint_def] >> metis_tac[]) >>
  `!x. dst = Var x ==> not_fresh_at prepared x` by
    (qpat_assum `!x. src = Var x \/ dst = Var x ==> not_fresh_at current x` mp_tac >>
     qpat_assum `prepared.cs_next_var = current.cs_next_var + 1` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     `current.cs_next_var <= prepared.cs_next_var` by decide_tac >>
     metis_tac[not_fresh_at_mono]) >>
  `0 < encoded_size ==> ?p. dst = Var p /\ ptr_covers Gs ts p us encoded_size` by
    (strip_tac >>
     `?p. dst = Var p /\ ptr_covers Gu tu p u encoded_size` by metis_tac[] >>
     qexists_tac `p` >> conj_tac >- first_assum ACCEPT_TAC >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers Gu tu p u encoded_size`, `dst = Var p`,
        `!x. src = Var x \/ dst = Var x ==> not_fresh_at current x`,
        `!x. not_fresh_at current x ==> lookup_var x us = _ /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     metis_tac[appendStorageGhostPtrTheory.ptr_covers_old_transport]) >>
  Cases_on `dyn` >- suspend "member_dynamic_child" >>
  suspend "member_static_child"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_child]:
  drule_all window_static_child_context >>
  disch_then (qx_choose_then `head` (qx_choose_then `ready` strip_assume_tac)) >>
  `k < LENGTH ats /\ ~is_dynamic (EL k ats)` by
    (conj_tac >- decide_tac >> metis_tac[]) >>
  `SUM (MAP abi_member_head_size (TAKE k ats)) +
     LENGTH (enc (EL k ats) (EL k avs)) <= head_lengths ats 0` by
    (irule window_structural_member_static_bounds >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `head_lengths ats 0 <= encoded_size` by
    (qpat_assum `LIST_REL abi_encoder_structural_valid ats avs` mp_tac >>
     qpat_assum `enc at (ListV avs) = enc (Tuple ats) (ListV avs)` mp_tac >>
     qpat_assum `Abbrev (encoded_size = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     drule window_structural_member_tuple_length >> disch_tac >>
     simp_tac bool_ss [Abbr `encoded_size`] >>
     qpat_assum `enc at (ListV avs) = _` (fn th => rewrite_tac[th]) >>
     decide_tac) >>
  suspend "member_static_prepare"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_prepare]:
  qabbrev_tac `head_offset = SUM (MAP abi_member_head_size (TAKE k ats))` >>
  qabbrev_tac `head_var = STRING #"%" (toString prepared.cs_next_var)` >>
  `eval_operand (Lit (n2w head_offset)) us = SOME (n2w head_offset)` by
    simp[eval_operand_def] >>
  drule_all window_emit_add_pure >>
  disch_then (qx_choose_then `head_raw` strip_assume_tac) >>
  `head = Var head_var /\
   emitted_insts prepared ready =
     [mk_inst prepared.cs_next_id ADD [dst;Lit (n2w head_offset)] [head_var]]` by
    (qpat_assum `emit_op ADD [dst;_] prepared = _` mp_tac >>
     qpat_assum `Abbrev (head_var = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     drule emitted_insts_emit_op >> simp[Abbr `head_var`]) >>
  `head_raw = update_var head_var (n2w (d+head_offset)) us` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`window_pure_seq prepared ready us head_raw`,
        `emitted_insts prepared ready = _`,
        `eval_operand dst us = SOME (n2w d)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     qpat_x_assum `window_pure_seq _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_pure_seq_def, window_seq_def] >> strip_tac >>
     qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     asm_rewrite_tac[] >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, eval_operand_def, word_add_n2w]) >>
  `abi_encode_exec_frame func us head_raw` by
    (irule exprSimAbiEncodeFramedArrayBodyTheory.abi_encode_framed_ordinary_pure_sequence >>
     goal_assum (drule_at Any) >>
     qpat_assum `emitted_insts prepared ready = _` (fn th => rewrite_tac[th]) >>
     simp[mk_inst_def, is_terminator_def, is_alloca_op_def, is_ext_call_op_def]) >>
  qabbrev_tac `head_inst =
    mk_inst prepared.cs_next_id ADD [dst;Lit (n2w head_offset)] [head_var]` >>
  qabbrev_tac `Gh = step_prov PG Gs head_inst head_raw` >>
  qabbrev_tac `th = step_taint head_inst us head_raw ts` >>
  `th = ts with t_var := ts.t_var |+ (head_var,{})` by
    (simp_tac bool_ss [Abbr `th`, Abbr `head_inst`] >>
     irule scalar_add_taint >>
     qpat_assum `head_raw = update_var _ _ us` (fn th => rewrite_tac[th]) >>
     simp[NoAsms, update_var_def]) >>
  suspend "member_head_path"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_head_path]:
  `step_inst_base head_inst us = OK head_raw` by
    (qpat_assum `window_pure_seq prepared ready us head_raw` mp_tac >>
     qpat_assum `emitted_insts prepared ready = _` mp_tac >>
     qpat_assum `Abbrev (head_inst = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[markerTheory.Abbrev_def, window_pure_seq_def, window_seq_def,
       run_inst_seq_def, AllCaseEqs()]) >>
  `!D. ptr_inst_ok D lo 0 ctx func Gs ts head_inst us` by
    (gen_tac >>
     irule (Q.INST [`lo0` |-> `0`] ptr_inst_ok_lower_bound_transport) >>
     simp_tac bool_ss [ZERO_LESS_EQ] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`op_taint ts dst = {}`, `ctx_has_dalloca ctx ==> allocas_below_fmp us`,
        `step_inst_base head_inst us = OK head_raw`,
        `head_raw = update_var _ _ us`, `Abbrev (head_inst = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     gvs[markerTheory.Abbrev_def] >>
     irule append_scalar_inst_check >>
     asm_simp_tac (srw_ss()) [update_var_def] >>
     rpt strip_tac >> gvs[op_taint_def]) >>
  `!D. inst_seq_ptr D lo ctx func PG Gs ts [head_inst] us Gh th` by
    (gen_tac >> pure_rewrite_tac[inst_seq_ptr_def] >>
     qpat_assum `step_inst_base head_inst us = OK head_raw`
       (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, Abbr `Gh`, Abbr `th`,
       step_prov_inst_idx, step_taint_inst_idx_left, step_taint_inst_idx_right] >>
     first_assum MATCH_ACCEPT_TAC) >>
  `ready.cs_current_insts = prepared.cs_current_insts ++ [head_inst] /\
   ready.cs_current_bb = prepared.cs_current_bb` by
    (qpat_assum `emit_op ADD _ prepared = _` mp_tac >>
     qpat_assum `Abbrev (head_inst = _)` mp_tac >>
     qpat_assum `Abbrev (head_var = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def, LET_THM] >>
     rpt strip_tac >> gvs[]) >>
  `?head_bb. lookup_block us.vs_current_bb func.fn_blocks = SOME head_bb /\
    isPREFIX [head_inst] (DROP us.vs_inst_idx head_bb.bb_instructions)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`fn_has_code prepared ready func`, `ready.cs_current_insts = _`,
        `ready.cs_current_bb = _`, `us.vs_current_bb = _`, `us.vs_inst_idx = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rw[fn_has_code_def, IS_PREFIX_APPEND] >>
     rename1 `lookup_block _ _ = SOME head_bb` >>
     qexists_tac `head_bb` >> qpat_x_assum `head_bb.bb_instructions = _` SUBST1_TAC >>
     asm_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (us,Gs,ts) []
    (OK (head_raw with vs_inst_idx := LENGTH ready.cs_current_insts),Gh,th)` by
    (gen_tac >>
     `us.vs_inst_idx + 1 = LENGTH ready.cs_current_insts` by
       (qpat_assum `us.vs_inst_idx = LENGTH prepared.cs_current_insts`
          (fn th => rewrite_tac[th]) >>
        qpat_assum `ready.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
        simp[NoAsms]) >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
       [head_inst]` by
       simp[NoAsms, Abbr `head_inst`, mk_inst_def, is_terminator_def] >>
     `run_inst_seq_mem_ok [head_inst] us` by
       (simp[NoAsms, fragExecMemTheory.run_inst_seq_mem_ok_def,
         Abbr `head_inst`, mk_inst_def,
         unitTransformDefsTheory.inst_mem_below_frontier_def,
         memSafeRunTheory.inst_dload_in_section_def,
         contextCodegenRelTheory.source_memory_read_ranges_def,
         codegenRelTheory.source_memory_write_ranges_def] >>
        CASE_TAC >> simp[NoAsms]) >>
     `run_inst_seq [head_inst] us = OK head_raw` by
       (qpat_assum `step_inst_base head_inst us = OK head_raw`
          (fn th => simp[NoAsms, run_inst_seq_def, th])) >>
     `inst_seq_ptr D lo ctx func PG Gs ts [head_inst] us Gh th` by metis_tac[] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`~us.vs_halted`, `lookup_block us.vs_current_bb func.fn_blocks = SOME head_bb`,
        `isPREFIX [head_inst] (DROP us.vs_inst_idx head_bb.bb_instructions)`,
        `EVERY _ [head_inst]`, `run_inst_seq_mem_ok [head_inst] us`,
        `inst_seq_ptr D lo ctx func PG Gs ts [head_inst] us Gh th`,
        `run_inst_seq [head_inst] us = OK head_raw`,
        `us.vs_inst_idx + 1 = LENGTH ready.cs_current_insts`,
        `Abbrev (head_inst = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     `(ctx_has_dalloca ctx ==>
        !pre i post v. [head_inst] = pre ++ i::post /\
          run_inst_seq pre us = OK v ==> dalloca_no_wrap i v)` by
       simp[NoAsms, Once EQ_SYM_EQ, APPEND_EQ_SING, Abbr `head_inst`, mk_inst_def] >>
     drule_all run_inst_seq_gas_origin_ptr_path >>
     simp_tac (srw_ss()) [Abbr `head_inst`, mk_inst_def] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `window_phase ctx func prepared ready sites [(d,encoded_size)] us
    (head_raw with vs_inst_idx := LENGTH ready.cs_current_insts)` by
    (irule window_pure_seq_phase >> asm_simp_tac bool_ss []) >>
  suspend "member_head_transport"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_head_transport]:
  qabbrev_tac `uh = head_raw with vs_inst_idx := LENGTH ready.cs_current_insts` >>
  `P ctx func explicit prepared ready us uh` by
    (simp_tac bool_ss [Abbr `uh`] >> irule members_payload_pure >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     pure_rewrite_tac[abi_members_straight_code_def] >> disj1_tac >>
     goal_assum (drule_at Any)) >>
  `window_phase ctx func prepared ready sites [(d,encoded_size)] us uh` by
    (qpat_assum `window_phase ctx func prepared ready _ _ us _` mp_tac >>
     simp_tac bool_ss [Abbr `uh`]) >>
  drule window_phase_resources >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  `abi_encode_exec_frame func us uh` by
    (simp_tac bool_ss [Abbr `uh`, abi_encode_exec_frame_inst_idx] >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp uh /\
    uh.vs_alloca_next + pending_alloca_size func uh <= w2n uh.vs_initial_fmp` by
    (qpat_assum `abi_encode_exec_frame func us uh` (fn frame =>
       qpat_assum `alloca_inv uh` (fn inv =>
         qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp us /\ us.vs_alloca_next + pending_alloca_size func us <= w2n us.vs_initial_fmp` (fn bound =>
           ACCEPT_TAC (MATCH_MP window_exec_frame_alloca_budget
             (LIST_CONJ [frame,inv,bound])))))) >>
  `eval_operand dst uh = SOME (n2w d)` by
    (irule window_phase_operand >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >> metis_tac[]) >>
  `!x. not_fresh_at prepared x ==> head_var <> x` by
    (simp[NoAsms, Abbr `head_var`, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  `!x. not_fresh_at prepared x ==>
    lookup_var x uh = lookup_var x us /\
    FLOOKUP Gh x = FLOOKUP Gs x /\
    op_taint th (Var x) = op_taint ts (Var x)` by
    (gen_tac >> strip_tac >>
     `head_var <> x` by metis_tac[] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`head_var <> x`, `head_raw = update_var _ _ us`,
        `Abbrev (uh = _)`, `Abbrev (Gh = _)`, `Abbrev (head_inst = _)`,
        `th = ts with t_var := _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     asm_simp_tac (srw_ss()) [Abbr `uh`, Abbr `Gh`, Abbr `head_inst`,
       scalar_step_old_prov, scalar_step_old_taint, update_var_def,
       lookup_var_def, op_taint_def, FLOOKUP_UPDATE]) >>
  `eval_operand head uh = SOME (n2w (d+head_offset)) /\
   op_taint th head = {}` by
    (qpat_assum `head = Var head_var` (fn th => rewrite_tac[th]) >>
     simp_tac bool_ss [Abbr `uh`] >>
     qpat_assum `head_raw = update_var _ _ us` (fn th => rewrite_tac[th]) >>
     qpat_assum `th = ts with t_var := _` (fn th => rewrite_tac[th]) >>
     simp[NoAsms, eval_operand_def, lookup_var_def,
       update_var_def, op_taint_def, FLOOKUP_UPDATE]) >>
  `uh.vs_memory = us.vs_memory /\ uh.vs_allocas = us.vs_allocas /\
   uh.vs_alloca_next = us.vs_alloca_next /\ th.t_mem = ts.t_mem /\
   th.t_stor = ts.t_stor /\ th.t_trans = ts.t_trans /\ th.t_imm = ts.t_imm` by
    (simp_tac bool_ss [Abbr `uh`] >>
     qpat_assum `head_raw = update_var _ _ us` (fn th => rewrite_tac[th]) >>
     qpat_assum `th = ts with t_var := _` (fn th => rewrite_tac[th]) >>
     simp[NoAsms, update_var_def]) >>
  suspend "member_head_coverage"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_head_coverage]:
  qabbrev_tac `child_size = LENGTH (enc (EL k ats) (EL k avs))` >>
  `head_offset + child_size <= encoded_size` by
    (qpat_assum `head_offset + child_size <= head_lengths ats 0` mp_tac >>
     qpat_assum `head_lengths ats 0 <= encoded_size` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `0 < child_size ==>
    d+head_offset+child_size <= uh.vs_alloca_next /\
    ?p. head = Var p /\ ptr_covers Gh th p uh child_size` by
    (strip_tac >>
     `0 < encoded_size /\ head_offset < encoded_size` by decide_tac >>
     `?p. dst = Var p /\ ptr_covers Gs ts p us encoded_size` by metis_tac[] >>
     `us.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
     `d+encoded_size <= us.vs_alloca_next` by first_assum ACCEPT_TAC >>
     `d < dimword (:256) /\ d+head_offset < dimword (:256)` by decide_tac >>
     conj_tac >- (asm_rewrite_tac[] >> decide_tac) >>
     qexists_tac `head_var` >> conj_tac >- first_assum ACCEPT_TAC >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers Gs ts p us encoded_size`, `dst = Var p`,
        `eval_operand dst us = SOME (n2w d)`,
        `Abbrev (Gh = _)`, `Abbrev (head_inst = _)`,
        `th = ts with t_var := _`, `Abbrev (uh = _)`,
        `head_raw = update_var _ _ us`,
        `d < dimword (:256)`, `d+head_offset < dimword (:256)`,
        `head_offset + child_size <= encoded_size`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     gvs[markerTheory.Abbrev_def, ptr_covers_def, eval_operand_def,
       step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, update_var_def, lookup_var_def,
       op_taint_def, FLOOKUP_UPDATE, w2n_n2w, LESS_MOD] >> decide_tac) >>
  suspend "member_static_call"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_call]:
  `allocas_from lo uh /\ lo <= uh.vs_alloca_next` by
    (conj_tac >-
       (qpat_assum `allocas_from lo us` mp_tac >>
        qpat_assum `uh.vs_allocas = us.vs_allocas` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[allocas_from_def]) >>
     qpat_assum `uh.vs_alloca_next = us.vs_alloca_next` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `eval_operand elem_src uh = SOME (n2w (sb+source_offset))` by
    (irule window_phase_operand >> goal_assum (drule_at Any) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `op_taint th elem_src = {}` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`op_taint ts elem_src = {}`,
        `!x. elem_src = Var x ==> not_fresh_at prepared x`,
        `!x. not_fresh_at prepared x ==> lookup_var x uh = _ /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `elem_src` >> simp[op_taint_def] >> metis_tac[]) >>
  `!x. elem_src = Var x \/ head = Var x ==> not_fresh_at ready x` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. head = Var x ==> not_fresh_at ready x`,
        `!x. elem_src = Var x ==> not_fresh_at prepared x`,
        `prepared.cs_next_var <= ready.cs_next_var`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> metis_tac[not_fresh_at_mono]) >>
  `d+head_offset+child_size <= uh.vs_alloca_next` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`head_offset+child_size <= encoded_size`,
        `d+encoded_size <= us.vs_alloca_next`,
        `uh.vs_alloca_next = us.vs_alloca_next`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!mem. mem_agree_outside th.t_mem uh.vs_memory mem ==>
    abi_encoder_window_input ei (EL k ats) (EL k avs)
      (sb+source_offset) (MIN ms (cap-source_offset)) mem` by
    (qpat_assum `uh.vs_memory = us.vs_memory` (fn th => rewrite_tac[th]) >>
     qpat_assum `th.t_mem = ts.t_mem` (fn th => rewrite_tac[th]) >>
     qpat_assum `Abbrev (source_offset = _)`
       (fn th => pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     first_assum ACCEPT_TAC) >>
  `0 < MIN ms (cap-source_offset) ==>
    ?p. elem_src = Var p /\ ptr_covers Gh th p uh (MIN ms (cap-source_offset))` by
    (strip_tac >>
     qpat_assum `0 < MIN ms (cap-source_offset) ==> _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then strip_assume_tac >>
     qexists_tac `p` >> conj_tac >- first_assum ACCEPT_TAC >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers Gs ts p us (MIN ms (cap-source_offset))`,
        `elem_src = Var p`,
        `!x. elem_src = Var x ==> not_fresh_at prepared x`,
        `!x. not_fresh_at prepared x ==> lookup_var x uh = _ /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     metis_tac[appendStorageGhostPtrTheory.ptr_covers_old_transport]) >>
  `0 < MIN ms (cap-source_offset) ==>
    sb+source_offset+MIN ms (cap-source_offset) <= uh.vs_alloca_next` by
    (strip_tac >>
     qpat_assum `0 < MIN ms (cap-source_offset) ==>
       sb+source_offset+MIN ms (cap-source_offset) <= us.vs_alloca_next /\ _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o CONJUNCT1) >>
     qpat_assum `uh.vs_alloca_next = us.vs_alloca_next` (fn th => rewrite_tac[th]) >>
     simp_tac bool_ss []) >>
  `0 < MIN ms (cap-source_offset) ==>
    regions_disjoint (sb+source_offset,MIN ms (cap-source_offset))
      (d+head_offset,child_size)` by
    (strip_tac >>
     `MIN ms (cap-source_offset) <= cap-source_offset` by simp[NoAsms, MIN_LE] >>
     `0 < cap` by decide_tac >>
     `regions_disjoint (sb,cap) (d,encoded_size)` by
       (qpat_assum `0 < cap ==> sb+cap <= u.vs_alloca_next /\ _` mp_tac >>
        qpat_assum `0 < cap` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`regions_disjoint (sb,cap) (d,encoded_size)`,
        `MIN ms (cap-source_offset) <= cap-source_offset`,
        `0 < MIN ms (cap-source_offset)`,
        `head_offset+child_size <= encoded_size`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
  `0 < MIN ms (cap-source_offset) ==>
    sb+source_offset+MIN ms (cap-source_offset) <= uh.vs_alloca_next /\
    regions_disjoint (sb+source_offset,MIN ms (cap-source_offset))
      (d+head_offset,child_size) /\
    ?p. elem_src = Var p /\ ptr_covers Gh th p uh (MIN ms (cap-source_offset))` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`0 < MIN ms (cap-source_offset) ==>
          sb+source_offset+MIN ms (cap-source_offset) <= uh.vs_alloca_next`,
        `0 < MIN ms (cap-source_offset) ==> regions_disjoint _ _`,
        `0 < MIN ms (cap-source_offset) ==> ?p. elem_src = Var p /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `0 < child_size ==> ?p. head = Var p /\ ptr_covers Gh th p uh child_size` by
    (qpat_assum `0 < child_size ==> d+head_offset+child_size <= uh.vs_alloca_next /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `window_alloca_sites func (frag_ids ready child_end) SUBSET sites` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`st.cs_next_id <= current.cs_next_id`,
        `prepared.cs_next_id = current.cs_next_id+1`,
        `prepared.cs_next_id <= ready.cs_next_id`,
        `child_end.cs_next_id <= end_st.cs_next_id`,
        `end_st.cs_next_id <= en.cs_next_id`, `Abbrev (sites = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     simp_tac bool_ss [Abbr `sites`] >> irule window_alloca_sites_mono >>
     simp[SUBSET_DEF, abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `!id b sz. id IN sites /\ FLOOKUP uh.vs_allocas id = SOME (b,sz) ==>
    sz = 32 /\ (0 < cap ==> regions_disjoint (sb,cap) (b,sz)) /\
    regions_disjoint (d,encoded_size) (b,sz)` by
    (qpat_assum `!id b sz. id IN sites /\ FLOOKUP u.vs_allocas id = _ ==> _` mp_tac >>
     qpat_assum `uh.vs_allocas = us.vs_allocas` mp_tac >>
     qpat_assum `us.vs_allocas = u.vs_allocas` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> asm_rewrite_tac[]) >>
  `!inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready child_end /\
    FLOOKUP uh.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\
    (0 < MIN ms (cap-source_offset) ==>
      regions_disjoint (sb+source_offset,MIN ms (cap-source_offset)) (b,sz)) /\
    regions_disjoint (d+head_offset,child_size) (b,sz)` by
    (rpt gen_tac >> strip_tac >>
     `inst.inst_id IN sites` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`window_alloca_sites func (frag_ids ready child_end) SUBSET sites`,
           `MEM inst (fn_insts func)`, `inst.inst_opcode = ALLOCA`,
           `inst.inst_id IN frag_ids ready child_end`] >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[SUBSET_DEF, window_alloca_sites_def] >> metis_tac[]) >>
     qpat_assum `!id b sz. id IN sites /\ FLOOKUP uh.vs_allocas id = _ ==> sz = 32 /\ _`
       (qspecl_then [`inst.inst_id`, `b`, `sz`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then strip_assume_tac >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (strip_tac >>
         `MIN ms (cap-source_offset) <= cap-source_offset` by simp[NoAsms, MIN_LE] >>
         `0 < cap` by decide_tac >>
         `regions_disjoint (sb,cap) (b,sz)` by
           (qpat_assum `0 < cap ==> regions_disjoint (sb,cap) (b,sz)` mp_tac >>
            qpat_assum `0 < cap` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`regions_disjoint (sb,cap) (b,sz)`,
            `MIN ms (cap-source_offset) <= cap-source_offset`,
            `0 < MIN ms (cap-source_offset)`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
     qpat_assum `regions_disjoint (d,encoded_size) (b,sz)` mp_tac >>
     qpat_assum `head_offset+child_size <= encoded_size` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
  qpat_assum `!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> _`
    (qspecl_then [`ei`, `az`, `ms`, `F`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then
    [`head`, `elem_src`, `ready`, `child_len`, `child_end`, `ctx`, `func`,
     `uh`, `EL k ats`, `EL k avs`, `sb+source_offset`,
     `MIN ms (cap-source_offset)`, `d+head_offset`, `Gh`, `th`,
     `lo`, `explicit`, `PG`] mp_tac) >>
  (impl_tac >- suspend "member_static_pre") >>
  disch_then (qx_choose_then `child_actual`
    (qx_choose_then `Gc` (qx_choose_then `tc` strip_assume_tac))) >>
  suspend "member_static_post"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_pre]:
  qpat_x_assum `!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> _` kall_tac >>
  qpat_x_assum `!k current end_st result u Gu tu dp site slot. _` kall_tac >>
  map_every (fn q => qpat_assum q (fn th =>
    pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]))
    [`Abbrev (head_offset = _)`, `Abbrev (source_offset = _)`,
     `Abbrev (child_size = _)`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_dynamic_child]:
  drule_all abiEncoderChildContextTheory.abi_encoder_dynamic_child_context >>
  disch_then (qx_choose_then `ops` (qx_choose_then `dyn_ready`
    (qx_choose_then `body_len` (qx_choose_then `body_end` strip_assume_tac)))) >>
  `k < LENGTH ats /\ is_dynamic (EL k ats)` by
    (conj_tac >- decide_tac >> metis_tac[]) >>
  `EXISTS (\(_,_,_,flag). flag) infos` by
    (qpat_assum `MEM (ei,az,ms,T) infos` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[EXISTS_MEM] >> strip_tac >> qexists_tac `(ei,az,ms,T)` >> simp[]) >>
  `SUM (MAP abi_member_head_size (TAKE k ats)) + 32 <= head_lengths ats 0 /\
   head_lengths ats 0 +
     LENGTH (FLAT (abi_tuple_tails (TAKE k ats) (TAKE k avs))) +
     LENGTH (enc (EL k ats) (EL k avs)) <=
     LENGTH (enc (Tuple ats) (ListV avs))` by
    (irule window_structural_member_dynamic_bounds >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "member_dynamic_prefix"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_post]:
  `window_phase ctx func ready child_end
    (window_alloca_sites func (frag_ids ready child_end))
    [(d+head_offset,child_size)] uh child_actual` by
    (qpat_assum `window_strong_result ctx func ready child_end child_len
       (EL k ats) (EL k avs) (d+head_offset) uh child_actual` mp_tac >>
     qpat_assum `Abbrev (child_size = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [markerTheory.Abbrev_def, window_strong_result_def,
       abi_encoder_window_result_def, window_phase_def] >> metis_tac[]) >>
  drule window_phase_resources >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  drule window_phase_effect >> strip_tac >>
  `!id r. FLOOKUP uh.vs_allocas id = SOME r ==>
    FLOOKUP child_actual.vs_allocas id = SOME r` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `abi_encoder_registered_effect
       (window_alloca_sites func (frag_ids ready child_end))
       [(d+head_offset,child_size)] uh child_actual` mp_tac >>
     qpat_assum `FLOOKUP uh.vs_allocas id = SOME r` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[abi_encoder_registered_effect_allocated]) >>
  `!id b sz. id IN window_alloca_sites func (frag_ids ready child_end) /\
    FLOOKUP child_actual.vs_allocas id = SOME (b,sz) ==> sz = 32` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `window_strong_result ctx func ready child_end child_len
       (EL k ats) (EL k avs) (d+head_offset) uh child_actual` mp_tac >>
     qpat_assum `id IN window_alloca_sites func (frag_ids ready child_end)` mp_tac >>
     qpat_assum `FLOOKUP child_actual.vs_allocas id = SOME (b,sz)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[window_strong_result_sizes]) >>
  `!id b sz. id IN sites /\ FLOOKUP child_actual.vs_allocas id = SOME (b,sz) ==>
    sz = 32` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`abi_encoder_registered_effect (window_alloca_sites func (frag_ids ready child_end))
          [(d+head_offset,child_size)] uh child_actual`,
        `!id b sz. id IN sites /\ FLOOKUP uh.vs_allocas id = _ ==> sz = 32 /\ _`,
        `!id b sz. id IN window_alloca_sites func (frag_ids ready child_end) /\
          FLOOKUP child_actual.vs_allocas id = _ ==> sz = 32`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     `!id b sz. id IN sites /\ FLOOKUP uh.vs_allocas id = SOME (b,sz) ==> sz = 32` by
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!id b sz. id IN sites /\ _ ==> sz = 32 /\ _`
          (qspecl_then [`id`, `b`, `sz`] mp_tac) >>
        (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then (ACCEPT_TAC o CONJUNCT1)) >>
     mp_tac (Q.INST
       [`R` |-> `sites`, `ids` |-> `window_alloca_sites func (frag_ids ready child_end)`,
        `outs` |-> `[(d+head_offset,child_size)]`, `s` |-> `uh`, `t` |-> `child_actual`]
       window_registered_sizes_transport) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `d+encoded_size <= uh.vs_alloca_next` by
    (qpat_assum `uh.vs_alloca_next = us.vs_alloca_next` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `!id b sz. id IN sites /\ FLOOKUP uh.vs_allocas id = SOME (b,sz) ==>
    regions_disjoint (d,encoded_size) (b,sz)` by
    (qpat_assum `!id b sz. id IN sites /\ FLOOKUP uh.vs_allocas id = _ ==> sz = 32 /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!id b sz. id IN sites /\ FLOOKUP child_actual.vs_allocas id = SOME (b,sz) ==>
    regions_disjoint (d,encoded_size) (b,sz)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`window_alloca_growth uh child_actual`,
        `!id r. FLOOKUP uh.vs_allocas id = SOME r ==> FLOOKUP child_actual.vs_allocas id = SOME r`,
        `d+encoded_size <= uh.vs_alloca_next`,
        `!id b sz. id IN sites /\ FLOOKUP uh.vs_allocas id = _ ==>
          regions_disjoint (d,encoded_size) (b,sz)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     mp_tac (Q.INST [`q` |-> `d`, `n` |-> `encoded_size`, `ids` |-> `sites`,
       `s` |-> `uh`, `t` |-> `child_actual`] window_alloca_growth_protected) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `0 < cap ==> sb+cap <= uh.vs_alloca_next` by
    (strip_tac >>
     qpat_assum `0 < cap ==> sb+cap <= u.vs_alloca_next /\ _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o CONJUNCT1) >>
     qpat_assum `uh.vs_alloca_next = us.vs_alloca_next` (fn th => rewrite_tac[th]) >>
     qpat_assum `us.vs_alloca_next = u.vs_alloca_next` (fn th => rewrite_tac[th]) >>
     simp_tac bool_ss []) >>
  `0 < cap ==> !id b sz. id IN sites /\
    FLOOKUP child_actual.vs_allocas id = SOME (b,sz) ==>
    regions_disjoint (sb,cap) (b,sz)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`window_alloca_growth uh child_actual`,
        `!id r. FLOOKUP uh.vs_allocas id = SOME r ==> FLOOKUP child_actual.vs_allocas id = SOME r`,
        `0 < cap ==> sb+cap <= uh.vs_alloca_next`,
        `!id b sz. id IN sites /\ FLOOKUP uh.vs_allocas id = _ ==> sz = 32 /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     `sb+cap <= uh.vs_alloca_next` by metis_tac[] >>
     `!id b sz. id IN sites /\ FLOOKUP uh.vs_allocas id = SOME (b,sz) ==>
       regions_disjoint (sb,cap) (b,sz)` by
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!id b sz. id IN sites /\ _ ==> sz = 32 /\ _`
          (qspecl_then [`id`, `b`, `sz`] mp_tac) >>
        (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then (fn th => MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 th))) >>
        first_assum ACCEPT_TAC) >>
     mp_tac (Q.INST [`q` |-> `sb`, `n` |-> `cap`, `ids` |-> `sites`,
       `s` |-> `uh`, `t` |-> `child_actual`] window_alloca_growth_protected) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `mem_bytes_at sb cap child_actual.vs_memory = mem_bytes_at sb cap uh.vs_memory` by
    (Cases_on `cap = 0` >-
       (qpat_assum `cap = 0` SUBST_ALL_TAC >>
        simp[NoAsms, valueEncodingDefsTheory.mem_bytes_at_def]) >>
     mp_tac (Q.INST [`p` |-> `sb`, `n` |-> `cap`,
       `ids` |-> `window_alloca_sites func (frag_ids ready child_end)`,
       `outs` |-> `[(d+head_offset,child_size)]`, `s` |-> `uh`, `t` |-> `child_actual`]
       abi_encoder_window_effect_bytes) >>
     (impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >> conj_tac
        >- (`regions_disjoint (sb,cap) (d,encoded_size)` by
              (qpat_assum `0 < cap ==> sb+cap <= u.vs_alloca_next /\ _` mp_tac >>
               (impl_tac >- (qpat_assum `cap <> 0` mp_tac >>
                 POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)) >>
               disch_then (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2)) >>
            map_every (fn pat => qpat_assum pat mp_tac)
              [`regions_disjoint (sb,cap) (d,encoded_size)`,
               `cap <> 0`, `head_offset+child_size <= encoded_size`] >>
            POP_ASSUM_LIST (K ALL_TAC) >>
            simp_tac bool_ss [EVERY_DEF, regions_disjoint_def] >> decide_tac) >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`0 < cap ==> !id b sz. id IN sites /\ _ ==> regions_disjoint (sb,cap) (b,sz)`,
           `window_alloca_sites func (frag_ids ready child_end) SUBSET sites`, `cap <> 0`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [SUBSET_DEF] >>
        metis_tac[NOT_ZERO_LT_ZERO])) >> disch_then ACCEPT_TAC) >>
  suspend "member_static_advance"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_advance]:
  `!i. i < cap ==> (sb+i IN tc.t_mem <=> sb+i IN th.t_mem)` by
    (gen_tac >> strip_tac >>
     `0 < cap` by decide_tac >>
     qpat_assum `!i. (i < d+head_offset \/ d+head_offset+_ <= i) /\ _ ==>
       (i IN tc.t_mem <=> i IN th.t_mem)`
       (qspec_then `sb+i` MATCH_MP_TAC) >> conj_tac
     >- (qpat_assum `Abbrev (child_size = _)`
           (fn th => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
         `regions_disjoint (sb,cap) (d,encoded_size)` by
           (qpat_assum `0 < cap ==> sb+cap <= u.vs_alloca_next /\ _` mp_tac >>
            (impl_tac >- first_assum ACCEPT_TAC) >>
            disch_then (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2)) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`regions_disjoint (sb,cap) (d,encoded_size)`, `i < cap`,
            `head_offset+child_size <= encoded_size`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
     rpt gen_tac >> strip_tac >>
     `id IN sites` by
       (qpat_assum `window_alloca_sites func (frag_ids ready child_end) SUBSET sites` mp_tac >>
        qpat_assum `id IN window_alloca_sites func (frag_ids ready child_end)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [SUBSET_DEF] >> metis_tac[]) >>
     `regions_disjoint (sb,cap) (b,sz)` by
       (qpat_assum `0 < cap ==> !id b sz. id IN sites /\ _ ==> regions_disjoint (sb,cap) (b,sz)` mp_tac >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then (qspecl_then [`id`, `b`, `sz`] mp_tac) >>
        (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
     qpat_assum `regions_disjoint (sb,cap) (b,sz)` mp_tac >>
     qpat_assum `i < cap` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
  `!i. i < cap ==> (sb+i IN tc.t_mem <=> sb+i IN tn.t_mem)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!i. i < cap ==> (sb+i IN tc.t_mem <=> sb+i IN th.t_mem)`,
        `!i. i < cap ==> (sb+i IN tu.t_mem <=> sb+i IN tn.t_mem)`,
        `th.t_mem = ts.t_mem`, `ts.t_mem = tu.t_mem`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `window_member_prefix infos ats avs k d uh.vs_memory` by
    (qpat_assum `uh.vs_memory = us.vs_memory` (fn th => rewrite_tac[th]) >>
     qpat_assum `us.vs_memory = u.vs_memory` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `mem_bytes_at (d+head_offset) child_size child_actual.vs_memory =
    enc (EL k ats) (EL k avs)` by
    (simp_tac bool_ss [Abbr `child_size`] >>
     qpat_assum `window_strong_result ctx func ready child_end child_len
       (EL k ats) (EL k avs) (d+head_offset) uh child_actual`
       (ACCEPT_TAC o CONJUNCT1 o CONJUNCT1 o
         REWRITE_RULE [window_strong_result_def, abi_encoder_window_result_def])) >>
  `k <= LENGTH ats` by decide_tac >>
  `head_bytes k = head_offset` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LIST_REL abi_encoder_structural_valid ats avs`, `k <= LENGTH ats`,
        `Abbrev (head_bytes = _)`, `Abbrev (head_offset = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     simp_tac bool_ss [Abbr `head_bytes`, Abbr `head_offset`] >>
     mp_tac (Q.INST [`hl` |-> `window_member_head_size infos`]
       window_structural_member_prefix_layout) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  `tail_bytes k <= LENGTH (FLAT (abi_tuple_tails ats avs))` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH ats = LENGTH avs`, `k < LENGTH ats`, `Abbrev (tail_bytes = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     simp_tac bool_ss [Abbr `tail_bytes`] >>
     mp_tac (Q.SPECL [`ats`, `avs`, `k`] window_member_tail_bound) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> decide_tac) >>
  `encoded_size = head_lengths ats 0 + LENGTH (FLAT (abi_tuple_tails ats avs))` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LIST_REL abi_encoder_structural_valid ats avs`,
        `enc at (ListV avs) = enc (Tuple ats) (ListV avs)`, `Abbrev (encoded_size = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     simp_tac bool_ss [Abbr `encoded_size`] >>
     qpat_assum `enc at (ListV avs) = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `LIST_REL abi_encoder_structural_valid ats avs`
       (ACCEPT_TAC o MATCH_MP window_structural_member_tuple_length)) >>
  `window_member_head_size infos + tail_bytes k <= encoded_size` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`tail_bytes k <= LENGTH (FLAT (abi_tuple_tails ats avs))`,
        `encoded_size = head_lengths ats 0 + LENGTH (FLAT (abi_tuple_tails ats avs))`,
        `window_member_head_size infos = head_lengths ats 0`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `d + head_bytes k <= uh.vs_alloca_next /\
   d + window_member_tail infos ats avs k <= uh.vs_alloca_next` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`head_bytes k = head_offset`, `head_offset+child_size <= encoded_size`,
        `window_member_head_size infos + tail_bytes k <= encoded_size`,
        `d+encoded_size <= uh.vs_alloca_next`, `Abbrev (tail_bytes = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     full_simp_tac bool_ss [window_member_tail_def, Abbr `tail_bytes`] >>
     decide_tac) >>
  suspend "member_static_prefix_frame"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_prefix_frame]:
  `regions_disjoint (d,head_bytes k) (d+head_offset,child_size)` by
    (qpat_assum `head_bytes k = head_offset` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
  `regions_disjoint (d+window_member_head_size infos,tail_bytes k)
    (d+head_offset,child_size)` by
    (qpat_assum `head_offset+child_size <= head_lengths ats 0` mp_tac >>
     qpat_assum `window_member_head_size infos = head_lengths ats 0` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
  `!id b sz. id IN window_alloca_sites func (frag_ids ready child_end) /\
    FLOOKUP uh.vs_allocas id = SOME (b,sz) ==>
    regions_disjoint (d,head_bytes k) (b,sz) /\
    regions_disjoint (d+window_member_head_size infos,tail_bytes k) (b,sz)` by
    (rpt gen_tac >> strip_tac >>
     `id IN sites` by
       (qpat_assum `window_alloca_sites func (frag_ids ready child_end) SUBSET sites` mp_tac >>
        qpat_assum `id IN window_alloca_sites func (frag_ids ready child_end)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [SUBSET_DEF] >> metis_tac[]) >>
     `regions_disjoint (d,encoded_size) (b,sz)` by
       (qpat_assum `!id b sz. id IN sites /\ FLOOKUP uh.vs_allocas id = _ ==>
          regions_disjoint (d,encoded_size) (b,sz)`
          (qspecl_then [`id`, `b`, `sz`] MATCH_MP_TAC) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`regions_disjoint (d,encoded_size) (b,sz)`, `head_bytes k = head_offset`,
        `head_offset+child_size <= encoded_size`,
        `window_member_head_size infos + tail_bytes k <= encoded_size`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
  `window_member_prefix infos ats avs k d child_actual.vs_memory` by
    (mp_tac (Q.INST
       [`ids` |-> `window_alloca_sites func (frag_ids ready child_end)`,
        `outs` |-> `[(d+head_offset,child_size)]`, `s` |-> `uh`, `t` |-> `child_actual`]
       window_member_prefix_frame) >>
     (impl_tac >-
       (map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac
          [GSYM (BETA_RULE (AP_THM (REWRITE_RULE [markerTheory.Abbrev_def] th) ``k:num``))]))
          [`Abbrev (head_bytes = _)`, `Abbrev (tail_bytes = _)`] >>
        simp_tac bool_ss [EVERY_DEF] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `window_member_prefix infos ats avs (SUC k) d child_actual.vs_memory` by
    (mp_tac (Q.INST [`mem` |-> `child_actual.vs_memory`]
       window_structural_member_prefix_static_step) >>
     (impl_tac >-
       (qpat_assum `Abbrev (head_offset = _)`
          (fn th => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
        qpat_assum `Abbrev (child_size = _)`
          (fn th => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  suspend "member_static_clean_prefix"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_clean_prefix]:
  `abi_encoder_structural_valid (EL k ats) (EL k avs)` by
    (qpat_assum `LIST_REL abi_encoder_structural_valid ats avs` mp_tac >>
     qpat_assum `k < LENGTH ats` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [LIST_REL_EL_EQN] >> metis_tac[]) >>
  `abi_member_head_size (EL k ats) = child_size` by
    (qpat_assum `abi_encoder_structural_valid (EL k ats) (EL k avs)` mp_tac >>
     qpat_assum `~is_dynamic (EL k ats)` mp_tac >>
     qpat_assum `Abbrev (child_size = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     drule abiEncoderOpenInputTheory.abi_encoder_structural_valid_layout >>
     asm_simp_tac (srw_ss()) [abiEncoderOpenInputTheory.abi_encoder_layout_valid_def,
       abiDecodeRangesTheory.abi_member_head_size_def, Abbr `child_size`]) >>
  `SUC k <= LENGTH ats` by decide_tac >>
  `head_bytes (SUC k) = SUM (MAP abi_member_head_size (TAKE (SUC k) ats))` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LIST_REL abi_encoder_structural_valid ats avs`, `SUC k <= LENGTH ats`,
        `Abbrev (head_bytes = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     simp_tac bool_ss [Abbr `head_bytes`] >>
     mp_tac (Q.INST [`hl` |-> `window_member_head_size infos`, `k` |-> `SUC k`]
       window_structural_member_prefix_layout) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  `head_bytes (SUC k) = head_offset+child_size` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`head_bytes (SUC k) = SUM (MAP abi_member_head_size (TAKE (SUC k) ats))`,
        `abi_member_head_size (EL k ats) = child_size`, `k < LENGTH ats`,
        `Abbrev (head_offset = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     asm_simp_tac (srw_ss()) [Abbr `head_offset`, TAKE_SUC, TAKE1_DROP,
       MAP_APPEND, SUM_APPEND]) >>
  `tail_bytes (SUC k) = tail_bytes k` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH ats = LENGTH avs`, `k < LENGTH ats`, `~is_dynamic (EL k ats)`,
        `Abbrev (tail_bytes = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     mp_tac window_member_tail_step >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
     qpat_assum `~is_dynamic (EL k ats)` (fn neg =>
       qpat_x_assum `window_member_tail infos ats avs (SUC k) = _`
         (mp_tac o REWRITE_RULE [neg])) >>
     simp_tac bool_ss [window_member_tail_def, Abbr `tail_bytes`, ADD_CLAUSES] >>
     decide_tac) >>
  suspend "member_static_taint_prefix"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_taint_prefix]:
  `!i. (d <= i /\ i < d+head_bytes k) \/
    (d+window_member_head_size infos <= i /\
     i < d+window_member_head_size infos+tail_bytes k) ==>
    (i IN tc.t_mem <=> i IN th.t_mem)` by
    (gen_tac >> disch_tac >>
     `d <= i /\ i < d+encoded_size` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`(d <= i /\ i < d+head_bytes k) \/ _`, `head_bytes k = head_offset`,
           `head_offset+child_size <= encoded_size`,
           `window_member_head_size infos+tail_bytes k <= encoded_size`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     qpat_assum `!i. (i < d+head_offset \/ d+head_offset+_ <= i) /\ _ ==>
       (i IN tc.t_mem <=> i IN th.t_mem)`
       (qspec_then `i` MATCH_MP_TAC) >> conj_tac
     >- (qpat_assum `Abbrev (child_size = _)`
           (fn th => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`(d <= i /\ i < d+head_bytes k) \/ _`, `head_bytes k = head_offset`,
            `head_offset+child_size <= head_lengths ats 0`,
            `window_member_head_size infos = head_lengths ats 0`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     rpt gen_tac >> strip_tac >>
     `id IN sites` by
       (qpat_assum `window_alloca_sites func (frag_ids ready child_end) SUBSET sites` mp_tac >>
        qpat_assum `id IN window_alloca_sites func (frag_ids ready child_end)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [SUBSET_DEF] >> metis_tac[]) >>
     `regions_disjoint (d,encoded_size) (b,sz)` by
       (qpat_assum `!id b sz. id IN sites /\ FLOOKUP child_actual.vs_allocas id = _ ==>
          regions_disjoint (d,encoded_size) (b,sz)`
          (qspecl_then [`id`, `b`, `sz`] MATCH_MP_TAC) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `regions_disjoint (d,encoded_size) (b,sz)` mp_tac >>
     qpat_assum `d <= i` mp_tac >> qpat_assum `i < d+encoded_size` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
  `!i. (d <= i /\ i < d+head_bytes k) \/
    (d+window_member_head_size infos <= i /\
     i < d+window_member_head_size infos+tail_bytes k) ==> i NOTIN tc.t_mem` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!i. (d <= i /\ i < d+head_bytes k) \/ _ ==> (i IN tc.t_mem <=> i IN th.t_mem)`,
        `!i. (d <= i /\ i < d+head_bytes k) \/ _ ==> i NOTIN tu.t_mem`,
        `th.t_mem = ts.t_mem`, `ts.t_mem = tu.t_mem`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!i. d+head_offset <= i /\ i < d+head_offset+child_size ==> i NOTIN tc.t_mem` by
    (simp_tac bool_ss [Abbr `child_size`] >> first_assum ACCEPT_TAC) >>
  `!i. (d <= i /\ i < d+head_bytes (SUC k)) \/
    (d+window_member_head_size infos <= i /\
     i < d+window_member_head_size infos+tail_bytes (SUC k)) ==>
    ((d <= i /\ i < d+head_bytes k) \/
     (d+window_member_head_size infos <= i /\
      i < d+window_member_head_size infos+tail_bytes k)) \/
    (d+head_offset <= i /\ i < d+head_offset+child_size)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`head_bytes (SUC k) = head_offset+child_size`,
        `tail_bytes (SUC k) = tail_bytes k`, `head_bytes k = head_offset`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!i. (d <= i /\ i < d+head_bytes (SUC k)) \/
    (d+window_member_head_size infos <= i /\
     i < d+window_member_head_size infos+tail_bytes (SUC k)) ==> i NOTIN tc.t_mem` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!i. (d <= i /\ i < d+head_bytes (SUC k)) \/ _ ==> _`,
        `!i. (d <= i /\ i < d+head_bytes k) \/ _ ==> i NOTIN tc.t_mem`,
        `!i. d+head_offset <= i /\ i < d+head_offset+child_size ==> i NOTIN tc.t_mem`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  suspend "member_static_cursor"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_cursor]:
  `current.cs_next_var <= prepared.cs_next_var` by
    (qpat_assum `prepared.cs_next_var = current.cs_next_var+1` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `window_phase ctx func current ready sites [(d,encoded_size)] u uh` by
    (mp_tac (Q.INST [`st` |-> `current`, `mid` |-> `prepared`, `en` |-> `ready`,
       `ids` |-> `sites`, `outs` |-> `[(d,encoded_size)]`,
       `left` |-> `sites`, `right` |-> `sites`,
       `left_out` |-> `[(d,encoded_size)]`, `right_out` |-> `[(d,encoded_size)]`,
       `s` |-> `u`, `t` |-> `us`, `u` |-> `uh`] window_phase_chain) >>
     (impl_tac >- (simp_tac bool_ss [SUBSET_REFL] >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `abi_encode_exec_frame func u uh` by
    (mp_tac (Q.INST [`fn` |-> `func`, `s` |-> `u`, `t` |-> `us`, `u` |-> `uh`]
       abi_encode_exec_frame_trans) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `!x. not_fresh_at current x ==>
    lookup_var x uh = lookup_var x u /\ FLOOKUP Gh x = FLOOKUP Gu x /\
    op_taint th (Var x) = op_taint tu (Var x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. not_fresh_at current x ==> lookup_var x us = _ /\ _`,
        `!x. not_fresh_at prepared x ==> lookup_var x uh = _ /\ _`,
        `prepared.cs_next_var = current.cs_next_var+1`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gen_tac >> strip_tac >>
     `current.cs_next_var <= prepared.cs_next_var` by decide_tac >>
     `not_fresh_at prepared x` by metis_tac[not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at current x ==> _` (qspec_then `x` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
     qpat_assum `!x. not_fresh_at prepared x ==> _` (qspec_then `x` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> metis_tac[]) >>
  suspend "member_static_cursor_state"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_cursor_state]:
  `EXISTS (\(_,_,_,flag). flag) infos ==>
    site IN sites /\ site < child_end.cs_next_id /\
    (?p. dp = Var p /\ not_fresh_at child_end p /\ ptr_covers Gc tc p child_actual 32) /\
    eval_operand dp child_actual = SOME (n2w slot) /\
    FLOOKUP child_actual.vs_allocas site = SOME (slot,32) /\
    slot+32 <= child_actual.vs_alloca_next /\
    mem_word_at slot child_actual.vs_memory = n2w (window_member_tail infos ats avs (SUC k)) /\
    (!i. slot <= i /\ i < slot+32 ==> i NOTIN tc.t_mem)` by
    (strip_tac >>
     qpat_assum `EXISTS (\(_,_,_,flag). flag) infos ==>
       site IN sites /\ site < current.cs_next_id /\ _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then strip_assume_tac >>
     `not_fresh_at ready p` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`not_fresh_at current p`, `current.cs_next_var <= prepared.cs_next_var`,
           `prepared.cs_next_var <= ready.cs_next_var`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
        `current.cs_next_var <= ready.cs_next_var` by decide_tac >>
        metis_tac[not_fresh_at_mono]) >>
     `!x. dp = Var x ==> not_fresh_at current x` by
       (qpat_assum `dp = Var p` (fn th => rewrite_tac[th]) >>
        simp[NoAsms] >> first_assum ACCEPT_TAC) >>
     `!x. dp = Var x ==> not_fresh_at ready x` by
       (qpat_assum `dp = Var p` (fn th => rewrite_tac[th]) >>
        simp[NoAsms] >> first_assum ACCEPT_TAC) >>
     `eval_operand dp uh = SOME (n2w slot)` by
       (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`, `st` |-> `current`,
          `en` |-> `ready`, `ids` |-> `sites`, `outs` |-> `[(d,encoded_size)]`,
          `s` |-> `u`, `t` |-> `uh`, `op` |-> `dp`, `w` |-> `n2w slot`]
          window_phase_operand) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then ACCEPT_TAC) >>
     `eval_operand dp child_actual = SOME (n2w slot)` by
       (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`, `st` |-> `ready`,
          `en` |-> `child_end`, `ids` |-> `window_alloca_sites func (frag_ids ready child_end)`,
          `outs` |-> `[(d+head_offset,child_size)]`, `s` |-> `uh`, `t` |-> `child_actual`,
          `op` |-> `dp`, `w` |-> `n2w slot`] window_phase_operand) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then ACCEPT_TAC) >>
     `FLOOKUP uh.vs_allocas site = SOME (slot,32)` by
       (qpat_assum `uh.vs_allocas = us.vs_allocas` (fn th => rewrite_tac[th]) >>
        qpat_assum `us.vs_allocas = u.vs_allocas` (fn th => rewrite_tac[th]) >>
        first_assum ACCEPT_TAC) >>
     `FLOOKUP child_actual.vs_allocas site = SOME (slot,32)` by
       (qpat_assum `!id r. FLOOKUP uh.vs_allocas id = SOME r ==> _`
          (qspecl_then [`site`, `(slot,32)`] MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
     `slot+32 <= child_actual.vs_alloca_next` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`slot+32 <= u.vs_alloca_next`, `uh.vs_alloca_next = us.vs_alloca_next`,
           `us.vs_alloca_next = u.vs_alloca_next`] >>
        qpat_assum `window_alloca_growth uh child_actual`
          (mp_tac o CONJUNCT1 o REWRITE_RULE [window_alloca_growth_def]) >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     suspend "member_static_cursor_details") >>
  suspend "member_static_root_state"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_cursor_details]:
  `not_fresh_at child_end p` by
    (qpat_assum `not_fresh_at ready p` mp_tac >>
     qpat_assum `ready.cs_next_var <= child_end.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[not_fresh_at_mono]) >>
  `site < child_end.cs_next_id` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`site < current.cs_next_id`, `prepared.cs_next_id = current.cs_next_id+1`,
        `prepared.cs_next_id <= ready.cs_next_id`, `ready.cs_next_id <= child_end.cs_next_id`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `lookup_var p child_actual = lookup_var p u` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`dp = Var p`, `eval_operand dp child_actual = SOME (n2w slot)`,
        `eval_operand dp u = SOME (n2w slot)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gvs[eval_operand_def]) >>
  `FLOOKUP Gc p = FLOOKUP Gu p /\
   op_taint tc (Var p) = op_taint tu (Var p)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. not_fresh_at current x ==> lookup_var x uh = _ /\ _`,
        `!x. not_fresh_at ready x ==> FLOOKUP Gc x = FLOOKUP Gh x /\ _`,
        `not_fresh_at current p`, `not_fresh_at ready p`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `ptr_covers Gc tc p child_actual 32` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers Gu tu p u 32`, `lookup_var p child_actual = lookup_var p u`,
        `FLOOKUP Gc p = FLOOKUP Gu p`, `op_taint tc (Var p) = op_taint tu (Var p)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     full_simp_tac (srw_ss()) [ptr_covers_def]) >>
  `site < ready.cs_next_id` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`site < current.cs_next_id`, `prepared.cs_next_id = current.cs_next_id+1`,
        `prepared.cs_next_id <= ready.cs_next_id`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `site NOTIN window_alloca_sites func (frag_ids ready child_end)` by
    (mp_tac (SPEC ``site:num`` (REWRITE_RULE [SUBSET_DEF]
       (Q.INST [`ids` |-> `frag_ids ready child_end`] window_alloca_sites_subset))) >>
     qpat_assum `site < ready.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  suspend "member_static_cursor_memory"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_cursor_memory]:
  `regions_disjoint (d,encoded_size) (slot,32)` by
    (qpat_assum `!id b sz. id IN sites /\ FLOOKUP uh.vs_allocas id = _ ==>
       regions_disjoint (d,encoded_size) (b,sz)`
       (qspecl_then [`site`, `slot`, `32`] MATCH_MP_TAC) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `regions_disjoint (slot,32) (d+head_offset,child_size)` by
    (qpat_assum `regions_disjoint (d,encoded_size) (slot,32)` mp_tac >>
     qpat_assum `head_offset+child_size <= encoded_size` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at slot 32 child_actual.vs_memory = mem_bytes_at slot 32 uh.vs_memory` by
    (mp_tac (Q.INST
       [`ids` |-> `window_alloca_sites func (frag_ids ready child_end)`,
        `outs` |-> `[(d+head_offset,child_size)]`, `s` |-> `uh`, `t` |-> `child_actual`,
        `parent` |-> `site`, `p` |-> `slot`, `n` |-> `32`]
       abi_encoder_window_effect_parent) >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       simp_tac bool_ss [EVERY_DEF] >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `mem_word_at slot child_actual.vs_memory = mem_word_at slot u.vs_memory` by
    (rewrite_tac[abiStaticAggregatePropsTheory.mem_word_at_bytes] >>
     qpat_assum `mem_bytes_at slot 32 child_actual.vs_memory = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `uh.vs_memory = us.vs_memory` (fn th => rewrite_tac[th]) >>
     qpat_assum `us.vs_memory = u.vs_memory` (fn th => rewrite_tac[th])) >>
  `window_member_tail infos ats avs (SUC k) = window_member_tail infos ats avs k` by
    (qpat_assum `tail_bytes (SUC k) = tail_bytes k`
       (mp_tac o AP_TERM ``\n:num. window_member_head_size infos+n``) >>
     simp_tac bool_ss [window_member_tail_def, Abbr `tail_bytes`]) >>
  `mem_word_at slot child_actual.vs_memory = n2w (window_member_tail infos ats avs (SUC k))` by
    (qpat_assum `mem_word_at slot child_actual.vs_memory = mem_word_at slot u.vs_memory`
       (fn th => rewrite_tac[th]) >>
     qpat_assum `mem_word_at slot u.vs_memory = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `window_member_tail infos ats avs (SUC k) = _` (fn th => rewrite_tac[th])) >>
  `!i. slot <= i /\ i < slot+32 ==> i NOTIN tc.t_mem` by
    (gen_tac >> strip_tac >>
     `i IN tc.t_mem <=> i IN th.t_mem` by
       (qpat_assum `!i. (i < d+head_offset \/ d+head_offset+_ <= i) /\ _ ==>
       (i IN tc.t_mem <=> i IN th.t_mem)`
          (qspec_then `i` MATCH_MP_TAC) >> conj_tac
        >- (qpat_assum `Abbrev (child_size = _)`
              (fn th => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
            qpat_assum `regions_disjoint (slot,32) (d+head_offset,child_size)` mp_tac >>
            qpat_assum `slot <= i` mp_tac >> qpat_assum `i < slot+32` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
        rpt gen_tac >> strip_tac >>
        `site <> id` by
          (qpat_assum `site NOTIN window_alloca_sites func (frag_ids ready child_end)` mp_tac >>
           qpat_assum `id IN window_alloca_sites func (frag_ids ready child_end)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
        `regions_disjoint (slot,32) (b,sz)` by
          (mp_tac (Q.INST [`s` |-> `child_actual`, `id` |-> `site`, `other` |-> `id`,
             `b` |-> `slot`, `sz` |-> `32`, `p` |-> `b`, `n` |-> `sz`]
             allocaSiteResourceTheory.alloca_site_registered_disjoint) >>
           (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
        qpat_assum `regions_disjoint (slot,32) (b,sz)` mp_tac >>
        qpat_assum `slot <= i` mp_tac >> qpat_assum `i < slot+32` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
     `i NOTIN th.t_mem` by
       (qpat_assum `th.t_mem = ts.t_mem` (fn th => rewrite_tac[th]) >>
        qpat_assum `ts.t_mem = tu.t_mem` (fn th => rewrite_tac[th]) >>
        qpat_assum `!i. slot <= i /\ i < slot+32 ==> i NOTIN tu.t_mem`
          (qspec_then `i` MATCH_MP_TAC) >> conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `i IN tc.t_mem <=> i IN th.t_mem` mp_tac >>
     qpat_assum `i NOTIN th.t_mem` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac `p` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_root_state]:
  `lo <= child_actual.vs_alloca_next` by
    (qpat_assum `lo <= uh.vs_alloca_next` mp_tac >>
     qpat_assum `window_alloca_growth uh child_actual`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [window_alloca_growth_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `allocas_from lo child_actual` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`allocas_from lo uh`, `lo <= uh.vs_alloca_next`,
        `!id r. FLOOKUP uh.vs_allocas id = SOME r ==> FLOOKUP child_actual.vs_allocas id = SOME r`,
        `window_alloca_growth uh child_actual`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     qpat_assum `window_alloca_growth uh child_actual`
       (strip_assume_tac o REWRITE_RULE [window_alloca_growth_def]) >>
     simp_tac bool_ss [allocas_from_def] >> rpt gen_tac >> strip_tac >>
     Cases_on `FLOOKUP uh.vs_allocas aid`
     >- (`uh.vs_alloca_next <= b` by
           (qpat_assum `!i b sz. FLOOKUP uh.vs_allocas i = NONE /\ _ ==> _`
              (qspecl_then [`aid`, `b`, `sz`] MATCH_MP_TAC) >>
            conj_tac >> first_assum ACCEPT_TAC) >>
         qpat_assum `uh.vs_alloca_next <= b` mp_tac >>
         qpat_assum `lo <= uh.vs_alloca_next` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     rename1 `FLOOKUP uh.vs_allocas aid = SOME old_slot` >>
     qpat_assum `!id r. FLOOKUP uh.vs_allocas id = SOME r ==> _`
       (qspecl_then [`aid`, `old_slot`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
     gvs[allocas_from_def] >>
     qpat_assum `!aid b sz. FLOOKUP uh.vs_allocas aid = SOME (b,sz) ==> lo <= b`
       (qspecl_then [`aid`, `b`, `sz`] MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
  `!id b sz. id IN sites /\ FLOOKUP child_actual.vs_allocas id = SOME (b,sz) ==>
    sz = 32 /\ (0 < cap ==> regions_disjoint (sb,cap) (b,sz)) /\
    regions_disjoint (d,encoded_size) (b,sz)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!id b sz. id IN sites /\ FLOOKUP child_actual.vs_allocas id = _ ==> sz = 32`,
        `0 < cap ==> !id b sz. id IN sites /\ _ ==> regions_disjoint (sb,cap) (b,sz)`,
        `!id b sz. id IN sites /\ FLOOKUP child_actual.vs_allocas id = _ ==>
          regions_disjoint (d,encoded_size) (b,sz)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `mem_bytes_at sb cap child_actual.vs_memory = mem_bytes_at sb cap s.vs_memory` by
    (qpat_assum `mem_bytes_at sb cap child_actual.vs_memory = mem_bytes_at sb cap uh.vs_memory`
       (fn th => rewrite_tac[th]) >>
     qpat_assum `uh.vs_memory = us.vs_memory` (fn th => rewrite_tac[th]) >>
     qpat_assum `us.vs_memory = u.vs_memory` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  suspend "member_static_root_operands"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_root_operands]:
  `current.cs_next_var <= ready.cs_next_var` by
    (qpat_assum `current.cs_next_var <= prepared.cs_next_var` mp_tac >>
     qpat_assum `prepared.cs_next_var <= ready.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at ready x` by
    (qpat_assum `!x. src = Var x \/ dst = Var x ==> not_fresh_at current x` mp_tac >>
     qpat_assum `current.cs_next_var <= ready.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[not_fresh_at_mono]) >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at child_end x` by
    (qpat_assum `!x. src = Var x \/ dst = Var x ==> not_fresh_at ready x` mp_tac >>
     qpat_assum `ready.cs_next_var <= child_end.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[not_fresh_at_mono]) >>
  `eval_operand src uh = SOME (n2w sb)` by
    (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`, `st` |-> `current`,
       `en` |-> `ready`, `ids` |-> `sites`, `outs` |-> `[(d,encoded_size)]`,
       `s` |-> `u`, `t` |-> `uh`, `op` |-> `src`, `w` |-> `n2w sb`] window_phase_operand) >>
     (impl_tac >-
       (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gen_tac >> strip_tac >>
        qpat_assum `!x. src = Var x \/ dst = Var x ==> not_fresh_at current x`
          (qspec_then `x` MATCH_MP_TAC) >> disj1_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `eval_operand src child_actual = SOME (n2w sb)` by
    (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`, `st` |-> `ready`,
       `en` |-> `child_end`, `ids` |-> `window_alloca_sites func (frag_ids ready child_end)`,
       `outs` |-> `[(d+head_offset,child_size)]`, `s` |-> `uh`, `t` |-> `child_actual`,
       `op` |-> `src`, `w` |-> `n2w sb`] window_phase_operand) >>
     (impl_tac >-
       (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gen_tac >> strip_tac >>
        qpat_assum `!x. src = Var x \/ dst = Var x ==> not_fresh_at ready x`
          (qspec_then `x` MATCH_MP_TAC) >> disj1_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `eval_operand dst child_actual = SOME (n2w d)` by
    (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`, `st` |-> `ready`,
       `en` |-> `child_end`, `ids` |-> `window_alloca_sites func (frag_ids ready child_end)`,
       `outs` |-> `[(d+head_offset,child_size)]`, `s` |-> `uh`, `t` |-> `child_actual`,
       `op` |-> `dst`, `w` |-> `n2w d`] window_phase_operand) >>
     (impl_tac >-
       (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gen_tac >> strip_tac >>
        qpat_assum `!x. src = Var x \/ dst = Var x ==> not_fresh_at ready x`
          (qspec_then `x` MATCH_MP_TAC) >> disj2_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `!x. not_fresh_at current x ==> FLOOKUP Gc x = FLOOKUP Gu x /\
    op_taint tc (Var x) = op_taint tu (Var x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. not_fresh_at current x ==> lookup_var x uh = _ /\ _`,
        `!x. not_fresh_at ready x ==> FLOOKUP Gc x = FLOOKUP Gh x /\ _`,
        `current.cs_next_var <= ready.cs_next_var`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gen_tac >> strip_tac >>
     `not_fresh_at ready x` by metis_tac[not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at current x ==> _` (qspec_then `x` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
     qpat_assum `!x. not_fresh_at ready x ==> _` (qspec_then `x` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> metis_tac[]) >>
  `op_taint tc src = {} /\ op_taint tc dst = {}` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. not_fresh_at current x ==> FLOOKUP Gc x = FLOOKUP Gu x /\ _`,
        `!x. src = Var x \/ dst = Var x ==> not_fresh_at current x`,
        `op_taint tu src = {}`, `op_taint tu dst = {}`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> conj_tac
     >- (Cases_on `src` >> simp[op_taint_def] >> metis_tac[]) >>
     Cases_on `dst` >> simp[op_taint_def] >> metis_tac[]) >>
  suspend "member_static_root_pointers"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_root_pointers]:
  `d+encoded_size <= child_actual.vs_alloca_next` by
    (qpat_assum `d+encoded_size <= uh.vs_alloca_next` mp_tac >>
     qpat_assum `window_alloca_growth uh child_actual`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [window_alloca_growth_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `0 < cap ==> sb+cap <= child_actual.vs_alloca_next /\
    regions_disjoint (sb,cap) (d,encoded_size) /\
    ?p. src = Var p /\ ptr_covers Gc tc p child_actual cap` by
    (strip_tac >>
     qpat_assum `0 < cap ==> sb+cap <= u.vs_alloca_next /\ _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then strip_assume_tac >>
     `not_fresh_at current p` by
       (qpat_assum `!x. src = Var x \/ dst = Var x ==> not_fresh_at current x`
          (qspec_then `p` MATCH_MP_TAC) >> disj1_tac >> first_assum ACCEPT_TAC) >>
     `lookup_var p child_actual = lookup_var p u` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`src = Var p`, `eval_operand src child_actual = SOME (n2w sb)`,
           `eval_operand src u = SOME (n2w sb)`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gvs[eval_operand_def]) >>
     `FLOOKUP Gc p = FLOOKUP Gu p /\ op_taint tc (Var p) = op_taint tu (Var p)` by
       (qpat_assum `!x. not_fresh_at current x ==> FLOOKUP Gc x = FLOOKUP Gu x /\ _`
          (qspec_then `p` MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
     `ptr_covers Gc tc p child_actual cap` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`ptr_covers Gu tu p u cap`, `lookup_var p child_actual = lookup_var p u`,
           `FLOOKUP Gc p = FLOOKUP Gu p`, `op_taint tc (Var p) = op_taint tu (Var p)`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> full_simp_tac (srw_ss()) [ptr_covers_def]) >>
     `sb+cap <= uh.vs_alloca_next` by
       (qpat_assum `0 < cap ==> sb+cap <= uh.vs_alloca_next` MATCH_MP_TAC >> first_assum ACCEPT_TAC) >>
     `sb+cap <= child_actual.vs_alloca_next` by
       (qpat_assum `sb+cap <= uh.vs_alloca_next` mp_tac >>
        qpat_assum `window_alloca_growth uh child_actual`
          (mp_tac o CONJUNCT1 o REWRITE_RULE [window_alloca_growth_def]) >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexists_tac `p` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `0 < encoded_size ==> ?p. dst = Var p /\ ptr_covers Gc tc p child_actual encoded_size` by
    (strip_tac >>
     qpat_assum `0 < encoded_size ==> ?p. dst = Var p /\ ptr_covers Gu tu p u encoded_size` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then strip_assume_tac >>
     `not_fresh_at current p` by
       (qpat_assum `!x. src = Var x \/ dst = Var x ==> not_fresh_at current x`
          (qspec_then `p` MATCH_MP_TAC) >> disj2_tac >> first_assum ACCEPT_TAC) >>
     `lookup_var p child_actual = lookup_var p u` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`dst = Var p`, `eval_operand dst child_actual = SOME (n2w d)`,
           `eval_operand dst u = SOME (n2w d)`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gvs[eval_operand_def]) >>
     `FLOOKUP Gc p = FLOOKUP Gu p /\ op_taint tc (Var p) = op_taint tu (Var p)` by
       (qpat_assum `!x. not_fresh_at current x ==> FLOOKUP Gc x = FLOOKUP Gu x /\ _`
          (qspec_then `p` MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
     `ptr_covers Gc tc p child_actual encoded_size` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`ptr_covers Gu tu p u encoded_size`, `lookup_var p child_actual = lookup_var p u`,
           `FLOOKUP Gc p = FLOOKUP Gu p`, `op_taint tc (Var p) = op_taint tu (Var p)`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> full_simp_tac (srw_ss()) [ptr_covers_def]) >>
     qexists_tac `p` >> conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "member_static_tail"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_static_tail]:
  `abi_encoder_member_span (TAKE (SUC k) infos) = source_offset+ms /\
   SUM (MAP abi_member_head_size (TAKE (SUC k) ats)) = head_offset+az` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`k < LENGTH infos`, `k < LENGTH ats`,
        `EL k infos = (ei,az,ms,F)`,
        `az = abi_member_head_size (EL k ats)`,
        `Abbrev (source_offset = _)`, `Abbrev (head_offset = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     asm_simp_tac (srw_ss()) [Abbr `source_offset`,Abbr `head_offset`,
       TAKE_SUC,TAKE1_DROP,abi_encoder_member_span_def,SUM_APPEND]) >>
  `current.cs_next_var <= child_end.cs_next_var /\
   current.cs_next_id <= child_end.cs_next_id` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`prepared.cs_next_var = current.cs_next_var+1`,
        `prepared.cs_next_id = current.cs_next_id+1`,
        `prepared.cs_next_var <= child_end.cs_next_var`,
        `prepared.cs_next_id <= child_end.cs_next_id`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!x. not_fresh_at current x ==> not_fresh_at child_end x` by
    (qpat_assum `current.cs_next_var <= child_end.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[not_fresh_at_mono]) >>
  `current.cs_next_var <= ready.cs_next_var` by
    (qpat_assum `current.cs_next_var <= prepared.cs_next_var` mp_tac >>
     qpat_assum `prepared.cs_next_var <= ready.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp child_actual /\
    child_actual.vs_alloca_next + pending_alloca_size func child_actual <= w2n child_actual.vs_initial_fmp` by
    (qpat_assum `abi_encode_exec_frame func uh child_actual` (fn frame =>
       qpat_assum `alloca_inv child_actual` (fn inv =>
         qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp uh /\ uh.vs_alloca_next + pending_alloca_size func uh <= w2n uh.vs_initial_fmp` (fn bound =>
           ACCEPT_TAC (MATCH_MP window_exec_frame_alloca_budget
             (LIST_CONJ [frame,inv,bound])))))) >>
  qpat_x_assum `!k current end_st result u Gu tu dp site slot. _`
    (qspecl_then [`SUC k`,`child_end`,`end_st`,`result`,
      `child_actual`,`Gc`,`tc`,`dp`,`site`,`slot`] mp_tac) >>
  impl_tac
  >- (map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac[th]))
         [`DROP (SUC k) infos = rest`,
          `abi_encoder_member_span (TAKE (SUC k) infos) = source_offset+ms`,
          `SUM (MAP abi_member_head_size (TAKE (SUC k) ats)) = head_offset+az`] >>
      (* Before this simplification, the compiler equation is rewritten
         using the two offset equalities above and DROP(SUC k)infos=rest.
         No search is run on the recursive IH: qpat_x_assum consumed it. *)
      rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
        (map_every (fn pat => qpat_assum pat mp_tac)
           [`st.cs_next_var <= current.cs_next_var`,
            `st.cs_next_id <= current.cs_next_id`,
            `current.cs_next_var <= child_end.cs_next_var`,
            `current.cs_next_id <= child_end.cs_next_id`,
            `k < LENGTH infos`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)]) >>
  disch_then (qx_choose_then `tail_actual` (qx_choose_then `Gf`
    (qx_choose_then `tf` strip_assume_tac))) >>
  `window_phase ctx func current child_end sites [(d,encoded_size)]
    u child_actual` by
    (mp_tac (Q.INST
       [`st` |-> `current`,`mid` |-> `ready`,`en` |-> `child_end`,
        `left` |-> `sites`,
        `right` |-> `window_alloca_sites func (frag_ids ready child_end)`,
        `left_out` |-> `[(d,encoded_size)]`,
        `right_out` |-> `[(d+head_offset,child_size)]`,
        `ids` |-> `sites`,`outs` |-> `[(d,encoded_size)]`,
        `s` |-> `u`,`t` |-> `uh`,`u` |-> `child_actual`]
       window_phase_chain) >>
     (impl_tac >-
       (simp_tac (srw_ss()) [SUBSET_REFL,EVERY_DEF] >>
        rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
          (qpat_assum `head_offset+child_size <= encoded_size` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> decide_tac)])) >>
     disch_then ACCEPT_TAC) >>
  `window_phase ctx func current end_st sites [(d,encoded_size)]
    u tail_actual` by
    (mp_tac (Q.INST
       [`st` |-> `current`,`mid` |-> `child_end`,`en` |-> `end_st`,
        `left` |-> `sites`,`right` |-> `sites`,
        `left_out` |-> `[(d,encoded_size)]`,
        `right_out` |-> `[(d,encoded_size)]`,
        `ids` |-> `sites`,`outs` |-> `[(d,encoded_size)]`,
        `s` |-> `u`,`t` |-> `child_actual`,`u` |-> `tail_actual`]
       window_phase_chain) >>
     (impl_tac >- (simp_tac bool_ss [SUBSET_REFL] >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `abi_encode_exec_frame func u tail_actual` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `uh` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule abi_encode_exec_frame_trans >> qexists_tac `child_actual` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!id r. FLOOKUP child_actual.vs_allocas id = SOME r ==>
    FLOOKUP tail_actual.vs_allocas id = SOME r` by
    (qpat_assum `window_phase ctx func child_end end_st sites _
       child_actual tail_actual` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_phase_def,abi_encoder_registered_effect_def]) >>
  `!x. not_fresh_at current x ==>
    FLOOKUP Gf x = FLOOKUP Gu x /\
    op_taint tf (Var x) = op_taint tu (Var x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. not_fresh_at current x ==> not_fresh_at child_end x`,
        `!x. not_fresh_at child_end x ==> FLOOKUP Gf x = _ /\ _`,
        `!x. not_fresh_at ready x ==> FLOOKUP Gc x = _ /\ _`,
        `!x. not_fresh_at current x ==> lookup_var x uh = _ /\ _`,
        `current.cs_next_var <= prepared.cs_next_var`,
        `prepared.cs_next_var <= ready.cs_next_var`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gen_tac >> strip_tac >>
     `not_fresh_at child_end x` by metis_tac[] >>
     `not_fresh_at ready x` by metis_tac[not_fresh_at_mono,LESS_EQ_TRANS] >>
     qpat_assum `!x. not_fresh_at child_end x ==> _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at ready x ==> _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at current x ==> _`
       (qspec_then `x` mp_tac) >> asm_rewrite_tac[] >> metis_tac[]) >>
  `!i. (i<d \/ d+encoded_size<=i) /\
    (!id b sz. id IN sites /\
      FLOOKUP tail_actual.vs_allocas id = SOME (b,sz) ==>
      i<b \/ b+sz<=i) ==> (i IN tf.t_mem <=> i IN tu.t_mem)` by
    (gen_tac >> disch_then (fn th =>
       ASSUME_TAC (CONJUNCT1 th) >> ASSUME_TAC (CONJUNCT2 th)) >>
     `i IN tf.t_mem <=> i IN tc.t_mem` by
       (qpat_assum `!i. _ ==> (i IN tf.t_mem <=> i IN tc.t_mem)`
          (qspec_then `i` MATCH_MP_TAC) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     SUBGOAL_THEN ``i<d+head_offset \/ d+head_offset+child_size<=i`` ASSUME_TAC
     >- (qpat_assum `i<d \/ d+encoded_size<=i` mp_tac >>
        qpat_assum `head_offset+child_size<=encoded_size` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     `!id b sz. id IN window_alloca_sites func (frag_ids ready child_end) /\
       FLOOKUP child_actual.vs_allocas id = SOME (b,sz) ==>
       i<b \/ b+sz<=i` by
       (rpt gen_tac >> strip_tac >>
        `id IN sites` by
          (qpat_assum `window_alloca_sites func (frag_ids ready child_end)
             SUBSET sites` mp_tac >>
           qpat_assum `id IN window_alloca_sites func (frag_ids ready child_end)`
             mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [SUBSET_DEF] >> metis_tac[]) >>
        `FLOOKUP tail_actual.vs_allocas id = SOME (b,sz)` by
          (qpat_assum `!id r. FLOOKUP child_actual.vs_allocas id = _ ==> _`
             (qspecl_then [`id`,`(b,sz)`] MATCH_MP_TAC) >>
           first_assum ACCEPT_TAC) >>
        qpat_assum `!id b sz. id IN sites /\
          FLOOKUP tail_actual.vs_allocas id = _ ==> _`
          (qspecl_then [`id`,`b`,`sz`] MATCH_MP_TAC) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     `i IN tc.t_mem <=> i IN th.t_mem` by
       (qpat_assum `!i. (i < d+head_offset \/ d+head_offset+_ <= i) /\ _ ==>
          (i IN tc.t_mem <=> i IN th.t_mem)`
          (qspec_then `i` MATCH_MP_TAC) >>
        qpat_assum `Abbrev (child_size = _)`
          (fn th => pure_rewrite_tac
            [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`i IN tf.t_mem <=> i IN tc.t_mem`,
        `i IN tc.t_mem <=> i IN th.t_mem`,
        `th.t_mem=ts.t_mem`,`ts.t_mem=tu.t_mem`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
  `tf.t_stor=tu.t_stor /\ tf.t_trans=tu.t_trans /\ tf.t_imm=tu.t_imm` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`tf.t_stor=tc.t_stor`,`tc.t_stor=th.t_stor`,`th.t_stor=ts.t_stor`,
        `ts.t_stor=tu.t_stor`,
        `tf.t_trans=tc.t_trans`,`tc.t_trans=th.t_trans`,`th.t_trans=ts.t_trans`,
        `ts.t_trans=tu.t_trans`,
        `tf.t_imm=tc.t_imm`,`tc.t_imm=th.t_imm`,`th.t_imm=ts.t_imm`,
        `ts.t_imm=tu.t_imm`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (u,Gu,tu) [] (OK tail_actual,Gf,tf)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tu) [] (OK us,Gs,ts)`
       (qspec_then `D` mp_tac) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`us`,`Gs`,`ts`,`[]`,`OK uh`,`Gh`,`th`] mp_tac) >>
     (impl_tac >- (conj_tac >- REFL_TAC >>
       qpat_assum `!D. gas_origin_ptr_path _ (us,Gs,ts) [] (OK uh,Gh,th)`
         (qspec_then `D` ACCEPT_TAC))) >>
     simp_tac bool_ss [APPEND] >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then
       [`uh`,`Gh`,`th`,`[]`,`OK child_actual`,`Gc`,`tc`] mp_tac) >>
     (impl_tac >- (conj_tac >- REFL_TAC >>
       qpat_assum `!D. gas_origin_ptr_path _ (uh,Gh,th) [] (OK child_actual,Gc,tc)`
         (qspec_then `D` ACCEPT_TAC))) >>
     simp_tac bool_ss [APPEND] >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then
       [`child_actual`,`Gc`,`tc`,`[]`,`OK tail_actual`,`Gf`,`tf`] mp_tac) >>
     (impl_tac >- (conj_tac >- REFL_TAC >>
       qpat_assum `!D. gas_origin_ptr_path _ (child_actual,Gc,tc) []
         (OK tail_actual,Gf,tf)` (qspec_then `D` ACCEPT_TAC))) >>
     simp_tac bool_ss [APPEND]) >>
  `P ctx func explicit current ready u uh` by
    (irule members_payload_comp >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`prepared`,`us`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  `P ctx func explicit current child_end u child_actual` by
    (irule members_payload_comp >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`ready`,`uh`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  `P ctx func explicit current end_st u tail_actual` by
    (irule members_payload_comp >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`child_end`,`child_actual`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`tail_actual`,`Gf`,`tf`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[parent_assembly]:
  `!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
    sz = 32 /\ (0 < cap ==> regions_disjoint (sb,cap) (b,sz)) /\
    regions_disjoint (d,encoded_size) (b,sz)` by
    (rpt gen_tac >> strip_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`!inst b sz. MEM inst (fn_insts func) /\ _ ==> _`,
        `id IN sites`, `FLOOKUP s.vs_allocas id = SOME (b,sz)`,
        `Abbrev (sites = _)`, `Abbrev (encoded_size = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     qpat_x_assum `id IN sites` mp_tac >>
     simp_tac (srw_ss()) [Abbr `sites`, window_alloca_sites_def] >>
     strip_tac >>
     qpat_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> _`
       (qspecl_then [`inst`, `b`, `sz`] mp_tac) >>
     metis_tac[]) >>
  drule_all window_complex_dynamic_layout >> strip_tac >>
  Cases_on `EXISTS (\(_,_,_,dyn). dyn) infos`
  >- suspend "parent_dynamic"
  >> drule_all abi_encoder_complex_static_trace >> strip_tac >>
  `window_member_prefix infos ats avs 0 d s.vs_memory` by
    (irule window_member_prefix_zero >> conj_tac >> first_assum ACCEPT_TAC) >>
  `head_bytes 0 = 0 /\ tail_bytes 0 = 0` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`Abbrev (head_bytes = _)`, `Abbrev (tail_bytes = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     simp[Abbr `head_bytes`, Abbr `tail_bytes`, TAKE_0,
       abi_tuple_heads_def, abi_tuple_tails_def]) >>
  qpat_assum `!remaining k current end_st result u Gu tu dp site slot. _`
    (qspecl_then [`infos`, `0`, `st`, `en`, `ignored`,
      `s`, `G`, `tn`, `Lit 0w`, `0`, `0`] mp_tac) >>
  impl_tac
  >- (map_every (fn pat => qpat_assum pat mp_tac)
       [`compile_abi_encode_complex_elems dst src infos 0 0 (Lit 0w) st = (ignored,en)`,
        `fn_has_code st en func`, `alloca_inv s`, `alloca_room ctx func s`,
        `ctx_has_dalloca ctx ==> allocas_below_fmp s /\ s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp`,
        `allocas_from lo s`, `lo <= s.vs_alloca_next`,
        `~s.vs_halted`, `s.vs_current_bb = st.cs_current_bb`,
        `s.vs_inst_idx = LENGTH st.cs_current_insts`,
        `eval_operand src s = SOME (n2w sb)`,
        `eval_operand dst s = SOME (n2w d)`,
        `op_taint tn src = {}`, `op_taint tn dst = {}`,
        `!x. src = Var x \/ dst = Var x ==> not_fresh_at st x`,
        `0 < cap ==> _`, `d + encoded_size <= s.vs_alloca_next`,
        `0 < encoded_size ==> _`,
        `!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = _ ==> _`,
        `LENGTH infos = LENGTH ats`, `LENGTH ats = LENGTH avs`,
        `~EXISTS (\(_,_,_,dyn). dyn) infos`,
        `window_member_prefix infos ats avs 0 d s.vs_memory`,
        `head_bytes 0 = 0`, `tail_bytes 0 = 0`] >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
      simp_tac (srw_ss()) [DROP_0, TAKE_0, abi_encoder_member_span_def] >>
      asm_rewrite_tac[] >>
      rpt strip_tac >> fs[]) >>
  disch_then (qx_choose_then `t`
    (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac))) >>
  qpat_x_assum `!remaining k current end_st result u Gu tu dp site slot. _` kall_tac >>
  qpat_x_assum `!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> _` kall_tac >>
  `mem_bytes_at d encoded_size t.vs_memory = enc at (ListV avs)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`window_member_prefix infos ats avs (LENGTH infos) d t.vs_memory`,
        `LIST_REL abi_encoder_structural_valid ats avs`,
        `window_member_head_size infos = head_lengths ats 0`,
        `enc at (ListV avs) = enc (Tuple ats) (ListV avs)`,
        `Abbrev (encoded_size = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     drule_all window_structural_member_prefix_complete >>
     qpat_assum `Abbrev (encoded_size = _)`
       (fn th => pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     qpat_assum `enc at (ListV avs) = enc (Tuple ats) (ListV avs)`
       (fn th => pure_rewrite_tac [th]) >> disch_then ACCEPT_TAC) >>
  `LIST_REL abi_encoder_layout_valid ats avs` by
    (qpat_assum `LIST_REL abi_encoder_structural_valid ats avs`
       (ACCEPT_TAC o MATCH_MP abiEncoderOpenInputTheory.abi_encoder_structural_list_layout)) >>
  `SUM (MAP2 abi_member_tail_size ats avs) = 0` by
    (qpat_assum `EXISTS (\(_,_,_,dyn). dyn) infos <=> any_dynamic ats` mp_tac >>
     qpat_assum `~EXISTS (\(_,_,_,dyn). dyn) infos` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     irule abiEncoderComplexDynamicTheory.abi_encoder_static_tuple_tails >>
     metis_tac[]) >>
  `encoded_size = window_member_head_size infos` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LIST_REL abi_encoder_layout_valid ats avs`,
        `SUM (MAP2 abi_member_tail_size ats avs) = 0`,
        `enc at (ListV avs) = enc (Tuple ats) (ListV avs)`,
        `window_member_head_size infos = head_lengths ats 0`,
        `Abbrev (encoded_size = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     drule abiEncoderOpenInputTheory.abi_encoder_open_tuple_length >> disch_tac >>
     qpat_assum `Abbrev (encoded_size = _)`
       (fn th => pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     qpat_assum `enc at (ListV avs) = enc (Tuple ats) (ListV avs)`
       (fn th => pure_rewrite_tac [th]) >>
     qpat_assum `window_member_head_size infos = head_lengths ats 0`
       (fn th => pure_rewrite_tac [th, abiDecodeRangesTheory.head_lengths_acc, ADD_CLAUSES]) >>
     qpat_assum `LENGTH (enc (Tuple ats) (ListV avs)) = _`
       (fn th => pure_rewrite_tac [th]) >>
     qpat_assum `SUM (MAP2 abi_member_tail_size ats avs) = 0`
       (fn th => rewrite_tac [th, ADD_CLAUSES])) >>
  `eval_operand out t = SOME (n2w encoded_size)` by
    (qpat_assum `out = Lit _` mp_tac >>
     qpat_assum `encoded_size = window_member_head_size infos` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     asm_simp_tac bool_ss [window_member_head_size_def, eval_operand_def]) >>
  qexistsl_tac [`t`, `Gf`, `tf`] >>
  conj_tac
  >- (map_every (fn pat => qpat_assum pat mp_tac)
       [`window_phase ctx func st en sites [(d,encoded_size)] s t`,
        `mem_bytes_at d encoded_size t.vs_memory = enc at (ListV avs)`,
        `eval_operand out t = SOME (n2w encoded_size)`,
        `!id b sz. id IN sites /\ FLOOKUP t.vs_allocas id = _ ==> _`,
        `Abbrev (encoded_size = _)`, `Abbrev (sites = _)`] >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
      irule window_complex_phase_result >>
      map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac
        [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]))
        [`Abbrev (encoded_size = _)`, `Abbrev (sites = _)`] >>
      asm_rewrite_tac[] >> metis_tac[]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`abi_encode_exec_frame func s t`,
     `!i. d <= i /\ i < d+encoded_size ==> i NOTIN tf.t_mem`,
     `!x. not_fresh_at st x ==> FLOOKUP Gf x = _ /\ _`,
     `!i. (i < d \/ d+encoded_size <= i) /\ _ ==>
       (i IN tf.t_mem <=> i IN tn.t_mem)`,
     `tf.t_stor = tn.t_stor`, `tf.t_trans = tn.t_trans`, `tf.t_imm = tn.t_imm`,
     `P ctx func explicit st en s t`,
     `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,Gf,tf)`, `out = Lit _`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  asm_rewrite_tac[] >>
  qpat_assum `out = Lit _` (fn th => pure_rewrite_tac [th]) >>
  simp_tac (srw_ss()) [op_taint_def]
QED

(* The empty registered effect and execution frame fix the frontier. *)

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_dynamic_prefix]:
  qabbrev_tac `head_offset=SUM (MAP abi_member_head_size (TAKE k ats))` >>
  qabbrev_tac `tail_offset=window_member_tail infos ats avs k` >>
  qabbrev_tac `child_size=LENGTH (enc (EL k ats) (EL k avs))` >>
  `window_member_head_size infos <= encoded_size` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LIST_REL abi_encoder_structural_valid ats avs`,
        `window_member_head_size infos=head_lengths ats 0`,
        `enc at (ListV avs)=enc (Tuple ats) (ListV avs)`,
        `Abbrev (encoded_size = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     drule window_structural_member_tuple_length >>
     asm_simp_tac bool_ss [Abbr `encoded_size`] >> decide_tac) >>
  `head_offset+32<=encoded_size /\ tail_offset+child_size<=encoded_size /\
   tail_offset<=encoded_size /\ 0<encoded_size` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`head_offset+32<=head_lengths ats 0`,
        `head_lengths ats 0 +
          LENGTH (FLAT (abi_tuple_tails (TAKE k ats) (TAKE k avs))) +
          child_size <=
          LENGTH (enc (Tuple ats) (ListV avs))`,
        `window_member_head_size infos=head_lengths ats 0`,
        `window_member_head_size infos<=encoded_size`,
        `enc at (ListV avs)=enc (Tuple ats) (ListV avs)`,
        `Abbrev (head_offset = _)`,`Abbrev (tail_offset = _)`,
        `Abbrev (child_size = _)`,`Abbrev (encoded_size = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     fs[markerTheory.Abbrev_def,window_member_tail_def] >> decide_tac) >>
  `?dst_var. dst=Var dst_var /\ ptr_covers Gs ts dst_var us encoded_size` by
    (qpat_assum `0<encoded_size ==> ?p. dst=Var p /\ _` MATCH_MP_TAC >>
     first_assum ACCEPT_TAC) >>
  rename1 `dst=Var dst_var` >>
  `site IN sites /\ site<current.cs_next_id /\
   (?cursor_var. dp=Var cursor_var /\ not_fresh_at current cursor_var /\
      ptr_covers Gu tu cursor_var u 32) /\
   eval_operand dp u=SOME (n2w slot) /\
   FLOOKUP u.vs_allocas site=SOME (slot,32) /\
   slot+32<=u.vs_alloca_next /\
   mem_word_at slot u.vs_memory=n2w tail_offset /\
   (!i. slot<=i /\ i<slot+32 ==> i NOTIN tu.t_mem)` by
    (qpat_assum `EXISTS (\(_,_,_,dyn). dyn) infos ==>
       site IN sites /\ site<current.cs_next_id /\ _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `Abbrev (tail_offset = _)`
       (fn th => pure_rewrite_tac
         [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
     disch_then ACCEPT_TAC) >>
  rename1 `dp=Var cursor_var` >>
  `current.cs_next_var<=prepared.cs_next_var` by
    (qpat_assum `prepared.cs_next_var=current.cs_next_var+1` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `not_fresh_at prepared dst_var /\ not_fresh_at prepared cursor_var` by
    (conj_tac
     >- (qpat_assum `!x. dst=Var x ==> not_fresh_at prepared x` MATCH_MP_TAC >>
         first_assum ACCEPT_TAC) >>
     irule not_fresh_at_mono >> qexists_tac `current` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `ptr_covers Gs ts cursor_var us 32` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers Gu tu cursor_var u 32`,
        `not_fresh_at current cursor_var`,
        `!x. not_fresh_at current x ==> lookup_var x us = _ /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     qpat_assum `!x. not_fresh_at current x ==> _`
       (qspec_then `cursor_var` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then strip_assume_tac >>
     full_simp_tac (srw_ss()) [ptr_covers_def]) >>
  `eval_operand dp us=SOME (n2w slot)` by
    (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`,
       `st` |-> `current`, `en` |-> `prepared`, `ids` |-> `sites`,
       `outs` |-> `[(d,encoded_size)]`, `s` |-> `u`, `t` |-> `us`,
       `op` |-> `dp`, `w` |-> `n2w slot`] window_phase_operand) >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       qpat_assum `dp=Var cursor_var` mp_tac >>
       qpat_assum `not_fresh_at current cursor_var` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> simp[])) >>
     disch_then ACCEPT_TAC) >>
  `slot+32<=us.vs_alloca_next /\
   mem_word_at slot us.vs_memory=n2w tail_offset /\
   (!i. slot<=i /\ i<slot+32 ==> i NOTIN ts.t_mem)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`slot+32<=u.vs_alloca_next`,
        `mem_word_at slot u.vs_memory=n2w tail_offset`,
        `!i. slot<=i /\ i<slot+32 ==> i NOTIN tu.t_mem`,
        `us.vs_memory=u.vs_memory`,`us.vs_alloca_next=u.vs_alloca_next`,
        `ts.t_mem=tu.t_mem`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
  `abi_encode_child_prefix (Var dst_var) head_offset (Var cursor_var)
    prepared=(ops,dyn_ready)` by
    (qpat_assum `abi_encode_child_prefix dst _ dp prepared=(ops,dyn_ready)`
       mp_tac >>
     qpat_assum `Abbrev (head_offset = _)` mp_tac >>
     qpat_assum `dst=Var dst_var` mp_tac >>
     qpat_assum `dp=Var cursor_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [markerTheory.Abbrev_def]) >>
  mp_tac (Q.INST
    [`dst` |-> `dst_var`,`dp` |-> `cursor_var`,
     `ho` |-> `head_offset`,`off` |-> `tail_offset`,`bound` |-> `encoded_size`,
     `st` |-> `prepared`,`en` |-> `dyn_ready`,`ops` |-> `ops`,
     `s` |-> `us`,`G` |-> `Gs`,`tn` |-> `ts`,
     `ctx` |-> `ctx`,`func` |-> `func`,`d` |-> `d`,`slot` |-> `slot`,
     `lo` |-> `lo`,`explicit` |-> `explicit`,`PG` |-> `PG`]
    window_child_prefix_joint) >>
  (impl_tac
  >- (qpat_x_assum `!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> _` kall_tac >>
      qpat_x_assum `!k current end_st result u Gu tu dp site slot. _` kall_tac >>
      qpat_assum `dst=Var dst_var` (fn th => pure_rewrite_tac[GSYM th]) >>
      qpat_assum `dp=Var cursor_var` (fn th => pure_rewrite_tac[GSYM th]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_tac >> pop_assum (qx_choose_then `dyn_actual` (qx_choose_then `Gp`
    (qx_choose_then `tp` (qx_choose_then `hp`
      (qx_choose_then `child_ptr` strip_assume_tac))))) >>
  `P ctx func explicit prepared dyn_ready us dyn_actual` by
    (irule members_payload_phase >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       (CHANGED_TAC (pure_rewrite_tac[abi_members_straight_code_def]) >>
        ntac 3 disj2_tac >> disj1_tac >> goal_assum (drule_at Any)),
       (qpat_assum `window_phase ctx func prepared dyn_ready {} [] us dyn_actual`
          mp_tac >> simp_tac bool_ss [window_phase_def])]) >>
  `alloca_inv dyn_actual /\ alloca_room ctx func dyn_actual /\
   window_alloca_growth us dyn_actual /\
   ~dyn_actual.vs_halted /\ dyn_actual.vs_current_bb=dyn_ready.cs_current_bb /\
   dyn_actual.vs_inst_idx=LENGTH dyn_ready.cs_current_insts /\
   abi_encoder_registered_effect {} [] us dyn_actual` by
    (qpat_assum `window_phase ctx func prepared dyn_ready {} [] us dyn_actual`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_phase_def]) >>
  `!x. not_fresh_at prepared x ==>
    lookup_var x dyn_actual=lookup_var x us /\
    FLOOKUP Gp x=FLOOKUP Gs x /\
    op_taint tp (Var x)=op_taint ts (Var x)` by
    (gen_tac >> strip_tac >>
     `EVERY (\i. i.inst_opcode<>INVOKE /\ ~MEM x i.inst_outputs)
       (emitted_insts prepared dyn_ready)` by
       (qpat_assum `abi_encode_child_prefix (Var dst_var) head_offset
          (Var cursor_var) prepared=(ops,dyn_ready)` mp_tac >>
        qpat_assum `not_fresh_at prepared x` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [abi_encode_child_prefix_def,emitHelperTheory.emit_op_def,
          fresh_var_def,fresh_id_def,emit_def,comp_bind_def,
          comp_return_def,comp_ignore_bind_def,LET_THM] >>
        rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
        qpat_x_assum `_ = dyn_ready` (SUBST1_TAC o SYM) >>
        full_simp_tac (srw_ss()) [emitted_insts_def,APPEND_ASSOC,DROP_LENGTH_APPEND,
          mk_inst_def,loweringStateRelDefsTheory.not_fresh_at_def] >>
        pure_rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >>
        simp_tac (srw_ss()) [] >> rpt conj_tac >>
        qpat_assum `!n. prepared.cs_next_var <= n ==> _` MATCH_MP_TAC >> decide_tac) >>
     `lookup_var x (dyn_actual with vs_inst_idx:=us.vs_inst_idx)=
       lookup_var x us` by
       (irule (Q.ISPEC `lookup_var x` run_inst_seq_preserves_field) >>
        qexists_tac `emitted_insts prepared dyn_ready` >>
        reverse conj_tac >- first_assum ACCEPT_TAC >>
        rpt gen_tac >> strip_tac >>
        irule abiEncoderWindowLookupTheory.abi_window_step_non_output >>
        goal_assum (drule_at Any) >>
        qpat_assum `EVERY _ (emitted_insts prepared dyn_ready)` mp_tac >>
        qpat_assum `MEM i (emitted_insts prepared dyn_ready)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [EVERY_MEM] >> metis_tac[]) >>
     `lookup_var x dyn_actual=lookup_var x us` by
       (qpat_assum `lookup_var x (dyn_actual with vs_inst_idx:=us.vs_inst_idx)=_`
          mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> simp[lookup_var_def]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!x. not_fresh_at prepared x ==> FLOOKUP Gp x=_ /\ _`
       (qspec_then `x` MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
  `dyn_actual.vs_allocas=us.vs_allocas` by
    (qpat_assum `abi_encoder_registered_effect {} [] us dyn_actual` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [abi_encoder_registered_effect_def,
       finite_mapTheory.fmap_eq_flookup]) >>
  `dyn_actual.vs_alloca_next=us.vs_alloca_next` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`dyn_actual.vs_allocas=us.vs_allocas`,
        `window_alloca_growth us dyn_actual`,
        `abi_encode_exec_frame func us dyn_actual`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     `pending_alloca_size func dyn_actual=pending_alloca_size func us` by
       (qpat_assum `dyn_actual.vs_allocas=us.vs_allocas` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[pending_alloca_size_def]) >>
     qpat_assum `abi_encode_exec_frame func us dyn_actual`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [abi_encode_exec_frame_def]) >>
     qpat_assum `window_alloca_growth us dyn_actual`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [window_alloca_growth_def]) >>
     qpat_assum `pending_alloca_size func dyn_actual=pending_alloca_size func us`
       (fn th => pure_rewrite_tac[th]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp dyn_actual /\
    dyn_actual.vs_alloca_next + pending_alloca_size func dyn_actual <= w2n dyn_actual.vs_initial_fmp` by
    (qpat_assum `abi_encode_exec_frame func us dyn_actual` (fn frame =>
       qpat_assum `alloca_inv dyn_actual` (fn inv =>
         qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp us /\ us.vs_alloca_next + pending_alloca_size func us <= w2n us.vs_initial_fmp` (fn bound =>
           ACCEPT_TAC (MATCH_MP window_exec_frame_alloca_budget
             (LIST_CONJ [frame,inv,bound])))))) >>
  suspend "member_dynamic_call"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_dynamic_call]:
  `prepared.cs_next_id <= dyn_ready.cs_next_id` by
    (qpat_assum `dyn_ready.cs_next_id=prepared.cs_next_id+3` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `prepared.cs_next_var <= dyn_ready.cs_next_var` by
    (qpat_assum `dyn_ready.cs_next_var=prepared.cs_next_var+3` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `0 < child_size ==> ?p. SND (SND ops) = Var p /\
    ptr_covers Gp tp p dyn_actual child_size` by
    (strip_tac >> qexists_tac `child_ptr` >> conj_tac >- first_assum ACCEPT_TAC >>
     mp_tac (Q.INST [`G` |-> `Gp`, `tn` |-> `tp`, `root` |-> `child_ptr`,
       `s` |-> `dyn_actual`, `cap` |-> `encoded_size-tail_offset`,
       `sz` |-> `child_size`] reasonCopySourcePtrTheory.ptr_covers_mono) >>
     (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> decide_tac)) >>
     disch_then ACCEPT_TAC) >>
  `body_end.cs_next_id <= end_st.cs_next_id` by
    (qpat_assum `body_end.cs_next_id+3 = child_end.cs_next_id` mp_tac >>
     qpat_assum `child_end.cs_next_id <= end_st.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `allocas_from lo dyn_actual /\ lo <= dyn_actual.vs_alloca_next` by
    (conj_tac >-
       (qpat_assum `allocas_from lo us` mp_tac >>
        qpat_assum `dyn_actual.vs_allocas = us.vs_allocas` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[allocas_from_def]) >>
     qpat_assum `dyn_actual.vs_alloca_next = us.vs_alloca_next` (fn tp => rewrite_tac[tp]) >>
     first_assum ACCEPT_TAC) >>
  `eval_operand elem_src dyn_actual = SOME (n2w (sb+source_offset))` by
    (irule window_phase_operand >> goal_assum (drule_at Any) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `op_taint tp elem_src = {}` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`op_taint ts elem_src = {}`,
        `!x. elem_src = Var x ==> not_fresh_at prepared x`,
        `!x. not_fresh_at prepared x ==> lookup_var x dyn_actual = _ /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `elem_src` >> simp[op_taint_def] >> metis_tac[]) >>
  `!x. elem_src = Var x \/ SND (SND ops) = Var x ==> not_fresh_at dyn_ready x` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. FST ops = Var x \/ FST (SND ops) = Var x \/ SND (SND ops) = Var x ==>
          not_fresh_at dyn_ready x`,
        `!x. elem_src = Var x ==> not_fresh_at prepared x`,
        `prepared.cs_next_var <= dyn_ready.cs_next_var`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> metis_tac[not_fresh_at_mono]) >>
  `d+tail_offset+child_size <= dyn_actual.vs_alloca_next` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`tail_offset+child_size <= encoded_size`,
        `d+encoded_size <= us.vs_alloca_next`,
        `dyn_actual.vs_alloca_next = us.vs_alloca_next`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!mem. mem_agree_outside tp.t_mem dyn_actual.vs_memory mem ==>
    abi_encoder_window_input ei (EL k ats) (EL k avs)
      (sb+source_offset) (MIN ms (cap-source_offset)) mem` by
    (qpat_assum `dyn_actual.vs_memory = us.vs_memory` (fn tp => rewrite_tac[tp]) >>
     qpat_assum `tp.t_mem = ts.t_mem` (fn tp => rewrite_tac[tp]) >>
     qpat_assum `Abbrev (source_offset = _)`
       (fn tp => pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] tp]) >>
     first_assum ACCEPT_TAC) >>
  `0 < MIN ms (cap-source_offset) ==>
    ?p. elem_src = Var p /\ ptr_covers Gp tp p dyn_actual (MIN ms (cap-source_offset))` by
    (strip_tac >>
     qpat_assum `0 < MIN ms (cap-source_offset) ==> _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then strip_assume_tac >>
     qexists_tac `p` >> conj_tac >- first_assum ACCEPT_TAC >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers Gs ts p us (MIN ms (cap-source_offset))`,
        `elem_src = Var p`,
        `!x. elem_src = Var x ==> not_fresh_at prepared x`,
        `!x. not_fresh_at prepared x ==> lookup_var x dyn_actual = _ /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     metis_tac[appendStorageGhostPtrTheory.ptr_covers_old_transport]) >>
  `0 < MIN ms (cap-source_offset) ==>
    sb+source_offset+MIN ms (cap-source_offset) <= dyn_actual.vs_alloca_next` by
    (strip_tac >>
     qpat_assum `0 < MIN ms (cap-source_offset) ==>
       sb+source_offset+MIN ms (cap-source_offset) <= us.vs_alloca_next /\ _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o CONJUNCT1) >>
     qpat_assum `dyn_actual.vs_alloca_next = us.vs_alloca_next` (fn tp => rewrite_tac[tp]) >>
     simp_tac bool_ss []) >>
  `0 < MIN ms (cap-source_offset) ==>
    regions_disjoint (sb+source_offset,MIN ms (cap-source_offset))
      (d+tail_offset,child_size)` by
    (strip_tac >>
     `MIN ms (cap-source_offset) <= cap-source_offset` by simp[NoAsms, MIN_LE] >>
     `0 < cap` by decide_tac >>
     `regions_disjoint (sb,cap) (d,encoded_size)` by
       (qpat_assum `0 < cap ==> sb+cap <= u.vs_alloca_next /\ _` mp_tac >>
        qpat_assum `0 < cap` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`regions_disjoint (sb,cap) (d,encoded_size)`,
        `MIN ms (cap-source_offset) <= cap-source_offset`,
        `0 < MIN ms (cap-source_offset)`,
        `tail_offset+child_size <= encoded_size`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
  `0 < MIN ms (cap-source_offset) ==>
    sb+source_offset+MIN ms (cap-source_offset) <= dyn_actual.vs_alloca_next /\
    regions_disjoint (sb+source_offset,MIN ms (cap-source_offset))
      (d+tail_offset,child_size) /\
    ?p. elem_src = Var p /\ ptr_covers Gp tp p dyn_actual (MIN ms (cap-source_offset))` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`0 < MIN ms (cap-source_offset) ==>
          sb+source_offset+MIN ms (cap-source_offset) <= dyn_actual.vs_alloca_next`,
        `0 < MIN ms (cap-source_offset) ==> regions_disjoint _ _`,
        `0 < MIN ms (cap-source_offset) ==> ?p. elem_src = Var p /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `window_alloca_sites func (frag_ids dyn_ready body_end) SUBSET sites` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`st.cs_next_id <= current.cs_next_id`,
        `prepared.cs_next_id = current.cs_next_id+1`,
        `prepared.cs_next_id <= dyn_ready.cs_next_id`,
        `body_end.cs_next_id <= end_st.cs_next_id`,
        `end_st.cs_next_id <= en.cs_next_id`, `Abbrev (sites = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     simp_tac bool_ss [Abbr `sites`] >> irule window_alloca_sites_mono >>
     simp[SUBSET_DEF, abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `!id b sz. id IN sites /\ FLOOKUP dyn_actual.vs_allocas id = SOME (b,sz) ==>
    sz = 32 /\ (0 < cap ==> regions_disjoint (sb,cap) (b,sz)) /\
    regions_disjoint (d,encoded_size) (b,sz)` by
    (qpat_assum `!id b sz. id IN sites /\ FLOOKUP u.vs_allocas id = _ ==> _` mp_tac >>
     qpat_assum `dyn_actual.vs_allocas = us.vs_allocas` mp_tac >>
     qpat_assum `us.vs_allocas = u.vs_allocas` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> asm_rewrite_tac[]) >>
  `!inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids dyn_ready body_end /\
    FLOOKUP dyn_actual.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\
    (0 < MIN ms (cap-source_offset) ==>
      regions_disjoint (sb+source_offset,MIN ms (cap-source_offset)) (b,sz)) /\
    regions_disjoint (d+tail_offset,child_size) (b,sz)` by
    (rpt gen_tac >> strip_tac >>
     `inst.inst_id IN sites` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`window_alloca_sites func (frag_ids dyn_ready body_end) SUBSET sites`,
           `MEM inst (fn_insts func)`, `inst.inst_opcode = ALLOCA`,
           `inst.inst_id IN frag_ids dyn_ready body_end`] >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[SUBSET_DEF, window_alloca_sites_def] >> metis_tac[]) >>
     qpat_assum `!id b sz. id IN sites /\ FLOOKUP dyn_actual.vs_allocas id = _ ==> sz = 32 /\ _`
       (qspecl_then [`inst.inst_id`, `b`, `sz`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then strip_assume_tac >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (strip_tac >>
         `MIN ms (cap-source_offset) <= cap-source_offset` by simp[NoAsms, MIN_LE] >>
         `0 < cap` by decide_tac >>
         `regions_disjoint (sb,cap) (b,sz)` by
           (qpat_assum `0 < cap ==> regions_disjoint (sb,cap) (b,sz)` mp_tac >>
            qpat_assum `0 < cap` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`regions_disjoint (sb,cap) (b,sz)`,
            `MIN ms (cap-source_offset) <= cap-source_offset`,
            `0 < MIN ms (cap-source_offset)`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
     qpat_assum `regions_disjoint (d,encoded_size) (b,sz)` mp_tac >>
     qpat_assum `tail_offset+child_size <= encoded_size` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
  qpat_assum `!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> _`
    (qspecl_then [`ei`, `az`, `ms`, `T`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then
    [`SND (SND ops)`, `elem_src`, `dyn_ready`, `body_len`, `body_end`, `ctx`, `func`,
     `dyn_actual`, `EL k ats`, `EL k avs`, `sb+source_offset`,
     `MIN ms (cap-source_offset)`, `d+tail_offset`, `Gp`, `tp`,
     `lo`, `explicit`, `PG`] mp_tac) >>
  (impl_tac >- suspend "member_dynamic_pre") >>
  disch_then (qx_choose_then `body_actual`
    (qx_choose_then `Gb` (qx_choose_then `tb` strip_assume_tac))) >>
  suspend "member_dynamic_post"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_dynamic_pre]:
  qpat_x_assum `!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> _` kall_tac >>
  qpat_x_assum `!k current end_st result u Gu tu dp site slot. _` kall_tac >>
  map_every (fn q => qpat_assum q (fn tp =>
    pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] tp)]))
    [`Abbrev (tail_offset = _)`, `Abbrev (source_offset = _)`,
     `Abbrev (child_size = _)`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED


Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_dynamic_post]:
  `window_phase ctx func dyn_ready body_end
    (window_alloca_sites func (frag_ids dyn_ready body_end))
    [(d+tail_offset,child_size)] dyn_actual body_actual` by
    (qpat_assum `window_strong_result ctx func dyn_ready body_end body_len
       (EL k ats) (EL k avs) (d+tail_offset) dyn_actual body_actual` mp_tac >>
     qpat_assum `Abbrev (child_size = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [markerTheory.Abbrev_def, window_strong_result_def,
       abi_encoder_window_result_def, window_phase_def] >> metis_tac[]) >>
  drule window_phase_resources >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  drule window_phase_effect >> strip_tac >>
  `!id r. FLOOKUP dyn_actual.vs_allocas id = SOME r ==>
    FLOOKUP body_actual.vs_allocas id = SOME r` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `abi_encoder_registered_effect
       (window_alloca_sites func (frag_ids dyn_ready body_end))
       [(d+tail_offset,child_size)] dyn_actual body_actual` mp_tac >>
     qpat_assum `FLOOKUP dyn_actual.vs_allocas id = SOME r` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[abi_encoder_registered_effect_allocated]) >>
  `!id b sz. id IN window_alloca_sites func (frag_ids dyn_ready body_end) /\
    FLOOKUP body_actual.vs_allocas id = SOME (b,sz) ==> sz = 32` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `window_strong_result ctx func dyn_ready body_end body_len
       (EL k ats) (EL k avs) (d+tail_offset) dyn_actual body_actual` mp_tac >>
     qpat_assum `id IN window_alloca_sites func (frag_ids dyn_ready body_end)` mp_tac >>
     qpat_assum `FLOOKUP body_actual.vs_allocas id = SOME (b,sz)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[window_strong_result_sizes]) >>
  `!id b sz. id IN sites /\ FLOOKUP body_actual.vs_allocas id = SOME (b,sz) ==>
    sz = 32` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`abi_encoder_registered_effect (window_alloca_sites func (frag_ids dyn_ready body_end))
          [(d+tail_offset,child_size)] dyn_actual body_actual`,
        `!id b sz. id IN sites /\ FLOOKUP dyn_actual.vs_allocas id = _ ==> sz = 32 /\ _`,
        `!id b sz. id IN window_alloca_sites func (frag_ids dyn_ready body_end) /\
          FLOOKUP body_actual.vs_allocas id = _ ==> sz = 32`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     `!id b sz. id IN sites /\ FLOOKUP dyn_actual.vs_allocas id = SOME (b,sz) ==> sz = 32` by
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!id b sz. id IN sites /\ _ ==> sz = 32 /\ _`
          (qspecl_then [`id`, `b`, `sz`] mp_tac) >>
        (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then (ACCEPT_TAC o CONJUNCT1)) >>
     mp_tac (Q.INST
       [`R` |-> `sites`, `ids` |-> `window_alloca_sites func (frag_ids dyn_ready body_end)`,
        `outs` |-> `[(d+tail_offset,child_size)]`, `s` |-> `dyn_actual`, `t` |-> `body_actual`]
       window_registered_sizes_transport) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `d+encoded_size <= dyn_actual.vs_alloca_next` by
    (qpat_assum `dyn_actual.vs_alloca_next = us.vs_alloca_next` (fn tp => rewrite_tac[tp]) >>
     first_assum ACCEPT_TAC) >>
  `!id b sz. id IN sites /\ FLOOKUP dyn_actual.vs_allocas id = SOME (b,sz) ==>
    regions_disjoint (d,encoded_size) (b,sz)` by
    (qpat_assum `!id b sz. id IN sites /\ FLOOKUP dyn_actual.vs_allocas id = _ ==> sz = 32 /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!id b sz. id IN sites /\ FLOOKUP body_actual.vs_allocas id = SOME (b,sz) ==>
    regions_disjoint (d,encoded_size) (b,sz)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`window_alloca_growth dyn_actual body_actual`,
        `!id r. FLOOKUP dyn_actual.vs_allocas id = SOME r ==> FLOOKUP body_actual.vs_allocas id = SOME r`,
        `d+encoded_size <= dyn_actual.vs_alloca_next`,
        `!id b sz. id IN sites /\ FLOOKUP dyn_actual.vs_allocas id = _ ==>
          regions_disjoint (d,encoded_size) (b,sz)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     mp_tac (Q.INST [`q` |-> `d`, `n` |-> `encoded_size`, `ids` |-> `sites`,
       `s` |-> `dyn_actual`, `t` |-> `body_actual`] window_alloca_growth_protected) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `0 < cap ==> sb+cap <= dyn_actual.vs_alloca_next` by
    (strip_tac >>
     qpat_assum `0 < cap ==> sb+cap <= u.vs_alloca_next /\ _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o CONJUNCT1) >>
     qpat_assum `dyn_actual.vs_alloca_next = us.vs_alloca_next` (fn tp => rewrite_tac[tp]) >>
     qpat_assum `us.vs_alloca_next = u.vs_alloca_next` (fn tp => rewrite_tac[tp]) >>
     simp_tac bool_ss []) >>
  `0 < cap ==> !id b sz. id IN sites /\
    FLOOKUP body_actual.vs_allocas id = SOME (b,sz) ==>
    regions_disjoint (sb,cap) (b,sz)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`window_alloca_growth dyn_actual body_actual`,
        `!id r. FLOOKUP dyn_actual.vs_allocas id = SOME r ==> FLOOKUP body_actual.vs_allocas id = SOME r`,
        `0 < cap ==> sb+cap <= dyn_actual.vs_alloca_next`,
        `!id b sz. id IN sites /\ FLOOKUP dyn_actual.vs_allocas id = _ ==> sz = 32 /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     `sb+cap <= dyn_actual.vs_alloca_next` by metis_tac[] >>
     `!id b sz. id IN sites /\ FLOOKUP dyn_actual.vs_allocas id = SOME (b,sz) ==>
       regions_disjoint (sb,cap) (b,sz)` by
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!id b sz. id IN sites /\ _ ==> sz = 32 /\ _`
          (qspecl_then [`id`, `b`, `sz`] mp_tac) >>
        (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then (fn tp => MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 tp))) >>
        first_assum ACCEPT_TAC) >>
     mp_tac (Q.INST [`q` |-> `sb`, `n` |-> `cap`, `ids` |-> `sites`,
       `s` |-> `dyn_actual`, `t` |-> `body_actual`] window_alloca_growth_protected) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `mem_bytes_at sb cap body_actual.vs_memory = mem_bytes_at sb cap dyn_actual.vs_memory` by
    (Cases_on `cap = 0` >-
       (qpat_assum `cap = 0` SUBST_ALL_TAC >>
        simp[NoAsms, valueEncodingDefsTheory.mem_bytes_at_def]) >>
     mp_tac (Q.INST [`p` |-> `sb`, `n` |-> `cap`,
       `ids` |-> `window_alloca_sites func (frag_ids dyn_ready body_end)`,
       `outs` |-> `[(d+tail_offset,child_size)]`, `s` |-> `dyn_actual`, `t` |-> `body_actual`]
       abi_encoder_window_effect_bytes) >>
     (impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >> conj_tac
        >- (`regions_disjoint (sb,cap) (d,encoded_size)` by
              (qpat_assum `0 < cap ==> sb+cap <= u.vs_alloca_next /\ _` mp_tac >>
               (impl_tac >- (qpat_assum `cap <> 0` mp_tac >>
                 POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)) >>
               disch_then (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2)) >>
            map_every (fn pat => qpat_assum pat mp_tac)
              [`regions_disjoint (sb,cap) (d,encoded_size)`,
               `cap <> 0`, `tail_offset+child_size <= encoded_size`] >>
            POP_ASSUM_LIST (K ALL_TAC) >>
            simp_tac bool_ss [EVERY_DEF, regions_disjoint_def] >> decide_tac) >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`0 < cap ==> !id b sz. id IN sites /\ _ ==> regions_disjoint (sb,cap) (b,sz)`,
           `window_alloca_sites func (frag_ids dyn_ready body_end) SUBSET sites`, `cap <> 0`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [SUBSET_DEF] >>
        metis_tac[NOT_ZERO_LT_ZERO])) >> disch_then ACCEPT_TAC) >>
  suspend "member_dynamic_advance"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_dynamic_advance]:
  `!i. i < cap ==> (sb+i IN tb.t_mem <=> sb+i IN tp.t_mem)` by
    (gen_tac >> strip_tac >>
     `0 < cap` by decide_tac >>
     qpat_assum `!i. (i < d+tail_offset \/ d+tail_offset+_ <= i) /\ _ ==>
       (i IN tb.t_mem <=> i IN tp.t_mem)`
       (qspec_then `sb+i` MATCH_MP_TAC) >> conj_tac
     >- (qpat_assum `Abbrev (child_size = _)`
           (fn tp => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] tp)]) >>
         `regions_disjoint (sb,cap) (d,encoded_size)` by
           (qpat_assum `0 < cap ==> sb+cap <= u.vs_alloca_next /\ _` mp_tac >>
            (impl_tac >- first_assum ACCEPT_TAC) >>
            disch_then (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2)) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`regions_disjoint (sb,cap) (d,encoded_size)`, `i < cap`,
            `tail_offset+child_size <= encoded_size`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
     rpt gen_tac >> strip_tac >>
     `id IN sites` by
       (qpat_assum `window_alloca_sites func (frag_ids dyn_ready body_end) SUBSET sites` mp_tac >>
        qpat_assum `id IN window_alloca_sites func (frag_ids dyn_ready body_end)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [SUBSET_DEF] >> metis_tac[]) >>
     `regions_disjoint (sb,cap) (b,sz)` by
       (qpat_assum `0 < cap ==> !id b sz. id IN sites /\ _ ==> regions_disjoint (sb,cap) (b,sz)` mp_tac >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then (qspecl_then [`id`, `b`, `sz`] mp_tac) >>
        (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
     qpat_assum `regions_disjoint (sb,cap) (b,sz)` mp_tac >>
     qpat_assum `i < cap` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
  `!i. i < cap ==> (sb+i IN tb.t_mem <=> sb+i IN tn.t_mem)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!i. i < cap ==> (sb+i IN tb.t_mem <=> sb+i IN tp.t_mem)`,
        `!i. i < cap ==> (sb+i IN tu.t_mem <=> sb+i IN tn.t_mem)`,
        `tp.t_mem = ts.t_mem`, `ts.t_mem = tu.t_mem`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `window_member_prefix infos ats avs k d dyn_actual.vs_memory` by
    (qpat_assum `dyn_actual.vs_memory = us.vs_memory` (fn tp => rewrite_tac[tp]) >>
     qpat_assum `us.vs_memory = u.vs_memory` (fn tp => rewrite_tac[tp]) >>
     first_assum ACCEPT_TAC) >>
  `mem_bytes_at (d+tail_offset) child_size body_actual.vs_memory =
    enc (EL k ats) (EL k avs)` by
    (simp_tac bool_ss [Abbr `child_size`] >>
     qpat_assum `window_strong_result ctx func dyn_ready body_end body_len
       (EL k ats) (EL k avs) (d+tail_offset) dyn_actual body_actual`
       (ACCEPT_TAC o CONJUNCT1 o CONJUNCT1 o
         REWRITE_RULE [window_strong_result_def, abi_encoder_window_result_def])) >>
  suspend "member_dynamic_suffix_prepare"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_dynamic_suffix_prepare]:
  `dyn_ready.cs_next_var<=body_end.cs_next_var /\
   dyn_ready.cs_next_id<=body_end.cs_next_id` by
    (conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. dp=Var x ==> not_fresh_at dyn_ready x` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`dp=Var cursor_var`,`not_fresh_at prepared cursor_var`,
        `dyn_ready.cs_next_var=prepared.cs_next_var+3`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     `prepared.cs_next_var<=dyn_ready.cs_next_var` by decide_tac >>
     qpat_x_assum `dp=Var cursor_var` SUBST_ALL_TAC >> simp_tac (srw_ss()) [] >>
     irule not_fresh_at_mono >> qexists_tac `prepared` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand dp dyn_actual=SOME (n2w slot)` by
    (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`,
       `st` |-> `prepared`, `en` |-> `dyn_ready`, `ids` |-> `{}`, `outs` |-> `[]`,
       `s` |-> `us`, `t` |-> `dyn_actual`, `op` |-> `dp`, `w` |-> `n2w slot`]
       window_phase_operand) >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       qpat_assum `dp=Var cursor_var` mp_tac >>
       qpat_assum `not_fresh_at prepared cursor_var` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> simp[])) >> disch_then ACCEPT_TAC) >>
  `ptr_covers Gp tp cursor_var dyn_actual 32` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers Gs ts cursor_var us 32`,
        `not_fresh_at prepared cursor_var`,
        `!x. not_fresh_at prepared x ==> lookup_var x dyn_actual=_ /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     qpat_assum `!x. not_fresh_at prepared x ==> _`
       (qspec_then `cursor_var` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then strip_assume_tac >>
     full_simp_tac (srw_ss()) [ptr_covers_def]) >>
  `(!x. FST ops=Var x \/ dp=Var x \/ FST (SND ops)=Var x ==>
     not_fresh_at dyn_ready x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. FST ops=Var x \/ FST (SND ops)=Var x \/
          SND (SND ops)=Var x ==> not_fresh_at dyn_ready x`,
        `!x. dp=Var x ==> not_fresh_at dyn_ready x`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `eval_operand (FST ops) body_actual=SOME (n2w (d+head_offset))` by
    (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`,
       `st` |-> `dyn_ready`, `en` |-> `body_end`,
       `ids` |-> `window_alloca_sites func (frag_ids dyn_ready body_end)`,
       `outs` |-> `[(d+tail_offset,child_size)]`,
       `s` |-> `dyn_actual`, `t` |-> `body_actual`,
       `op` |-> `FST (ops : operand # operand # operand)`, `w` |-> `n2w (d+head_offset)`] window_phase_operand) >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       gen_tac >> strip_tac >>
       qpat_assum `!x. FST ops=Var x \/ dp=Var x \/ FST (SND ops)=Var x ==> _`
         (qspec_then `x` MATCH_MP_TAC) >>
       FIRST [disj1_tac >> first_assum ACCEPT_TAC,
         disj2_tac >> disj1_tac >> first_assum ACCEPT_TAC,
         disj2_tac >> disj2_tac >> first_assum ACCEPT_TAC])) >>
     disch_then ACCEPT_TAC) >>
  `eval_operand (dp) body_actual=SOME (n2w (slot))` by
    (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`,
       `st` |-> `dyn_ready`, `en` |-> `body_end`,
       `ids` |-> `window_alloca_sites func (frag_ids dyn_ready body_end)`,
       `outs` |-> `[(d+tail_offset,child_size)]`,
       `s` |-> `dyn_actual`, `t` |-> `body_actual`,
       `op` |-> `dp`, `w` |-> `n2w (slot)`] window_phase_operand) >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       gen_tac >> strip_tac >>
       qpat_assum `!x. FST ops=Var x \/ dp=Var x \/ FST (SND ops)=Var x ==> _`
         (qspec_then `x` MATCH_MP_TAC) >>
       FIRST [disj1_tac >> first_assum ACCEPT_TAC,
         disj2_tac >> disj1_tac >> first_assum ACCEPT_TAC,
         disj2_tac >> disj2_tac >> first_assum ACCEPT_TAC])) >>
     disch_then ACCEPT_TAC) >>
  `eval_operand (FST (SND ops)) body_actual=SOME (n2w (tail_offset))` by
    (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`,
       `st` |-> `dyn_ready`, `en` |-> `body_end`,
       `ids` |-> `window_alloca_sites func (frag_ids dyn_ready body_end)`,
       `outs` |-> `[(d+tail_offset,child_size)]`,
       `s` |-> `dyn_actual`, `t` |-> `body_actual`,
       `op` |-> `FST (SND (ops : operand # operand # operand))`, `w` |-> `n2w (tail_offset)`] window_phase_operand) >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       gen_tac >> strip_tac >>
       qpat_assum `!x. FST ops=Var x \/ dp=Var x \/ FST (SND ops)=Var x ==> _`
         (qspec_then `x` MATCH_MP_TAC) >>
       FIRST [disj1_tac >> first_assum ACCEPT_TAC,
         disj2_tac >> disj1_tac >> first_assum ACCEPT_TAC,
         disj2_tac >> disj2_tac >> first_assum ACCEPT_TAC])) >>
     disch_then ACCEPT_TAC) >>
  `ptr_covers Gb tb hp body_actual 32 /\
   ptr_covers Gb tb cursor_var body_actual 32` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers Gp tp hp dyn_actual 32`,
        `ptr_covers Gp tp cursor_var dyn_actual 32`,
        `!x. not_fresh_at dyn_ready x ==> FLOOKUP Gb x=_ /\ _`,
        `!x. FST ops=Var x \/ dp=Var x \/ FST (SND ops)=Var x ==> _`,
        `FST ops=Var hp`,`dp=Var cursor_var`,
        `window_phase ctx func dyn_ready body_end _ _ dyn_actual body_actual`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     `not_fresh_at dyn_ready hp /\ not_fresh_at dyn_ready cursor_var` by
       metis_tac[] >>
     metis_tac[ptr_covers_def,window_phase_vars]) >>
  `op_taint tb (FST (SND ops))={}` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`op_taint tp (FST (SND ops))={}`,
        `!x. FST ops=Var x \/ dp=Var x \/ FST (SND ops)=Var x ==> _`,
        `!x. not_fresh_at dyn_ready x ==> FLOOKUP Gb x=_ /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `FST (SND ops)` >> simp[op_taint_def] >> metis_tac[]) >>
  `eval_operand body_len body_actual=SOME (n2w child_size)` by
    (qpat_assum `window_strong_result ctx func dyn_ready body_end body_len
       (EL k ats) (EL k avs) (d+tail_offset) dyn_actual body_actual` mp_tac >>
     qpat_assum `Abbrev (child_size = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [markerTheory.Abbrev_def,window_strong_result_def,
       abi_encoder_window_result_def] >> metis_tac[]) >>
  `FLOOKUP body_actual.vs_allocas site=SOME (slot,32)` by
    (qpat_assum `!id r. FLOOKUP dyn_actual.vs_allocas id=SOME r ==> _`
       (qspecl_then [`site`,`(slot,32)`] MATCH_MP_TAC) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP u.vs_allocas site=SOME (slot,32)`,
        `dyn_actual.vs_allocas=us.vs_allocas`,`us.vs_allocas=u.vs_allocas`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
  `d+encoded_size<=body_actual.vs_alloca_next /\
   slot+32<=body_actual.vs_alloca_next` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`d+encoded_size<=dyn_actual.vs_alloca_next`,
        `slot+32<=us.vs_alloca_next`,
        `dyn_actual.vs_alloca_next=us.vs_alloca_next`] >>
     qpat_assum `window_alloca_growth dyn_actual body_actual`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [window_alloca_growth_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `d+head_offset+32<=body_actual.vs_alloca_next` by
    (qpat_assum `head_offset+32<=encoded_size` mp_tac >>
     qpat_assum `d+encoded_size<=body_actual.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `regions_disjoint (d+head_offset,32) (slot,32)` by
    (`regions_disjoint (d,encoded_size) (slot,32)` by
       (qpat_assum `!id b sz. id IN sites /\
          FLOOKUP body_actual.vs_allocas id=_ ==>
          regions_disjoint (d,encoded_size) (b,sz)`
          (qspecl_then [`site`,`slot`,`32`] MATCH_MP_TAC) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `regions_disjoint (d,encoded_size) (slot,32)` mp_tac >>
     qpat_assum `head_offset+32<=encoded_size` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
  `!x. FST ops=Var x \/ dp=Var x \/ FST (SND ops)=Var x \/
    body_len=Var x ==> not_fresh_at body_end x` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. FST ops=Var x \/ dp=Var x \/ FST (SND ops)=Var x ==> _`,
        `dyn_ready.cs_next_var<=body_end.cs_next_var`,
        `!x. body_len=Var x ==> not_fresh_at body_end x`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     metis_tac[not_fresh_at_mono]) >>
  `allocas_from lo body_actual` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`allocas_from lo dyn_actual`, `lo <= dyn_actual.vs_alloca_next`,
        `!id r. FLOOKUP dyn_actual.vs_allocas id = SOME r ==> FLOOKUP body_actual.vs_allocas id = SOME r`,
        `window_alloca_growth dyn_actual body_actual`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     qpat_assum `window_alloca_growth dyn_actual body_actual`
       (strip_assume_tac o REWRITE_RULE [window_alloca_growth_def]) >>
     simp_tac bool_ss [allocas_from_def] >> rpt gen_tac >> strip_tac >>
     Cases_on `FLOOKUP dyn_actual.vs_allocas aid`
     >- (`dyn_actual.vs_alloca_next <= b` by
           (qpat_assum `!i b sz. FLOOKUP dyn_actual.vs_allocas i = NONE /\ _ ==> _`
              (qspecl_then [`aid`, `b`, `sz`] MATCH_MP_TAC) >>
            conj_tac >> first_assum ACCEPT_TAC) >>
         qpat_assum `dyn_actual.vs_alloca_next <= b` mp_tac >>
         qpat_assum `lo <= dyn_actual.vs_alloca_next` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     rename1 `FLOOKUP dyn_actual.vs_allocas aid = SOME old_slot` >>
     qpat_assum `!id r. FLOOKUP dyn_actual.vs_allocas id = SOME r ==> _`
       (qspecl_then [`aid`, `old_slot`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
     gvs[allocas_from_def] >>
     qpat_assum `!aid b sz. FLOOKUP dyn_actual.vs_allocas aid = SOME (b,sz) ==> lo <= b`
       (qspecl_then [`aid`, `b`, `sz`] MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
  `lo <= body_actual.vs_alloca_next` by
    (qpat_assum `lo <= dyn_actual.vs_alloca_next` mp_tac >>
     qpat_assum `window_alloca_growth dyn_actual body_actual`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [window_alloca_growth_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp body_actual /\
    body_actual.vs_alloca_next + pending_alloca_size func body_actual <= w2n body_actual.vs_initial_fmp` by
    (qpat_assum `abi_encode_exec_frame func dyn_actual body_actual` (fn frame =>
       qpat_assum `alloca_inv body_actual` (fn inv =>
         qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp dyn_actual /\ dyn_actual.vs_alloca_next + pending_alloca_size func dyn_actual <= w2n dyn_actual.vs_initial_fmp` (fn bound =>
           ACCEPT_TAC (MATCH_MP window_exec_frame_alloca_budget
             (LIST_CONJ [frame,inv,bound])))))) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp body_actual` by
    qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp body_actual /\ body_actual.vs_alloca_next + pending_alloca_size func body_actual <= w2n body_actual.vs_initial_fmp`
      (fn th => ACCEPT_TAC (DISCH (fst (dest_imp (concl th)))
        (CONJUNCT1 (UNDISCH th)))) >>
  mp_tac (Q.INST
    [`head` |-> `hp`,`dp` |-> `cursor_var`,
     `offset` |-> `FST (SND (ops : operand # operand # operand))`,`len` |-> `body_len`,
     `st` |-> `body_end`,`en` |-> `child_end`,`out` |-> `child_len`,
     `s` |-> `body_actual`,`G` |-> `Gb`,`tn` |-> `tb`,
     `h` |-> `d+head_offset`,`slot` |-> `slot`,`site` |-> `site`,
     `off` |-> `tail_offset`,`n` |-> `child_size`,
     `ctx` |-> `ctx`,`func` |-> `func`,
     `lo` |-> `lo`,`explicit` |-> `explicit`,`PG` |-> `PG`]
    window_child_suffix_joint) >>
  (impl_tac >- suspend "member_dynamic_suffix_pre") >>
  disch_then (qx_choose_then `child_actual` (qx_choose_then `Gc`
    (qx_choose_then `tc` strip_assume_tac))) >>
  suspend "member_dynamic_suffix_post"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_dynamic_suffix_pre]:
  qpat_x_assum `!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> _` kall_tac >>
  qpat_x_assum `!k current end_st result u Gu tu dp site slot. _` kall_tac >>
  qpat_assum `FST ops=Var hp` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `dp=Var cursor_var` (fn th => pure_rewrite_tac[GSYM th]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_dynamic_suffix_post]:
  `P ctx func explicit body_end child_end body_actual child_actual` by
    (irule members_payload_phase >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       (CHANGED_TAC (pure_rewrite_tac[abi_members_straight_code_def]) >>
        ntac 4 disj2_tac >> goal_assum (drule_at Any)),
       (qpat_assum `window_phase ctx func body_end child_end _ _ body_actual child_actual`
          mp_tac >> simp_tac bool_ss [window_phase_def])]) >>
  `head_bytes k=head_offset /\
   tail_offset=window_member_head_size infos+tail_bytes k /\
   head_offset+32<=window_member_head_size infos` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LIST_REL abi_encoder_structural_valid ats avs`,`k<LENGTH ats`,
        `head_offset+32<=head_lengths ats 0`,
        `window_member_head_size infos=head_lengths ats 0`,
        `Abbrev (head_bytes = _)`,`Abbrev (head_offset = _)`,
        `Abbrev (tail_bytes = _)`,`Abbrev (tail_offset = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     mp_tac (Q.INST [`hl` |-> `window_member_head_size infos`]
       window_structural_member_prefix_layout) >>
     (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> decide_tac)) >>
     simp_tac bool_ss [Abbr `head_bytes`,Abbr `head_offset`,
       Abbr `tail_bytes`,Abbr `tail_offset`,window_member_tail_def] >>
     rpt strip_tac >> decide_tac) >>
  `window_phase ctx func dyn_ready child_end sites
    [(d+head_offset,32);(d+tail_offset,child_size)] dyn_actual child_actual` by
    (mp_tac (Q.INST
       [`st` |-> `dyn_ready`,`mid` |-> `body_end`,`en` |-> `child_end`,
        `left` |-> `window_alloca_sites func (frag_ids dyn_ready body_end)`,
        `left_out` |-> `[(d+tail_offset,child_size)]`,
        `right` |-> `{site}`,`right_out` |-> `[(d+head_offset,32)]`,
        `ids` |-> `sites`,
        `outs` |-> `[(d+head_offset,32);(d+tail_offset,child_size)]`,
        `s` |-> `dyn_actual`,`t` |-> `body_actual`,`u` |-> `child_actual`]
       window_phase_chain) >>
     (impl_tac >-
       (simp_tac (srw_ss()) [NoAsms,EVERY_DEF,INSERT_SUBSET,EMPTY_SUBSET] >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `abi_encoder_registered_effect sites
    [(d+head_offset,32);(d+tail_offset,child_size)] dyn_actual child_actual /\
   window_alloca_growth dyn_actual child_actual` by
    (qpat_assum `window_phase ctx func dyn_ready child_end sites _
       dyn_actual child_actual` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_phase_def]) >>
  `d+head_bytes k<=dyn_actual.vs_alloca_next /\
   d+window_member_tail infos ats avs k<=dyn_actual.vs_alloca_next` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`d+encoded_size<=dyn_actual.vs_alloca_next`,
        `head_bytes k=head_offset`,`head_offset+32<=encoded_size`,
        `tail_offset<=encoded_size`,`Abbrev (tail_offset = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [markerTheory.Abbrev_def] >> decide_tac) >>
  `window_member_prefix infos ats avs k d child_actual.vs_memory` by
    (mp_tac (Q.INST [`s` |-> `dyn_actual`,`t` |-> `child_actual`,
       `ids` |-> `sites`,
       `outs` |-> `[(d+head_offset,32);(d+tail_offset,child_size)]`]
       window_member_prefix_frame) >>
     (impl_tac >-
       (map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac
          [GSYM (BETA_RULE (AP_THM
            (REWRITE_RULE [markerTheory.Abbrev_def] th) ``k:num``))]))
          [`Abbrev (head_bytes = _)`,`Abbrev (tail_bytes = _)`] >>
        simp_tac bool_ss [EVERY_DEF] >> rpt conj_tac >>
        FIRST [first_assum ACCEPT_TAC,
          (map_every (fn pat => qpat_assum pat mp_tac)
             [`head_bytes k=head_offset`,
              `tail_offset=window_member_head_size infos+tail_bytes k`,
              `head_offset+32<=window_member_head_size infos`] >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [regions_disjoint_def] >> decide_tac),
          (rpt gen_tac >> strip_tac >>
           qpat_assum `!id b sz. id IN sites /\ FLOOKUP dyn_actual.vs_allocas id=_
             ==> sz=32 /\ _` (qspecl_then [`i`,`b`,`sz`] mp_tac) >>
           (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
           disch_then (mp_tac o CONJUNCT2 o CONJUNCT2) >>
           qpat_assum `head_bytes k=head_offset` mp_tac >>
           qpat_assum `head_offset+32<=encoded_size` mp_tac >>
           qpat_assum `tail_offset<=encoded_size` mp_tac >>
           qpat_assum `tail_offset=window_member_head_size infos+tail_bytes k` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [regions_disjoint_def] >> decide_tac)])) >>
     disch_then ACCEPT_TAC) >>
  `mem_bytes_at (d+tail_offset) child_size child_actual.vs_memory=
     enc (EL k ats) (EL k avs)` by
    (`mem_bytes_at (d+tail_offset) child_size child_actual.vs_memory=
      mem_bytes_at (d+tail_offset) child_size body_actual.vs_memory` by
       (mp_tac (Q.INST [`ids` |-> `{site}`, `outs` |-> `[(d+head_offset,32)]`,
          `s` |-> `body_actual`, `t` |-> `child_actual`,
          `p` |-> `d+tail_offset`, `n` |-> `child_size`]
          abi_encoder_window_effect_bytes) >>
        (impl_tac >- (conj_tac
         >- (qpat_assum `window_phase ctx func body_end child_end {site}
               [(d+head_offset,32)] body_actual child_actual`
               (ACCEPT_TAC o MATCH_MP window_phase_effect)) >>
         conj_tac
         >- (map_every (fn pat => qpat_assum pat mp_tac)
               [`head_offset+32<=window_member_head_size infos`,
                `tail_offset=window_member_head_size infos+tail_bytes k`] >>
             POP_ASSUM_LIST (K ALL_TAC) >>
             simp_tac (srw_ss()) [EVERY_DEF,regions_disjoint_def] >> decide_tac) >>
         `regions_disjoint (d,encoded_size) (slot,32)` by
           (qpat_assum `!id b sz. id IN sites /\ FLOOKUP body_actual.vs_allocas id=_
              ==> regions_disjoint (d,encoded_size) (b,sz)`
              (qspecl_then [`site`,`slot`,`32`] MATCH_MP_TAC) >>
            conj_tac >> first_assum ACCEPT_TAC) >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`FLOOKUP child_actual.vs_allocas site=SOME (slot,32)`,
            `regions_disjoint (d,encoded_size) (slot,32)`,
            `tail_offset+child_size<=encoded_size`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> rpt gen_tac >> strip_tac >>
         full_simp_tac (srw_ss()) [IN_SING] >> gvs[] >>
         full_simp_tac bool_ss [regions_disjoint_def] >> decide_tac)) >>
        disch_then ACCEPT_TAC) >>
     qpat_assum `mem_bytes_at (d+tail_offset) child_size child_actual.vs_memory=_`
       (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  `window_member_prefix infos ats avs (SUC k) d child_actual.vs_memory` by
    (mp_tac (Q.INST [`mem` |-> `child_actual.vs_memory`]
       window_structural_member_prefix_dynamic_step) >>
     (impl_tac >-
       (map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac
          [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]))
          [`Abbrev (head_offset = _)`,`Abbrev (tail_offset = _)`,
           `Abbrev (child_size = _)`] >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  suspend "member_dynamic_suffix_clean"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_dynamic_suffix_clean]:
  `head_bytes (SUC k)=head_offset+32` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LIST_REL abi_encoder_structural_valid ats avs`, `k<LENGTH ats`,
        `is_dynamic (EL k ats)`, `Abbrev (head_bytes = _)`,
        `Abbrev (head_offset = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     `SUC k<=LENGTH ats` by decide_tac >>
     mp_tac (Q.INST [`hl` |-> `window_member_head_size infos`, `k` |-> `SUC k`]
       window_structural_member_prefix_layout) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (mp_tac o CONJUNCT2) >>
     qpat_assum `is_dynamic (EL k ats)` mp_tac >>
     qpat_assum `k<LENGTH ats` mp_tac >>
     rpt disch_tac >>
     asm_simp_tac (srw_ss()) [Abbr `head_bytes`, Abbr `head_offset`,
       TAKE_SUC,TAKE1_DROP,MAP_APPEND,SUM_APPEND,
       abiDecodeRangesTheory.abi_member_head_size_def]) >>
  `tail_bytes (SUC k)=tail_bytes k+child_size` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH ats=LENGTH avs`, `k<LENGTH ats`, `is_dynamic (EL k ats)`,
        `Abbrev (tail_bytes = _)`, `Abbrev (child_size = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     mp_tac window_member_tail_step >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
     qpat_assum `is_dynamic (EL k ats)` (fn pos =>
       qpat_x_assum `window_member_tail infos ats avs (SUC k) = _`
         (mp_tac o REWRITE_RULE [pos])) >>
     simp_tac bool_ss [window_member_tail_def, Abbr `tail_bytes`, Abbr `child_size`] >>
     decide_tac) >>
  `!i. (d<=i /\ i<d+head_bytes k) \/
    (d+window_member_head_size infos<=i /\
      i<d+window_member_head_size infos+tail_bytes k) ==> i NOTIN tb.t_mem` by
    (gen_tac >> disch_tac >>
     SUBGOAL_THEN ``d<=i /\ i<d+encoded_size /\
       (i<d+tail_offset \/ d+tail_offset+child_size<=i)``
       (fn th => ASSUME_TAC (CONJUNCT1 th) >>
         ASSUME_TAC (CONJUNCT1 (CONJUNCT2 th)) >>
         ASSUME_TAC (CONJUNCT2 (CONJUNCT2 th)))
     >-        (map_every (fn pat => qpat_assum pat mp_tac)
          [`(d<=i /\ i<d+head_bytes k) \/ _`,
           `head_bytes k=head_offset`,`head_offset+32<=encoded_size`,
           `head_offset+32<=window_member_head_size infos`,
           `tail_offset=window_member_head_size infos+tail_bytes k`,
           `tail_offset<=encoded_size`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     `i IN tb.t_mem <=> i IN tp.t_mem` by
       (qpat_assum `!i. (i<d+tail_offset \/ d+tail_offset+_<=i) /\ _ ==>
          (i IN tb.t_mem <=> i IN tp.t_mem)` (qspec_then `i` MATCH_MP_TAC) >>
        conj_tac >-
          (qpat_assum `Abbrev (child_size = _)` (fn th => pure_rewrite_tac
             [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
           first_assum ACCEPT_TAC) >>
        rpt gen_tac >> strip_tac >>
        `id IN sites` by
          (qpat_assum `window_alloca_sites func (frag_ids dyn_ready body_end)
             SUBSET sites` mp_tac >>
           qpat_assum `id IN window_alloca_sites func (frag_ids dyn_ready body_end)`
             mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [SUBSET_DEF] >> metis_tac[]) >>
        `regions_disjoint (d,encoded_size) (b,sz)` by
          (qpat_assum `!id b sz. id IN sites /\ FLOOKUP body_actual.vs_allocas id=_
             ==> regions_disjoint (d,encoded_size) (b,sz)`
             (qspecl_then [`id`,`b`,`sz`] MATCH_MP_TAC) >>
           conj_tac >> first_assum ACCEPT_TAC) >>
        qpat_assum `regions_disjoint (d,encoded_size) (b,sz)` mp_tac >>
        qpat_assum `d<=i` mp_tac >> qpat_assum `i<d+encoded_size` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`i IN tb.t_mem <=> i IN tp.t_mem`,
        `!i. (d<=i /\ i<d+head_bytes k) \/ _ ==> i NOTIN tu.t_mem`,
        `(d<=i /\ i<d+head_bytes k) \/ _`,
        `tp.t_mem=ts.t_mem`,`ts.t_mem=tu.t_mem`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!i. (d<=i /\ i<d+head_bytes (SUC k)) \/
    (d+window_member_head_size infos<=i /\
      i<d+window_member_head_size infos+tail_bytes (SUC k)) ==>
    ((d<=i /\ i<d+head_bytes k) \/
     (d+window_member_head_size infos<=i /\
       i<d+window_member_head_size infos+tail_bytes k)) \/
    (d+head_offset<=i /\ i<d+head_offset+32) \/
    (d+tail_offset<=i /\ i<d+tail_offset+child_size)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`head_bytes (SUC k)=head_offset+32`,
        `tail_bytes (SUC k)=tail_bytes k+child_size`,
        `head_bytes k=head_offset`,
        `tail_offset=window_member_head_size infos+tail_bytes k`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!i. (d<=i /\ i<d+head_bytes (SUC k)) \/
    (d+window_member_head_size infos<=i /\
      i<d+window_member_head_size infos+tail_bytes (SUC k)) ==> i NOTIN tc.t_mem` by
    (qpat_assum `!i. (d<=i /\ i<d+head_bytes k) \/ _ ==> i NOTIN tb.t_mem` mp_tac >>
     qpat_assum `!i. d+tail_offset<=i /\ i<d+tail_offset+_ ==> i NOTIN tb.t_mem` mp_tac >>
     qpat_assum `tc.t_mem=tb.t_mem DIFF _` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`head_bytes (SUC k)=head_offset+32`,
        `tail_bytes (SUC k)=tail_bytes k+child_size`,
        `head_bytes k=head_offset`,
        `tail_offset=window_member_head_size infos+tail_bytes k`,
        `Abbrev (child_size = _)`,
        `!i. (d<=i /\ i<d+head_bytes (SUC k)) \/ _ ==> _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     qpat_assum `Abbrev (child_size = _)` (fn th =>
       RULE_ASSUM_TAC (REWRITE_RULE
         [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])) >>
     qpat_assum `tc.t_mem=tb.t_mem DIFF _` (fn th =>
       pure_rewrite_tac[th,IN_DIFF,IN_UNION,GSPECIFICATION]) >>
     RULE_ASSUM_TAC (REWRITE_RULE [ADD_ASSOC]) >> pure_rewrite_tac[ADD_ASSOC] >>
     simp_tac (srw_ss()) [NoAsms] >> metis_tac[]) >>
  suspend "member_dynamic_suffix_source"
QED

(* Source and global phase/frame follow in a separate bounded block, so
   source proof does not unfold prefix-layout arithmetic or recursive IH. *)

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_dynamic_suffix_source]:
  `abi_encoder_registered_effect {site} [(d+head_offset,32)]
    body_actual child_actual` by
    (irule window_phase_effect >> goal_assum (drule_at Any)) >>
  `regions_disjoint (d,encoded_size) (slot,32)` by
    (qpat_assum `!id b sz. id IN sites /\ FLOOKUP body_actual.vs_allocas id=_
       ==> regions_disjoint (d,encoded_size) (b,sz)`
       (qspecl_then [`site`,`slot`,`32`] MATCH_MP_TAC) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `0<cap ==> regions_disjoint (sb,cap) (slot,32) /\
    regions_disjoint (sb,cap) (d+head_offset,32)` by
    (strip_tac >> conj_tac
     >- (qpat_assum `0<cap ==> !id b sz. id IN sites /\ _ ==>
          regions_disjoint (sb,cap) (b,sz)` mp_tac >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         disch_then (qspecl_then [`site`,`slot`,`32`] MATCH_MP_TAC) >>
         conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `0<cap ==> sb+cap<=u.vs_alloca_next /\ _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o CONJUNCT1 o CONJUNCT2) >>
     qpat_assum `head_offset+32<=encoded_size` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at sb cap child_actual.vs_memory=
    mem_bytes_at sb cap body_actual.vs_memory` by
    (Cases_on `cap=0`
     >- (qpat_x_assum `cap=0` SUBST_ALL_TAC >> simp_tac (srw_ss()) [NoAsms,mem_bytes_at_def]) >>
     `0<cap` by decide_tac >>
     qpat_assum `0<cap ==> regions_disjoint (sb,cap) (slot,32) /\ _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then strip_assume_tac >>
     mp_tac (Q.INST [`ids` |-> `{site}`, `outs` |-> `[(d+head_offset,32)]`,
       `s` |-> `body_actual`, `t` |-> `child_actual`, `p` |-> `sb`, `n` |-> `cap`]
       abi_encoder_window_effect_bytes) >>
     (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> conj_tac
      >- (simp_tac (srw_ss()) [NoAsms,EVERY_DEF] >> first_assum ACCEPT_TAC) >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`FLOOKUP child_actual.vs_allocas site=SOME (slot,32)`,
         `regions_disjoint (sb,cap) (slot,32)`] >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> rpt gen_tac >> strip_tac >>
      gvs[IN_SING])) >> disch_then ACCEPT_TAC) >>
  `mem_bytes_at sb cap child_actual.vs_memory=mem_bytes_at sb cap s.vs_memory` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`mem_bytes_at sb cap child_actual.vs_memory=mem_bytes_at sb cap body_actual.vs_memory`,
        `mem_bytes_at sb cap body_actual.vs_memory=mem_bytes_at sb cap dyn_actual.vs_memory`,
        `dyn_actual.vs_memory=us.vs_memory`,`us.vs_memory=u.vs_memory`,
        `mem_bytes_at sb cap u.vs_memory=mem_bytes_at sb cap s.vs_memory`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
  `!i. i<cap ==> (sb+i IN tc.t_mem <=> sb+i IN tn.t_mem)` by
    (gen_tac >> strip_tac >>
     `regions_disjoint (sb,cap) (slot,32) /\
      regions_disjoint (sb,cap) (d+head_offset,32)` by
       (qpat_assum `0<cap ==> regions_disjoint (sb,cap) (slot,32) /\ _`
          MATCH_MP_TAC >> decide_tac) >>
     `~(slot<=sb+i /\ sb+i<slot+32) /\
      ~(d+head_offset<=sb+i /\ sb+i<d+head_offset+32)` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`regions_disjoint (sb,cap) (slot,32)`,
           `regions_disjoint (sb,cap) (d+head_offset,32)`, `i<cap`] >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
     qpat_assum `!i. i<cap ==> (sb+i IN tb.t_mem <=> sb+i IN tn.t_mem)`
       (qspec_then `i` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
     qpat_assum `tc.t_mem=tb.t_mem DIFF _` (fn th =>
       pure_rewrite_tac[th,IN_DIFF,IN_UNION,GSPECIFICATION]) >>
     simp_tac (srw_ss()) [NoAsms] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`sb+i IN tb.t_mem <=> sb+i IN tn.t_mem`,
        `~(slot<=sb+i /\ sb+i<slot+32)`,
        `~(d+head_offset<=sb+i /\ sb+i<d+head_offset+32)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> tautLib.TAUT_TAC) >>
  suspend "member_dynamic_suffix_phase"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_dynamic_suffix_phase]:
  `window_phase ctx func dyn_ready child_end sites [(d,encoded_size)]
    dyn_actual child_actual` by
    (mp_tac (Q.INST [`st` |-> `dyn_ready`,`en` |-> `child_end`,
       `ids` |-> `sites`,`more` |-> `sites`,
       `outs` |-> `[(d+head_offset,32);(d+tail_offset,child_size)]`,
       `wider` |-> `[(d,encoded_size)]`,
       `s` |-> `dyn_actual`,`t` |-> `child_actual`] window_phase_enlarge) >>
     (impl_tac >-
       (simp_tac (srw_ss()) [NoAsms,SUBSET_REFL,EVERY_DEF] >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qpat_assum `head_offset+32<=encoded_size` mp_tac >>
        qpat_assum `tail_offset+child_size<=encoded_size` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)) >> disch_then ACCEPT_TAC) >>
  `window_phase ctx func current dyn_ready sites [(d,encoded_size)] u dyn_actual` by
    (mp_tac (Q.INST [`st` |-> `current`,`mid` |-> `prepared`,`en` |-> `dyn_ready`,
       `left` |-> `sites`,`left_out` |-> `[(d,encoded_size)]`,
       `right` |-> `{}`,`right_out` |-> `[]`,
       `ids` |-> `sites`,`outs` |-> `[(d,encoded_size)]`,
       `s` |-> `u`,`t` |-> `us`,`u` |-> `dyn_actual`] window_phase_chain) >>
     (impl_tac >- (simp_tac (srw_ss()) [NoAsms,SUBSET_REFL,EMPTY_SUBSET,EVERY_DEF] >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `current.cs_next_var<=dyn_ready.cs_next_var` by
    (qpat_assum `current.cs_next_var<=prepared.cs_next_var` mp_tac >>
     qpat_assum `dyn_ready.cs_next_var=prepared.cs_next_var+3` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `window_phase ctx func current child_end sites [(d,encoded_size)] u child_actual` by
    (mp_tac (Q.INST [`st` |-> `current`,`mid` |-> `dyn_ready`,`en` |-> `child_end`,
       `left` |-> `sites`,`right` |-> `sites`,
       `left_out` |-> `[(d,encoded_size)]`,`right_out` |-> `[(d,encoded_size)]`,
       `ids` |-> `sites`,`outs` |-> `[(d,encoded_size)]`,
       `s` |-> `u`,`t` |-> `dyn_actual`,`u` |-> `child_actual`] window_phase_chain) >>
     (impl_tac >- (simp_tac (srw_ss()) [NoAsms,SUBSET_REFL] >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `abi_encode_exec_frame func u child_actual` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `us` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule abi_encode_exec_frame_trans >> qexists_tac `dyn_actual` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule abi_encode_exec_frame_trans >> qexists_tac `body_actual` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "member_dynamic_root_state"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_dynamic_root_state]:
  `current.cs_next_var <= prepared.cs_next_var /\
   current.cs_next_var <= dyn_ready.cs_next_var /\
   current.cs_next_var <= body_end.cs_next_var /\
   current.cs_next_var <= child_end.cs_next_var` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`prepared.cs_next_var=current.cs_next_var+1`,
        `dyn_ready.cs_next_var=prepared.cs_next_var+3`,
        `dyn_ready.cs_next_var<=body_end.cs_next_var`,
        `body_end.cs_next_var+1=child_end.cs_next_var`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `!x. not_fresh_at current x ==> FLOOKUP Gc x=FLOOKUP Gu x /\
    op_taint tc (Var x)=op_taint tu (Var x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. not_fresh_at current x ==> lookup_var x us = _ /\ _`,
        `!x. not_fresh_at prepared x ==> lookup_var x dyn_actual = _ /\ _`,
        `!x. not_fresh_at dyn_ready x ==> FLOOKUP Gb x=FLOOKUP Gp x /\ _`,
        `!x. not_fresh_at body_end x ==> FLOOKUP Gc x=FLOOKUP Gb x /\ _`,
        `current.cs_next_var<=prepared.cs_next_var`,
        `current.cs_next_var<=dyn_ready.cs_next_var`,
        `current.cs_next_var<=body_end.cs_next_var`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gen_tac >> strip_tac >>
     `not_fresh_at prepared x /\ not_fresh_at dyn_ready x /\
      not_fresh_at body_end x` by metis_tac[not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at current x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at prepared x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at dyn_ready x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at body_end x ==> _` (qspec_then `x` mp_tac) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  suspend "member_dynamic_root_operands"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_dynamic_root_operands]:
  `alloca_inv child_actual /\ alloca_room ctx func child_actual /\
   window_alloca_growth u child_actual /\ ~child_actual.vs_halted /\
   child_actual.vs_current_bb=child_end.cs_current_bb /\
   child_actual.vs_inst_idx=LENGTH child_end.cs_current_insts` by
    (qpat_assum `window_phase ctx func current child_end sites _ u child_actual`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_phase_def]) >>
  `!x. src=Var x \/ dst=Var x ==> not_fresh_at child_end x` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. src=Var x \/ dst=Var x ==> not_fresh_at current x`,
        `current.cs_next_var<=child_end.cs_next_var`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[not_fresh_at_mono]) >>
  `eval_operand src child_actual=SOME (n2w sb)` by
    (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`,
       `st` |-> `current`, `en` |-> `child_end`, `ids` |-> `sites`,
       `outs` |-> `[(d,encoded_size)]`, `s` |-> `u`, `t` |-> `child_actual`,
       `op` |-> `src`, `w` |-> `n2w sb`] window_phase_operand) >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       gen_tac >> strip_tac >>
       qpat_assum `!x. src=Var x \/ dst=Var x ==> not_fresh_at current x`
         (qspec_then `x` MATCH_MP_TAC) >> disj1_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `eval_operand dst child_actual=SOME (n2w d)` by
    (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`,
       `st` |-> `current`, `en` |-> `child_end`, `ids` |-> `sites`,
       `outs` |-> `[(d,encoded_size)]`, `s` |-> `u`, `t` |-> `child_actual`,
       `op` |-> `dst`, `w` |-> `n2w d`] window_phase_operand) >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       gen_tac >> strip_tac >>
       qpat_assum `!x. src=Var x \/ dst=Var x ==> not_fresh_at current x`
         (qspec_then `x` MATCH_MP_TAC) >> disj2_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `op_taint tc src={} /\ op_taint tc dst={}` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. not_fresh_at current x ==> FLOOKUP Gc x=FLOOKUP Gu x /\ _`,
        `!x. src=Var x \/ dst=Var x ==> not_fresh_at current x`,
        `op_taint tu src={}`,`op_taint tu dst={}`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> conj_tac
     >- (Cases_on `src` >> simp[op_taint_def] >> metis_tac[]) >>
     Cases_on `dst` >> simp[op_taint_def] >> metis_tac[]) >>
  `!p n. not_fresh_at current p /\ ptr_covers Gu tu p u n ==>
    ptr_covers Gc tc p child_actual n` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. not_fresh_at current x ==> FLOOKUP Gc x=FLOOKUP Gu x /\ _`,
        `window_phase ctx func current child_end sites _ u child_actual`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     metis_tac[ptr_covers_def,window_phase_vars]) >>
  `d+encoded_size<=child_actual.vs_alloca_next` by
    (qpat_assum `d+encoded_size<=u.vs_alloca_next` mp_tac >>
     qpat_assum `window_alloca_growth u child_actual`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [window_alloca_growth_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `0<cap ==> sb+cap<=child_actual.vs_alloca_next /\
    regions_disjoint (sb,cap) (d,encoded_size) /\
    ?p. src=Var p /\ ptr_covers Gc tc p child_actual cap` by
    (strip_tac >>
     qpat_assum `0<cap ==> sb+cap<=u.vs_alloca_next /\ _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then strip_assume_tac >>
     `not_fresh_at current p` by
       (qpat_assum `!x. src=Var x \/ dst=Var x ==> not_fresh_at current x`
          (qspec_then `p` MATCH_MP_TAC) >> disj1_tac >> first_assum ACCEPT_TAC) >>
     `ptr_covers Gc tc p child_actual cap` by
       (qpat_assum `!p n. not_fresh_at current p /\ ptr_covers Gu tu p u n ==> _`
          (qspecl_then [`p`,`cap`] MATCH_MP_TAC) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     `sb+cap<=child_actual.vs_alloca_next` by
       (qpat_assum `sb+cap<=u.vs_alloca_next` mp_tac >>
        qpat_assum `window_alloca_growth u child_actual`
          (mp_tac o CONJUNCT1 o REWRITE_RULE [window_alloca_growth_def]) >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexists_tac `p` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `0<encoded_size ==> ?p. dst=Var p /\
    ptr_covers Gc tc p child_actual encoded_size` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`0<encoded_size ==> ?p. dst=Var p /\ ptr_covers Gu tu p u encoded_size`,
        `!x. src=Var x \/ dst=Var x ==> not_fresh_at current x`,
        `!p n. not_fresh_at current p /\ ptr_covers Gu tu p u n ==> _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `window_member_tail infos ats avs (SUC k)=tail_offset+child_size` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH ats=LENGTH avs`,`k<LENGTH ats`,`is_dynamic (EL k ats)`,
        `Abbrev (tail_offset = _)`,`Abbrev (child_size = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     mp_tac window_member_tail_step >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     asm_simp_tac bool_ss [Abbr `tail_offset`,Abbr `child_size`]) >>
  `EXISTS (\(_,_,_,flag). flag) infos ==>
    site IN sites /\ site<child_end.cs_next_id /\
    (?p. dp=Var p /\ not_fresh_at child_end p /\
      ptr_covers Gc tc p child_actual 32) /\
    eval_operand dp child_actual=SOME (n2w slot) /\
    FLOOKUP child_actual.vs_allocas site=SOME (slot,32) /\
    slot+32<=child_actual.vs_alloca_next /\
    mem_word_at slot child_actual.vs_memory=
      n2w (window_member_tail infos ats avs (SUC k)) /\
    (!i. slot<=i /\ i<slot+32 ==> i NOTIN tc.t_mem)` by
    (strip_tac >>
     `site<child_end.cs_next_id` by
       (qpat_assum `site<current.cs_next_id` mp_tac >>
        qpat_assum `prepared.cs_next_id=current.cs_next_id+1` mp_tac >>
        qpat_assum `prepared.cs_next_id<=child_end.cs_next_id` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     `not_fresh_at child_end cursor_var` by
       (qpat_assum `not_fresh_at current cursor_var` mp_tac >>
        qpat_assum `current.cs_next_var<=child_end.cs_next_var` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[not_fresh_at_mono]) >>
     `ptr_covers Gc tc cursor_var child_actual 32` by
       (qpat_assum `!p n. not_fresh_at current p /\ ptr_covers Gu tu p u n ==> _`
          (qspecl_then [`cursor_var`,`32`] MATCH_MP_TAC) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     `eval_operand dp child_actual=SOME (n2w slot)` by
       (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`,
          `st` |-> `current`, `en` |-> `child_end`, `ids` |-> `sites`,
          `outs` |-> `[(d,encoded_size)]`, `s` |-> `u`, `t` |-> `child_actual`,
          `op` |-> `dp`, `w` |-> `n2w slot`] window_phase_operand) >>
        (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          qpat_assum `dp=Var cursor_var` mp_tac >>
          qpat_assum `not_fresh_at current cursor_var` mp_tac >>
          POP_ASSUM_LIST (K ALL_TAC) >> simp[])) >> disch_then ACCEPT_TAC) >>
     `slot+32<=child_actual.vs_alloca_next` by
       (qpat_assum `slot+32<=u.vs_alloca_next` mp_tac >>
        qpat_assum `window_alloca_growth u child_actual`
          (mp_tac o CONJUNCT1 o REWRITE_RULE [window_alloca_growth_def]) >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     `mem_word_at slot child_actual.vs_memory=
       n2w (window_member_tail infos ats avs (SUC k))` by
       (qpat_assum `mem_word_at slot child_actual.vs_memory=n2w (tail_offset+child_size)`
          mp_tac >>
        qpat_assum `window_member_tail infos ats avs (SUC k)=_` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
     `!i. slot<=i /\ i<slot+32 ==> i NOTIN tc.t_mem` by
       (qpat_assum `tc.t_mem=tb.t_mem DIFF _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac (srw_ss()) [IN_DIFF,IN_UNION,GSPECIFICATION]) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       (qexists_tac `cursor_var` >> rpt conj_tac >> first_assum ACCEPT_TAC)]) >>
  suspend "member_dynamic_classifier"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_dynamic_classifier]:
  `abi_encoder_registered_effect {site} [(d+head_offset,32)]
    body_actual child_actual /\ window_alloca_growth body_actual child_actual` by
    (qpat_assum `window_phase ctx func body_end child_end {site} _
       body_actual child_actual` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_phase_def]) >>
  `!id r. FLOOKUP body_actual.vs_allocas id=SOME r ==>
    FLOOKUP child_actual.vs_allocas id=SOME r` by
    (qpat_assum `abi_encoder_registered_effect {site} _ body_actual child_actual`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [abi_encoder_registered_effect_def]) >>
  `!id b sz. id IN sites /\ FLOOKUP child_actual.vs_allocas id=SOME (b,sz) ==>
    sz=32` by
    (mp_tac (Q.INST [`R` |-> `sites`, `ids` |-> `{site}`,
       `outs` |-> `[(d+head_offset,32)]`, `s` |-> `body_actual`, `t` |-> `child_actual`]
       window_registered_sizes_transport) >>
     (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> conj_tac
      >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> strip_tac >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`FLOOKUP child_actual.vs_allocas site=SOME (slot,32)`,
         `id IN {site}`, `FLOOKUP child_actual.vs_allocas id=SOME (b,sz)`] >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gvs[IN_SING])) >>
     disch_then ACCEPT_TAC) >>
  `!id b sz. id IN sites /\ FLOOKUP child_actual.vs_allocas id=SOME (b,sz) ==>
    regions_disjoint (d,encoded_size) (b,sz)` by
    (mp_tac (Q.INST [`ids` |-> `sites`, `q` |-> `d`, `n` |-> `encoded_size`,
       `s` |-> `body_actual`, `t` |-> `child_actual`] window_alloca_growth_protected) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `0<cap ==> !id b sz. id IN sites /\
    FLOOKUP child_actual.vs_allocas id=SOME (b,sz) ==>
    regions_disjoint (sb,cap) (b,sz)` by
    (strip_tac >>
     `sb+cap<=body_actual.vs_alloca_next` by
       (qpat_assum `0<cap ==> sb+cap<=dyn_actual.vs_alloca_next` mp_tac >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        qpat_assum `window_alloca_growth dyn_actual body_actual`
          (mp_tac o CONJUNCT1 o REWRITE_RULE [window_alloca_growth_def]) >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     `!id b sz. id IN sites /\ FLOOKUP body_actual.vs_allocas id=SOME (b,sz) ==>
        regions_disjoint (sb,cap) (b,sz)` by
       (qpat_assum `0<cap ==> !id b sz. id IN sites /\ _ ==> _`
          MATCH_MP_TAC >> first_assum ACCEPT_TAC) >>
     mp_tac (Q.INST [`ids` |-> `sites`, `q` |-> `sb`, `n` |-> `cap`,
       `s` |-> `body_actual`, `t` |-> `child_actual`] window_alloca_growth_protected) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `!id b sz. id IN sites /\ FLOOKUP child_actual.vs_allocas id=SOME (b,sz) ==>
    sz=32 /\ (0<cap ==> regions_disjoint (sb,cap) (b,sz)) /\
    regions_disjoint (d,encoded_size) (b,sz)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!id b sz. id IN sites /\ FLOOKUP child_actual.vs_allocas id=_ ==> sz=32`,
        `!id b sz. id IN sites /\ FLOOKUP child_actual.vs_allocas id=_ ==>
          regions_disjoint (d,encoded_size) (b,sz)`,
        `0<cap ==> !id b sz. id IN sites /\
          FLOOKUP child_actual.vs_allocas id=_ ==> regions_disjoint (sb,cap) (b,sz)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  suspend "member_dynamic_tail"
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[member_dynamic_tail]:
  `!i. (i<d \/ d+encoded_size<=i) /\
    (!id b sz. id IN sites /\ FLOOKUP child_actual.vs_allocas id=SOME (b,sz) ==>
      i<b \/ b+sz<=i) ==> (i IN tc.t_mem <=> i IN tu.t_mem)` by
    (gen_tac >> disch_then (fn th => ASSUME_TAC (CONJUNCT1 th) >>
       ASSUME_TAC (CONJUNCT2 th)) >>
     SUBGOAL_THEN ``i<d+tail_offset \/ d+tail_offset+child_size<=i`` ASSUME_TAC
     >- (qpat_assum `i<d \/ d+encoded_size<=i` mp_tac >>
         qpat_assum `tail_offset+child_size<=encoded_size` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     `i IN tb.t_mem <=> i IN tp.t_mem` by
       (qpat_assum `!i. (i<d+tail_offset \/ d+tail_offset+_<=i) /\ _ ==>
          (i IN tb.t_mem <=> i IN tp.t_mem)` (qspec_then `i` MATCH_MP_TAC) >>
        conj_tac
        >- (qpat_assum `Abbrev (child_size = _)` (fn th => pure_rewrite_tac
             [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
            first_assum ACCEPT_TAC) >>
        rpt gen_tac >> strip_tac >>
        `id IN sites` by
          (qpat_assum `window_alloca_sites func (frag_ids dyn_ready body_end) SUBSET sites`
             mp_tac >>
           qpat_assum `id IN window_alloca_sites func (frag_ids dyn_ready body_end)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [SUBSET_DEF] >> metis_tac[]) >>
        `FLOOKUP child_actual.vs_allocas id=SOME (b,sz)` by
          (qpat_assum `!id r. FLOOKUP body_actual.vs_allocas id=SOME r ==> _`
             (qspecl_then [`id`,`(b,sz)`] MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
        qpat_assum `!id b sz. id IN sites /\ FLOOKUP child_actual.vs_allocas id=_ ==> _`
          (qspecl_then [`id`,`b`,`sz`] MATCH_MP_TAC) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     SUBGOAL_THEN ``i<slot \/ slot+32<=i`` ASSUME_TAC
     >- (qpat_assum `!id b sz. id IN sites /\ FLOOKUP child_actual.vs_allocas id=_ ==> _`
           (qspecl_then [`site`,`slot`,`32`] MATCH_MP_TAC) >>
         conj_tac >> first_assum ACCEPT_TAC) >>
     `~(d+head_offset<=i /\ i<d+head_offset+32) /\
      ~(slot<=i /\ i<slot+32)` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`i<d \/ d+encoded_size<=i`, `head_offset+32<=encoded_size`,
           `i<slot \/ slot+32<=i`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     qpat_assum `tp.t_mem=ts.t_mem` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
     qpat_assum `ts.t_mem=tu.t_mem` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
     qpat_assum `tc.t_mem=tb.t_mem DIFF _` (fn th =>
       pure_rewrite_tac[th,IN_DIFF,IN_UNION,GSPECIFICATION]) >>
     simp_tac (srw_ss()) [NoAsms] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`i IN tb.t_mem <=> i IN tu.t_mem`,
        `~(d+head_offset<=i /\ i<d+head_offset+32)`,
        `~(slot<=i /\ i<slot+32)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> tautLib.TAUT_TAC) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (u,Gu,tu) [] (OK child_actual,Gc,tc)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tu) [] (OK us,Gs,ts)`
       (qspec_then `D` mp_tac) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`us`,`Gs`,`ts`,`[]`,`OK dyn_actual`,`Gp`,`tp`] mp_tac) >>
     (impl_tac >- (conj_tac >- REFL_TAC >>
       qpat_assum `!D. gas_origin_ptr_path _ (us,Gs,ts) [] (OK dyn_actual,Gp,tp)`
         (qspec_then `D` ACCEPT_TAC))) >> simp_tac bool_ss [APPEND] >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then
       [`dyn_actual`,`Gp`,`tp`,`[]`,`OK body_actual`,`Gb`,`tb`] mp_tac) >>
     (impl_tac >- (conj_tac >- REFL_TAC >>
       qpat_assum `!D. gas_origin_ptr_path _ (dyn_actual,Gp,tp) [] (OK body_actual,Gb,tb)`
         (qspec_then `D` ACCEPT_TAC))) >> simp_tac bool_ss [APPEND] >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then
       [`body_actual`,`Gb`,`tb`,`[]`,`OK child_actual`,`Gc`,`tc`] mp_tac) >>
     (impl_tac >- (conj_tac >- REFL_TAC >>
       qpat_assum `!D. gas_origin_ptr_path _ (body_actual,Gb,tb) [] (OK child_actual,Gc,tc)`
         (qspec_then `D` ACCEPT_TAC))) >> simp_tac bool_ss [APPEND]) >>
  `tc.t_stor=tu.t_stor /\ tc.t_trans=tu.t_trans /\ tc.t_imm=tu.t_imm` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`tc.t_stor=tb.t_stor`,`tb.t_stor=tp.t_stor`,`tp.t_stor=ts.t_stor`,`ts.t_stor=tu.t_stor`,
        `tc.t_trans=tb.t_trans`,`tb.t_trans=tp.t_trans`,`tp.t_trans=ts.t_trans`,`ts.t_trans=tu.t_trans`,
        `tc.t_imm=tb.t_imm`,`tb.t_imm=tp.t_imm`,`tp.t_imm=ts.t_imm`,`ts.t_imm=tu.t_imm`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
  `abi_encoder_member_span (TAKE (SUC k) infos)=source_offset+ms /\
   SUM (MAP abi_member_head_size (TAKE (SUC k) ats))=head_offset+az` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`k<LENGTH infos`,`k<LENGTH ats`,`EL k infos=(ei,az,ms,T)`,
        `az=abi_member_head_size (EL k ats)`,
        `Abbrev (source_offset = _)`,`Abbrev (head_offset = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     asm_simp_tac (srw_ss()) [Abbr `source_offset`,Abbr `head_offset`,
       TAKE_SUC,TAKE1_DROP,abi_encoder_member_span_def,SUM_APPEND]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp child_actual /\
    child_actual.vs_alloca_next + pending_alloca_size func child_actual <= w2n child_actual.vs_initial_fmp` by
    (qpat_assum `abi_encode_exec_frame func u child_actual` (fn frame =>
       qpat_assum `alloca_inv child_actual` (fn inv =>
         qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u /\ u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp` (fn bound =>
           ACCEPT_TAC (MATCH_MP window_exec_frame_alloca_budget
             (LIST_CONJ [frame,inv,bound])))))) >>
  `current.cs_next_id<=child_end.cs_next_id` by
    (qpat_assum `prepared.cs_next_id=current.cs_next_id+1` mp_tac >>
     qpat_assum `prepared.cs_next_id<=child_end.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  qpat_x_assum `!k current end_st result u Gu tu dp site slot. _`
    (qspecl_then [`SUC k`,`child_end`,`end_st`,`result`,
      `child_actual`,`Gc`,`tc`,`dp`,`site`,`slot`] mp_tac) >>
  impl_tac
  >- (map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac[th]))
        [`DROP (SUC k) infos=rest`,
         `abi_encoder_member_span (TAKE (SUC k) infos)=source_offset+ms`,
         `SUM (MAP abi_member_head_size (TAKE (SUC k) ats))=head_offset+az`] >>
      rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
        (map_every (fn pat => qpat_assum pat mp_tac)
           [`st.cs_next_var<=current.cs_next_var`,`st.cs_next_id<=current.cs_next_id`,
            `current.cs_next_var<=child_end.cs_next_var`,
            `current.cs_next_id<=child_end.cs_next_id`,`k<LENGTH infos`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)]) >>
  disch_then (qx_choose_then `tail_actual` (qx_choose_then `Gf`
    (qx_choose_then `tf` strip_assume_tac))) >>
  `window_phase ctx func current end_st sites [(d,encoded_size)] u tail_actual` by
    (mp_tac (Q.INST [`st` |-> `current`,`mid` |-> `child_end`,`en` |-> `end_st`,
       `left` |-> `sites`,`right` |-> `sites`,
       `left_out` |-> `[(d,encoded_size)]`,`right_out` |-> `[(d,encoded_size)]`,
       `ids` |-> `sites`,`outs` |-> `[(d,encoded_size)]`,
       `s` |-> `u`,`t` |-> `child_actual`,`u` |-> `tail_actual`] window_phase_chain) >>
     (impl_tac >- (simp_tac bool_ss [SUBSET_REFL] >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `abi_encode_exec_frame func u tail_actual` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `child_actual` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!id r. FLOOKUP child_actual.vs_allocas id=SOME r ==>
    FLOOKUP tail_actual.vs_allocas id=SOME r` by
    (qpat_assum `window_phase ctx func child_end end_st sites _ child_actual tail_actual`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_phase_def,abi_encoder_registered_effect_def]) >>
  `!x. not_fresh_at current x ==> FLOOKUP Gf x=FLOOKUP Gu x /\
    op_taint tf (Var x)=op_taint tu (Var x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. not_fresh_at child_end x ==> FLOOKUP Gf x=_ /\ _`,
        `!x. not_fresh_at current x ==> FLOOKUP Gc x=_ /\ _`,
        `current.cs_next_var<=child_end.cs_next_var`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[not_fresh_at_mono]) >>
  `!i. (i<d \/ d+encoded_size<=i) /\
    (!id b sz. id IN sites /\ FLOOKUP tail_actual.vs_allocas id=SOME (b,sz) ==>
      i<b \/ b+sz<=i) ==> (i IN tf.t_mem <=> i IN tu.t_mem)` by
    (gen_tac >> disch_then (fn th => ASSUME_TAC (CONJUNCT1 th) >>
       ASSUME_TAC (CONJUNCT2 th)) >>
     `i IN tf.t_mem <=> i IN tc.t_mem` by
       (qpat_assum `!i. _ ==> (i IN tf.t_mem <=> i IN tc.t_mem)`
          (qspec_then `i` MATCH_MP_TAC) >> conj_tac >> first_assum ACCEPT_TAC) >>
     `i IN tc.t_mem <=> i IN tu.t_mem` by
       (qpat_assum `!i. _ ==> (i IN tc.t_mem <=> i IN tu.t_mem)`
          (qspec_then `i` MATCH_MP_TAC) >> conj_tac >- first_assum ACCEPT_TAC >>
        rpt gen_tac >> strip_tac >>
        `FLOOKUP tail_actual.vs_allocas id=SOME (b,sz)` by
          (qpat_assum `!id r. FLOOKUP child_actual.vs_allocas id=SOME r ==> _`
             (qspecl_then [`id`,`(b,sz)`] MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
        qpat_assum `!id b sz. id IN sites /\ FLOOKUP tail_actual.vs_allocas id=_ ==> _`
          (qspecl_then [`id`,`b`,`sz`] MATCH_MP_TAC) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `i IN tf.t_mem <=> i IN tc.t_mem` mp_tac >>
     qpat_assum `i IN tc.t_mem <=> i IN tu.t_mem` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `tf.t_stor=tu.t_stor /\ tf.t_trans=tu.t_trans /\ tf.t_imm=tu.t_imm` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`tf.t_stor=tc.t_stor`,`tc.t_stor=tu.t_stor`,
        `tf.t_trans=tc.t_trans`,`tc.t_trans=tu.t_trans`,
        `tf.t_imm=tc.t_imm`,`tc.t_imm=tu.t_imm`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (u,Gu,tu) [] (OK tail_actual,Gf,tf)` by
    (gen_tac >> qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tu) [] (OK child_actual,Gc,tc)`
       (qspec_then `D` mp_tac) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then
       [`child_actual`,`Gc`,`tc`,`[]`,`OK tail_actual`,`Gf`,`tf`] mp_tac) >>
     (impl_tac >- (conj_tac >- REFL_TAC >>
       qpat_assum `!D. gas_origin_ptr_path _ (child_actual,Gc,tc) [] (OK tail_actual,Gf,tf)`
         (qspec_then `D` ACCEPT_TAC))) >> simp_tac bool_ss [APPEND]) >>
  `P ctx func explicit current dyn_ready u dyn_actual` by
    (irule members_payload_comp >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`prepared`,`us`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  `P ctx func explicit current body_end u body_actual` by
    (irule members_payload_comp >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`dyn_ready`,`dyn_actual`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  `P ctx func explicit current child_end u child_actual` by
    (irule members_payload_comp >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`body_end`,`body_actual`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  `P ctx func explicit current end_st u tail_actual` by
    (irule members_payload_comp >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`child_end`,`child_actual`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`tail_actual`,`Gf`,`tf`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume compile_abi_encode_to_buf_complex_window_joint_payload[parent_dynamic]:
  qpat_x_assum `!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> _` kall_tac >>
  drule_all abi_encoder_complex_dynamic_trace >>
  disch_then (qx_choose_then `dyn_ptr` (qx_choose_then `ready`
    (qx_choose_then `ignored` (qx_choose_then `middle` strip_assume_tac)))) >>
  `?allocated.
    emit_op ALLOCA [Lit 32w] st = (dyn_ptr,allocated) /\
    emit_void MSTORE [dyn_ptr;Lit (n2w (window_member_head_size infos))]
      allocated = ((),ready)` by
    (qpat_assum `abi_encode_complex_prefix infos st = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [abi_encode_complex_prefix_def,
       contextTheory.compile_alloc_buffer_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM,
       GSYM window_member_head_size_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     Cases_on `emit_op ALLOCA [Lit 32w] st` >> gvs[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `ci_mono st allocated /\ ci_mono allocated ready /\
   ci_mono ready middle /\ ci_mono middle en` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`emit_op ALLOCA [Lit 32w] st = _`,
        `emit_void MSTORE _ allocated = _`,
        `compile_abi_encode_complex_elems dst src infos 0 0 dyn_ptr ready = _`,
        `emit_op MLOAD [dyn_ptr] middle = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     metis_tac[ci_mono_emit_op,ci_mono_emit_void,
       cj 3 ci_mono_compile_abi_encode,pairTheory.SND]) >>
  `cs_extends st ready /\ cs_extends ready middle /\
   cs_extends middle en /\
   st.cs_next_var <= ready.cs_next_var /\
   st.cs_next_id <= ready.cs_next_id /\
   ready.cs_next_var <= middle.cs_next_var /\
   ready.cs_next_id <= middle.cs_next_id /\
   middle.cs_next_id <= en.cs_next_id` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ci_mono st allocated`, `ci_mono allocated ready`,
        `ci_mono ready middle`, `ci_mono middle en`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [ci_mono_def] >> rpt strip_tac >>
     metis_tac[cs_extends_trans,LESS_EQ_TRANS]) >>
  `fn_has_code st ready func /\ fn_has_code ready middle func /\
   fn_has_code middle en func` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`fn_has_code st en func`, `cs_extends st ready`,
        `cs_extends ready middle`, `cs_extends middle en`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     metis_tac[fn_has_code_split,cs_extends_trans]) >>
  `st.cs_next_id IN sites` by
    (qpat_assum `emit_op ALLOCA [Lit 32w] st = (dyn_ptr,allocated)`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
     `fn_has_code st allocated func` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`fn_has_code st ready func`,`ci_mono st allocated`,
           `ci_mono allocated ready`] >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [ci_mono_def] >> rpt disch_tac >>
        metis_tac[fn_has_code_split]) >>
     `MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
       (irule exprSimAbiEncodeFramedBuiltinTheory.abi_encode_emitted_instruction_member >>
        qexistsl_tac [`allocated`,`st`] >> asm_rewrite_tac[] >> simp[]) >>
     qpat_assum `MEM (mk_inst st.cs_next_id ALLOCA _ _) (fn_insts func)` mp_tac >>
     qpat_assum `allocated.cs_next_id=st.cs_next_id+1` mp_tac >>
     qpat_assum `ci_mono allocated ready` mp_tac >>
     qpat_assum `ready.cs_next_id<=middle.cs_next_id` mp_tac >>
     qpat_assum `middle.cs_next_id<=en.cs_next_id` mp_tac >>
     qpat_assum `Abbrev (sites = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     simp_tac (srw_ss()) [Abbr `sites`,window_alloca_sites_def,
       abiEncoderPropsTheory.frag_ids_def] >> conj_tac
     >- (fs[ci_mono_def] >> decide_tac) >>
     qexists_tac `mk_inst st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString st.cs_next_var)]` >> simp[mk_inst_def]) >>
  `!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz=32` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = _ ==> _`
       (qspecl_then [`st.cs_next_id`, `b`, `sz`] (fn frame =>
         qpat_assum `st.cs_next_id IN sites` (fn member =>
           qpat_assum `FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz)`
             (ACCEPT_TAC o CONJUNCT1 o MATCH_MP frame o CONJ member))))) >>
  `eval_operand (Lit (n2w (window_member_head_size infos))) s =
      SOME (n2w (window_member_head_size infos)) /\
   op_taint tn (Lit (n2w (window_member_head_size infos))) = {} /\
   (!x. Lit (n2w (window_member_head_size infos)) = Var x ==>
      not_fresh_at st x)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [eval_operand_def,op_taint_def]) >>
  drule_all window_cursor_init_joint >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choose_then `u` (qx_choose_then `slot` (qx_choose_then `p`
      (qx_choose_then `Gu` (qx_choose_then `tu` strip_assume_tac)))))) >>
  `P ctx func explicit st ready s u` by
    (irule members_payload_phase >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       (CHANGED_TAC (pure_rewrite_tac[abi_members_straight_code_def]) >>
        ntac 2 disj2_tac >> disj1_tac >>
        qexistsl_tac [`dyn_ptr`,`Lit (n2w (window_member_head_size infos))`,`allocated`] >>
        conj_tac >> first_assum ACCEPT_TAC),
       (qpat_assum `window_phase ctx func st ready _ [] s u` mp_tac >>
        simp_tac bool_ss [window_phase_def])]) >>
  `abi_encoder_registered_effect {st.cs_next_id} [] s u /\
   window_alloca_growth s u /\ alloca_inv u /\ alloca_room ctx func u /\
   ~u.vs_halted /\ u.vs_current_bb = ready.cs_current_bb /\
   u.vs_inst_idx = LENGTH ready.cs_current_insts` by
    (qpat_assum `window_phase ctx func st ready _ [] s u` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_phase_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp` by
    (qpat_assum `abi_encode_exec_frame func s u` (fn frame =>
       qpat_assum `alloca_inv u` (fn inv =>
         qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s /\ s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp` (fn bound =>
           ACCEPT_TAC (MATCH_MP window_exec_frame_alloca_budget
             (LIST_CONJ [frame,inv,bound])))))) >>
  `!id r. FLOOKUP s.vs_allocas id = SOME r ==>
    FLOOKUP u.vs_allocas id = SOME r` by
    (qpat_assum `abi_encoder_registered_effect _ _ s u` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [abi_encoder_registered_effect_def]) >>
  `!id b sz. id IN sites /\ FLOOKUP u.vs_allocas id = SOME (b,sz) ==>
    sz=32` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`abi_encoder_registered_effect {st.cs_next_id} [] s u`,
        `!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = _ ==> _`,
        `FLOOKUP u.vs_allocas st.cs_next_id = SOME (slot,32)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     mp_tac (Q.INST [`s` |-> `s`, `t` |-> `u`, `R` |-> `sites`,
       `ids` |-> `{st.cs_next_id}`, `outs` |-> `[]`] window_registered_sizes_transport) >>
     (impl_tac >- (rpt conj_tac
       >- first_assum ACCEPT_TAC
       >- metis_tac[]
       >> simp_tac (srw_ss()) [IN_SING] >> rpt strip_tac >> gvs[])) >>
     disch_then MATCH_ACCEPT_TAC) >>
  `!id b sz. id IN sites /\ FLOOKUP u.vs_allocas id = SOME (b,sz) ==>
    regions_disjoint (d,encoded_size) (b,sz)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`window_alloca_growth s u`,
        `!id r. FLOOKUP s.vs_allocas id = SOME r ==> FLOOKUP u.vs_allocas id = SOME r`,
        `d+encoded_size <= s.vs_alloca_next`,
        `!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = _ ==> _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     mp_tac (Q.INST [`s` |-> `s`, `t` |-> `u`, `ids` |-> `sites`,
       `q` |-> `d`, `n` |-> `encoded_size`] window_alloca_growth_protected) >>
     (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >>
     disch_then MATCH_ACCEPT_TAC) >>
  `0 < cap ==> !id b sz. id IN sites /\
    FLOOKUP u.vs_allocas id = SOME (b,sz) ==>
    regions_disjoint (sb,cap) (b,sz)` by
    (strip_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`window_alloca_growth s u`,
        `!id r. FLOOKUP s.vs_allocas id = SOME r ==> FLOOKUP u.vs_allocas id = SOME r`,
        `0 < cap`, `0 < cap ==> _`,
        `!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = _ ==> _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     mp_tac (Q.INST [`s` |-> `s`, `t` |-> `u`, `ids` |-> `sites`,
       `q` |-> `sb`, `n` |-> `cap`] window_alloca_growth_protected) >>
     (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >>
     disch_then MATCH_ACCEPT_TAC) >>
  `mem_bytes_at sb cap u.vs_memory = mem_bytes_at sb cap s.vs_memory` by
    (Cases_on `cap=0`
     >- (qpat_assum `cap=0` (fn th => pure_rewrite_tac [th]) >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [mem_bytes_at_def]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`abi_encoder_registered_effect {st.cs_next_id} [] s u`,
        `window_alloca_growth s u`,
        `0 < cap ==> sb+cap <= s.vs_alloca_next /\ _`, `~(cap=0)`,
        `st.cs_next_id IN sites`,
        `!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = _ ==> _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     mp_tac (Q.INST [`s` |-> `s`, `t` |-> `u`, `q` |-> `sb`, `n` |-> `cap`,
       `ids` |-> `{st.cs_next_id}`, `outs` |-> `[]`] window_alloca_growth_frame) >>
     (impl_tac >- (simp_tac (srw_ss()) [EVERY_DEF,IN_SING] >>
       asm_rewrite_tac[] >> metis_tac[NOT_ZERO_LT_ZERO])) >>
     disch_then ACCEPT_TAC) >>
  `!i. i<cap ==> (sb+i IN tu.t_mem <=> sb+i IN tn.t_mem)` by
    (gen_tac >> strip_tac >>
     `0 < cap` by
       (qpat_assum `i < cap` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     `regions_disjoint (sb,cap) (slot,32)` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`0 < cap ==> !id b sz. id IN sites /\ FLOOKUP u.vs_allocas id = _ ==> _`,
           `0 < cap`, `st.cs_next_id IN sites`,
           `FLOOKUP u.vs_allocas st.cs_next_id = SOME (slot,32)`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
        metis_tac[]) >>
     `~(slot <= sb+i /\ sb+i < slot+32)` by
       (qpat_assum `regions_disjoint (sb,cap) (slot,32)` mp_tac >>
        qpat_assum `i < cap` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`tu.t_mem = _`, `~(slot <= sb+i /\ sb+i < slot+32)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     asm_simp_tac (srw_ss()) [IN_DIFF,GSPECIFICATION]) >>
  `p = STRING #"%" (toString st.cs_next_var)` by
    (qpat_assum `emit_op ALLOCA [Lit 32w] st = _` mp_tac >>
     qpat_assum `dyn_ptr = Var p` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     drule emitted_insts_emit_op >> simp[]) >>
  `!x. not_fresh_at st x ==> p <> x` by
    (gen_tac >> strip_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`not_fresh_at st x`, `p = STRING #"%" (toString st.cs_next_var)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     qpat_assum `not_fresh_at st x`
       (mp_tac o Q.SPEC `st.cs_next_var` o
        REWRITE_RULE [loweringStateRelDefsTheory.not_fresh_at_def]) >>
     asm_rewrite_tac[LESS_EQ_REFL] >> metis_tac[]) >>
  `!x. not_fresh_at st x ==>
    FLOOKUP Gu x = FLOOKUP G x /\
    op_taint tu (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `p<>x` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`p<>x`, `Gu = G |+ (p,(slot,32))`, `tu.t_var = tn.t_var |+ (p,{})`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     asm_simp_tac (srw_ss()) [op_taint_def,FLOOKUP_UPDATE]) >>
  `eval_operand src u = SOME (n2w sb) /\
   eval_operand dst u = SOME (n2w d)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`window_phase ctx func st ready {st.cs_next_id} [] s u`,
        `!x. src = Var x \/ dst = Var x ==> not_fresh_at st x`,
        `eval_operand src s = SOME (n2w sb)`,
        `eval_operand dst s = SOME (n2w d)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     metis_tac[window_phase_operand]) >>
  `op_taint tu src = {} /\ op_taint tu dst = {}` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. not_fresh_at st x ==> FLOOKUP Gu x = _ /\ _`,
        `!x. src = Var x \/ dst = Var x ==> _`,
        `op_taint tn src = {}`,`op_taint tn dst = {}`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `src` >> Cases_on `dst` >>
     fs[op_taint_def] >> metis_tac[]) >>
  `(!x. src=Var x \/ dst=Var x ==> not_fresh_at ready x) /\
   (0<cap ==> ?x. src=Var x /\ ptr_covers Gu tu x u cap) /\
   (0<encoded_size ==> ?x. dst=Var x /\ ptr_covers Gu tu x u encoded_size)` by
    (qpat_x_assum `!remaining k current end_st result u Gu tu dp site slot. _` kall_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. src=Var x \/ dst=Var x ==> not_fresh_at st x`,
        `st.cs_next_var <= ready.cs_next_var`,
        `0 < cap ==> sb+cap <= s.vs_alloca_next /\ _`,
        `0 < encoded_size ==> ?x. dst=Var x /\ _`,
        `!x. not_fresh_at st x ==> FLOOKUP Gu x = _ /\ _`,
        `window_phase ctx func st ready {st.cs_next_id} [] s u`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     rpt conj_tac
     >- (rpt strip_tac >> irule not_fresh_at_mono >>
         qexists_tac `st` >> asm_rewrite_tac[] >>
         qpat_x_assum `!x. src=Var x \/ dst=Var x ==> _` irule >> simp[])
     >> strip_tac >> fs[] >>
     `!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
       lookup_var x u = SOME w` by
       (rpt strip_tac >> irule window_phase_vars >>
        qexistsl_tac [`ctx`,`ready`,`func`,`{st.cs_next_id}`,`[]`,`s`,`st`] >>
        asm_rewrite_tac[]) >>
     fs[ptr_covers_def] >> metis_tac[]) >>
  `window_member_prefix infos ats avs 0 d u.vs_memory` by
    (irule window_member_prefix_zero >> conj_tac >> first_assum ACCEPT_TAC) >>
  `head_bytes 0=0 /\ tail_bytes 0=0` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`Abbrev (head_bytes = _)`,`Abbrev (tail_bytes = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     simp_tac (srw_ss()) [Abbr `head_bytes`,Abbr `tail_bytes`,
       TAKE_0,abi_tuple_heads_def,abi_tuple_tails_def]) >>
  `s.vs_alloca_next <= u.vs_alloca_next` by
    (qpat_assum `window_alloca_growth s u` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_alloca_growth_def]) >>
  `0<cap ==> sb+cap <= u.vs_alloca_next` by
    (strip_tac >>
     qpat_assum `0<cap ==> sb+cap <= s.vs_alloca_next /\ _`
       (mp_tac o CONJUNCT1 o C MATCH_MP (ASSUME ``0<cap``)) >>
     qpat_assum `s.vs_alloca_next <= u.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `d+encoded_size <= u.vs_alloca_next` by
    (qpat_assum `d+encoded_size <= s.vs_alloca_next` mp_tac >>
     qpat_assum `s.vs_alloca_next <= u.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `st.cs_next_id < ready.cs_next_id` by
    (qpat_assum `emit_op ALLOCA [Lit 32w] st = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
     qpat_assum `allocated.cs_next_id = st.cs_next_id+1` mp_tac >>
     qpat_assum `ci_mono allocated ready` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [ci_mono_def] >> rpt strip_tac >> decide_tac) >>
  `!i. slot<=i /\ i<slot+32 ==> i NOTIN tu.t_mem` by
    (qpat_assum `tu.t_mem = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     asm_simp_tac (srw_ss()) [IN_DIFF,GSPECIFICATION]) >>
  qpat_x_assum `!remaining k current end_st result u Gu tu dp site slot. _`
    (qspecl_then [`infos`,`0`,`ready`,`middle`,`ignored`,
      `u`,`Gu`,`tu`,`dyn_ptr`,`st.cs_next_id`,`slot`] mp_tac) >>
  impl_tac
  >- (map_every (fn pat => qpat_assum pat mp_tac)
       [`compile_abi_encode_complex_elems dst src infos 0 0 dyn_ptr ready = (ignored,middle)`,
        `fn_has_code ready middle func`,
        `st.cs_next_var <= ready.cs_next_var`,
        `st.cs_next_id <= ready.cs_next_id`, `middle.cs_next_id <= en.cs_next_id`,
        `alloca_inv u`, `alloca_room ctx func u`,
        `ctx_has_dalloca ctx ==> allocas_below_fmp u /\ u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp`,
        `allocas_from lo u`, `lo <= u.vs_alloca_next`,
        `~u.vs_halted`, `u.vs_current_bb = ready.cs_current_bb`,
        `u.vs_inst_idx = LENGTH ready.cs_current_insts`,
        `eval_operand src u = SOME (n2w sb)`, `eval_operand dst u = SOME (n2w d)`,
        `op_taint tu src = {}`, `op_taint tu dst = {}`,
        `!x. src=Var x \/ dst=Var x ==> not_fresh_at ready x`,
        `0<cap ==> ?x. src=Var x /\ _`,
        `0<encoded_size ==> ?x. dst=Var x /\ _`,
        `0<cap ==> sb+cap <= s.vs_alloca_next /\ _`,
        `d+encoded_size <= u.vs_alloca_next`, `0<cap ==> sb+cap <= u.vs_alloca_next`,
        `!id b sz. id IN sites /\ FLOOKUP u.vs_allocas id=_ ==> sz=32`,
        `!id b sz. id IN sites /\ FLOOKUP u.vs_allocas id=_ ==> regions_disjoint (d,encoded_size) (b,sz)`,
        `0<cap ==> !id b sz. id IN sites /\ FLOOKUP u.vs_allocas id=_ ==> _`,
        `mem_bytes_at sb cap u.vs_memory = mem_bytes_at sb cap s.vs_memory`,
        `!i. i<cap ==> (sb+i IN tu.t_mem <=> sb+i IN tn.t_mem)`,
        `window_member_prefix infos ats avs 0 d u.vs_memory`,
        `head_bytes 0=0`, `tail_bytes 0=0`,
        `st.cs_next_id IN sites`, `st.cs_next_id < ready.cs_next_id`,
        `dyn_ptr=Var p`, `not_fresh_at ready p`, `ptr_covers Gu tu p u 32`,
        `eval_operand dyn_ptr u = SOME (n2w slot)`,
        `FLOOKUP u.vs_allocas st.cs_next_id = SOME (slot,32)`,
        `slot+32 <= u.vs_alloca_next`,
        `mem_word_at slot u.vs_memory = n2w (window_member_head_size infos)`,
        `!i. slot<=i /\ i<slot+32 ==> i NOTIN tu.t_mem`] >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  `0<cap ==> sb+cap<=u.vs_alloca_next /\
    regions_disjoint (sb,cap) (d,encoded_size) /\
    ?x. src=Var x /\ ptr_covers Gu tu x u cap` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`0<cap ==> sb+cap<=u.vs_alloca_next`,
        `0<cap ==> ?x. src=Var x /\ ptr_covers Gu tu x u cap`,
        `0<cap ==> sb+cap<=s.vs_alloca_next /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> strip_tac >>
     qpat_assum `0<cap ==> sb+cap<=u.vs_alloca_next`
       (mp_tac o C MATCH_MP (ASSUME ``0<cap``)) >>
     qpat_assum `0<cap ==> ?x. src=Var x /\ _`
       (mp_tac o C MATCH_MP (ASSUME ``0<cap``)) >>
     qpat_assum `0<cap ==> sb+cap<=s.vs_alloca_next /\ _`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o C MATCH_MP (ASSUME ``0<cap``)) >>
     rpt disch_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!id b sz. id IN sites /\ FLOOKUP u.vs_allocas id=SOME (b,sz) ==>
    sz=32 /\ (0<cap ==> regions_disjoint (sb,cap) (b,sz)) /\
    regions_disjoint (d,encoded_size) (b,sz)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!id b sz. id IN sites /\ FLOOKUP u.vs_allocas id=_ ==> sz=32`,
        `!id b sz. id IN sites /\ FLOOKUP u.vs_allocas id=_ ==>
          regions_disjoint (d,encoded_size) (b,sz)`,
        `0<cap ==> !id b sz. id IN sites /\ FLOOKUP u.vs_allocas id=_ ==>
          regions_disjoint (sb,cap) (b,sz)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     rpt gen_tac >> strip_tac >> rpt conj_tac
     >- (qpat_assum `!id b sz. _ ==> sz=32`
           (qspecl_then [`id`,`b`,`sz`] MATCH_MP_TAC) >>
         conj_tac >> first_assum ACCEPT_TAC)
     >- (strip_tac >>
         qpat_assum `0<cap ==> !id b sz. _`
           (mp_tac o C MATCH_MP (ASSUME ``0<cap``)) >>
         disch_then (qspecl_then [`id`,`b`,`sz`] MATCH_MP_TAC) >>
         conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!id b sz. _ ==> regions_disjoint (d,encoded_size) (b,sz)`
       (qspecl_then [`id`,`b`,`sz`] MATCH_MP_TAC) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==>
    st.cs_next_id IN sites /\ st.cs_next_id<ready.cs_next_id /\
    (?x. dyn_ptr=Var x /\ not_fresh_at ready x /\ ptr_covers Gu tu x u 32) /\
    eval_operand dyn_ptr u=SOME (n2w slot) /\
    FLOOKUP u.vs_allocas st.cs_next_id=SOME (slot,32) /\
    slot+32<=u.vs_alloca_next /\
    mem_word_at slot u.vs_memory=n2w (window_member_head_size infos) /\
    (!i. slot<=i /\ i<slot+32 ==> i NOTIN tu.t_mem)` by
    (strip_tac >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      (qexists_tac `p` >> rpt conj_tac >> first_assum ACCEPT_TAC)]) >>
  simp_tac (srw_ss()) [NoAsms,DROP_0,TAKE_0,
    abi_encoder_member_span_def,window_member_tail_def,
    abi_tuple_tails_def,MAP,SUM,ADD_CLAUSES] >>
  (* No MP remains in source/scratch/cursor clauses: their full formulas
     are now assumptions. Do not split those clauses into their guards. *)
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qpat_assum `head_bytes 0=0` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `tail_bytes 0=0` (fn th => pure_rewrite_tac[th]) >>
     decide_tac)]) >>
  disch_then (qx_choose_then `v` (qx_choose_then `Gv`
    (qx_choose_then `tv` strip_assume_tac))) >>
  `mem_bytes_at d encoded_size v.vs_memory = enc at (ListV avs)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`window_member_prefix infos ats avs (LENGTH infos) d v.vs_memory`,
        `LIST_REL abi_encoder_structural_valid ats avs`,
        `window_member_head_size infos = head_lengths ats 0`,
        `enc at (ListV avs) = enc (Tuple ats) (ListV avs)`,
        `Abbrev (encoded_size = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     drule_all window_structural_member_prefix_complete >>
     qpat_assum `Abbrev (encoded_size = _)`
       (fn th => pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     qpat_assum `enc at (ListV avs) = enc (Tuple ats) (ListV avs)`
       (fn th => pure_rewrite_tac [th]) >> disch_then ACCEPT_TAC) >>
  `eval_operand dyn_ptr v = SOME (n2w slot) /\
   mem_word_at slot v.vs_memory = n2w encoded_size /\
   (!i. slot<=i /\ i<slot+32 ==> i NOTIN tv.t_mem) /\
   ptr_covers Gv tv p v 32` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`EXISTS (\(_,_,_,dyn). dyn) infos ==> eval_operand dyn_ptr v = _ /\ _`,
        `EXISTS (\(_,_,_,dyn). dyn) infos`, `dyn_ptr=Var p`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     qpat_assum `_ ==> eval_operand dyn_ptr v = _ /\ _`
       (fn th => first_assum (mp_tac o MATCH_MP th)) >>
     strip_tac >> gvs[]) >>
  `alloca_inv v /\ alloca_room ctx func v /\
   window_alloca_growth u v /\ ~v.vs_halted /\
   v.vs_current_bb=middle.cs_current_bb /\
   v.vs_inst_idx=LENGTH middle.cs_current_insts` by
    (qpat_assum `window_phase ctx func ready middle sites _ u v` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [window_phase_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp v /\
    v.vs_alloca_next + pending_alloca_size func v <= w2n v.vs_initial_fmp` by
    (qpat_assum `abi_encode_exec_frame func u v` (fn frame =>
       qpat_assum `alloca_inv v` (fn inv =>
         qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u /\ u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp` (fn bound =>
           ACCEPT_TAC (MATCH_MP window_exec_frame_alloca_budget
             (LIST_CONJ [frame,inv,bound])))))) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp v` by
    qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp v /\ v.vs_alloca_next + pending_alloca_size func v <= w2n v.vs_initial_fmp`
      (fn th => ACCEPT_TAC (DISCH (fst (dest_imp (concl th)))
        (CONJUNCT1 (UNDISCH th)))) >>
  `slot+32 <= v.vs_alloca_next` by
    (qpat_assum `slot+32 <= u.vs_alloca_next` mp_tac >>
     qpat_assum `window_alloca_growth u v`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [window_alloca_growth_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  drule_all abiEncoderWindowCursorTheory.window_cursor_load_sequence >>
  disch_then (qx_choose_then `raw_load` strip_assume_tac) >>
  qpat_assum `emit_op MLOAD [dyn_ptr] middle = (out,en)`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qabbrev_tac `q=STRING #"%" (toString middle.cs_next_var)` >>
  qabbrev_tac `ld=mk_inst middle.cs_next_id MLOAD [dyn_ptr] [q]` >>
  `emitted_insts middle en = [ld]` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`emitted_insts middle en = _`,`Abbrev (ld = _)`,`Abbrev (q = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     asm_simp_tac (srw_ss()) [Abbr `ld`,Abbr `q`]) >>
  `step_inst_base ld v=OK (update_var q (mload slot v) v)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`eval_operand dyn_ptr v = SOME (n2w slot)`,
        `slot < dimword (:256)`,`Abbrev (ld = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     mp_tac (Q.SPECL [`dyn_ptr`,`n2w slot`,`middle.cs_next_id`,`q`,`v`] step_MLOAD) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     asm_simp_tac (srw_ss()) [Abbr `ld`,w2n_n2w,LESS_MOD]) >>
  `raw_load=update_var q (mload slot v) v` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`window_pure_seq middle en v raw_load`,
        `emitted_insts middle en = [ld]`,
        `step_inst_base ld v=OK (update_var q (mload slot v) v)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     qpat_assum `window_pure_seq middle en v raw_load`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [window_seq_def] o
        CONJUNCT1 o REWRITE_RULE [window_pure_seq_def]) >>
     asm_simp_tac (srw_ss()) [run_inst_seq_def]) >>
  qabbrev_tac `t=raw_load with vs_inst_idx := LENGTH en.cs_current_insts` >>
  `P ctx func explicit middle en v t` by
    (simp_tac bool_ss [Abbr `t`] >> irule members_payload_pure >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     pure_rewrite_tac[abi_members_straight_code_def] >> disj2_tac >> disj1_tac >>
     goal_assum (drule_at Any)) >>
  qabbrev_tac `Gload=step_prov PG Gv ld raw_load` >>
  qabbrev_tac `tt=step_taint ld v raw_load tv` >>
  `window_phase ctx func middle en {} [] v t` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`window_pure_seq middle en v raw_load`,`fn_has_code middle en func`,
        `alloca_inv v`,`alloca_room ctx func v`,`~v.vs_halted`,
        `v.vs_current_bb=middle.cs_current_bb`,
        `v.vs_inst_idx=LENGTH middle.cs_current_insts`,`Abbrev (t = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     simp_tac bool_ss [Abbr `t`] >>
     irule window_pure_seq_phase >> asm_rewrite_tac[]) >>
  `abi_encode_exec_frame func v t` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`raw_load=update_var q (mload slot v) v`,`Abbrev (t = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     asm_simp_tac (srw_ss()) [Abbr `t`,abi_encode_exec_frame_def,
       pending_alloca_size_def,update_var_def,
       exprSimAbiEncodeSemanticTheory.abi_encode_semantic_obs_def]) >>
  `op_taint tt out={} /\ tt.t_mem=tv.t_mem /\
   tt.t_stor=tv.t_stor /\ tt.t_trans=tv.t_trans` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`eval_operand dyn_ptr v = SOME (n2w slot)`,`slot < dimword (:256)`,
        `!i. slot<=i /\ i<slot+32 ==> i NOTIN tv.t_mem`,
        `out=Var q`,
        `raw_load=update_var q (mload slot v) v`,
        `Abbrev (q = _)`,`Abbrev (tt = _)`,`Abbrev (ld = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     mp_tac (Q.SPECL [`PG`,`Gv`,`tv`,`v`,`middle.cs_next_id`,
       `dyn_ptr`,`q`,`n2w slot`] wordLoadStorePtrTheory.mload_ghost_clean) >>
     (impl_tac >- (asm_simp_tac (srw_ss()) [w2n_n2w,LESS_MOD] >>
       first_assum ACCEPT_TAC)) >>
     asm_simp_tac (srw_ss()) [Abbr `tt`,Abbr `ld`,Abbr `q`,w2n_n2w,LESS_MOD]) >>
  `tt.t_imm=tv.t_imm` by
    (qpat_assum `Abbrev (tt = _)` mp_tac >>
     qpat_assum `Abbrev (ld = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     simp_tac bool_ss [Abbr `tt`] >>
     irule (cj 3 step_taint_nonmemory_frame) >>
     simp_tac (srw_ss()) [Abbr `ld`,mk_inst_def]) >>
  `!x. not_fresh_at middle x ==>
    FLOOKUP Gload x=FLOOKUP Gv x /\
    op_taint tt (Var x)=op_taint tv (Var x)` by
    (rpt strip_tac >>
     `q<>x` by
       (qpat_assum `not_fresh_at middle x` mp_tac >>
        qpat_assum `Abbrev (q = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
        qpat_assum `not_fresh_at middle x`
          (mp_tac o Q.SPEC `middle.cs_next_var` o
           REWRITE_RULE [loweringStateRelDefsTheory.not_fresh_at_def]) >>
        asm_simp_tac (srw_ss()) [Abbr `q`,LESS_EQ_REFL]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`q<>x`,`Abbrev (Gload = _)`,`Abbrev (tt = _)`,`Abbrev (ld = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     asm_simp_tac (srw_ss()) [Abbr `Gload`,Abbr `tt`,Abbr `ld`,
       step_prov_other_output,step_taint_other_output,mk_inst_def]) >>
  `en.cs_current_bb=middle.cs_current_bb` by
    (qpat_assum `emit_op MLOAD [dyn_ptr] middle=(out,en)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[emit_op_def,emit_inst_def,fresh_var_def,fresh_id_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def,emit_def,LET_THM] >>
     rpt strip_tac >> gvs[]) >>
  `en.cs_current_insts=middle.cs_current_insts++[ld]` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`en.cs_current_insts = _`,`Abbrev (ld = _)`,`Abbrev (q = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     asm_simp_tac (srw_ss()) [Abbr `ld`,Abbr `q`]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (v,Gv,tv) [] (OK t,Gload,tt)` by
    (gen_tac >>
     `?bb. lookup_block v.vs_current_bb func.fn_blocks=SOME bb /\
       isPREFIX [ld] (DROP v.vs_inst_idx bb.bb_instructions)` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`fn_has_code middle en func`,`en.cs_current_insts=middle.cs_current_insts++[ld]`,
           `en.cs_current_bb=middle.cs_current_bb`,
           `v.vs_current_bb=middle.cs_current_bb`,
           `v.vs_inst_idx=LENGTH middle.cs_current_insts`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rw[fn_has_code_def,IS_PREFIX_APPEND] >>
        qexists_tac `bb` >> qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
        asm_rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >>
        simp_tac (srw_ss()) []) >>
     `ptr_inst_ok D lo 0 ctx func Gv tv ld v` by
       (irule (Q.INST [`lo0` |-> `0`] ptr_inst_ok_lower_bound_transport) >>
        simp_tac bool_ss [ZERO_LESS_EQ] >> conj_tac
        >- first_assum ACCEPT_TAC >>
        simp_tac bool_ss [Abbr `ld`] >>
        qpat_assum `dyn_ptr=Var p` (fn th => pure_rewrite_tac [th]) >>
        irule wordLoadStorePtrTheory.ptr_inst_ok_mload >>
        conj_tac >- (first_assum ACCEPT_TAC) >>
        first_assum ACCEPT_TAC) >>
     `inst_seq_ptr D lo ctx func PG Gv tv [ld] v Gload tt` by
       (`step_inst_base ld v=OK raw_load` by
          (qpat_assum `raw_load=update_var q (mload slot v) v`
             (fn th => pure_rewrite_tac [th]) >> first_assum ACCEPT_TAC) >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`step_inst_base ld v=OK raw_load`,
           `ptr_inst_ok D lo 0 ctx func Gv tv ld v`,
           `Abbrev (Gload = _)`,`Abbrev (tt = _)`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
        asm_simp_tac (srw_ss()) [inst_seq_ptr_def,Abbr `Gload`,Abbr `tt`,
          step_prov_inst_idx,step_taint_inst_idx_left,step_taint_inst_idx_right]) >>
     `run_inst_seq_mem_ok [ld] v` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`eval_operand dyn_ptr v = SOME (n2w slot)`,`slot < dimword (:256)`,
           `slot+32 <= v.vs_alloca_next`,`Abbrev (ld = _)`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
        asm_simp_tac (srw_ss()) [fragExecMemTheory.run_inst_seq_mem_ok_def,
          Abbr `ld`,mk_inst_def,unitTransformDefsTheory.inst_mem_below_frontier_def,
          memSafeRunTheory.inst_dload_in_section_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def,
          codegenRelTheory.fixed_source_write_range_def,w2n_n2w] >>
        CASE_TAC >> simp[fragExecMemTheory.run_inst_seq_mem_ok_def]) >>
     `run_inst_seq [ld] v=OK raw_load` by
       (qpat_assum `window_pure_seq middle en v raw_load` mp_tac >>
        qpat_assum `emitted_insts middle en=[ld]` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[window_pure_seq_def,window_seq_def]) >>
     `v.vs_inst_idx+1=LENGTH en.cs_current_insts` by
       (qpat_assum `en.cs_current_insts=middle.cs_current_insts++[ld]` mp_tac >>
        qpat_assum `v.vs_inst_idx=LENGTH middle.cs_current_insts` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) [ld]` by
       simp_tac (srw_ss()) [NoAsms,EVERY_DEF,Abbr `ld`,mk_inst_def,is_terminator_def] >>
     `(ctx_has_dalloca ctx ==>
        !pre i post u. [ld] = pre ++ i::post /\
          run_inst_seq pre v = OK u ==> dalloca_no_wrap i u)` by
       simp[NoAsms, Once EQ_SYM_EQ, APPEND_EQ_SING, Abbr `ld`, mk_inst_def] >>
     mp_tac (Q.SPECL [`[ld]`,`v`,`raw_load`,`Gv`,`tv`,`Gload`,`tt`,`ctx`,`func`,`bb`]
       run_inst_seq_gas_origin_ptr_path) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `v.vs_inst_idx+1=LENGTH en.cs_current_insts`
       (fn ix => qpat_assum `Abbrev (t = _)` (fn endpoint =>
         simp_tac (srw_ss()) [NoAsms,Abbr `ld`,mk_inst_def,LENGTH,ADD_CLAUSES,
           is_terminator_def,ix,REWRITE_RULE [markerTheory.Abbrev_def] endpoint]))) >>
  `window_phase ctx func st middle sites [(d,encoded_size)] s v` by
    (mp_tac (Q.INST
       [`st` |-> `st`,`mid` |-> `ready`,`en` |-> `middle`,
        `left` |-> `{st.cs_next_id}`,`left_out` |-> `[]`,
        `right` |-> `sites`,`right_out` |-> `[(d,encoded_size)]`,
        `ids` |-> `sites`,`outs` |-> `[(d,encoded_size)]`,
        `s` |-> `s`,`t` |-> `u`,`u` |-> `v`] window_phase_chain) >>
     (impl_tac >- asm_rewrite_tac[EVERY_DEF,SUBSET_REFL,INSERT_SUBSET,EMPTY_SUBSET]) >>
     disch_then ACCEPT_TAC) >>
  `window_phase ctx func st en sites [(d,encoded_size)] s t` by
    (mp_tac (Q.INST
       [`st` |-> `st`,`mid` |-> `middle`,`en` |-> `en`,
        `left` |-> `sites`,`left_out` |-> `[(d,encoded_size)]`,
        `right` |-> `{}`,`right_out` |-> `[]`,
        `ids` |-> `sites`,`outs` |-> `[(d,encoded_size)]`,
        `s` |-> `s`,`t` |-> `v`,`u` |-> `t`] window_phase_chain) >>
     (impl_tac >- (asm_rewrite_tac[EVERY_DEF,SUBSET_REFL,EMPTY_SUBSET] >>
       decide_tac)) >> disch_then ACCEPT_TAC) >>
  `abi_encode_exec_frame func s t` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `u` >>
     asm_rewrite_tac[] >> irule abi_encode_exec_frame_trans >>
     qexists_tac `v` >> asm_rewrite_tac[]) >>
  `mem_bytes_at d encoded_size t.vs_memory=enc at (ListV avs)` by
    (qpat_assum `window_pure_seq middle en v raw_load` mp_tac >>
     qpat_assum `mem_bytes_at d encoded_size v.vs_memory=enc at (ListV avs)` mp_tac >>
     qpat_assum `Abbrev (t = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     fs[window_pure_seq_def,Abbr `t`]) >>
  `eval_operand out t=SOME (n2w encoded_size)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`out=Var q`,
        `Abbrev (q = _)`,`Abbrev (t = _)`,
        `raw_load=update_var q (mload slot v) v`,
        `mem_word_at slot v.vs_memory=n2w encoded_size`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     fs[Abbr `q`,Abbr `t`,mem_word_at_eq_mload,eval_operand_def,
        update_var_def,lookup_var_def,FLOOKUP_UPDATE]) >>
  `!id b sz. id IN sites /\ FLOOKUP t.vs_allocas id=SOME (b,sz) ==> sz=32` by
    (qpat_assum `window_pure_seq middle en v raw_load` mp_tac >>
     qpat_assum `!id b sz. id IN sites /\ FLOOKUP v.vs_allocas id=_ ==> _` mp_tac >>
     qpat_assum `Abbrev (t = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     fs[window_pure_seq_def,Abbr `t`] >> metis_tac[]) >>
  `window_strong_result ctx func st en out at (ListV avs) d s t` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`window_phase ctx func st en sites [(d,encoded_size)] s t`,
        `mem_bytes_at d encoded_size t.vs_memory=enc at (ListV avs)`,
        `eval_operand out t=SOME (n2w encoded_size)`,
        `!id b sz. id IN sites /\ FLOOKUP t.vs_allocas id=_ ==> sz=32`,
        `Abbrev (encoded_size = _)`,`Abbrev (sites = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     irule window_complex_phase_result >>
     map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac
       [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]))
       [`Abbrev (encoded_size = _)`,`Abbrev (sites = _)`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>

  `!x. not_fresh_at st x ==> FLOOKUP Gload x=FLOOKUP G x /\
    op_taint tt (Var x)=op_taint tn (Var x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`!x. not_fresh_at middle x ==> FLOOKUP Gload x = _ /\ _`,
        `!x. not_fresh_at ready x ==> FLOOKUP Gv x = _ /\ _`,
        `!x. not_fresh_at st x ==> FLOOKUP Gu x = _ /\ _`,
        `st.cs_next_var<=ready.cs_next_var`,
        `ready.cs_next_var<=middle.cs_next_var`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gen_tac >> strip_tac >>
     `not_fresh_at ready x /\ not_fresh_at middle x` by
       metis_tac[not_fresh_at_mono,LESS_EQ_TRANS] >>
     qpat_assum `!x. not_fresh_at middle x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at ready x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at st x ==> _` (qspec_then `x` mp_tac) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `t.vs_allocas=v.vs_allocas` by
    (qpat_assum `window_pure_seq middle en v raw_load` mp_tac >>
     qpat_assum `Abbrev (t = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     fs[window_pure_seq_def,Abbr `t`]) >>
  `FLOOKUP t.vs_allocas st.cs_next_id=SOME (slot,32)` by
    (qpat_assum `window_phase ctx func ready middle sites _ u v` mp_tac >>
     qpat_assum `FLOOKUP u.vs_allocas st.cs_next_id=SOME (slot,32)` mp_tac >>
     qpat_assum `t.vs_allocas=v.vs_allocas` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_phase_def,abi_encoder_registered_effect_def] >>
     metis_tac[]) >>
  `!i. (i<d \/ d+encoded_size<=i) /\
    (!id b sz. id IN sites /\ FLOOKUP t.vs_allocas id=SOME (b,sz) ==>
      i<b \/ b+sz<=i) ==> (i IN tt.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >>
     disch_then (fn th => ASSUME_TAC (CONJUNCT1 th) THEN ASSUME_TAC (CONJUNCT2 th)) >>
     `i IN tv.t_mem <=> i IN tu.t_mem` by
       (qpat_assum `!i. _ ==> (i IN tv.t_mem <=> i IN tu.t_mem)`
          (qspec_then `i` MATCH_MP_TAC) >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qpat_assum `t.vs_allocas=v.vs_allocas`
          (fn th => pure_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
     SUBGOAL_THEN ``i<slot \/ slot+32<=i`` ASSUME_TAC
     >- (qpat_assum `!id b sz. id IN sites /\ FLOOKUP t.vs_allocas id=_ ==> i<b \/ b+sz<=i`
           (qspecl_then [`st.cs_next_id`,`slot`,`32`] MATCH_MP_TAC) >>
         conj_tac >> first_assum ACCEPT_TAC) >>
     `~(slot<=i /\ i<slot+32)` by
       (qpat_assum `i<slot \/ slot+32<=i` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`i IN tv.t_mem <=> i IN tu.t_mem`, `tt.t_mem=tv.t_mem`,
        `tu.t_mem = _`, `~(slot<=i /\ i<slot+32)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [IN_DIFF,GSPECIFICATION] >> tautLib.TAUT_TAC) >>
  `tt.t_stor=tn.t_stor /\ tt.t_trans=tn.t_trans /\ tt.t_imm=tn.t_imm` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`tt.t_stor=tv.t_stor`,`tv.t_stor=tu.t_stor`,`tu.t_stor=tn.t_stor`,
        `tt.t_trans=tv.t_trans`,`tv.t_trans=tu.t_trans`,`tu.t_trans=tn.t_trans`,
        `tt.t_imm=tv.t_imm`,`tv.t_imm=tu.t_imm`,`tu.t_imm=tn.t_imm`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss []) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,Gload,tt)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK u,Gu,tu)`
       (qspec_then `D` mp_tac) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`u`,`Gu`,`tu`,`[]`,`OK v`,`Gv`,`tv`] mp_tac) >>
     asm_rewrite_tac[APPEND] >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`v`,`Gv`,`tv`,`[]`,`OK t`,`Gload`,`tt`] mp_tac) >>
     asm_rewrite_tac[APPEND]) >>
  `!x. out=Var x ==> not_fresh_at en x` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`out=Var q`,`Abbrev (q = _)`,
        `en.cs_next_var=middle.cs_next_var+1`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     asm_simp_tac (srw_ss()) [Abbr `q`,loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >> decide_tac) >>
  `P ctx func explicit st middle s v` by
    (irule members_payload_comp >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`ready`,`u`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `P ctx func explicit st en s t` by
    (irule members_payload_comp >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`middle`,`v`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  qexistsl_tac [`t`,`Gload`,`tt`] >>
  map_every (fn pat => qpat_assum pat (fn abr => pure_rewrite_tac
    [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] abr)]))
    [`Abbrev (sites = _)`,`Abbrev (encoded_size = _)`] >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`window_strong_result ctx func st en out at (ListV avs) d s t`,
     `abi_encode_exec_frame func s t`,`op_taint tt out={}`,
     `!x. out=Var x ==> not_fresh_at en x`,
     `!i. d<=i /\ i<d+encoded_size ==> i NOTIN tv.t_mem`,
     `tt.t_mem=tv.t_mem`,
     `!x. not_fresh_at st x ==> FLOOKUP Gload x=_ /\ _`,
     `!i. (i<d \/ d+encoded_size<=i) /\ _ ==> (i IN tt.t_mem <=> i IN tn.t_mem)`,
     `tt.t_stor=tn.t_stor`,`tt.t_trans=tn.t_trans`,`tt.t_imm=tn.t_imm`,
     `P ctx func explicit st en s t`,
     `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gload,tt)`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  asm_rewrite_tac[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED


Finalise compile_abi_encode_to_buf_complex_window_joint_payload

(* The original callback remains sufficient when no geometry is requested. *)
Theorem compile_abi_encode_to_buf_complex_window_joint:
  (!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==>
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
        !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
          (s,G,tn) [] (OK t,G',tn')) ==>
  !dst src st out en ctx func s at av sb cap d G tn lo explicit PG.
    compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,en) /\
    abi_encoder_admissible (AbiComplex infos) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      abi_encoder_window_input (AbiComplex infos) at av sb cap mem) /\
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
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,G',tn')
Proof
  MATCH_ACCEPT_TAC
    (SIMP_RULE bool_ss [abi_members_path_laws_def]
      (Q.INST [`P` |-> `\ctx func explicit a b s t. T`]
        compile_abi_encode_to_buf_complex_window_joint_payload))
QED
