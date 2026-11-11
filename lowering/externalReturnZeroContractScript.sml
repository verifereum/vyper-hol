Theory externalReturnZeroContract
Ancestors
  externalReturnZeroWindow externalReturnZeroRun abiEncoderWindowContract
  abiEncoderWindowStructuralMembers abiEncoderWindowMembers abiEncoderWindow
  abiEncoderInput abiEncoderWindowPhase abiEncoderRegisteredEffect
  abiEncoderExtendSim abiEncoderProps compileEnv venomState venomInst venomMemDefs
  contractABI valueEncoding words list finite_map pred_set
  abiEncoderWindowLeaves abiEncoderLeaves abiEncoderPrimitiveEffect
  emitHelperProps exprLoweringProps venomExecSemantics

Definition zero_window_pre_def:
  zero_window_pre ctx func st st' dst src ei at av sb d s <=>
    abi_encoder_admissible ei /\
    abi_encoder_window_input ei at av sb 0 s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\
    eval_operand dst s = SOME (n2w d) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_room ctx func s /\
    d + LENGTH (enc at av) <= s.vs_alloca_next /\
    (!inst b sz.
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition zero_strong_contract_def:
  zero_strong_contract ei <=>
    !dst src st out st' ctx func s at av sb d.
      compile_abi_encode_to_buf dst src ei st = (out,st') /\
      zero_window_pre ctx func st st' dst src ei at av sb d s ==>
      ?t. window_strong_result ctx func st st' out at av d s t
End

Theorem zero_window_pre_ghost:
  zero_window_pre ctx func st st' dst src ei at av sb d s ==>
  abi_encoder_window_pre ctx func st st' dst (Lit 0w) ei at av 0 0 d s
Proof
  simp_tac bool_ss [zero_window_pre_def, abi_encoder_window_pre_def] >>
  strip_tac >>
  `abi_encoder_window_input ei at av 0 0 s.vs_memory` by
    metis_tac[zero_window_relocate] >>
  `!x. regions_disjoint (0,0) x` by (Cases >> simp[regions_disjoint_def]) >>
  simp[eval_operand_def] >> metis_tac[]
QED

Definition zero_members_inv_def:
  zero_members_inv ctx func infos at ats avs k src dst dp site slot
    sb d st en s <=>
    window_structural_members_inv ctx func infos at ats avs k (Lit 0w) dst dp site slot
      0 0 d st en s /\
    eval_operand src s = SOME (n2w sb) /\
    (!x. src = Var x ==> not_fresh_at st x)
End

Theorem zero_member_source_prepare:
  zero_members_inv ctx func infos at ats avs k src dst dp site slot
    sb d st en s /\ emit_op ADD [src;Lit (n2w so)] st = (child_src,ready) /\
  fn_has_code st ready func /\ fn_has_code ready en func /\
  st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id ==>
  ?t. window_phase ctx func st ready {} [] s t /\
    zero_members_inv ctx func infos at ats avs k src dst dp site slot
      sb d ready en t /\
    eval_operand child_src t = SOME (n2w (sb+so)) /\
    (!x. child_src = Var x ==> not_fresh_at ready x)
Proof
  simp_tac bool_ss [zero_members_inv_def] >> strip_tac >>
  `alloca_inv s /\ alloca_room ctx func s /\
   ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[window_structural_members_inv_def, abi_encoder_window_pre_def] >>
  `eval_operand (Lit (n2w so)) s = SOME (n2w so)` by simp[eval_operand_def] >>
  drule_all window_emit_add_phase >> strip_tac >>
  qexists_tac `t` >> simp[word_add_n2w] >>
  conj_tac
  >- (irule window_structural_members_inv_pure_phase >> metis_tac[]) >>
  conj_tac
  >- (Cases_on `src` >> gvs[eval_operand_def] >> metis_tac[window_phase_vars]) >>
  fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem zero_copy_strong_contract:
  zero_strong_contract (AbiCopy 0)
Proof
  simp_tac bool_ss [zero_strong_contract_def] >> rpt gen_tac >> strip_tac >>
  `!i b sz. i IN window_alloca_sites func (frag_ids st st') /\
    FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (fs[zero_window_pre_def, window_alloca_sites_def] >> metis_tac[]) >>
  pop_assum (mk_asm "sizes") >>
  qpat_x_assum `zero_window_pre _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [zero_window_pre_def]) >>
  `enc at av = []` by fs[abi_encoder_window_copy_iff, mem_bytes_at_def] >>
  drule abi_encode_copy_code >> strip_tac >>
  `d < dimword (:256)` by
    (drule alloca_room_next_lt >> simp[] >> decide_tac) >>
  `eval_operand src s = SOME (n2w (sb MOD dimword (:256)))` by simp[] >>
  `eval_operand (Lit 0w) s = SOME (n2w 0)` by simp[eval_operand_def] >>
  `run_inst_seq (emitted_insts st st') s =
     OK (mcopy d (sb MOD dimword (:256)) 0 s) /\
   inst_extends st st' /\ st'.cs_blocks = st.cs_blocks /\
   st'.cs_current_bb = st.cs_current_bb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by
    (irule window_emit_copy_run >> simp[] >> metis_tac[]) >>
  `abi_encoder_extend_sim ctx func s
    ((mcopy d (sb MOD dimword (:256)) 0 s)
       with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_run_sequence_extend_sim >>
     (conj_tac >- first_assum ACCEPT_TAC) >> qexists_tac `st` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_encoder_registered_effect (window_alloca_sites func (frag_ids st st'))
    [(d,0)] s ((mcopy d (sb MOD dimword (:256)) 0 s)
      with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_registered_effect_trans >>
     qexists_tac `mcopy d (sb MOD dimword (:256)) 0 s` >>
     simp[abi_encoder_registered_output_copy, abi_encoder_registered_inst_idx]) >>
  `abi_encoder_registered_effect (frag_ids st st') [(d,0)] s
    ((mcopy d (sb MOD dimword (:256)) 0 s)
      with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`window_alloca_sites func (frag_ids st st')`, `[(d,0)]`] >>
     simp[window_alloca_sites_subset]) >>
  mp_tac (Q.INST [`d` |-> `d`, `sb` |-> `sb MOD dimword (:256)`, `n` |-> `0`,
    `ix` |-> `LENGTH st'.cs_current_insts`] window_copy_state_resources) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qexists_tac `(mcopy d (sb MOD dimword (:256)) 0 s)
    with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  asm_simp_tac (srw_ss())
    [eval_operand_def, mem_bytes_at_def, abi_encoder_extend_sim_sim] >>
  conj_tac >- asm "sizes" ACCEPT_TAC >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem zero_window_pre_actual:
  abi_encoder_window_pre ctx func st en dst (Lit 0w) ei at av 0 0 d s /\
  eval_operand src s = SOME (n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) ==>
  zero_window_pre ctx func st en dst src ei at av sb d s
Proof
  simp_tac bool_ss [abi_encoder_window_pre_def, zero_window_pre_def] >>
  strip_tac >>
  `abi_encoder_window_input ei at av sb 0 s.vs_memory` by
    metis_tac[zero_window_relocate] >>
  metis_tac[]
QED
