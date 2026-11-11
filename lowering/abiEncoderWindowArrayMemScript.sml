(* Same-witness memory safety for the complete array encoder. *)
Theory abiEncoderWindowArrayMem
Ancestors
  abiEncoderWindowArray abiEncoderWindowArrayExit abiEncoderWindowArrayRoundMem
  abiEncoderWindowArrayBody abiEncoderWindowArrayLayout abiEncoderWindowArrayInvariant
  freshWrites abiEncoderWindowArrayRound abiEncoderArrayContext abiEncoderRegisteredEffect
  abiEncoderArrayLoopCode
  abiEncoderWindowArrayEntryMem abiEncoderWindowArrayCursorMem abiEncoderWindowLoopMem
  windowPhaseMem windowSequenceMem windowTransitionMem abiEncoderArrayCode allocaFootprint
  abiEncoderWindowSequence abiEncoderWindowPhase emitHelperProps emitHelper
  compileEnv exprLoweringProps fragExec fragExecMem venomState venomExecSemantics venomInst
  words list rich_list pred_set finite_map instIdxIndep memSafeRun instMemFrontier arithmetic
  valueEncoding valueEncodingProps venomMemDefs memContinuation abiEncoderWindowContract

Theorem window_array_static_exit_seq_mem[local]:
  abi_encode_array_static_exit src asz st = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb+32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  simp_tac bool_ss [abi_encode_array_static_exit_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  rename1 `emit_op MLOAD [src] st = (len,c1)` >>
  rename1 `emit_op MUL [len;Lit (n2w asz)] c1 = (payload,c2)` >>
  `inst_extends st c1 /\ inst_extends c1 c2 /\ inst_extends c2 en` by
    metis_tac[inst_extends_emit_op] >>
  `emitted_insts st en = emitted_insts st c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 en` by
    metis_tac[emitted_insts_append, inst_extends_def, inst_extends_trans] >>
  asm_rewrite_tac[] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- (drule emit_mload_mem_ok >> disch_then irule >> simp[]) >>
  rpt strip_tac >> match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- (qpat_assum `emit_op MUL _ _ = _` (mp_then Any mp_tac emit_op_mem_ok) >>
      disch_then irule >> simp[] >>
      irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  rpt strip_tac >> drule emit_op_mem_ok >> disch_then irule >> simp[] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem window_array_dynamic_exit_seq_mem[local]:
  abi_encode_array_dynamic_exit src dp st = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb+32 <= s.vs_alloca_next /\
  eval_operand dp s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\
  (!x. dp = Var x ==> not_fresh_at st x) ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  simp_tac bool_ss [abi_encode_array_dynamic_exit_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  rename1 `emit_op MLOAD [src] st = (unused,c1)` >>
  rename1 `emit_op MLOAD [dp] c1 = (off,c2)` >>
  `inst_extends st c1 /\ inst_extends c1 c2 /\ inst_extends c2 en` by
    metis_tac[inst_extends_emit_op] >>
  `emitted_insts st en = emitted_insts st c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 en` by
    metis_tac[emitted_insts_append, inst_extends_def, inst_extends_trans] >>
  `?t. window_pure_seq st c1 s t` by metis_tac[window_emit_load_pure] >>
  asm_rewrite_tac[] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- (qpat_assum `emit_op MLOAD [src] _ = _` (mp_then Any mp_tac emit_mload_mem_ok) >>
      disch_then irule >> simp[]) >>
  rpt strip_tac >>
  `s' = t` by fs[window_pure_seq_def, window_seq_def] >> gvs[] >>
  rename1 `window_pure_seq st c1 s t` >>
  `eval_operand dp t = SOME (n2w slot)` by
    (irule window_seq_eval >> metis_tac[window_pure_seq_def]) >>
  `t.vs_alloca_next = s.vs_alloca_next` by fs[window_pure_seq_def] >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- (qpat_assum `emit_op MLOAD [dp] _ = _` (mp_then Any mp_tac emit_mload_mem_ok) >>
      disch_then irule >> simp[]) >>
  rpt strip_tac >> drule emit_op_mem_ok >> disch_then irule >> simp[] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem window_array_scalar_exit_seq_mem[local]:
  (if active then abi_encode_array_dynamic_exit src dp st
   else abi_encode_array_static_exit src asz st) = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb+32 <= s.vs_alloca_next /\
  (active ==> eval_operand dp s = SOME (n2w slot) /\ slot < dimword (:256) /\
    slot+32 <= s.vs_alloca_next /\ (!x. dp = Var x ==> not_fresh_at st x)) ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  Cases_on `active` >> simp_tac bool_ss [COND_CLAUSES, IMP_CLAUSES] >>
  strip_tac
  >- (drule_all window_array_dynamic_exit_seq_mem >> simp[]) >>
  drule_all window_array_static_exit_seq_mem >> simp[]
QED

Theorem window_array_scalar_exit_run_mem:
  abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap s.vs_memory /\
  abi_encoder_array_prefix ty avs (LENGTH avs) d s.vs_memory /\
  (if active then abi_encode_array_dynamic_exit src dp st
   else abi_encode_array_static_exit src asz st) = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb+32 <= s.vs_alloca_next /\
  (active ==> eval_operand dp s = SOME (n2w slot) /\ slot < dimword (:256) /\
    slot+32 <= s.vs_alloca_next /\ (!x. dp = Var x ==> not_fresh_at st x) /\
    mload slot s = n2w (LENGTH avs * abi_member_head_size ty +
       SUM (MAP (abi_member_tail_size ty) avs))) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    window_array_transition ctx func st {} [] s t /\
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) t.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out t = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    (!x. out = Var x ==> not_fresh_at en x) /\ mem_cont_sim ctx func s t
Proof
  strip_tac >>
  `?t. window_pure_seq st en s t /\
    eval_operand out t = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    (!x. out = Var x ==> not_fresh_at en x)` by
    (irule window_array_scalar_exit_pure >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (irule window_array_scalar_exit_seq_mem >> metis_tac[]) >>
  `mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_seq_mem_cont, window_pure_seq_def] >>
  `mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) s.vs_memory =
      enc (Array NONE ty) (ListV avs)` by metis_tac[window_array_prefix_complete] >>
  `window_phase ctx func st en {} [] s
     (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_pure_seq_phase] >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  asm_rewrite_tac[] >> conj_tac
  >- metis_tac[window_array_pure_phase_transition] >>
  `t.vs_memory = s.vs_memory` by fs[window_pure_seq_def] >>
  simp_tac (srw_ss()) [Excl "enc_def", eval_op_inst_idx] >> asm_rewrite_tac[]
QED

Theorem window_array_completed_exit_mem:
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op exit_st.cs_current_bb sb cap d (LENGTH avs) s /\
  exit_st.cs_current_insts = [] /\ owner.cs_next_var <= exit_st.cs_next_var /\
  (if active then abi_encode_array_dynamic_exit src dp exit_st
   else abi_encode_array_static_exit src asz exit_st) = (out,en) /\
  fn_has_code exit_st en func ==>
  ?t. window_array_transition ctx func owner {} [] s t /\
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) t.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out t = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    mem_cont_sim ctx func s t
Proof
  strip_tac >>
  `abi_encoder_window_input (AbiDynArray ei asz msz active)
     (Array NONE ty) (ListV avs) sb cap s.vs_memory /\
   abi_encoder_array_prefix ty avs (LENGTH avs) d s.vs_memory /\
   eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
   sb+32 <= s.vs_alloca_next /\
   alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
   s.vs_current_bb = exit_st.cs_current_bb /\
   s.vs_inst_idx = LENGTH exit_st.cs_current_insts` by
    (fs[window_array_inv_def, window_array_root_def] >>
     `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
     `32 <= cap` by fs[abiEncoderWindowTheory.abi_encoder_window_array_iff] >>
     decide_tac) >>
  `(active ==> eval_operand dp s = SOME (n2w dslot) /\ dslot < dimword (:256) /\
      dslot+32 <= s.vs_alloca_next /\ (!x. dp = Var x ==> not_fresh_at exit_st x) /\
      mload dslot s = n2w (LENGTH avs * abi_member_head_size ty +
        SUM (MAP (abi_member_tail_size ty) avs)))` by
    (strip_tac >>
     `window_array_cursor T owner dp dsite dslot
       (LENGTH avs * abi_member_head_size ty + SUM (MAP (abi_member_tail_size ty) avs))
       sb cap d (LENGTH (enc (Array NONE ty) (ListV avs))) s` by
       fs[window_array_inv_def] >>
     `dslot+32 <= s.vs_alloca_next` by metis_tac[window_array_cursor_frontier] >>
     fs[window_array_cursor_def, mload_def, mem_word_at_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  drule_all window_array_scalar_exit_run_mem >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >> conj_tac
  >- (irule window_array_transition_owner_weaken >> goal_assum (drule_at Any) >>
      metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  metis_tac[window_phase_control]
QED

Theorem window_array_exit_parent_mem:
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op exit_st.cs_current_bb sb cap d (LENGTH avs) s /\
  window_array_cursor T owner pp psite pb 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  exit_st.cs_current_insts = [] /\ owner.cs_next_var <= exit_st.cs_next_var /\
  (if active then abi_encode_array_dynamic_exit src dp exit_st
   else abi_encode_array_static_exit src asz exit_st) = (size_op,mid) /\
  abi_encode_array_finish pp size_op mid = (out,en) /\
  fn_has_code exit_st mid func /\ fn_has_code mid en func ==>
  ?t. window_array_transition ctx func owner {psite} [] s t /\
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) t.vs_memory =
      enc (Array NONE ty) (ListV avs) /\
    eval_operand out t = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    mem_cont_sim ctx func s t
Proof
  strip_tac >> drule_all window_array_completed_exit_mem >> strip_tac >>
  rename1 `window_array_transition ctx func owner {} [] s u` >>
  `window_array_cursor T owner pp psite pb 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) u` by
    (irule window_array_cursor_frame >>
     qexistsl_tac [`{}`, `ctx`, `func`, `[]`, `s`] >> asm_rewrite_tac[] >> simp[]) >>
  `exit_st.cs_next_var <= mid.cs_next_var` by
    (Cases_on `active` >> full_simp_tac bool_ss []
     >- (drule (cj 2 abi_encode_array_exit_shape) >> simp[]) >>
     drule (cj 1 abi_encode_array_exit_shape) >> simp[]) >>
  `!x. not_fresh_at owner x ==> not_fresh_at mid x` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `owner` >> asm_rewrite_tac[] >> decide_tac) >>
  `eval_operand pp u = SOME (n2w pb) /\ pb < dimword (:256) /\
   mload pb u = 0w /\ FLOOKUP u.vs_allocas psite = SOME (pb,32) /\
   (!x. pp = Var x \/ size_op = Var x ==> not_fresh_at mid x) /\
   alloca_inv u /\ alloca_room ctx func u /\ ~u.vs_halted` by
    (fs[window_array_cursor_def, window_array_transition_def,
        mload_def, mem_word_at_def] >> metis_tac[]) >>
  drule_all window_array_parent_finish_mem >> strip_tac >>
  suspend "finish"
QED

Resume window_array_exit_parent_mem[finish]:
  `window_array_transition ctx func owner {psite} [] u t` by
    (irule window_array_transition_owner_weaken >> goal_assum (drule_at Any) >>
     asm_rewrite_tac[]) >>
  `mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) t.vs_memory =
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) u.vs_memory` by
    (irule abi_encoder_window_effect_bytes >>
     qexistsl_tac [`{psite}`, `[]`] >>
     `abi_encoder_registered_effect {psite} [] u t` by
       metis_tac[window_array_transition_effect] >>
     asm_rewrite_tac[EVERY_DEF, IN_SING] >> rpt strip_tac >>
     `FLOOKUP t.vs_allocas psite = SOME (pb,32)` by
       metis_tac[window_array_transition_effect,
         abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_allocated] >>
     gvs[window_array_cursor_def]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >> conj_tac
  >- (irule window_array_transition_trans >> qexists_tac `u` >> asm_rewrite_tac[] >>
      irule window_array_transition_enlarge >>
      qexistsl_tac [`{}`, `[]`] >> asm_rewrite_tac[] >> simp[]) >>
  metis_tac[window_phase_control, mem_cont_sim_trans]
QED

Finalise window_array_exit_parent_mem

Theorem window_array_actual_control_loop_mem:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  (if active then
     abi_encode_array_dynamic_body ip dp src dst ei asz msz body_st = (idx,body_end)
   else abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end)) /\
  (!dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\ mem_cont_sim ctx func s t) /\
  window_alloca_sites func (frag_ids body_st body_end) SUBSET ids /\
  isite IN ids /\ isite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  (active ==> dsite IN ids /\
    dsite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\ dsite <> isite) /\
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op (FST labels) sb cap d j s /\
  j <= LENGTH avs ==>
  ?t. window_array_transition ctx func owner ids
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t /\
    mem_cont_sim ctx func s t /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op (SND (SND labels)) sb cap d (LENGTH avs) t
Proof
  strip_tac >>
  `!k u. k < LENGTH avs /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op (FST (SND labels)) sb cap d k u ==>
    ?v. window_array_transition ctx func owner ids
        [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] u v /\
      mem_cont_sim ctx func u v /\
      window_array_inv ctx func owner ids ei asz msz active ty avs src dst
        ip isite islot dp dsite dslot count_op (FST labels) sb cap d (SUC k) v` by
    (rpt gen_tac >> strip_tac >> Cases_on `active` >> full_simp_tac bool_ss []
     >- (irule window_array_dynamic_round_mem >> goal_assum (drule_at Any) >> metis_tac[]) >>
     irule window_array_static_round_mem >> goal_assum (drule_at Any) >> metis_tac[]) >>
  irule window_array_control_loop_mem >>
  full_simp_tac bool_ss [abi_encoder_array_loop_code_def] >> conj_tac
  >- metis_tac[] >>
  qmatch_asmsub_rename_tac `lookup_block body_st.cs_current_bb _ = SOME body_bb` >>
  qexistsl_tac [`body_bb`, `FST (SND labels)`,
    `STRING #"%" (toString (owner.cs_next_var+1))`,
    `STRING #"%" (toString (owner.cs_next_var+2))`, `FST labels`,
    `owner.cs_next_id+1`, `STRING #"%" (toString owner.cs_next_var)`, `j`] >>
  asm_rewrite_tac[] >> rpt strip_tac >> fs[not_fresh_at_def] >> metis_tac[]
QED

Theorem window_array_loop_parent_mem:
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  (if active then abi_encode_array_dynamic_body ip dp src dst ei asz msz body_st = (idx,body_end)
   else abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end)) /\
  (!dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\ mem_cont_sim ctx func s t) /\
  window_alloca_sites func (frag_ids body_st body_end) SUBSET ids /\
  isite IN ids /\ isite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
  (active ==> dsite IN ids /\ dsite NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
    dsite <> isite) /\ psite NOTIN ids /\
  window_array_inv ctx func owner ids ei asz msz active ty avs src dst
    ip isite islot dp dsite dslot count_op (FST labels) sb cap d 0 s /\
  window_array_cursor T owner pp psite pb 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s ==>
  ?t. window_array_transition ctx func owner ids
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t /\
    mem_cont_sim ctx func s t /\
    window_array_inv ctx func owner ids ei asz msz active ty avs src dst
      ip isite islot dp dsite dslot count_op (SND (SND labels)) sb cap d (LENGTH avs) t /\
    window_array_cursor T owner pp psite pb 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t
Proof
  strip_tac >> `0 <= LENGTH avs` by simp[] >>
  drule_all window_array_actual_control_loop_mem >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >> irule window_array_cursor_frame >>
  qexistsl_tac [`ids`, `ctx`, `func`,
    `[(d,LENGTH (enc (Array NONE ty) (ListV avs)))]`, `s`] >>
  asm_rewrite_tac[] >> fs[window_array_cursor_def, regions_disjoint_def] >> decide_tac
QED

Theorem window_array_constructor_sites_mem[local]:
  abi_encode_array_prefix src dst st = ((pp,count_op),mid) /\
  (if active then abi_encode_array_dynamic_init count_op asz mid = ((ip,dp),owner)
   else abi_decode_index_init mid = (ip,owner) /\ dp = Lit 0w) /\
  fn_has_code st mid func /\ fn_has_code mid owner func /\
  mid.cs_next_id = st.cs_next_id+4 /\
  owner.cs_next_id = mid.cs_next_id+(if active then 5 else 2) /\
  owner.cs_next_id <= en.cs_next_id ==>
  st.cs_next_id IN window_alloca_sites func (frag_ids st en) /\
  mid.cs_next_id IN window_alloca_sites func (frag_ids st en) /\
  (active ==> mid.cs_next_id+2 IN window_alloca_sites func (frag_ids st en)) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst mid.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString mid.cs_next_var)]) (fn_insts func) /\
  (active ==> MEM (mk_inst (mid.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (mid.cs_next_var+1))]) (fn_insts func))
Proof
  strip_tac >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    metis_tac[window_array_prefix_alloca_member] >>
  `MEM (mk_inst mid.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString mid.cs_next_var)]) (fn_insts func) /\
   (active ==> MEM (mk_inst (mid.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (mid.cs_next_var+1))]) (fn_insts func))` by
    (Cases_on `active` >> full_simp_tac bool_ss []
     >- (drule_all window_array_dynamic_alloca_members >> simp[]) >>
     drule_all window_array_index_alloca_member >> simp[]) >>
  `st.cs_next_id < en.cs_next_id /\ st.cs_next_id <= mid.cs_next_id /\
   mid.cs_next_id < en.cs_next_id /\
   (active ==> st.cs_next_id <= mid.cs_next_id+2 /\ mid.cs_next_id+2 < en.cs_next_id)` by
    (Cases_on `active` >> gvs[] >> decide_tac) >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- (irule window_array_alloca_site >> simp[] >> metis_tac[])
  >- (irule window_array_alloca_site >> simp[] >> metis_tac[]) >>
  strip_tac >> irule window_array_alloca_site >> fs[] >>
  `st.cs_next_id + 6 = mid.cs_next_id + 2` by decide_tac >>
  metis_tac[]
QED

Theorem window_array_constructor_entry_mem:
  window_array_root ctx func st (window_alloca_sites func (frag_ids st en))
    ei asz msz active ty avs src dst sb cap d s /\
  abi_encode_array_prefix src dst st = ((pp,count_op),mid) /\
  (if active then abi_encode_array_dynamic_init count_op asz mid = ((ip,dp),owner)
   else abi_decode_index_init mid = (ip,owner) /\ dp = Lit 0w) /\
  abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels /\
  fn_has_code st mid func /\ fn_has_code mid owner func /\
  mid.cs_next_id = st.cs_next_id+4 /\
  owner.cs_next_id = mid.cs_next_id+(if active then 5 else 2) /\
  owner.cs_next_id <= en.cs_next_id /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  st.cs_next_id IN window_alloca_sites func (frag_ids st en) /\
  mid.cs_next_id IN window_alloca_sites func (frag_ids st en) /\
  (active ==> mid.cs_next_id+2 IN window_alloca_sites func (frag_ids st en)) /\
  ?t pb bi bd.
    window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
      [(d,32)] s t /\
    window_array_inv ctx func owner (window_alloca_sites func (frag_ids st en))
      ei asz msz active ty avs src dst ip mid.cs_next_id bi dp
      (if active then mid.cs_next_id+2 else 0) bd count_op (FST labels) sb cap d 0 t /\
    window_array_cursor T owner pp st.cs_next_id pb 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) t /\ mem_cont_sim ctx func s t
Proof
  strip_tac >> drule_all window_array_constructor_sites_mem >> strip_tac >>
  asm_rewrite_tac[] >> Cases_on `active` >> full_simp_tac bool_ss []
  >- (drule_all window_array_dynamic_entry_run_mem >> metis_tac[]) >>
  drule_all window_array_static_entry_run_mem >> strip_tac >>
  qexistsl_tac [`t`, `pb`, `bi`, `0`] >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem window_array_strong_contract_mem:
  (!dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\ mem_cont_sim ctx func s t) ==>
  !dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src (AbiDynArray ei asz msz active) st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src (AbiDynArray ei asz msz active)
      at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\ mem_cont_sim ctx func s t
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule window_array_pre_root >> strip_tac >> gvs[] >>
  `fn_has_code st st' func /\ abi_encoder_admissible (AbiDynArray ei asz msz active)` by
    fs[abi_encoder_window_pre_def] >>
  drule_all abi_encode_array_context >> strip_tac >>
  drule_all window_array_loop_context >> strip_tac >>
  PairCases_on `ops` >>
  rename1 `abi_encode_array_prefix src dst st = ((pp,count_op),loop_st)` >>
  suspend "code"
QED

Resume window_array_strong_contract_mem[code]:
  full_simp_tac bool_ss [pairTheory.FST, pairTheory.SND] >>
  drule window_array_loop_code_bounds >> strip_tac >>
  `owner.cs_next_id <= st'.cs_next_id` by decide_tac >>
  `~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_encoder_window_pre_def] >>
  drule_all window_array_constructor_entry_mem >> strip_tac >>
  rename1 `window_array_transition ctx func st _ [(d,32)] s entry` >>
  qabbrev_tac `ids = window_alloca_sites func (frag_ids st st')` >>
  qabbrev_tac `loop_ids = ids DELETE st.cs_next_id` >>
  `window_alloca_sites func (frag_ids body_st body_end) SUBSET ids /\
   loop_st.cs_next_id NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
   loop_st.cs_next_id+2 NOTIN window_alloca_sites func (frag_ids body_st body_end) /\
   st.cs_next_id NOTIN window_alloca_sites func (frag_ids body_st body_end)` by
    (simp_tac bool_ss [Abbr `ids`] >> irule window_array_body_sites >>
     conj_tac >- decide_tac >>
     conj_tac >- (qexists_tac `loop_end` >> asm_rewrite_tac[] >> decide_tac) >>
     qexistsl_tac [`active`, `count_op`, `exit_st`, `ip`, `labels`, `owner`] >>
     asm_rewrite_tac[]) >>
  `window_alloca_sites func (frag_ids body_st body_end) SUBSET loop_ids /\
   loop_st.cs_next_id IN loop_ids /\
   (active ==> (if active then loop_st.cs_next_id+2 else 0) IN loop_ids /\
    (if active then loop_st.cs_next_id+2 else 0) <>
       loop_st.cs_next_id) /\ st.cs_next_id NOTIN loop_ids /\ loop_ids SUBSET ids` by
    (simp_tac (srw_ss()) [Abbr `loop_ids`, SUBSET_DEF] >>
     rpt conj_tac >> rpt strip_tac >> gvs[] >>
     fs[SUBSET_DEF] >> metis_tac[]) >>
  `window_array_inv ctx func owner loop_ids ei asz msz active ty avs src dst
    ip loop_st.cs_next_id bi dp (if active then loop_st.cs_next_id+2 else 0) bd
    count_op (FST labels) sb cap d 0 entry` by
    (irule window_array_inv_sites_subset >> goal_assum (drule_at Any) >>
     asm_rewrite_tac[]) >>
  suspend "loop"
QED

Resume window_array_strong_contract_mem[loop]:
  `(active ==> (if active then loop_st.cs_next_id+2 else 0) NOTIN
    window_alloca_sites func (frag_ids body_st body_end))` by
    (Cases_on `active` >> gvs[]) >>
  `(active ==> (if active then loop_st.cs_next_id+2 else 0) IN loop_ids /\
    (if active then loop_st.cs_next_id+2 else 0) NOTIN
      window_alloca_sites func (frag_ids body_st body_end) /\
    (if active then loop_st.cs_next_id+2 else 0) <> loop_st.cs_next_id)` by
    metis_tac[] >>
  drule_all window_array_loop_parent_mem >> strip_tac >>
  rename1 `window_array_transition ctx func owner loop_ids _ entry completed` >>
  `window_array_inv ctx func owner loop_ids ei asz msz active ty avs src dst
    ip loop_st.cs_next_id bi dp (if active then loop_st.cs_next_id+2 else 0) bd
    count_op exit_st.cs_current_bb sb cap d (LENGTH avs) completed` by
    metis_tac[] >>
  drule_all window_array_exit_parent_mem >> strip_tac >>
  `mem_cont_sim ctx func s t` by metis_tac[mem_cont_sim_trans] >>
  suspend "package"
QED

Resume window_array_strong_contract_mem[package]:
  `!x. not_fresh_at st x ==> not_fresh_at owner x` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `st` >> asm_rewrite_tac[] >> decide_tac) >>
  `window_array_transition ctx func st ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] entry completed` by
    (irule window_array_transition_owner_weaken >> qexists_tac `owner` >>
     asm_rewrite_tac[] >> irule window_array_transition_region >>
     qexistsl_tac [`loop_ids`, `[(d,LENGTH (enc (Array NONE ty) (ListV avs))) ]`] >>
     asm_rewrite_tac[] >> simp[]) >>
  `window_array_transition ctx func st ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] completed t` by
    (irule window_array_transition_owner_weaken >> qexists_tac `owner` >>
     asm_rewrite_tac[] >> irule window_array_transition_region >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`] >>
     asm_rewrite_tac[] >> simp[]) >>
  `32 <= LENGTH (enc (Array NONE ty) (ListV avs))` by
    (`abi_encoder_window_input (AbiDynArray ei asz msz active)
       (Array NONE ty) (ListV avs) sb cap s.vs_memory` by
       fs[window_array_root_def] >>
     drule window_array_layout >> decide_tac) >>
  `window_array_transition ctx func st ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s entry` by
    (irule window_array_transition_region >> qexistsl_tac [`ids`, `[(d,32)]`] >>
     asm_rewrite_tac[] >> simp[]) >>
  `window_array_transition ctx func st ids
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t` by
    (irule window_array_transition_trans >>
     qexists_tac `entry` >> asm_rewrite_tac[] >>
     irule window_array_transition_trans >>
     qexists_tac `completed` >> asm_rewrite_tac[]) >>
  suspend "result"
QED

Resume window_array_strong_contract_mem[result]:
  `window_sizes32 ids s` by fs[window_array_root_def] >>
  `window_sizes32 ids t` by
    (qpat_x_assum `window_array_transition ctx func st ids _ s t` mp_tac >>
     simp_tac bool_ss [window_array_transition_def] >>
     strip_tac >> first_x_assum irule >> asm_rewrite_tac[]) >>
  qpat_x_assum `window_array_transition ctx func st ids _ s t` mp_tac >>
  simp_tac bool_ss [window_array_transition_def] >> strip_tac >>
  `abi_encoder_registered_effect (frag_ids st st')
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`ids`, `[(d,LENGTH (enc (Array NONE ty) (ListV avs))) ]`] >>
     asm_rewrite_tac[] >>
     simp_tac bool_ss [Abbr `ids`] >> irule window_alloca_sites_subset) >>
  qexists_tac `t` >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  asm_rewrite_tac[] >>
  conj_tac >- metis_tac[abiEncoderExtendSimTheory.abi_encoder_extend_sim_sim] >>
  qpat_x_assum `window_sizes32 ids t` mp_tac >>
  simp_tac bool_ss [window_sizes32_def, Abbr `ids`] >>
  strip_tac >> asm_rewrite_tac[]
QED

Finalise window_array_strong_contract_mem
