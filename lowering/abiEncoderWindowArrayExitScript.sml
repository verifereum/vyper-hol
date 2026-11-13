(* Scalar exit sequences retain the actual source memory and allocation map. *)
Theory abiEncoderWindowArrayExit
Ancestors
  abiEncoderWindowArrayBody abiEncoderWindowArrayLayout abiEncoderWindow
  valueEncoding valueEncodingDefs valueEncodingProps contractABI
  abiEncoderArrayCode abiEncoderWindowSequence
  abiEncoderWindowPhase emitHelper compileEnv venomState venomInst words list arithmetic

Theorem window_array_static_exit_pure_observed:
  abi_encode_array_static_exit src asz st = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  mload sb s = n2w n ==>
  ?t. window_pure_seq st en s t /\
    eval_operand out t = SOME (n2w (32+n*asz)) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  simp_tac bool_ss [abi_encode_array_static_exit_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  rename1 `emit_op MLOAD [src] st = (len,c1)` >>
  rename1 `emit_op MUL [len;Lit (n2w asz)] c1 = (payload,c2)` >>
  `?t1. window_pure_seq st c1 s t1 /\
      eval_operand len t1 = SOME (n2w n) /\
      (!x. len = Var x ==> not_fresh_at c1 x)` by
    (drule_all window_emit_load_pure >> simp[]) >>
  `?t2. window_pure_seq c1 c2 t1 t2 /\
      eval_operand payload t2 = SOME (n2w (n*asz)) /\
      (!x. payload = Var x ==> not_fresh_at c2 x)` by
    (`eval_operand (Lit (n2w asz)) t1 = SOME (n2w asz)` by simp[eval_operand_def] >>
     drule_all window_array_mul_pure >> simp[word_mul_n2w]) >>
  `eval_operand (Lit 32w) t2 = SOME (32w:bytes32)` by simp[eval_operand_def] >>
  drule_all window_emit_add_pure >> simp[word_add_n2w] >> strip_tac >>
  `!x. ~not_fresh_at c1 x ==> lookup_var x t1 = lookup_var x s` by
    (rpt strip_tac >> irule window_array_register_high >> qexistsl_tac [`c1`, `MLOAD`, `[src]`, `len`, `st`] >> simp[]) >>
  `!x. ~not_fresh_at c2 x ==> lookup_var x t2 = lookup_var x t1` by
    (rpt strip_tac >> irule window_array_register_high >>
     qexistsl_tac [`c2`, `MUL`, `[len;Lit (n2w asz)]`, `payload`, `c1`] >> simp[]) >>
  `!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x t2` by
    (rpt strip_tac >> irule window_array_register_high >>
     qexistsl_tac [`en`, `ADD`, `[Lit 32w;payload]`, `out`, `c2`] >> simp[]) >>
  `st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
    c2.cs_next_var <= en.cs_next_var` by
    metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  `!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  metis_tac[window_pure_seq_chain]
QED

Theorem window_array_static_exit_pure:
  abi_encode_array_static_exit src asz st = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  mload sb s = n2w n ==>
  ?t. window_pure_seq st en s t /\
    eval_operand out t = SOME (n2w (32+n*asz)) /\
    (!x. out = Var x ==> not_fresh_at en x)
Proof
  strip_tac >> drule_all window_array_static_exit_pure_observed >>
  strip_tac >> qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem window_array_dynamic_exit_pure_observed:
  abi_encode_array_dynamic_exit src dyn_ptr st = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  eval_operand dyn_ptr s = SOME (n2w slot) /\ slot < dimword (:256) /\
  (!x. dyn_ptr = Var x ==> not_fresh_at st x) /\
  mload slot s = n2w offset ==>
  ?t. window_pure_seq st en s t /\
    eval_operand out t = SOME (n2w (32+offset)) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  simp_tac bool_ss [abi_encode_array_dynamic_exit_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  rename1 `emit_op MLOAD [src] st = (unused,c1)` >>
  rename1 `emit_op MLOAD [dyn_ptr] c1 = (off,c2)` >>
  `?t1. window_pure_seq st c1 s t1 /\
      eval_operand unused t1 = SOME (mload sb s) /\
      (!x. unused = Var x ==> not_fresh_at c1 x)` by
    (metis_tac[window_emit_load_pure]) >>
  `eval_operand dyn_ptr t1 = SOME (n2w slot)` by
    (irule window_seq_eval >> metis_tac[window_pure_seq_def]) >>
  `mload slot t1 = n2w offset` by
    fs[window_pure_seq_def, mload_def] >>
  `?t2. window_pure_seq c1 c2 t1 t2 /\
      eval_operand off t2 = SOME (n2w offset) /\
      (!x. off = Var x ==> not_fresh_at c2 x)` by
    (drule_all window_emit_load_pure >> simp[]) >>
  `eval_operand (Lit 32w) t2 = SOME (32w:bytes32)` by simp[eval_operand_def] >>
  drule_all window_emit_add_pure >> simp[word_add_n2w] >> strip_tac >>
  `!x. ~not_fresh_at c1 x ==> lookup_var x t1 = lookup_var x s` by
    (rpt strip_tac >> irule window_array_register_high >>
     qexistsl_tac [`c1`, `MLOAD`, `[src]`, `unused`, `st`] >> simp[]) >>
  `!x. ~not_fresh_at c2 x ==> lookup_var x t2 = lookup_var x t1` by
    (rpt strip_tac >> irule window_array_register_high >>
     qexistsl_tac [`c2`, `MLOAD`, `[dyn_ptr]`, `off`, `c1`] >> simp[]) >>
  `!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x t2` by
    (rpt strip_tac >> irule window_array_register_high >>
     qexistsl_tac [`en`, `ADD`, `[Lit 32w;off]`, `out`, `c2`] >> simp[]) >>
  `st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
    c2.cs_next_var <= en.cs_next_var` by
    metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  `!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  metis_tac[window_pure_seq_chain]
QED

Theorem window_array_dynamic_exit_pure:
  abi_encode_array_dynamic_exit src dyn_ptr st = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  eval_operand dyn_ptr s = SOME (n2w slot) /\ slot < dimword (:256) /\
  (!x. dyn_ptr = Var x ==> not_fresh_at st x) /\
  mload slot s = n2w offset ==>
  ?t. window_pure_seq st en s t /\
    eval_operand out t = SOME (n2w (32+offset)) /\
    (!x. out = Var x ==> not_fresh_at en x)
Proof
  strip_tac >> drule_all window_array_dynamic_exit_pure_observed >>
  strip_tac >> qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem window_array_static_exit_phase_observed:
  abi_encode_array_static_exit src asz st = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  mload sb s = n2w n /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    window_array_transition ctx func st {} [] s t /\
    eval_operand out t = SOME (n2w (32+n*asz)) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all window_array_static_exit_pure_observed >> strip_tac >>
  `window_phase ctx func st en {} [] s
     (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_pure_seq_phase] >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  asm_rewrite_tac[] >> conj_tac
  >- metis_tac[window_array_pure_phase_transition] >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

Theorem window_array_dynamic_exit_phase_observed:
  abi_encode_array_dynamic_exit src dyn_ptr st = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  eval_operand dyn_ptr s = SOME (n2w slot) /\ slot < dimword (:256) /\
  (!x. dyn_ptr = Var x ==> not_fresh_at st x) /\
  mload slot s = n2w offset /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    window_array_transition ctx func st {} [] s t /\
    eval_operand out t = SOME (n2w (32+offset)) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all window_array_dynamic_exit_pure_observed >> strip_tac >>
  `window_phase ctx func st en {} [] s
     (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_pure_seq_phase] >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  asm_rewrite_tac[] >> conj_tac
  >- metis_tac[window_array_pure_phase_transition] >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

Theorem window_array_exit_offset:
  abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap mem ==>
  32 + (if active then LENGTH avs * abi_member_head_size ty +
       SUM (MAP (abi_member_tail_size ty) avs) else LENGTH avs * asz) =
    LENGTH (enc (Array NONE ty) (ListV avs))
Proof
  strip_tac >> drule window_array_layout >> strip_tac >>
  Cases_on `active` >- (asm_rewrite_tac[] >> rewrite_tac[ADD_ASSOC]) >>
  `asz = abi_member_head_size ty /\ ~is_dynamic ty` by
    fs[abi_encoder_window_array_iff] >>
  `SUM (MAP (abi_member_tail_size ty) avs) = 0` by
    (qpat_x_assum `abi_encoder_window_input _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `LENGTH (enc _ _) = _` kall_tac >>
     Induct_on `avs` >> simp[abiDecodeRangesTheory.abi_member_tail_size_def]) >>
  asm_rewrite_tac[] >> simp[]
QED

Theorem window_array_scalar_exit_pure_observed:
  abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap s.vs_memory /\
  (if active then abi_encode_array_dynamic_exit src dp st
   else abi_encode_array_static_exit src asz st) = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  (active ==> eval_operand dp s = SOME (n2w slot) /\ slot < dimword (:256) /\
    (!x. dp = Var x ==> not_fresh_at st x) /\
    mload slot s = n2w (LENGTH avs * abi_member_head_size ty +
       SUM (MAP (abi_member_tail_size ty) avs))) ==>
  ?t. window_pure_seq st en s t /\
    eval_operand out t = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule window_array_exit_offset >> strip_tac >>
  Cases_on `active` >> full_simp_tac bool_ss [COND_CLAUSES, IMP_CLAUSES]
  >- (drule_all window_array_dynamic_exit_pure_observed >>
      asm_rewrite_tac[]) >>
  `mload sb s = n2w (LENGTH avs)` by
    (qpat_x_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp[abi_encoder_window_array_iff, mload_def, mem_word_at_def]) >>
  drule_all window_array_static_exit_pure_observed >> asm_rewrite_tac[]
QED

Theorem window_array_scalar_exit_run_observed:
  abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap s.vs_memory /\
  abi_encoder_array_prefix ty avs (LENGTH avs) d s.vs_memory /\
  (if active then abi_encode_array_dynamic_exit src dp st
   else abi_encode_array_static_exit src asz st) = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  (active ==> eval_operand dp s = SOME (n2w slot) /\ slot < dimword (:256) /\
    (!x. dp = Var x ==> not_fresh_at st x) /\
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
    (!x. out = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all window_array_scalar_exit_pure_observed >> strip_tac >>
  `mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) s.vs_memory =
      enc (Array NONE ty) (ListV avs)` by
    metis_tac[window_array_prefix_complete] >>
  `window_phase ctx func st en {} [] s
     (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_pure_seq_phase] >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  asm_rewrite_tac[] >> conj_tac
  >- metis_tac[window_array_pure_phase_transition] >>
  `t.vs_memory = s.vs_memory` by fs[window_pure_seq_def] >>
  simp_tac (srw_ss()) [] >> asm_rewrite_tac[] >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

(* Original interfaces are projections of the same execution witnesses. *)
Theorem window_array_static_exit_phase:
  abi_encode_array_static_exit src asz st = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  mload sb s = n2w n /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    window_array_transition ctx func st {} [] s t /\
    eval_operand out t = SOME (n2w (32+n*asz)) /\
    (!x. out = Var x ==> not_fresh_at en x)
Proof
  strip_tac >> drule_all window_array_static_exit_phase_observed >>
  strip_tac >> qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem window_array_dynamic_exit_phase:
  abi_encode_array_dynamic_exit src dyn_ptr st = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  eval_operand dyn_ptr s = SOME (n2w slot) /\ slot < dimword (:256) /\
  (!x. dyn_ptr = Var x ==> not_fresh_at st x) /\
  mload slot s = n2w offset /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    window_array_transition ctx func st {} [] s t /\
    eval_operand out t = SOME (n2w (32+offset)) /\
    (!x. out = Var x ==> not_fresh_at en x)
Proof
  strip_tac >> drule_all window_array_dynamic_exit_phase_observed >>
  strip_tac >> qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem window_array_scalar_exit_pure:
  abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap s.vs_memory /\
  (if active then abi_encode_array_dynamic_exit src dp st
   else abi_encode_array_static_exit src asz st) = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  (active ==> eval_operand dp s = SOME (n2w slot) /\ slot < dimword (:256) /\
    (!x. dp = Var x ==> not_fresh_at st x) /\
    mload slot s = n2w (LENGTH avs * abi_member_head_size ty +
       SUM (MAP (abi_member_tail_size ty) avs))) ==>
  ?t. window_pure_seq st en s t /\
    eval_operand out t = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    (!x. out = Var x ==> not_fresh_at en x)
Proof
  strip_tac >> drule_all window_array_scalar_exit_pure_observed >>
  strip_tac >> qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem window_array_scalar_exit_run:
  abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap s.vs_memory /\
  abi_encoder_array_prefix ty avs (LENGTH avs) d s.vs_memory /\
  (if active then abi_encode_array_dynamic_exit src dp st
   else abi_encode_array_static_exit src asz st) = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  (active ==> eval_operand dp s = SOME (n2w slot) /\ slot < dimword (:256) /\
    (!x. dp = Var x ==> not_fresh_at st x) /\
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
    (!x. out = Var x ==> not_fresh_at en x)
Proof
  strip_tac >> drule_all window_array_scalar_exit_run_observed >>
  strip_tac >> qexists_tac `t` >> asm_rewrite_tac[]
QED
