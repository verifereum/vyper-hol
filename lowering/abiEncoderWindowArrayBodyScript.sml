(* Straight-line support for actual-window array bodies. *)
Theory abiEncoderWindowArrayBody
Ancestors
  abiEncoderWindowContract abiEncoderRegisteredEffect abiEncoderWindowStructuralMembers
  abiEncoderWindowArrayLayout abiEncoderOpenInput abiCanonicalWindows abiEncoderArrayPrefix abiEncoderTuple abiEncoderMemory valueEncoding valueEncodingProps contractABI rich_list
  abiEncoderArrayDynamicMemory abiEncoderWindowArrayInvariant abiEncoderArrayBodyCode abiEncoderArrayCode abiEncoderArrayTail abiEncoderWindowSequence
  abiEncoderWindowPhase abiEncoderWindowLeaves abiEncoderWindowChild
  abiEncoderAdmissible abiEncoder emitHelperProps emitHelper compileEnv
  pred_set instIdxIndep freshWrites exprLoweringProps fragExec venomState venomExecSemantics venomInst words list finite_map arithmetic

Theorem window_array_register_high:
  emit_op opc ops st = (out,en) /\ opc <> INVOKE /\
  window_pure_seq st en s t ==>
  !x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s
Proof
  rpt strip_tac >>
  `lookup_var x (t with vs_inst_idx := t.vs_inst_idx) = lookup_var x s` suffices_by simp[] >>
  irule window_seq_high_vars >> qexistsl_tac [`en`, `st`] >> simp[] >> conj_tac
  >- (irule abiEncoderWindowLookupTheory.abi_window_emit_register_bounds >>
      qexistsl_tac [`ops`, `opc`, `out`] >> asm_rewrite_tac[]) >>
  metis_tac[window_pure_seq_def]
QED

Theorem window_array_mul_pure_observed:
  emit_op MUL [lhs;rhs] st = (out,en) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b ==>
  ?t. window_pure_seq st en s t /\ eval_operand out t = SOME (a*b) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts st en) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) (a*b) s)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     asm_simp_tac (srw_ss()) [run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_pure2_def, eval_operands_def]) >>
  `?t. window_pure_seq st en s t /\ eval_operand out t = SOME (a*b) /\
    (!x. out = Var x ==> not_fresh_at en x)` by
    (qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) (a*b) s` >>
     irule window_emit_register_pure >> (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`[lhs;rhs]`, `MUL`] >> simp[is_terminator_def]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >> rpt strip_tac >>
  irule window_array_register_high >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`MUL`, `[lhs;rhs]`, `out`, `st`] >> simp[]
QED

Theorem window_array_mul_pure:
  emit_op MUL [lhs;rhs] st = (out,en) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b ==>
  ?t. window_pure_seq st en s t /\ eval_operand out t = SOME (a*b) /\
    (!x. out = Var x ==> not_fresh_at en x)
Proof
  strip_tac >> drule_all window_array_mul_pure_observed >> metis_tac[]
QED

Theorem window_array_mul_phase_observed:
  emit_op MUL [lhs;rhs] st = (out,en) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (a*b) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all window_array_mul_pure_observed >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  Cases_on `out` >> fs[eval_operand_def, lookup_var_def]
QED

Theorem window_array_mul_phase:
  emit_op MUL [lhs;rhs] st = (out,en) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand out t = SOME (a*b) /\
    (!x. out = Var x ==> not_fresh_at en x)
Proof
  strip_tac >> drule_all window_array_mul_phase_observed >> metis_tac[]
QED

Theorem window_array_phase_transition:
  window_phase ctx func owner en ids outs s t /\
  (!R. window_sizes32 R s ==> window_sizes32 R t) ==>
  window_array_transition ctx func owner ids outs s t
Proof
  simp_tac bool_ss [window_phase_def, window_array_transition_def] >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem window_array_pure_phase_sizes:
  window_phase ctx func owner en {} [] s t ==>
  !R. window_sizes32 R s ==> window_sizes32 R t
Proof
  strip_tac >> drule window_phase_effect >>
  simp_tac bool_ss [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def,
    window_sizes32_def] >> strip_tac >> fs[]
QED

Theorem window_array_pure_phase_transition:
  window_phase ctx func owner en {} [] s t ==>
  window_array_transition ctx func owner {} [] s t
Proof
  metis_tac[window_array_phase_transition, window_array_pure_phase_sizes]
QED

Theorem window_array_static_info_eq:
  abi_encoder_admissible (AbiDynArray ei asz msz F) ==>
  compile_abi_encode_static_info dst src ei = compile_abi_encode_to_buf dst src ei
Proof
  simp_tac bool_ss [Once abi_encoder_admissible_def] >> strip_tac >>
  irule abi_encode_static_info_agrees >> asm_rewrite_tac[]
QED

Theorem window_array_coordinates_pure_observed:
  abi_decode_indexed_coordinates base_op idx stride st = (ops,en) /\
  eval_operand base_op s = SOME (n2w b) /\ eval_operand idx s = SOME (n2w j) /\
  (!x. idx = Var x ==> not_fresh_at st x) ==>
  ?t. window_pure_seq st en s t /\
    eval_operand (FST ops) t = SOME (n2w (b+32)) /\
    eval_operand (SND ops) t = SOME (n2w (b+32+j*stride)) /\
    (!x. FST ops = Var x \/ SND ops = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  simp_tac bool_ss [abiDecoderDynamicLoopSetupTheory.abi_decode_indexed_coordinates_def,
    comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [base_op; Lit 32w] st = (data_op,c1)` >>
  rename1 `emit_op MUL [idx; Lit (n2w stride)] c1 = (off_op,c2)` >>
  rename1 `emit_op ADD [data_op;off_op] c2 = (address_op,en)` >>
  `?t1. window_pure_seq st c1 s t1 /\
      eval_operand data_op t1 = SOME (n2w (b+32)) /\
      (!x. data_op = Var x ==> not_fresh_at c1 x)` by
    (`eval_operand (Lit 32w) s = SOME (32w:bytes32)` by simp[eval_operand_def] >>
     drule_all window_emit_add_pure >> simp[word_add_n2w]) >>
  `eval_operand idx t1 = SOME (n2w j)` by
    (irule window_seq_eval >>
     metis_tac[window_pure_seq_def]) >>
  `?t2. window_pure_seq c1 c2 t1 t2 /\
      eval_operand off_op t2 = SOME (n2w (j*stride)) /\
      (!x. off_op = Var x ==> not_fresh_at c2 x)` by
    (`eval_operand (Lit (n2w stride)) t1 = SOME (n2w stride)` by simp[eval_operand_def] >>
     drule_all window_array_mul_pure >> simp[word_mul_n2w]) >>
  `eval_operand data_op t2 = SOME (n2w (b+32))` by
    (irule window_seq_eval >> metis_tac[window_pure_seq_def]) >>
  `?t3. window_pure_seq c2 en t2 t3 /\
      eval_operand address_op t3 = SOME (n2w (b+32+j*stride)) /\
      (!x. address_op = Var x ==> not_fresh_at en x)` by
    (drule_all window_emit_add_pure >> simp[word_add_n2w]) >>
  `c1.cs_next_var <= c2.cs_next_var /\ c2.cs_next_var <= en.cs_next_var` by
    metis_tac[window_pure_seq_def, window_seq_mono] >>
  `eval_operand data_op t3 = SOME (n2w (b+32))` by
    (irule window_seq_eval >>
     metis_tac[window_pure_seq_def, not_fresh_at_mono]) >>
  `!x. ~not_fresh_at c1 x ==> lookup_var x t1 = lookup_var x s` by
    (rpt strip_tac >> irule window_array_register_high >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`ADD`, `[base_op; Lit 32w]`, `data_op`, `st`] >> simp[]) >>
  `!x. ~not_fresh_at c2 x ==> lookup_var x t2 = lookup_var x t1` by
    (rpt strip_tac >> irule window_array_register_high >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`MUL`, `[idx; Lit (n2w stride)]`, `off_op`, `c1`] >> simp[]) >>
  `!x. ~not_fresh_at en x ==> lookup_var x t3 = lookup_var x t2` by
    (rpt strip_tac >> irule window_array_register_high >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`ADD`, `[data_op;off_op]`, `address_op`, `c2`] >> simp[]) >>
  qexists_tac `t3` >> simp[] >> conj_tac
  >- metis_tac[window_pure_seq_chain] >> conj_tac
  >- metis_tac[not_fresh_at_mono] >>
  metis_tac[not_fresh_at_mono]
QED

Theorem window_array_coordinates_pure:
  abi_decode_indexed_coordinates base_op idx stride st = (ops,en) /\
  eval_operand base_op s = SOME (n2w b) /\ eval_operand idx s = SOME (n2w j) /\
  (!x. idx = Var x ==> not_fresh_at st x) ==>
  ?t. window_pure_seq st en s t /\
    eval_operand (FST ops) t = SOME (n2w (b+32)) /\
    eval_operand (SND ops) t = SOME (n2w (b+32+j*stride)) /\
    (!x. FST ops = Var x \/ SND ops = Var x ==> not_fresh_at en x)
Proof
  strip_tac >> drule_all window_array_coordinates_pure_observed >> metis_tac[]
QED

Theorem window_array_head_setup_pure_observed:
  abi_decode_array_head_setup ip src stride st = (ops,en) /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = n2w j /\ eval_operand src s = SOME (n2w b) /\
  (!x. src = Var x ==> not_fresh_at st x) ==>
  ?t. window_pure_seq st en s t /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (b+32)) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (b+32+j*stride)) /\
    (!x. FST ops = Var x \/ FST (SND ops) = Var x \/ SND (SND ops) = Var x ==>
      not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  simp_tac bool_ss [abiDecoderDynamicLoopSetupTheory.abi_decode_array_head_setup_def,
    comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [ip] st = (idx,mid)` >>
  rename1 `abi_decode_indexed_coordinates src idx stride mid = (coords,en)` >>
  `?t1. window_pure_seq st mid s t1 /\ eval_operand idx t1 = SOME (n2w j) /\
    (!x. idx = Var x ==> not_fresh_at mid x)` by
    (drule_all window_emit_load_pure >> asm_rewrite_tac[]) >>
  `eval_operand src t1 = SOME (n2w b)` by
    (irule window_seq_eval >> metis_tac[window_pure_seq_def]) >>
  `?t2. window_pure_seq mid en t1 t2 /\
    eval_operand (FST coords) t2 = SOME (n2w (b+32)) /\
    eval_operand (SND coords) t2 = SOME (n2w (b+32+j*stride)) /\
    (!x. FST coords = Var x \/ SND coords = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t2 = lookup_var x t1)` by
    (drule_all window_array_coordinates_pure_observed >> simp[]) >>
  `eval_operand idx t2 = SOME (n2w j)` by
    (irule window_seq_eval >> metis_tac[window_pure_seq_def]) >>
  `mid.cs_next_var <= en.cs_next_var` by
    metis_tac[window_pure_seq_def, window_seq_mono] >>
  `!x. ~not_fresh_at mid x ==> lookup_var x t1 = lookup_var x s` by
    (rpt strip_tac >> irule window_array_register_high >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`MLOAD`, `[ip]`, `idx`, `st`] >> simp[]) >>
  qexists_tac `t2` >> simp[] >> conj_tac
  >- metis_tac[window_pure_seq_chain] >> conj_tac
  >- metis_tac[not_fresh_at_mono] >>
  metis_tac[not_fresh_at_mono]
QED

Theorem window_array_head_setup_pure:
  abi_decode_array_head_setup ip src stride st = (ops,en) /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = n2w j /\ eval_operand src s = SOME (n2w b) /\
  (!x. src = Var x ==> not_fresh_at st x) ==>
  ?t. window_pure_seq st en s t /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (b+32)) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (b+32+j*stride)) /\
    (!x. FST ops = Var x \/ FST (SND ops) = Var x \/ SND (SND ops) = Var x ==>
      not_fresh_at en x)
Proof
  strip_tac >> drule_all window_array_head_setup_pure_observed >> metis_tac[]
QED

Theorem window_array_addresses_pure_observed:
  abi_encode_array_addresses ip src dst asz msz st = (coords,en) /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = n2w j /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) ==>
  ?t. window_pure_seq st en s t /\
    eval_operand (FST (FST coords)) t = SOME (n2w j) /\
    eval_operand (SND (FST coords)) t = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) t = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) t = SOME (n2w (d+32+j*asz)) /\
    (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
         FST (SND coords) = Var x \/ SND (SND coords) = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule abi_encode_array_addresses_trace >> strip_tac >> gvs[] >>
  `?t1. window_pure_seq st middle s t1 /\
    eval_operand (FST src_ops) t1 = SOME (n2w j) /\
    eval_operand (FST (SND src_ops)) t1 = SOME (n2w (sb+32)) /\
    eval_operand (SND (SND src_ops)) t1 = SOME (n2w (sb+32+j*msz)) /\
    (!x. FST src_ops = Var x \/ FST (SND src_ops) = Var x \/ SND (SND src_ops) = Var x ==>
      not_fresh_at middle x) /\
    (!x. ~not_fresh_at middle x ==> lookup_var x t1 = lookup_var x s)` by
    (`!x. src = Var x ==> not_fresh_at st x` by metis_tac[] >>
     drule_all window_array_head_setup_pure_observed >> simp[]) >>
  `eval_operand dst t1 = SOME (n2w d)` by
    (irule window_seq_eval >> metis_tac[window_pure_seq_def]) >>
  `?t2. window_pure_seq middle en t1 t2 /\
    eval_operand (FST dst_ops) t2 = SOME (n2w (d+32)) /\
    eval_operand (SND dst_ops) t2 = SOME (n2w (d+32+j*asz)) /\
    (!x. FST dst_ops = Var x \/ SND dst_ops = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t2 = lookup_var x t1)` by
    (`!x. FST src_ops = Var x ==> not_fresh_at middle x` by metis_tac[] >>
     drule_all window_array_coordinates_pure_observed >> simp[]) >>
  `eval_operand (FST src_ops) t2 = SOME (n2w j) /\
    eval_operand (SND (SND src_ops)) t2 = SOME (n2w (sb+32+j*msz))` by
    (conj_tac >> irule window_seq_eval >> metis_tac[window_pure_seq_def]) >>
  `middle.cs_next_var <= en.cs_next_var` by metis_tac[window_pure_seq_def, window_seq_mono] >>
  qexists_tac `t2` >> simp[] >> conj_tac
  >- metis_tac[window_pure_seq_chain] >> conj_tac
  >- metis_tac[not_fresh_at_mono] >>
  metis_tac[not_fresh_at_mono]
QED

Theorem window_array_addresses_pure:
  abi_encode_array_addresses ip src dst asz msz st = (coords,en) /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = n2w j /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) ==>
  ?t. window_pure_seq st en s t /\
    eval_operand (FST (FST coords)) t = SOME (n2w j) /\
    eval_operand (SND (FST coords)) t = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) t = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) t = SOME (n2w (d+32+j*asz)) /\
    (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
         FST (SND coords) = Var x \/ SND (SND coords) = Var x ==> not_fresh_at en x)
Proof
  strip_tac >> drule_all window_array_addresses_pure_observed >> metis_tac[]
QED

Theorem window_array_addresses_phase_observed:
  abi_encode_array_addresses ip src dst asz msz st = (coords,en) /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = n2w j /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand (FST (FST coords)) t = SOME (n2w j) /\
    eval_operand (SND (FST coords)) t = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) t = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) t = SOME (n2w (d+32+j*asz)) /\
    (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
         FST (SND coords) = Var x \/ SND (SND coords) = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all window_array_addresses_pure_observed >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  simp_tac (srw_ss()) [eval_op_inst_idx, lookup_var_def] >>
  asm_rewrite_tac[] >> metis_tac[lookup_var_def]
QED

Theorem window_array_addresses_phase:
  abi_encode_array_addresses ip src dst asz msz st = (coords,en) /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = n2w j /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand (FST (FST coords)) t = SOME (n2w j) /\
    eval_operand (SND (FST coords)) t = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) t = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) t = SOME (n2w (d+32+j*asz)) /\
    (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
         FST (SND coords) = Var x \/ SND (SND coords) = Var x ==> not_fresh_at en x)
Proof
  strip_tac >> drule_all window_array_addresses_phase_observed >> metis_tac[]
QED

(* Structural windows give exactly the two processed prefix lengths. *)
Theorem window_array_prefix_lengths:
  abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap source /\ j <= LENGTH avs ==>
  LENGTH (FLAT (abi_tuple_heads hl 0 (REPLICATE j ty) (TAKE j avs))) =
    j * abi_member_head_size ty /\
  LENGTH (FLAT (abi_tuple_tails (REPLICATE j ty) (TAKE j avs))) =
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs))
Proof
  strip_tac >>
  `LIST_REL abi_encoder_layout_valid (REPLICATE j ty) (TAKE j avs)` by
    (drule window_array_member_layout >>
     simp[LIST_REL_EL_EQN, EL_REPLICATE, EL_TAKE] >> metis_tac[]) >>
  `LENGTH (TAKE j avs) = j` by simp[] >>
  mp_tac (Q.SPECL [`TAKE j avs`, `ty`] abi_encoder_uniform_sizes) >>
  simp[abi_encoder_open_heads_length, abi_tuple_tails_length]
QED

Theorem window_array_prefix_static_advance:
  abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap source /\
  abi_encoder_array_prefix ty avs j d mem /\ j < LENGTH avs /\
  ~is_dynamic ty /\
  mem_bytes_at (d+32+j*abi_member_head_size ty)
    (LENGTH (enc ty (EL j avs))) mem = enc ty (EL j avs) ==>
  abi_encoder_array_prefix ty avs (SUC j) d mem
Proof
  strip_tac >>
  `j <= LENGTH avs` by decide_tac >>
  drule_all window_array_prefix_lengths >>
  disch_then (qspec_then `LENGTH avs * abi_member_head_size ty` strip_assume_tac) >>
  irule abi_encoder_array_prefix_advance >> asm_rewrite_tac[] >>
  `mem_word_at d mem = n2w (LENGTH avs) /\
   abi_encoder_tuple_prefix (LENGTH avs * abi_member_head_size ty)
     (REPLICATE j ty) (TAKE j avs) (d+32) mem` by
    fs[abi_encoder_array_prefix_def] >>
  asm_rewrite_tac[] >> irule abi_encoder_tuple_prefix_append >>
  asm_simp_tac (srw_ss()) [Excl "enc_def", ADD_ASSOC] >>
  simp_tac (srw_ss()) [mem_bytes_at_def]
QED

Theorem window_array_prefix_dynamic_advance:
  abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap source /\
  abi_encoder_array_prefix ty avs j d mem /\ j < LENGTH avs /\
  is_dynamic ty /\
  mem_word_at (d+32+j*abi_member_head_size ty) mem =
    n2w (LENGTH avs*abi_member_head_size ty +
      SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) /\
  mem_bytes_at (d+32+LENGTH avs*abi_member_head_size ty +
      SUM (MAP (abi_member_tail_size ty) (TAKE j avs)))
    (LENGTH (enc ty (EL j avs))) mem = enc ty (EL j avs) ==>
  abi_encoder_array_prefix ty avs (SUC j) d mem
Proof
  strip_tac >>
  `j <= LENGTH avs` by decide_tac >>
  drule_all window_array_prefix_lengths >>
  disch_then (qspec_then `LENGTH avs * abi_member_head_size ty` strip_assume_tac) >>
  irule abi_encoder_array_prefix_advance >> asm_rewrite_tac[] >>
  `mem_word_at d mem = n2w (LENGTH avs) /\
   abi_encoder_tuple_prefix (LENGTH avs * abi_member_head_size ty)
     (REPLICATE j ty) (TAKE j avs) (d+32) mem` by
    fs[abi_encoder_array_prefix_def] >>
  asm_rewrite_tac[] >> irule abi_encoder_tuple_prefix_append >>
  asm_simp_tac (srw_ss()) [Excl "enc_def", ADD_ASSOC,
    LENGTH_enc_number, abi_encoder_word_window, enc_number_def]
QED

(* Child results carry ambient size preservation on the execution witness. *)
Theorem window_array_child_transition:
  window_strong_result ctx func ready en out at av d s t /\
  owner.cs_next_var <= ready.cs_next_var ==>
  window_array_transition ctx func owner
    (window_alloca_sites func (frag_ids ready en))
    [(d,LENGTH (enc at av))] s t
Proof
  strip_tac >>
  `window_phase ctx func ready en
    (window_alloca_sites func (frag_ids ready en))
    [(d,LENGTH (enc at av))] s t` by
    metis_tac[window_phase_strong_result] >>
  `!R. window_sizes32 R s ==> window_sizes32 R t` by
    (gen_tac >> rewrite_tac[window_sizes32_def] >> strip_tac >>
     `!i b sz. i IN window_alloca_sites func (frag_ids ready en) /\
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
       fs[window_strong_result_def] >>
     drule window_strong_result_effect >> strip_tac >>
     drule window_registered_sizes_transport >>
     disch_then (qspec_then `R` mp_tac) >> asm_rewrite_tac[]) >>
  simp_tac bool_ss [window_array_transition_def] >>
  fs[window_phase_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem window_array_prefix_registered_frame:
  abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap source /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\
  d+LENGTH (enc (Array NONE ty) (ListV avs)) <= s.vs_alloca_next /\
  abi_encoder_registered_effect ids outs s t /\ window_alloca_growth s t /\
  EVERY (\r. venomMemDefs$regions_disjoint (d,32) r) outs /\
  EVERY (\r. venomMemDefs$regions_disjoint
    (d+32,j*abi_member_head_size ty) r) outs /\
  EVERY (\r. venomMemDefs$regions_disjoint
    (d+32+LENGTH avs*abi_member_head_size ty,
     SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) r) outs /\
  (!i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint
      (d,LENGTH (enc (Array NONE ty) (ListV avs))) (b,sz)) ==>
  abi_encoder_array_prefix ty avs j d t.vs_memory
Proof
  strip_tac >>
  `j <= LENGTH avs` by fs[abi_encoder_array_prefix_def] >>
  drule_all window_array_prefix_lengths >>
  disch_then (qspec_then `LENGTH avs*abi_member_head_size ty` strip_assume_tac) >>
  `SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) <=
     SUM (MAP (abi_member_tail_size ty) avs)` by
    (`SUM (MAP (abi_member_tail_size ty) avs) =
        SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) +
        SUM (MAP (abi_member_tail_size ty) (DROP j avs))` by
       metis_tac[TAKE_DROP, MAP_APPEND, SUM_APPEND] >> decide_tac) >>
  drule window_array_layout >> strip_tac >>
  `j*abi_member_head_size ty <= LENGTH avs*abi_member_head_size ty` by simp[] >>
  `!a n. d <= a /\ a+n <= d+LENGTH (enc (Array NONE ty) (ListV avs)) /\
      EVERY (\r. venomMemDefs$regions_disjoint (a,n) r) outs ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory` by
    (rpt strip_tac >> irule window_alloca_growth_frame >>
     (conj_tac >- decide_tac) >> asm_rewrite_tac[] >>
     qexistsl_tac [`ids`, `outs`] >> asm_rewrite_tac[] >> rpt strip_tac >>
     `venomMemDefs$regions_disjoint
        (d,LENGTH (enc (Array NONE ty) (ListV avs))) (b,sz)` by metis_tac[] >>
     pop_assum mp_tac >> pure_rewrite_tac[venomMemDefsTheory.regions_disjoint_def] >>
     decide_tac) >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 s.vs_memory` by
    (first_x_assum irule >> simp[] >> decide_tac) >>
  `mem_bytes_at (d+32) (j*abi_member_head_size ty) t.vs_memory =
    mem_bytes_at (d+32) (j*abi_member_head_size ty) s.vs_memory` by
    (first_x_assum irule >> simp[] >> decide_tac) >>
  `mem_bytes_at (d+32+LENGTH avs*abi_member_head_size ty)
      (SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) t.vs_memory =
    mem_bytes_at (d+32+LENGTH avs*abi_member_head_size ty)
      (SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) s.vs_memory` by
    (first_x_assum irule >> simp[] >> decide_tac) >>
  full_simp_tac bool_ss [abi_encoder_array_prefix_def, abi_encoder_tuple_prefix_def,
    mem_word_at_def, GSYM mem_bytes_at_def]
QED

Theorem window_array_element_run_core[local]:
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
  j < LENGTH avs /\ owner.cs_next_var <= ready.cs_next_var /\
  window_alloca_sites func (frag_ids ready en) SUBSET ids /\
  fn_has_code ready en func /\
  eval_operand child_src s = SOME (n2w (sb+32+j*msz)) /\
  eval_operand child_dst s = SOME (n2w (d+off)) /\
  (!x. child_src = Var x \/ child_dst = Var x ==> not_fresh_at ready x) /\
  off+LENGTH (enc ty (EL j avs)) <= LENGTH (enc (Array NONE ty) (ListV avs)) /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts /\
  window_strong_contract ei /\ (obsv ==> window_observed_contract ei) /\
  compile_abi_encode_to_buf child_dst child_src ei ready = (out,en) ==>
  ?t. window_array_transition ctx func owner
      (window_alloca_sites func (frag_ids ready en))
      [(d+off,LENGTH (enc ty (EL j avs)))] s t /\
    window_strong_result ctx func ready en out ty (EL j avs) (d+off) s t /\
    (obsv ==> !x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all window_array_root_live_pre >> strip_tac >>
  `?t. window_strong_result ctx func ready en out ty (EL j avs) (d+off) s t /\
    (obsv ==> !x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)` by
    (Cases_on `obsv`
     >- (gvs[] >> qpat_x_assum `window_observed_contract ei` mp_tac >>
         rewrite_tac[window_observed_contract_def] >> disch_then drule_all >> simp[]) >>
     gvs[] >> qpat_x_assum `window_strong_contract ei` mp_tac >>
     rewrite_tac[window_strong_contract_def] >> disch_then drule_all >> simp[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_array_child_transition >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem window_array_element_run:
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
  j < LENGTH avs /\ owner.cs_next_var <= ready.cs_next_var /\
  window_alloca_sites func (frag_ids ready en) SUBSET ids /\
  fn_has_code ready en func /\
  eval_operand child_src s = SOME (n2w (sb+32+j*msz)) /\
  eval_operand child_dst s = SOME (n2w (d+off)) /\
  (!x. child_src = Var x \/ child_dst = Var x ==> not_fresh_at ready x) /\
  off+LENGTH (enc ty (EL j avs)) <= LENGTH (enc (Array NONE ty) (ListV avs)) /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts /\
  window_strong_contract ei /\
  compile_abi_encode_to_buf child_dst child_src ei ready = (out,en) ==>
  ?t. window_array_transition ctx func owner
      (window_alloca_sites func (frag_ids ready en))
      [(d+off,LENGTH (enc ty (EL j avs)))] s t /\
    window_strong_result ctx func ready en out ty (EL j avs) (d+off) s t
Proof
  strip_tac >> drule_all (SIMP_RULE bool_ss [] (Q.INST [`obsv` |-> `F`]
    (SPEC_ALL window_array_element_run_core))) >> simp[]
QED

Theorem window_array_element_run_observed:
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
  j < LENGTH avs /\ owner.cs_next_var <= ready.cs_next_var /\
  window_alloca_sites func (frag_ids ready en) SUBSET ids /\
  fn_has_code ready en func /\
  eval_operand child_src s = SOME (n2w (sb+32+j*msz)) /\
  eval_operand child_dst s = SOME (n2w (d+off)) /\
  (!x. child_src = Var x \/ child_dst = Var x ==> not_fresh_at ready x) /\
  off+LENGTH (enc ty (EL j avs)) <= LENGTH (enc (Array NONE ty) (ListV avs)) /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts /\
  window_observed_contract ei /\
  compile_abi_encode_to_buf child_dst child_src ei ready = (out,en) ==>
  ?t. window_array_transition ctx func owner
      (window_alloca_sites func (frag_ids ready en))
      [(d+off,LENGTH (enc ty (EL j avs)))] s t /\
    window_strong_result ctx func ready en out ty (EL j avs) (d+off) s t /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule window_observed_contract_strong >> strip_tac >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`obsv` |-> `T`]
    (SPEC_ALL window_array_element_run_core))) >> simp[]
QED

Theorem window_array_static_prefix_frame:
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\ ~is_dynamic ty /\
  child_ids SUBSET ids /\
  window_array_transition ctx func ready child_ids
    [(d+32+j*abi_member_head_size ty,LENGTH (enc ty (EL j avs)))] s t ==>
  abi_encoder_array_prefix ty avs j d t.vs_memory
Proof
  strip_tac >>
  `abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap s.vs_memory /\
   d+LENGTH (enc (Array NONE ty) (ListV avs)) <= s.vs_alloca_next` by
    fs[window_array_root_def] >>
  drule_all window_array_prefix_step_geometry >> strip_tac >>
  `j*abi_member_head_size ty+LENGTH (enc ty (EL j avs)) <=
     LENGTH avs*abi_member_head_size ty` by metis_tac[] >>
  irule window_array_prefix_registered_frame >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`child_ids`,
    `[(d+32+j*abi_member_head_size ty,LENGTH (enc ty (EL j avs)))]`, `s`] >>
  asm_rewrite_tac[] >>
  `abi_encoder_registered_effect child_ids
      [(d+32+j*abi_member_head_size ty,LENGTH (enc ty (EL j avs)))] s t /\
   window_alloca_growth s t` by
    metis_tac[window_array_transition_effect, window_array_transition_resources] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- simp[venomMemDefsTheory.regions_disjoint_def]
  >- simp[venomMemDefsTheory.regions_disjoint_def]
  >- (qpat_x_assum `j * _ + LENGTH _ <= _` mp_tac >>
      simp_tac (srw_ss()) [EVERY_DEF, venomMemDefsTheory.regions_disjoint_def] >>
      strip_tac >> ntac 3 disj2_tac >>
      asm_rewrite_tac[GSYM ADD_ASSOC, LE_ADD_LCANCEL]) >>
  rpt strip_tac >>
  `i IN ids` by metis_tac[SUBSET_DEF] >>
  metis_tac[window_array_root_def]
QED

Theorem window_array_static_element_run_core[local]:
  window_array_root ctx func owner ids ei asz msz F ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  owner.cs_next_var <= ready.cs_next_var /\
  window_alloca_sites func (frag_ids ready en) SUBSET ids /\
  fn_has_code ready en func /\
  eval_operand child_src s = SOME (n2w (sb+32+j*msz)) /\
  eval_operand child_dst s = SOME (n2w (d+32+j*asz)) /\
  (!x. child_src = Var x \/ child_dst = Var x ==> not_fresh_at ready x) /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts /\
  window_strong_contract ei /\ (obsv ==> window_observed_contract ei) /\
  compile_abi_encode_static_info child_dst child_src ei ready = (out,en) ==>
  ?t. window_array_transition ctx func owner
      (window_alloca_sites func (frag_ids ready en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] s t /\
    window_strong_result ctx func ready en out ty (EL j avs) (d+32+j*asz) s t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory /\
    (obsv ==> !x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `abi_encoder_admissible (AbiDynArray ei asz msz F) /\
   abi_encoder_window_input (AbiDynArray ei asz msz F)
     (Array NONE ty) (ListV avs) sb cap s.vs_memory` by fs[window_array_root_def] >>
  `asz = abi_member_head_size ty /\ ~is_dynamic ty` by
    fs[abiEncoderWindowTheory.abi_encoder_window_array_iff] >>
  `compile_abi_encode_to_buf child_dst child_src ei ready = (out,en)` by
    metis_tac[window_array_static_info_eq] >>
  `32+j*asz+LENGTH (enc ty (EL j avs)) <=
    LENGTH (enc (Array NONE ty) (ListV avs))` by
    (drule_all window_array_prefix_step_geometry >> strip_tac >>
     `j*abi_member_head_size ty+LENGTH (enc ty (EL j avs)) <=
        LENGTH avs*abi_member_head_size ty` by metis_tac[] >>
     drule window_array_layout >> strip_tac >>
     asm_rewrite_tac[] >>
     qpat_x_assum `j * _ + LENGTH _ <= _` mp_tac >> decide_tac) >>
  `?t. window_array_transition ctx func owner
      (window_alloca_sites func (frag_ids ready en))
      [(d+(32+j*asz),LENGTH (enc ty (EL j avs)))] s t /\
    window_strong_result ctx func ready en out ty (EL j avs) (d+(32+j*asz)) s t /\
    (obsv ==> !x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)` by
    (irule window_array_element_run_core >> asm_rewrite_tac[] >>
     qexistsl_tac [`F`, `asz`, `cap`, `child_dst`, `child_src`, `dst`, `ei`,
       `ids`, `msz`, `sb`, `src`] >> asm_rewrite_tac[ADD_ASSOC]) >>
  qexists_tac `t` >> full_simp_tac bool_ss [ADD_ASSOC] >> asm_rewrite_tac[] >>
  irule window_array_prefix_static_advance >>
  `abi_encoder_array_prefix ty avs j d t.vs_memory` by
    (irule window_array_static_prefix_frame >> metis_tac[]) >>
  `mem_bytes_at (d+32+j*abi_member_head_size ty)
      (LENGTH (enc ty (EL j avs))) t.vs_memory = enc ty (EL j avs)` by
    metis_tac[window_strong_result_public, abi_encoder_window_result_output] >>
  metis_tac[]
QED

Theorem window_array_static_element_run:
  window_array_root ctx func owner ids ei asz msz F ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  owner.cs_next_var <= ready.cs_next_var /\
  window_alloca_sites func (frag_ids ready en) SUBSET ids /\
  fn_has_code ready en func /\
  eval_operand child_src s = SOME (n2w (sb+32+j*msz)) /\
  eval_operand child_dst s = SOME (n2w (d+32+j*asz)) /\
  (!x. child_src = Var x \/ child_dst = Var x ==> not_fresh_at ready x) /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts /\
  window_strong_contract ei /\
  compile_abi_encode_static_info child_dst child_src ei ready = (out,en) ==>
  ?t. window_array_transition ctx func owner
      (window_alloca_sites func (frag_ids ready en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] s t /\
    window_strong_result ctx func ready en out ty (EL j avs) (d+32+j*asz) s t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory
Proof
  strip_tac >> drule_all (SIMP_RULE bool_ss [] (Q.INST [`obsv` |-> `F`]
    (SPEC_ALL window_array_static_element_run_core))) >> simp[]
QED

Theorem window_array_static_element_run_observed:
  window_array_root ctx func owner ids ei asz msz F ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  owner.cs_next_var <= ready.cs_next_var /\
  window_alloca_sites func (frag_ids ready en) SUBSET ids /\
  fn_has_code ready en func /\
  eval_operand child_src s = SOME (n2w (sb+32+j*msz)) /\
  eval_operand child_dst s = SOME (n2w (d+32+j*asz)) /\
  (!x. child_src = Var x \/ child_dst = Var x ==> not_fresh_at ready x) /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts /\
  window_observed_contract ei /\
  compile_abi_encode_static_info child_dst child_src ei ready = (out,en) ==>
  ?t. window_array_transition ctx func owner
      (window_alloca_sites func (frag_ids ready en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] s t /\
    window_strong_result ctx func ready en out ty (EL j avs) (d+32+j*asz) s t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule window_observed_contract_strong >> strip_tac >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`obsv` |-> `T`]
    (SPEC_ALL window_array_static_element_run_core))) >> simp[]
QED

Theorem window_array_transition_eval:
  window_array_transition ctx func owner ids outs s t /\
  eval_operand op s = SOME w /\
  (!x. op = Var x ==> not_fresh_at owner x) ==>
  eval_operand op t = SOME w
Proof
  Cases_on `op` >> simp[eval_operand_def, window_array_transition_def] >>
  metis_tac[]
QED

Theorem window_array_root_transition:
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d s /\
  window_array_transition ctx func owner child_ids outs s t /\
  child_ids SUBSET ids /\
  EVERY (\r. venomMemDefs$regions_disjoint (sb,cap) r) outs ==>
  window_array_root ctx func owner ids ei asz msz active ty avs src dst sb cap d t
Proof
  strip_tac >>
  `abi_encoder_registered_effect child_ids outs s t /\
   window_alloca_growth s t /\ alloca_inv t /\ alloca_room ctx func t` by
    metis_tac[window_array_transition_effect, window_array_transition_resources] >>
  `!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  `abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap t.vs_memory` by
    (irule window_alloca_growth_source >>
     qexistsl_tac [`child_ids`, `outs`, `s`] >> asm_rewrite_tac[] >>
     fs[window_array_root_def] >> metis_tac[SUBSET_DEF]) >>
  `eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d)` by
    (full_simp_tac bool_ss [window_array_root_def] >>
     conj_tac >> irule window_array_transition_eval >> metis_tac[]) >>
  `window_sizes32 ids t` by
    metis_tac[window_array_transition_sizes, window_array_root_def] >>
  `(!i b sz. i IN ids /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
   (!i b sz. i IN ids /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint
      (d,LENGTH (enc (Array NONE ty) (ListV avs))) (b,sz))` by
    (conj_tac >> match_mp_tac window_alloca_growth_protected >>
     asm_rewrite_tac[] >> full_simp_tac bool_ss [window_array_root_def] >>
     metis_tac[]) >>
  simp_tac bool_ss [window_array_root_def] >> asm_rewrite_tac[] >>
  fs[window_array_root_def] >>
  metis_tac[window_alloca_growth_frontier]
QED

Theorem window_array_static_body_run_core[local]:
  window_array_root ctx func st ids ei asz msz F ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = n2w j /\
  abi_encode_array_static_body ip src dst ei asz msz st = (out,en) /\
  window_alloca_sites func (frag_ids st en) SUBSET ids /\
  fn_has_code st en func /\ window_strong_contract ei /\
  (obsv ==> window_observed_contract ei) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_array_transition ctx func st
      (window_alloca_sites func (frag_ids st en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] s t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory /\
    eval_operand out t = SOME (n2w j) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    (obsv ==> !x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `abi_encoder_static_leaf ei` by
    fs[window_array_root_def, Once abi_encoder_admissible_def] >>
  drule_all abi_encode_array_static_body_context >> strip_tac >> gvs[] >>
  `?p. window_phase ctx func st prepared {} [] s p /\
    eval_operand (FST (FST coords)) p = SOME (n2w j) /\
    eval_operand (SND (FST coords)) p = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) p = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) p = SOME (n2w (d+32+j*asz)) /\
    (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
      FST (SND coords) = Var x \/ SND (SND coords) = Var x ==>
      not_fresh_at prepared x) /\
    (!x. ~not_fresh_at prepared x ==> lookup_var x p = lookup_var x s)` by
    (full_simp_tac bool_ss [window_array_root_def] >>
     drule_all window_array_addresses_phase_observed >> metis_tac[]) >>
  `window_array_transition ctx func st {} [] s p` by
    metis_tac[window_array_pure_phase_transition] >>
  `window_array_root ctx func st ids ei asz msz F ty avs src dst sb cap d p` by
    (irule window_array_root_transition >> metis_tac[EMPTY_SUBSET, EVERY_DEF]) >>
  `abi_encoder_array_prefix ty avs j d p.vs_memory` by
    (irule window_array_prefix_registered_frame >>
     reverse conj_tac >- metis_tac[window_array_root_def] >>
     qexistsl_tac [`{}`, `[]`, `s`] >>
     asm_rewrite_tac[EVERY_DEF, NOT_IN_EMPTY] >>
     metis_tac[window_array_root_def, window_array_transition_effect,
       window_array_transition_resources]) >>
  `window_alloca_sites func (frag_ids prepared en) SUBSET ids` by
    (irule SUBSET_TRANS >>
     qexists_tac `window_alloca_sites func (frag_ids st en)` >>
     asm_rewrite_tac[] >> irule window_alloca_sites_mono >>
     simp_tac (srw_ss()) [SUBSET_DEF, abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `?t. window_array_transition ctx func st
      (window_alloca_sites func (frag_ids prepared en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] p t /\
    window_strong_result ctx func prepared en ignored ty (EL j avs)
      (d+32+j*asz) p t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory /\
    (obsv ==> !x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x p)` by
    (`st.cs_next_var <= prepared.cs_next_var /\
       ~p.vs_halted /\ p.vs_current_bb = prepared.cs_current_bb /\
       p.vs_inst_idx = LENGTH prepared.cs_current_insts /\
       (!x. SND (FST coords) = Var x \/ SND (SND coords) = Var x ==>
         not_fresh_at prepared x)` by
       (full_simp_tac bool_ss [window_phase_def] >> metis_tac[LESS_EQ_ADD]) >>
     drule_all window_array_static_element_run_core >> simp[]) >>
  `window_phase ctx func prepared en
      (window_alloca_sites func (frag_ids prepared en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] p t` by
    metis_tac[window_phase_strong_result] >>
  `eval_operand (FST (FST coords)) t = SOME (n2w j)` by
    (irule window_phase_eval >> metis_tac[window_phase_labels]) >>
  `window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `prepared`,
       `window_alloca_sites func (frag_ids prepared en)`,
       `[(d+32+j*asz,LENGTH (enc ty (EL j avs)))]`, `p`] >>
     asm_rewrite_tac[EMPTY_SUBSET, EVERY_DEF] >> conj_tac
     >- decide_tac >>
     irule window_alloca_sites_mono >>
     simp_tac (srw_ss()) [SUBSET_DEF, abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] s t` by
    (irule window_array_phase_transition >>
     conj_tac >- metis_tac[window_array_transition_sizes] >>
     qexists_tac `en` >> asm_rewrite_tac[]) >>
  `prepared.cs_next_var <= en.cs_next_var` by
    metis_tac[window_phase_def, window_seq_mono] >>
  `obsv ==> !x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s` by
    metis_tac[not_fresh_at_mono] >>
  qexists_tac `t` >>
  full_simp_tac bool_ss [AC ADD_COMM ADD_ASSOC, MULT_COMM] >>
  metis_tac[window_phase_control]
QED

Theorem window_array_static_body_run:
  window_array_root ctx func st ids ei asz msz F ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = n2w j /\
  abi_encode_array_static_body ip src dst ei asz msz st = (out,en) /\
  window_alloca_sites func (frag_ids st en) SUBSET ids /\
  fn_has_code st en func /\ window_strong_contract ei /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_array_transition ctx func st
      (window_alloca_sites func (frag_ids st en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] s t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory /\
    eval_operand out t = SOME (n2w j) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  strip_tac >> drule_all (SIMP_RULE bool_ss [] (Q.INST [`obsv` |-> `F`]
    (SPEC_ALL window_array_static_body_run_core))) >> simp[]
QED

Theorem window_array_static_body_run_observed:
  window_array_root ctx func st ids ei asz msz F ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = n2w j /\
  abi_encode_array_static_body ip src dst ei asz msz st = (out,en) /\
  window_alloca_sites func (frag_ids st en) SUBSET ids /\
  fn_has_code st en func /\ window_observed_contract ei /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_array_transition ctx func st
      (window_alloca_sites func (frag_ids st en))
      [(d+32+j*asz,LENGTH (enc ty (EL j avs)))] s t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory /\
    eval_operand out t = SOME (n2w j) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule window_observed_contract_strong >> strip_tac >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`obsv` |-> `T`]
    (SPEC_ALL window_array_static_body_run_core))) >> simp[]
QED

Theorem window_array_dynamic_prefix_frame:
  window_array_root ctx func owner ids ei asz msz T ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  child_ids SUBSET ids /\
  window_array_transition ctx func ready child_ids
    [(d+32+j*abi_member_head_size ty,32);
     (d+32+LENGTH avs*abi_member_head_size ty+
       SUM (MAP (abi_member_tail_size ty) (TAKE j avs)),
      LENGTH (enc ty (EL j avs)))] s t ==>
  abi_encoder_array_prefix ty avs j d t.vs_memory
Proof
  strip_tac >>
  `abi_encoder_window_input (AbiDynArray ei asz msz T)
      (Array NONE ty) (ListV avs) sb cap s.vs_memory /\
   d+LENGTH (enc (Array NONE ty) (ListV avs)) <= s.vs_alloca_next` by
    fs[window_array_root_def] >>
  `is_dynamic ty` by fs[abiEncoderWindowTheory.abi_encoder_window_array_iff] >>
  drule_all window_array_prefix_step_geometry >> strip_tac >>
  `j*abi_member_head_size ty+32 <= LENGTH avs*abi_member_head_size ty` by metis_tac[] >>
  irule window_array_prefix_registered_frame >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`child_ids`,
    `[(d+32+j*abi_member_head_size ty,32);
      (d+32+LENGTH avs*abi_member_head_size ty+
        SUM (MAP (abi_member_tail_size ty) (TAKE j avs)),
       LENGTH (enc ty (EL j avs)))]`, `s`] >>
  asm_rewrite_tac[] >>
  `abi_encoder_registered_effect child_ids
    [(d+32+j*abi_member_head_size ty,32);
     (d+32+LENGTH avs*abi_member_head_size ty+
       SUM (MAP (abi_member_tail_size ty) (TAKE j avs)),
      LENGTH (enc ty (EL j avs)))] s t /\ window_alloca_growth s t` by
    metis_tac[window_array_transition_effect, window_array_transition_resources] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- simp[venomMemDefsTheory.regions_disjoint_def]
  >- (simp_tac (srw_ss()) [EVERY_DEF, venomMemDefsTheory.regions_disjoint_def] >>
      ntac 2 disj2_tac >> disj1_tac >>
      qpat_x_assum `j * _ + 32 <= _` mp_tac >> decide_tac)
  >- (simp_tac (srw_ss()) [EVERY_DEF, venomMemDefsTheory.regions_disjoint_def] >>
      ntac 2 disj2_tac >>
      qpat_x_assum `j * _ + 32 <= _` mp_tac >> decide_tac) >>
  rpt strip_tac >>
  `i IN ids` by metis_tac[SUBSET_DEF] >>
  metis_tac[window_array_root_def]
QED

Theorem window_array_phase_sizes_transition:
  window_phase ctx func st en ids outs s t /\ window_sizes32 ids t ==>
  window_array_transition ctx func st ids outs s t
Proof
  strip_tac >> irule window_array_phase_transition >>
  conj_tac
  >- (gen_tac >> rewrite_tac[window_sizes32_def] >> strip_tac >>
      match_mp_tac window_registered_sizes_transport >>
      asm_rewrite_tac[] >>
      metis_tac[window_phase_effect, window_sizes32_def]) >>
  qexists_tac `en` >> asm_rewrite_tac[]
QED

Theorem window_array_suffix_run_observed:
  abi_encode_child_suffix head dp offset len st = (out,en) /\
  fn_has_code st en func /\
  eval_operand head s = SOME (n2w h) /\ eval_operand offset s = SOME (n2w off) /\
  eval_operand dp s = SOME (n2w slot) /\ eval_operand len s = SOME (n2w n) /\
  (!x. dp = Var x \/ len = Var x ==> not_fresh_at st x) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  (h+32 <= slot \/ slot+32 <= h) /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_array_transition ctx func st {site} [(h,32)] s t /\
    mem_word_at h t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+n) /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    eval_operand out t = SOME (n2w n) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all window_child_suffix_run_observed >> strip_tac >>
  `window_sizes32 {site} t` by simp[window_sizes32_def] >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[window_array_phase_sizes_transition] >>
  metis_tac[window_phase_control]
QED

Theorem window_array_suffix_run:
  abi_encode_child_suffix head dp offset len st = (out,en) /\
  fn_has_code st en func /\
  eval_operand head s = SOME (n2w h) /\ eval_operand offset s = SOME (n2w off) /\
  eval_operand dp s = SOME (n2w slot) /\ eval_operand len s = SOME (n2w n) /\
  (!x. dp = Var x \/ len = Var x ==> not_fresh_at st x) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  (h+32 <= slot \/ slot+32 <= h) /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_array_transition ctx func st {site} [(h,32)] s t /\
    mem_word_at h t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+n) /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    eval_operand out t = SOME (n2w n) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all window_array_suffix_run_observed >>
  strip_tac >> qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem window_array_dynamic_prefix_finish:
  window_array_root ctx func owner ids ei asz msz T ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  child_ids SUBSET ids /\
  window_array_transition ctx func ready child_ids
    [(d+32+j*abi_member_head_size ty,32);
     (d+32+LENGTH avs*abi_member_head_size ty+
       SUM (MAP (abi_member_tail_size ty) (TAKE j avs)),
      LENGTH (enc ty (EL j avs)))] s t /\
  mem_word_at (d+32+j*abi_member_head_size ty) t.vs_memory =
    n2w (LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE j avs))) /\
  mem_bytes_at (d+32+LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE j avs)))
    (LENGTH (enc ty (EL j avs))) t.vs_memory = enc ty (EL j avs) ==>
  abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory
Proof
  strip_tac >>
  `abi_encoder_array_prefix ty avs j d t.vs_memory` by
    (irule window_array_dynamic_prefix_frame >> metis_tac[]) >>
  `abi_encoder_window_input (AbiDynArray ei asz msz T)
    (Array NONE ty) (ListV avs) sb cap s.vs_memory` by
    fs[window_array_root_def] >>
  `is_dynamic ty` by fs[abiEncoderWindowTheory.abi_encoder_window_array_iff] >>
  irule window_array_prefix_dynamic_advance >> metis_tac[]
QED

Theorem window_array_tail_pure_observed:
  abi_encode_array_tail data_op dp st = (ops,en) /\
  eval_operand dp s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = n2w off /\ eval_operand data_op s = SOME (n2w d) /\
  (!x. data_op = Var x ==> not_fresh_at st x) ==>
  ?t. window_pure_seq st en s t /\
    eval_operand (FST ops) t = SOME (n2w off) /\
    eval_operand (SND ops) t = SOME (n2w (d+off)) /\
    (!x. FST ops = Var x \/ SND ops = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  simp_tac bool_ss [abi_encode_array_tail_def, comp_bind_def,
    comp_return_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [dp] st = (offset,mid)` >>
  rename1 `emit_op ADD [data_op;offset] mid = (child_dst,en)` >>
  `?p. window_pure_seq st mid s p /\
    eval_operand offset p = SOME (n2w off) /\
    (!x. offset = Var x ==> not_fresh_at mid x)` by
    (drule_all window_emit_load_pure >> asm_rewrite_tac[]) >>
  `eval_operand data_op p = SOME (n2w d)` by
    (irule window_seq_eval >> metis_tac[window_pure_seq_def]) >>
  `?t. window_pure_seq mid en p t /\
    eval_operand child_dst t = SOME (n2w (d+off)) /\
    (!x. child_dst = Var x ==> not_fresh_at en x)` by
    (drule_all window_emit_add_pure >> simp[word_add_n2w]) >>
  `eval_operand offset t = SOME (n2w off)` by
    (irule window_seq_eval >> metis_tac[window_pure_seq_def]) >>
  `!x. ~not_fresh_at mid x ==> lookup_var x p = lookup_var x s` by
    (rpt strip_tac >> irule window_array_register_high >>
     qexistsl_tac [`mid`, `MLOAD`, `[dp]`, `offset`, `st`] >> simp[]) >>
  `!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x p` by
    (rpt strip_tac >> irule window_array_register_high >>
     qexistsl_tac [`en`, `ADD`, `[data_op;offset]`, `child_dst`, `mid`] >> simp[]) >>
  `mid.cs_next_var <= en.cs_next_var` by
    metis_tac[window_pure_seq_def, window_seq_mono] >>
  `!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s` by
    metis_tac[not_fresh_at_mono] >>
  qexists_tac `t` >> asm_rewrite_tac[] >> conj_tac
  >- metis_tac[window_pure_seq_chain] >>
  metis_tac[not_fresh_at_mono]
QED

Theorem window_array_tail_pure:
  abi_encode_array_tail data_op dp st = (ops,en) /\
  eval_operand dp s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = n2w off /\ eval_operand data_op s = SOME (n2w d) /\
  (!x. data_op = Var x ==> not_fresh_at st x) ==>
  ?t. window_pure_seq st en s t /\
    eval_operand (FST ops) t = SOME (n2w off) /\
    eval_operand (SND ops) t = SOME (n2w (d+off)) /\
    (!x. FST ops = Var x \/ SND ops = Var x ==> not_fresh_at en x)
Proof
  strip_tac >> drule_all window_array_tail_pure_observed >>
  strip_tac >> qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem window_array_tail_phase_observed:
  abi_encode_array_tail data_op dp st = (ops,en) /\
  eval_operand dp s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = n2w off /\ eval_operand data_op s = SOME (n2w d) /\
  (!x. data_op = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand (FST ops) t = SOME (n2w off) /\
    eval_operand (SND ops) t = SOME (n2w (d+off)) /\
    (!x. FST ops = Var x \/ SND ops = Var x ==> not_fresh_at en x) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all window_array_tail_pure_observed >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  (conj_tac >- metis_tac[window_pure_seq_phase]) >>
  simp_tac (srw_ss()) [eval_op_inst_idx, lookup_var_def] >>
  asm_rewrite_tac[] >> metis_tac[lookup_var_def]
QED

Theorem window_array_tail_phase:
  abi_encode_array_tail data_op dp st = (ops,en) /\
  eval_operand dp s = SOME (n2w slot) /\ slot < dimword (:256) /\
  mload slot s = n2w off /\ eval_operand data_op s = SOME (n2w d) /\
  (!x. data_op = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand (FST ops) t = SOME (n2w off) /\
    eval_operand (SND ops) t = SOME (n2w (d+off)) /\
    (!x. FST ops = Var x \/ SND ops = Var x ==> not_fresh_at en x)
Proof
  strip_tac >> drule_all window_array_tail_phase_observed >>
  strip_tac >> qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem window_array_dynamic_prepare_observed[local]:
  window_array_root ctx func st ids ei asz msz T ty avs src dst sb cap d s /\
  eval_operand ip s = SOME (n2w islot) /\ islot < dimword (:256) /\
  mload islot s = n2w j /\
  window_array_cursor T st dp site slot off sb cap d n s /\
  abi_encode_array_addresses ip src dst asz msz st = (coords,addressed) /\
  abi_encode_array_tail (FST (SND coords)) dp addressed = (ops,prepared) /\
  fn_has_code st addressed func /\ fn_has_code addressed prepared func /\
  st.cs_next_var <= addressed.cs_next_var /\
  addressed.cs_next_var <= prepared.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?q. window_phase ctx func st prepared {} [] s q /\
    window_array_root ctx func st ids ei asz msz T ty avs src dst sb cap d q /\
    eval_operand (FST (FST coords)) q = SOME (n2w j) /\
    eval_operand (SND (FST coords)) q = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (SND (SND coords)) q = SOME (n2w (d+32+j*asz)) /\
    eval_operand (FST ops) q = SOME (n2w off) /\
    eval_operand (SND ops) q = SOME (n2w (d+32+off)) /\
    eval_operand dp q = SOME (n2w slot) /\
    FLOOKUP q.vs_allocas site = SOME (slot,32) /\
    mem_word_at slot q.vs_memory = n2w off /\
    (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
      SND (SND coords) = Var x \/ FST ops = Var x \/ SND ops = Var x \/
      dp = Var x ==> not_fresh_at prepared x) /\
    (!x. ~not_fresh_at prepared x ==> lookup_var x q = lookup_var x s)
Proof
  strip_tac >>
  `?p. window_phase ctx func st addressed {} [] s p /\
    eval_operand (FST (FST coords)) p = SOME (n2w j) /\
    eval_operand (SND (FST coords)) p = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) p = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) p = SOME (n2w (d+32+j*asz)) /\
    (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
      FST (SND coords) = Var x \/ SND (SND coords) = Var x ==>
      not_fresh_at addressed x) /\
    (!x. ~not_fresh_at addressed x ==> lookup_var x p = lookup_var x s)` by
    (full_simp_tac bool_ss [window_array_root_def] >>
     drule_all window_array_addresses_phase_observed >> metis_tac[]) >>
  `window_array_transition ctx func st {} [] s p` by
    metis_tac[window_array_pure_phase_transition] >>
  `eval_operand dp p = SOME (n2w slot) /\ mload slot p = n2w off` by
    (full_simp_tac bool_ss [window_array_cursor_def] >>
     conj_tac >- (irule window_array_transition_eval >> metis_tac[]) >>
     `mem_word_at slot p.vs_memory = mem_word_at slot s.vs_memory` by
       (irule window_array_transition_cursor_frame >>
        metis_tac[NOT_IN_EMPTY, EVERY_DEF]) >>
     full_simp_tac bool_ss [mload_def, mem_word_at_def, mem_bytes_at_def, LET_THM]) >>
  `?q. window_phase ctx func addressed prepared {} [] p q /\
    eval_operand (FST ops) q = SOME (n2w off) /\
    eval_operand (SND ops) q = SOME (n2w (d+32+off)) /\
    (!x. FST ops = Var x \/ SND ops = Var x ==> not_fresh_at prepared x) /\
    (!x. ~not_fresh_at prepared x ==> lookup_var x q = lookup_var x p)` by
    (`alloca_inv p /\ alloca_room ctx func p /\ ~p.vs_halted /\
      p.vs_current_bb = addressed.cs_current_bb /\
      p.vs_inst_idx = LENGTH addressed.cs_current_insts` by
      metis_tac[window_phase_resources, window_phase_control] >>
     `slot < dimword (:256)` by fs[window_array_cursor_def] >>
     `!x. FST (SND coords) = Var x ==> not_fresh_at addressed x` by metis_tac[] >>
     drule_all window_array_tail_phase_observed >>
     simp_tac bool_ss [AC ADD_COMM ADD_ASSOC]) >>
  `window_phase ctx func st prepared {} [] s q` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `addressed`, `{}`, `[]`, `p`] >> simp[EVERY_DEF]) >>
  `window_array_transition ctx func st {} [] s q` by
    metis_tac[window_array_pure_phase_transition] >>
  `!x. ~not_fresh_at prepared x ==> lookup_var x q = lookup_var x s` by
    metis_tac[not_fresh_at_mono] >>
  qexists_tac `q` >> asm_rewrite_tac[] >> rpt conj_tac
  >- (irule window_array_root_transition >> metis_tac[EMPTY_SUBSET, EVERY_DEF])
  >- (irule window_phase_eval >> metis_tac[window_phase_labels])
  >- (irule window_phase_eval >> metis_tac[window_phase_labels])
  >- (irule window_phase_eval >> metis_tac[window_phase_labels])
  >- (irule window_array_transition_eval >>
      full_simp_tac bool_ss [window_array_cursor_def] >> metis_tac[])
  >- metis_tac[window_array_cursor_def, window_phase_effect,
       abi_encoder_registered_effect_allocated]
  >- (`mem_word_at slot q.vs_memory = mem_word_at slot s.vs_memory` by
       (irule window_array_transition_cursor_frame >>
        metis_tac[window_array_cursor_def, NOT_IN_EMPTY, EVERY_DEF]) >>
      fs[window_array_cursor_def]) >>
  metis_tac[window_array_cursor_def, not_fresh_at_mono, LESS_EQ_TRANS]
QED

Theorem window_array_dynamic_child_finish_core[local]:
  window_array_transition ctx func owner child_ids [(b,n)] q r /\
  window_strong_result ctx func prepared child_end child_len ty av b q r /\
  n = LENGTH (enc ty av) /\
  eval_operand idx q = SOME (n2w j) /\ eval_operand head q = SOME (n2w h) /\
  eval_operand offset q = SOME (n2w off) /\ eval_operand dp q = SOME (n2w slot) /\
  (!x. idx = Var x \/ head = Var x \/ offset = Var x \/ dp = Var x ==>
    not_fresh_at prepared x) /\
  abi_encode_child_suffix head dp offset child_len child_end = (ignored,en) /\
  fn_has_code child_end en func /\
  (!x. child_len = Var x ==> not_fresh_at child_end x) /\
  FLOOKUP q.vs_allocas site = SOME (slot,32) /\ site NOTIN child_ids /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  (h+32 <= slot \/ slot+32 <= h) /\
  venomMemDefs$regions_disjoint (b,n) (h,32) /\
  venomMemDefs$regions_disjoint (b,n) (slot,32) /\
  owner.cs_next_var <= prepared.cs_next_var /\
  prepared.cs_next_var <= child_end.cs_next_var /\
  (obsv ==> !x. ~not_fresh_at child_end x ==> lookup_var x r = lookup_var x q) ==>
  ?t. window_array_transition ctx func owner (child_ids UNION {site})
      [(h,32);(b,n)] q t /\
    mem_bytes_at b n t.vs_memory = enc ty av /\
    mem_word_at h t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+n) /\
    eval_operand idx t = SOME (n2w j) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    (obsv ==> !x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x q)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `window_phase ctx func prepared child_end
     (window_alloca_sites func (frag_ids prepared child_end)) [(b,n)] q r` by
    metis_tac[window_phase_strong_result] >>
  `eval_operand idx r = SOME (n2w j) /\ eval_operand head r = SOME (n2w h) /\
   eval_operand offset r = SOME (n2w off) /\ eval_operand dp r = SOME (n2w slot)` by
    (rpt conj_tac >> irule window_phase_eval >> metis_tac[window_phase_labels]) >>
  `mem_bytes_at b n r.vs_memory = enc ty av /\
   eval_operand child_len r = SOME (n2w n)` by
    metis_tac[window_strong_result_public, abi_encoder_window_result_output] >>
  `FLOOKUP r.vs_allocas site = SOME (slot,32)` by
    metis_tac[window_array_transition_effect, abi_encoder_registered_effect_allocated] >>
  `!x. dp = Var x \/ child_len = Var x ==> not_fresh_at child_end x` by
    metis_tac[not_fresh_at_mono] >>
  `alloca_inv r /\ alloca_room ctx func r /\ ~r.vs_halted /\
   r.vs_current_bb = child_end.cs_current_bb /\
   r.vs_inst_idx = LENGTH child_end.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  drule_all window_array_suffix_run_observed >> strip_tac >>
  `window_phase ctx func owner child_end child_ids [(b,n)] q r` by
    metis_tac[window_array_transition_phase] >>
  `window_phase ctx func child_end en {site} [(h,32)] r t` by
    metis_tac[window_array_transition_phase] >>
  `window_phase ctx func owner en (child_ids UNION {site}) [(h,32);(b,n)] q t` by
    (irule window_phase_chain >>
     qexistsl_tac [`child_ids`, `[(b,n)]`, `child_end`, `{site}`, `[(h,32)]`, `r`] >>
     simp[SUBSET_UNION] >> decide_tac) >>
  `mem_bytes_at b n t.vs_memory = mem_bytes_at b n r.vs_memory` by
    (irule abi_encoder_window_effect_bytes >>
     qexistsl_tac [`{site}`, `[(h,32)]`] >> simp[] >>
     metis_tac[window_array_transition_effect, optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  `eval_operand idx t = SOME (n2w j)` by
    (irule window_phase_eval >> metis_tac[window_phase_labels, not_fresh_at_mono]) >>
  `child_end.cs_next_var <= en.cs_next_var` by
    (drule abiEncoderChildCodeTheory.abi_encode_child_suffix_shape >> simp[]) >>
  `obsv ==> !x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x q` by
    metis_tac[not_fresh_at_mono] >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_array_phase_transition >> conj_tac
  >- (gen_tac >> strip_tac >> metis_tac[window_array_transition_sizes]) >>
  qexists_tac `en` >> metis_tac[]
QED

Theorem window_array_dynamic_body_run_core[local]:
  window_array_root ctx func st ids ei asz msz T ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  eval_operand ip s = SOME (n2w islot) /\ islot < dimword (:256) /\
  mload islot s = n2w j /\
  window_array_cursor T st dp site slot off sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  off = LENGTH avs * abi_member_head_size ty +
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  abi_encode_array_dynamic_body ip dp src dst ei asz msz st = (out,en) /\
  window_alloca_sites func (frag_ids st en) SUBSET ids /\ site IN ids /\
  site NOTIN window_alloca_sites func (frag_ids st en) /\
  fn_has_code st en func /\ window_strong_contract ei /\
  (obsv ==> window_observed_contract ei) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_array_transition ctx func st
      (window_alloca_sites func (frag_ids st en) UNION {site})
      [(d+32+j*abi_member_head_size ty,32);
       (d+32+off,LENGTH (enc ty (EL j avs)))] s t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory /\
    mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc ty (EL j avs))) /\
    eval_operand out t = SOME (n2w j) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    (obsv ==> !x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  qpat_x_assum `out = _` SUBST_ALL_TAC >>
  `st.cs_next_var <= addressed.cs_next_var /\
   addressed.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  drule_all window_array_dynamic_prepare_observed >> strip_tac >>
  `!x. SND (FST coords) = Var x \/ SND ops = Var x ==> not_fresh_at prepared x` by
    metis_tac[] >>
  `window_alloca_sites func (frag_ids prepared child_end) SUBSET
    window_alloca_sites func (frag_ids st en)` by
    (irule window_alloca_sites_mono >>
     simp_tac (srw_ss()) [SUBSET_DEF, abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `window_alloca_sites func (frag_ids prepared child_end) SUBSET ids` by
    metis_tac[SUBSET_TRANS] >>
  `abi_encoder_window_input (AbiDynArray ei asz msz T)
    (Array NONE ty) (ListV avs) sb cap s.vs_memory` by
    metis_tac[window_array_root_def] >>
  `asz = abi_member_head_size ty /\ is_dynamic ty` by
    fs[abiEncoderWindowTheory.abi_encoder_window_array_iff] >>
  `32+off+LENGTH (enc ty (EL j avs)) <= LENGTH (enc (Array NONE ty) (ListV avs)) /\
   j*abi_member_head_size ty+32 <= off` by
    (drule_all window_array_prefix_step_geometry >>
     disch_then (mp_tac o CONJUNCT1) >> asm_rewrite_tac[] >>
     strip_tac >> decide_tac) >>
  `?r. window_array_transition ctx func st
      (window_alloca_sites func (frag_ids prepared child_end))
      [(d+(32+off),LENGTH (enc ty (EL j avs)))] q r /\
    window_strong_result ctx func prepared child_end child_len ty (EL j avs)
      (d+(32+off)) q r /\
    (obsv ==> !x. ~not_fresh_at child_end x ==> lookup_var x r = lookup_var x q)` by
    (`st.cs_next_var <= prepared.cs_next_var /\
      ~q.vs_halted /\ q.vs_current_bb = prepared.cs_current_bb /\
      q.vs_inst_idx = LENGTH prepared.cs_current_insts` by
      (conj_tac >- decide_tac >> metis_tac[window_phase_control]) >>
     `eval_operand (SND ops) q = SOME (n2w (d+(32+off)))` by
       (qpat_assum `eval_operand (SND ops) q = _` mp_tac >>
        simp_tac bool_ss [ADD_ASSOC]) >>
     drule_all window_array_element_run_core >> metis_tac[]) >>
  `d+LENGTH (enc (Array NONE ty) (ListV avs)) < dimword (:256)` by
    (full_simp_tac bool_ss [window_array_root_def, alloca_room_def] >> decide_tac) >>
  `d+32+j*asz < dimword (:256) /\ slot < dimword (:256) /\
   (d+32+j*asz+32 <= slot \/ slot+32 <= d+32+j*asz) /\
   venomMemDefs$regions_disjoint (d+(32+off),LENGTH (enc ty (EL j avs)))
     (d+32+j*asz,32) /\
   venomMemDefs$regions_disjoint (d+(32+off),LENGTH (enc ty (EL j avs))) (slot,32)` by
    (qpat_assum `d + LENGTH _ < _` mp_tac >>
     qpat_assum `32 + off + _ <= _` mp_tac >>
     qpat_assum `j * _ + 32 <= off` mp_tac >>
     qpat_assum `window_array_cursor _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `asz = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_array_cursor_def, venomMemDefsTheory.regions_disjoint_def] >>
     rpt strip_tac >> full_simp_tac arith_ss [] >> decide_tac) >>
  `!x. child_len = Var x ==> not_fresh_at child_end x` by
    (qpat_x_assum `abi_decoder_operand_live _ child_len` mp_tac >>
     Cases_on `child_len` >>
     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `!x. FST (FST coords) = Var x \/ SND (SND coords) = Var x \/
    FST ops = Var x \/ dp = Var x ==> not_fresh_at prepared x` by metis_tac[] >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  `window_array_transition ctx func prepared
      (window_alloca_sites func (frag_ids prepared child_end))
      [(d+(32+off),LENGTH (enc ty (EL j avs)))] q r` by
    metis_tac[window_array_child_transition, LESS_EQ_REFL] >>
  `?t. window_array_transition ctx func prepared
      (window_alloca_sites func (frag_ids prepared child_end) UNION {site})
      [(d+32+j*asz,32);(d+(32+off),LENGTH (enc ty (EL j avs)))] q t /\
    mem_bytes_at (d+(32+off)) (LENGTH (enc ty (EL j avs))) t.vs_memory = enc ty (EL j avs) /\
    mem_word_at (d+32+j*asz) t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc ty (EL j avs))) /\
    eval_operand (FST (FST coords)) t = SOME (n2w j) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    (obsv ==> !x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x q)` by
    (`site NOTIN window_alloca_sites func (frag_ids prepared child_end)` by
       metis_tac[SUBSET_DEF] >>
     irule window_array_dynamic_child_finish_core >>
     qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `abi_encode_child_suffix _ _ _ _ _ = _` (irule_at Any) >>
     asm_rewrite_tac[LESS_EQ_REFL] >> simp_tac bool_ss [ADD_ASSOC] >>
     asm_rewrite_tac[LESS_EQ_REFL]) >>
  `window_phase ctx func st en
      (window_alloca_sites func (frag_ids st en) UNION {site})
      [(d+32+j*asz,32);(d+(32+off),LENGTH (enc ty (EL j avs)))] s t` by
    (`window_phase ctx func prepared en
       (window_alloca_sites func (frag_ids prepared child_end) UNION {site})
       [(d+32+j*asz,32);(d+(32+off),LENGTH (enc ty (EL j avs)))] q t` by
       metis_tac[window_array_transition_phase] >>
     irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `prepared`,
       `window_alloca_sites func (frag_ids prepared child_end) UNION {site}`,
       `[(d+32+j*asz,32);(d+(32+off),LENGTH (enc ty (EL j avs)))]`, `q`] >>
     asm_rewrite_tac[EMPTY_SUBSET, EVERY_DEF] >>
     metis_tac[UNION_SUBSET, SUBSET_UNION, SUBSET_TRANS]) >>
  `window_array_transition ctx func st
      (window_alloca_sites func (frag_ids st en) UNION {site})
      [(d+32+j*asz,32);(d+(32+off),LENGTH (enc ty (EL j avs)))] s t` by
    (irule window_array_phase_transition >> conj_tac
     >- (gen_tac >> strip_tac >>
         `window_array_transition ctx func st {} [] s q` by
           metis_tac[window_array_pure_phase_transition] >>
         metis_tac[window_array_transition_sizes]) >>
     qexists_tac `en` >> asm_rewrite_tac[]) >>
  `prepared.cs_next_var <= en.cs_next_var` by decide_tac >>
  `obsv ==> !x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s` by
    metis_tac[not_fresh_at_mono] >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  qpat_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s` mp_tac >>
  qpat_assum `abi_encoder_array_prefix _ _ _ _ s.vs_memory` mp_tac >>
  qpat_assum `j < LENGTH avs` mp_tac >>
  qpat_assum `window_alloca_sites _ (frag_ids st en) SUBSET ids` mp_tac >>
  qpat_assum `site IN ids` mp_tac >>
  qpat_assum `window_array_transition _ _ _ (window_alloca_sites _ (frag_ids st en) UNION {site}) _ s t` mp_tac >>
  qpat_assum `mem_bytes_at _ _ t.vs_memory = _` mp_tac >>
  qpat_assum `mem_word_at (d+32+j*asz) t.vs_memory = _` mp_tac >>
  qpat_assum `asz = _` mp_tac >> qpat_assum `off = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  qpat_x_assum `asz = _` SUBST_ALL_TAC >>
  qpat_x_assum `off = _` SUBST_ALL_TAC >>
  full_simp_tac bool_ss [ADD_ASSOC] >> asm_rewrite_tac[] >>
  irule window_array_dynamic_prefix_finish >>
  qpat_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `window_array_transition _ _ _ (window_alloca_sites _ (frag_ids st en) UNION {site}) _ s t`
    (irule_at Any) >>
  asm_rewrite_tac[] >> simp_tac bool_ss [GSYM ADD_ASSOC] >> asm_rewrite_tac[] >>
  metis_tac[UNION_SUBSET, SUBSET_DEF, IN_SING]


QED

Theorem window_array_dynamic_body_run:
  window_array_root ctx func st ids ei asz msz T ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  eval_operand ip s = SOME (n2w islot) /\ islot < dimword (:256) /\
  mload islot s = n2w j /\
  window_array_cursor T st dp site slot off sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  off = LENGTH avs * abi_member_head_size ty +
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  abi_encode_array_dynamic_body ip dp src dst ei asz msz st = (out,en) /\
  window_alloca_sites func (frag_ids st en) SUBSET ids /\ site IN ids /\
  site NOTIN window_alloca_sites func (frag_ids st en) /\
  fn_has_code st en func /\ window_strong_contract ei /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_array_transition ctx func st
      (window_alloca_sites func (frag_ids st en) UNION {site})
      [(d+32+j*abi_member_head_size ty,32);
       (d+32+off,LENGTH (enc ty (EL j avs)))] s t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory /\
    mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc ty (EL j avs))) /\
    eval_operand out t = SOME (n2w j) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  strip_tac >> drule_all (SIMP_RULE bool_ss [] (Q.INST [`obsv` |-> `F`]
    (SPEC_ALL window_array_dynamic_body_run_core))) >> simp[]
QED

Theorem window_array_dynamic_body_run_observed:
  window_array_root ctx func st ids ei asz msz T ty avs src dst sb cap d s /\
  abi_encoder_array_prefix ty avs j d s.vs_memory /\ j < LENGTH avs /\
  eval_operand ip s = SOME (n2w islot) /\ islot < dimword (:256) /\
  mload islot s = n2w j /\
  window_array_cursor T st dp site slot off sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) s /\
  off = LENGTH avs * abi_member_head_size ty +
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  abi_encode_array_dynamic_body ip dp src dst ei asz msz st = (out,en) /\
  window_alloca_sites func (frag_ids st en) SUBSET ids /\ site IN ids /\
  site NOTIN window_alloca_sites func (frag_ids st en) /\
  fn_has_code st en func /\ window_observed_contract ei /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_array_transition ctx func st
      (window_alloca_sites func (frag_ids st en) UNION {site})
      [(d+32+j*abi_member_head_size ty,32);
       (d+32+off,LENGTH (enc ty (EL j avs)))] s t /\
    abi_encoder_array_prefix ty avs (SUC j) d t.vs_memory /\
    mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc ty (EL j avs))) /\
    eval_operand out t = SOME (n2w j) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule window_observed_contract_strong >> strip_tac >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`obsv` |-> `T`]
    (SPEC_ALL window_array_dynamic_body_run_core))) >> simp[]
QED

(* Keep the original local supplier interfaces as projections too. *)
Theorem window_array_dynamic_prepare[local]:
  window_array_root ctx func st ids ei asz msz T ty avs src dst sb cap d s /\
  eval_operand ip s = SOME (n2w islot) /\ islot < dimword (:256) /\
  mload islot s = n2w j /\
  window_array_cursor T st dp site slot off sb cap d n s /\
  abi_encode_array_addresses ip src dst asz msz st = (coords,addressed) /\
  abi_encode_array_tail (FST (SND coords)) dp addressed = (ops,prepared) /\
  fn_has_code st addressed func /\ fn_has_code addressed prepared func /\
  st.cs_next_var <= addressed.cs_next_var /\
  addressed.cs_next_var <= prepared.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?q. window_phase ctx func st prepared {} [] s q /\
    window_array_root ctx func st ids ei asz msz T ty avs src dst sb cap d q /\
    eval_operand (FST (FST coords)) q = SOME (n2w j) /\
    eval_operand (SND (FST coords)) q = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (SND (SND coords)) q = SOME (n2w (d+32+j*asz)) /\
    eval_operand (FST ops) q = SOME (n2w off) /\
    eval_operand (SND ops) q = SOME (n2w (d+32+off)) /\
    eval_operand dp q = SOME (n2w slot) /\
    FLOOKUP q.vs_allocas site = SOME (slot,32) /\
    mem_word_at slot q.vs_memory = n2w off /\
    (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
      SND (SND coords) = Var x \/ FST ops = Var x \/ SND ops = Var x \/
      dp = Var x ==> not_fresh_at prepared x)
Proof
  strip_tac >> drule_all window_array_dynamic_prepare_observed >>
  strip_tac >> qexists_tac `q` >> asm_rewrite_tac[]
QED

Theorem window_array_dynamic_child_finish[local]:
  window_array_transition ctx func owner child_ids [(b,n)] q r /\
  window_strong_result ctx func prepared child_end child_len ty av b q r /\
  n = LENGTH (enc ty av) /\
  eval_operand idx q = SOME (n2w j) /\ eval_operand head q = SOME (n2w h) /\
  eval_operand offset q = SOME (n2w off) /\ eval_operand dp q = SOME (n2w slot) /\
  (!x. idx = Var x \/ head = Var x \/ offset = Var x \/ dp = Var x ==>
    not_fresh_at prepared x) /\
  abi_encode_child_suffix head dp offset child_len child_end = (ignored,en) /\
  fn_has_code child_end en func /\
  (!x. child_len = Var x ==> not_fresh_at child_end x) /\
  FLOOKUP q.vs_allocas site = SOME (slot,32) /\ site NOTIN child_ids /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  (h+32 <= slot \/ slot+32 <= h) /\
  venomMemDefs$regions_disjoint (b,n) (h,32) /\
  venomMemDefs$regions_disjoint (b,n) (slot,32) /\
  owner.cs_next_var <= prepared.cs_next_var /\
  prepared.cs_next_var <= child_end.cs_next_var ==>
  ?t. window_array_transition ctx func owner (child_ids UNION {site})
      [(h,32);(b,n)] q t /\
    mem_bytes_at b n t.vs_memory = enc ty av /\
    mem_word_at h t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+n) /\
    eval_operand idx t = SOME (n2w j) /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`obsv` |-> `F`]
    (SPEC_ALL window_array_dynamic_child_finish_core))) >> simp[]
QED
