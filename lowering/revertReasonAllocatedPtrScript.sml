(* Allocating unwrap branches feed the shared checked encoder tail. *)
Theory revertReasonAllocatedPtr
Ancestors
  reasonRuntimeNormalizePtr revertReasonTailCodePtr exprSafeOperand
  exprLoweringProps stringUnwrapLayout freshWrites ptrDiscipline
  bodyPtrDefs context compileEnv words arithmetic pred_set finite_map venomInst
  venomState exprSimProps valueEncoding fragGasPathPtr vfmConstants

Theorem unwrap_allocated_string_output_old:
  unwrap_value cenv (LocatedValue (BaseT (StringT max)) r) sm = (Var root,sn) /\
  (r.ptr_location = LocStorage \/ r.ptr_location = LocTransient \/
   r.ptr_location = LocCode) ==>
  not_fresh_at sn root
Proof
  strip_tac >>
  (Cases_on `r.ptr_location = LocCode`
  >- (drule_all unwrap_string_code_layout >> strip_tac >>
      drule alloc_buffer_safe_operand >>
      `ci_mono sc sn` by
        metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND] >>
      fs[ci_mono_def] >> strip_tac >>
      drule_all safe_operand_mono >> fs[safe_operand_def]) >>
  fs[] >> (Cases_on `max = 0`
  >- (gvs[] >> drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_string_storage_zero_layout >>
      (impl_tac >- simp[]) >> strip_tac >>
      drule alloc_buffer_safe_operand >>
      `ci_mono sc sd /\ ci_mono sd sn` by
        metis_tac[ci_mono_emit_op, ci_mono_emit_void, pairTheory.SND] >>
      fs[ci_mono_def] >> strip_tac >>
      `sc.cs_next_var <= sn.cs_next_var` by decide_tac >>
      drule_all safe_operand_mono >> fs[safe_operand_def]) >>
  `0 < max` by decide_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_string_storage_layout >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule alloc_buffer_safe_operand >>
  `ci_mono sc sn` by
    metis_tac[ci_mono_compile_word_copy_loop, pairTheory.SND] >>
  fs[ci_mono_def] >> strip_tac >>
  drule_all safe_operand_mono >> fs[safe_operand_def]))
QED

(* Transport only live encoder resources; the normalizer supplies its actual
   endpoint and ghosts, never a second independently chosen execution. *)
Theorem revert_reason_framed_tail_ptr[local]:
  fn_has_code sn sb fn /\ sb.cs_current_bb = sn.cs_current_bb /\
  sb.cs_current_insts = sn.cs_current_insts ++
    (revert_reason_copy sn.cs_next_id sn.cs_next_var (Var q) (Var src) ++
     revert_reason_suffix sn.cs_next_id sn.cs_next_var (Var b) (Var p) (Var q)) /\
  t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts /\ ~t.vs_halted /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  not_fresh_at sm b /\ not_fresh_at sm p /\ not_fresh_at sm q /\
  not_fresh_at sn src /\ parent < sm.cs_next_id /\
  lookup_var b s = SOME B /\ lookup_var p s = SOME P /\
  lookup_var q s = SOME Q /\ lookup_var src t = SOME A /\
  ptr_covers G tn b s (64+ms) /\ ptr_covers G tn p s (32+ms) /\
  ptr_covers G tn q s ms /\ ptr_covers Gn tt src t (32+contractABI$ceil32 L) /\
  (!x C. not_fresh_at sm x /\ ptr_covers G tn x s C ==>
    lookup_var x t = lookup_var x s /\ ptr_covers Gn tt x t C) /\
  mload (w2n A) t = n2w L /\
  (!j. w2n A <= j /\ j < w2n A+32 ==> j NOTIN tt.t_mem) /\
  32+contractABI$ceil32 L <= ms /\ L+63 < dimword(:256) /\
  64+ms < dimword(:256) /\ w2n B+64+ms < dimword(:256) /\
  w2n P+32+ms < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ alloca_inv t /\ alloca_room ctx fn t /\
  (!i w a sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP t.vs_allocas i.inst_id = SOME (a,sz) ==> sz = w2n w) /\
  FLOOKUP s.vs_allocas parent = SOME (w2n Q,ms) /\
  (!aid a sz. FLOOKUP s.vs_allocas aid = SOME (a,sz) ==>
    FLOOKUP t.vs_allocas aid = SOME (a,sz)) ==>
  ?z Gf tnf. gas_path_ptr D 0 ctx fn PG Gn tt t 0 Gf tnf (Abort Revert_abort z)
Proof
  strip_tac >>
  `lookup_var b t = SOME B /\ ptr_covers Gn tt b t (64+ms)` by
    (qpat_x_assum `!x C. _` (qspecl_then [`b`,`64+ms`] mp_tac) >>
     asm_rewrite_tac[]) >>
  `lookup_var p t = SOME P /\ ptr_covers Gn tt p t (32+ms)` by
    (qpat_x_assum `!x C. _` (qspecl_then [`p`,`32+ms`] mp_tac) >>
     asm_rewrite_tac[]) >>
  `lookup_var q t = SOME Q /\ ptr_covers Gn tt q t ms` by
    (qpat_x_assum `!x C. _` (qspecl_then [`q`,`ms`] mp_tac) >>
     asm_rewrite_tac[]) >>
  `not_fresh_at sn b /\ not_fresh_at sn p /\ not_fresh_at sn q` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `parent <> sn.cs_next_id+5` by decide_tac >>
  drule_all revert_reason_tail_code >> strip_tac >>
  `!a sz. FLOOKUP t.vs_allocas (sn.cs_next_id+5) = SOME (a,sz) ==> sz = 32` by
    (rpt strip_tac >>
     qpat_x_assum `!i w a sz. _` drule >>
     simp[mk_inst_def]) >>
  `FLOOKUP t.vs_allocas parent = SOME (w2n Q,ms)` by metis_tac[] >>
  drule_at (Pat `_ = _ ++ _`) revert_reason_tail_at_compile_endpoint_ptr >>
  disch_then drule_all >> simp[]
QED

Theorem string_buffer_tail_observations[local]:
  eval_operand (Var root) t = SOME (n2w a) /\
  ptr_covers G tn root t (val_store_size (BaseTV (StringT max)) (StringV str)) /\
  a + val_store_size (BaseTV (StringT max)) (StringV str) < dimword(:256) /\
  mload a t = n2w (LENGTH str) /\ mem_word_taint tn.t_mem a = {} ==>
  lookup_var root t = SOME (n2w a) /\
  ptr_covers G tn root t (32+contractABI$ceil32 (LENGTH str)) /\
  mload (w2n (n2w a : 256 word)) t = n2w (LENGTH str) /\
  (!j. w2n (n2w a : 256 word) <= j /\ j < w2n (n2w a : 256 word)+32 ==>
    j NOTIN tn.t_mem)
Proof
  strip_tac >>
  `val_store_size (BaseTV (StringT max)) (StringV str) =
    32+contractABI$ceil32 (LENGTH str)` by
    simp[val_store_size_def, contractABITheory.ceil32_def, word_size_def] >>
  fs[eval_operand_def] >>
  qpat_x_assum `mem_word_taint _ _ = {}` mp_tac >>
  simp[mem_word_taint_def, EXTENSION] >> strip_tac >> rpt strip_tac >>
  first_x_assum (qspec_then `j-a` mp_tac) >> simp[] >> decide_tac
QED

Theorem revert_reason_storage_positive_unwrap_path_ptr:
  0 < max /\ r.ptr_location = (if tr then LocTransient else LocStorage) /\
  unwrap_value cenv (LocatedValue (BaseT (StringT max)) r) sm = (out,sn) /\
  storage_holds cx tr (BaseT (StringT max)) tv a es s /\
  read_result cx tv es = (INL (StringV str),es) /\
  val_wf (BaseTV (StringT max)) (StringV str) /\
  fn_has_code sm sn fn /\ copy_old_operand sm r.ptr_operand /\
  eval_operand r.ptr_operand s = SOME a /\ op_taint tn r.ptr_operand = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) a = {} /\
  type_slot_size (BaseTV (StringT max)) < dimword(:256) /\
  32 * type_slot_size (BaseTV (StringT max)) < dimword(:256) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_inv s /\ alloca_room ctx fn s /\ fn_inst_ids_distinct fn /\
  (!i w a sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (a,sz) ==> sz = w2n w) /\
  fn_has_code sn sb fn /\ sb.cs_current_bb = sn.cs_current_bb /\
  sb.cs_current_insts = sn.cs_current_insts ++
    (revert_reason_copy sn.cs_next_id sn.cs_next_var (Var q) out ++
     revert_reason_suffix sn.cs_next_id sn.cs_next_var (Var b) (Var p) (Var q)) /\
  not_fresh_at sm b /\ not_fresh_at sm p /\ not_fresh_at sm q /\
  lookup_var b s = SOME B /\ lookup_var p s = SOME P /\ lookup_var q s = SOME Q /\
  ptr_covers G tn b s (64+ms) /\ ptr_covers G tn p s (32+ms) /\
  ptr_covers G tn q s ms /\
  32+contractABI$ceil32 (LENGTH str) <= ms /\ LENGTH str+63 < dimword(:256) /\
  64+ms < dimword(:256) /\ w2n B+64+ms < dimword(:256) /\
  w2n P+32+ms < dimword(:256) /\
  FLOOKUP s.vs_allocas parent = SOME (w2n Q,ms) /\ parent < sm.cs_next_id ==>
  ?z Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (Abort Revert_abort z)
Proof
  strip_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_storage_string_positive_path_ptr >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  qpat_x_assum `out = Var root` SUBST_ALL_TAC >>
  `not_fresh_at sn root` by
    (irule unwrap_allocated_string_output_old >> goal_assum (drule_at Any) >>
     Cases_on `tr` >> simp[]) >>
  `ci_mono sm sn` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  drule_all string_buffer_tail_observations >> strip_tac >>
  `sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id` by
    fs[ci_mono_def] >>
  `?z Gh th. gas_path_ptr D 0 ctx fn PG Gf tf t 0 Gh th (Abort Revert_abort z)` by
    (drule_at (Pat `_ = _ ++ _`) revert_reason_framed_tail_ptr >>
     disch_then drule_all >> simp[]) >>
  drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ (OK _)`) gas_path_ptr_then >>
  disch_then drule >> simp[] >> metis_tac[]
QED

Theorem revert_reason_storage_zero_unwrap_path_ptr:
  r.ptr_location = (if tr then LocTransient else LocStorage) /\
  unwrap_value cenv (LocatedValue (BaseT (StringT 0)) r) sm = (out,sn) /\
  storage_holds cx tr (BaseT (StringT 0)) tv a es s /\
  read_result cx tv es = (INL (StringV str),es) /\
  val_wf (BaseTV (StringT 0)) (StringV str) /\
  fn_has_code sm sn fn /\ copy_old_operand sm r.ptr_operand /\
  eval_operand r.ptr_operand s = SOME a /\ op_taint tn r.ptr_operand = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) a = {} /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_inv s /\ alloca_room ctx fn s /\ fn_inst_ids_distinct fn /\
  (!i w a sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (a,sz) ==> sz = w2n w) /\
  fn_has_code sn sb fn /\ sb.cs_current_bb = sn.cs_current_bb /\
  sb.cs_current_insts = sn.cs_current_insts ++
    (revert_reason_copy sn.cs_next_id sn.cs_next_var (Var q) out ++
     revert_reason_suffix sn.cs_next_id sn.cs_next_var (Var b) (Var p) (Var q)) /\
  not_fresh_at sm b /\ not_fresh_at sm p /\ not_fresh_at sm q /\
  lookup_var b s = SOME B /\ lookup_var p s = SOME P /\ lookup_var q s = SOME Q /\
  ptr_covers G tn b s (64+ms) /\ ptr_covers G tn p s (32+ms) /\
  ptr_covers G tn q s ms /\
  32+contractABI$ceil32 (LENGTH str) <= ms /\ LENGTH str+63 < dimword(:256) /\
  64+ms < dimword(:256) /\ w2n B+64+ms < dimword(:256) /\
  w2n P+32+ms < dimword(:256) /\
  FLOOKUP s.vs_allocas parent = SOME (w2n Q,ms) /\ parent < sm.cs_next_id ==>
  ?z Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (Abort Revert_abort z)
Proof
  strip_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_storage_string_zero_path_ptr >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  qpat_x_assum `out = Var root` SUBST_ALL_TAC >>
  `not_fresh_at sn root` by
    (irule unwrap_allocated_string_output_old >> goal_assum (drule_at Any) >>
     Cases_on `tr` >> simp[]) >>
  `ci_mono sm sn` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  drule_all string_buffer_tail_observations >> strip_tac >>
  `sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id` by
    fs[ci_mono_def] >>
  `?z Gh th. gas_path_ptr D 0 ctx fn PG Gf tf t 0 Gh th (Abort Revert_abort z)` by
    (drule_at (Pat `_ = _ ++ _`) revert_reason_framed_tail_ptr >>
     disch_then drule_all >> simp[]) >>
  drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ (OK _)`) gas_path_ptr_then >>
  disch_then drule >> simp[] >> metis_tac[]
QED

Theorem revert_reason_runtime_immutable_unwrap_path_ptr:
  ~cenv.ce_is_ctor /\ r.ptr_location = LocCode /\
  unwrap_value cenv (LocatedValue (BaseT (StringT max)) r) sm = (out,sn) /\
  stmt_state_rel ctx fn cenv cx es s /\
  immutable_holds cenv cx (BaseT (StringT max)) (Value (StringV str)) a es s /\
  evaluate_type (get_tenv cx) (BaseT (StringT max)) = SOME (BaseTV (StringT max)) /\
  fn_has_code sm sn fn /\ copy_old_operand sm r.ptr_operand /\
  eval_operand r.ptr_operand s = SOME a /\ op_taint tn r.ptr_operand = {} /\
  32 * type_slot_size (BaseTV (StringT max)) < dimword(:256) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_inv s /\ alloca_room ctx fn s /\ fn_inst_ids_distinct fn /\
  (!i w a sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (a,sz) ==> sz = w2n w) /\
  fn_has_code sn sb fn /\ sb.cs_current_bb = sn.cs_current_bb /\
  sb.cs_current_insts = sn.cs_current_insts ++
    (revert_reason_copy sn.cs_next_id sn.cs_next_var (Var q) out ++
     revert_reason_suffix sn.cs_next_id sn.cs_next_var (Var b) (Var p) (Var q)) /\
  not_fresh_at sm b /\ not_fresh_at sm p /\ not_fresh_at sm q /\
  lookup_var b s = SOME B /\ lookup_var p s = SOME P /\ lookup_var q s = SOME Q /\
  ptr_covers G tn b s (64+ms) /\ ptr_covers G tn p s (32+ms) /\
  ptr_covers G tn q s ms /\
  32+contractABI$ceil32 (LENGTH str) <= ms /\ LENGTH str+63 < dimword(:256) /\
  64+ms < dimword(:256) /\ w2n B+64+ms < dimword(:256) /\
  w2n P+32+ms < dimword(:256) /\
  FLOOKUP s.vs_allocas parent = SOME (w2n Q,ms) /\ parent < sm.cs_next_id ==>
  ?z Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (Abort Revert_abort z)
Proof
  strip_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_runtime_immutable_string_path_ptr >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  qpat_x_assum `out = Var root` SUBST_ALL_TAC >>
  `not_fresh_at sn root` by
    (irule unwrap_allocated_string_output_old >> goal_assum (drule_at Any) >> simp[]) >>
  `ci_mono sm sn` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  drule_all string_buffer_tail_observations >> strip_tac >>
  `sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id` by
    fs[ci_mono_def] >>
  `?z Gh th. gas_path_ptr D 0 ctx fn PG Gf tf t 0 Gh th (Abort Revert_abort z)` by
    (drule_at (Pat `_ = _ ++ _`) revert_reason_framed_tail_ptr >>
     disch_then drule_all >> simp[]) >>
  drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ (OK _)`) gas_path_ptr_then >>
  disch_then drule >> simp[] >> metis_tac[]
QED
