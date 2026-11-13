(* The actual dynamic-storage body computes offsets before adding its roots. *)
Theory assignDynStorageAddressPtr
Ancestors
  bodyPtrPopLocalRootFrame widenedAssignPtrIndexAddresses assignTuplePtrCopyLen
  typedMemoryCopy freshWrites exprLoweringProps emitHelperProps emitHelper
  context compileEnv bodyPtrDefs fragExec fragGasPathPtr ptrDiscipline
  venomState words finite_map list arithmetic

Theorem dyn_storage_index_address_counted:
  !sa sb sc sd ctr stride prefix base_op mul_op offset_op dst fn ctx D PG G tn s k sw n.
    emit_op MUL [Var ctr;Lit (n2w stride)] sa = (mul_op,sb) /\
    emit_op ADD [Lit (n2w prefix);mul_op] sb = (offset_op,sc) /\
    emit_op ADD [base_op;offset_op] sc = (dst,sd) /\
    fn_has_code sa sd fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    not_fresh_at sa ctr /\ (!x. base_op = Var x ==> not_fresh_at sa x) /\
    lookup_var ctr s = SOME (n2w k) /\ eval_operand base_op s = SOME sw /\
    op_taint tn (Var ctr) = {} /\ op_taint tn base_op = {} /\
    (0 < n ==> ?p total. base_op = Var p /\ ptr_covers G tn p s total /\
      prefix+k*stride < total /\ prefix+k*stride+n <= total /\
      w2n sw+prefix+k*stride < dimword (:256)) ==>
    ?p t H tt.
      dst = Var p /\ not_fresh_at sd p /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t) /\
      t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
      eval_operand dst t = SOME (sw+n2w (prefix+k*stride)) /\
      op_taint tt dst = {} /\ (0 < n ==> ptr_covers H tt p t n) /\
      ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
      t.vs_inst_idx = LENGTH sd.cs_current_insts /\
      tt.t_mem = tn.t_mem /\ tt.t_stor = tn.t_stor /\
      tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sa sb /\ ci_mono sb sc /\ ci_mono sc sd` by
    metis_tac[typed_copy_emit_op_mono] >>
  `cs_extends sa sb /\ cs_extends sb sc /\ cs_extends sc sd /\
   cs_extends sb sd` by metis_tac[ci_mono_def, cs_extends_trans] >>
  `fn_has_code sa sb fn /\ fn_has_code sb sc fn /\ fn_has_code sc sd fn` by
    metis_tac[fn_has_code_split] >>
  `sa.cs_current_bb = sb.cs_current_bb /\
   sb.cs_current_bb = sc.cs_current_bb /\
   sc.cs_current_bb = sd.cs_current_bb` by
    metis_tac[emit_op_same_blocks, same_blocks_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x /\ not_fresh_at sc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def, LESS_EQ_TRANS] >>
  `!tm w u. eval_operand (Lit w) u = SOME w /\ op_taint tm (Lit w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  `eval_operand (Var ctr) s = SOME (n2w k) /\
   eval_operand (Lit (n2w stride)) s = SOME (n2w stride) /\
   op_taint tn (Lit (n2w stride)) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all pop_local_mul_exact >>
  disch_then (qspecl_then [`PG`,`G`,`D`] mp_tac) >>
  disch_then (qx_choosel_then [`x1`,`s1`,`G1`,`tn1`] strip_assume_tac) >>
  qpat_x_assum `s1 = s with <|vs_vars := _; vs_inst_idx := _|>`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `eval_operand mul_op s1 = SOME (n2w (k*stride))` by
    simp[GSYM word_mul_n2w] >>
  suspend "offset"
QED

Resume dyn_storage_index_address_counted[offset]:
  mp_tac (Q.INST [`n` |-> `0`, `off` |-> `k*stride`,
    `bop` |-> `Lit (n2w prefix)`, `offset` |-> `mul_op`,
    `sa` |-> `sb`, `sb` |-> `sc`, `dst` |-> `offset_op`,
    `fn` |-> `fn`, `ctx` |-> `ctx`, `s` |-> `s1`,
    `a` |-> `n2w prefix:bytes32`, `tn` |-> `tn1`, `G` |-> `G1`,
    `D` |-> `D`, `PG` |-> `PG`] (SPEC_ALL widened_assign_index_add_exact)) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`x2`,`s2`,`G2`,`tn2`] strip_assume_tac) >>
  qpat_x_assum `s2 = s1 with <|vs_vars := _; vs_inst_idx := _|>`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `eval_operand offset_op s2 = SOME (n2w (prefix+k*stride))` by
    simp[GSYM word_add_n2w] >>
  `s2.vs_labels = s.vs_labels` by simp[] >>
  `eval_operand base_op s2 = SOME sw /\ op_taint tn2 base_op = {}` by
    (Cases_on `base_op` >> gnvs[eval_operand_def, op_taint_def] >>
     metis_tac[]) >>
  `(0 < n ==> ?p total. base_op = Var p /\
    ptr_covers G2 tn2 p s2 total /\ prefix+k*stride < total /\
    prefix+k*stride+n <= total /\
    w2n sw+(prefix+k*stride) < dimword (:256))` by
    (strip_tac >> qpat_x_assum `0 < n ==> _` drule >>
     disch_then (qx_choosel_then [`root_var`,`cap_sz`] strip_assume_tac) >>
     qexistsl_tac [`root_var`,`cap_sz`] >> pure_asm_rewrite_tac[ADD_ASSOC] >>
     metis_tac[ptr_covers_lookup_frame]) >>
  suspend "address"
QED

Resume dyn_storage_index_address_counted[address]:
  mp_tac (Q.INST [`n` |-> `n`, `off` |-> `prefix+k*stride`,
    `bop` |-> `base_op`, `offset` |-> `offset_op`,
    `sa` |-> `sc`, `sb` |-> `sd`, `dst` |-> `dst`,
    `fn` |-> `fn`, `ctx` |-> `ctx`, `s` |-> `s2`,
    `a` |-> `sw`, `tn` |-> `tn2`, `G` |-> `G2`,
    `D` |-> `D`, `PG` |-> `PG`] (SPEC_ALL widened_assign_index_add_exact)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`x3`,`s3`,`G3`,`tn3`] strip_assume_tac) >>
  qpat_x_assum `s3 = s2 with <|vs_vars := _; vs_inst_idx := _|>`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2 (OK s2)` by
    (qpat_assum `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)`
       (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G3 tn3 (OK s3)` by
    (qpat_assum `gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2 (OK s2)`
       (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  qexistsl_tac [`x3`,`s3`,`G3`,`tn3`] >>
  simp[venom_state_component_equality] >>
  rpt strip_tac >> metis_tac[]
QED

Finalise dyn_storage_index_address_counted
