(* Counted selector write and arithmetic endpoints, without buffer allocation. *)
Theory extcallCalldataOpsMemory
Ancestors
  bodyDeclWordMemory bodyFieldMemoryProps exprSimMapKey valueEncodingProps
  emitHelperProps venomState exprLoweringProps words finite_map

Theorem extcall_calldata_add_mem:
  emit_op ADD [op; Lit (n2w k)] sa = (dst,sb) /\
  eval_operand op s = SOME (n2w a) /\ a+k < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand dst t = SOME (n2w (a+k)) /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `eval_operand (Lit (n2w k)) s = SOME (n2w k)` by
    simp[eval_operand_def] >>
  drule_all emit_ADD_frame >> strip_tac >>
  drule_all attr_add_gas_path >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(t with vs_vars := _) = s` mp_tac >>
     simp_tac (srw_ss()) [venom_state_component_equality]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    metis_tac[abiEncoderAddressReachTheory.abi_encoder_emit_address_shape] >>
  simp[eval_operand_def, lookup_var_def, wordsTheory.word_add_n2w] >>
  fs[lookup_var_def]
QED

Theorem extcall_selector_store_mem:
  emit_void MSTORE [Var p; Lit (n2w method_id)] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var p s = SOME (n2w b) /\ b+32 <= s.vs_alloca_next /\
  b+32 < dimword (:256) /\ alloca_history func s /\ alloca_inv s /\
  fn_inst_ids_distinct func ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t /\
      mem_bytes_at b 32 t.vs_memory = word_to_bytes (n2w method_id : bytes32) T /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      (!x. lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `w2n (n2w b : bytes32) = b` by simp[] >>
  `eval_operand (Lit (n2w method_id)) s = SOME (n2w method_id)` by
    simp[eval_operand_def] >>
  `w2n (n2w b : bytes32) + 32 <= s.vs_alloca_next` by simp[] >>
  drule_all annassign_word_mstore_path_mem >> strip_tac >>
  qexists_tac `mstore b (n2w method_id) s with
    vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `b < dimword (:256)` by decide_tac >>
  fs[] >>
  simp[mem_bytes_at_mstore_same] >>
  simp[mstore_def, lookup_var_def]
QED

Theorem extcall_calldata_bounds:
  L <= A /\ b+(MAX A R+32) < dimword (:256) /\
  b+(MAX A R+32) <= frontier ==>
  (b+28)+(L+4) <= frontier /\
  b+28 < dimword (:256) /\ L+4 < dimword (:256) /\
  b+32 < dimword (:256)
Proof
  simp_tac std_ss [arithmeticTheory.MAX_DEF] >> decide_tac
QED
