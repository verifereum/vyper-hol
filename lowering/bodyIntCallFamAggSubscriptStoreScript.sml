(* Counted word stores and their fresh-allocation continuation frame. *)
Theory bodyIntCallFamAggSubscriptStore
Ancestors
  bodyIntCallFamAggSubscriptMapSuffix bodyIntCallJointAggCore
  bodyIntCallJointContract placeMemoryCopyEffect placeMemoryPrimitiveForward
  exprSimLiteralBuffer emitHelperProps compileEnv context venomState venomInst
  venomMemProps valueEncodingProps exprLoweringProps intCallFrame emitHelper

Theorem intcall_mstore_effect:
  emit_void MSTORE [ptr_op; value] si = ((),sb) /\
  eval_operand ptr_op s = SOME addr /\ eval_operand value s = SOME w /\
  fn_has_code si sb func /\ ~s.vs_halted /\
  s.vs_current_bb = si.cs_current_bb /\
  s.vs_inst_idx = LENGTH si.cs_current_insts ==>
  typed_copy_effect ctx func si sb s
    (mstore (w2n addr) w s with vs_inst_idx := LENGTH sb.cs_current_insts)
    (w2n addr) 32
Proof
  rpt gen_tac >> strip_tac >>
  drule_all literal_emit_mstore_run >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = si.cs_current_bb` by
    (gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_id_def, emit_def]) >>
  `gas_marked_path F ctx func s 0
    (OK (mstore (w2n addr) w s with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >>
     qexistsl_tac [`emitted_insts si sb`, `si`] >>
     simp[mk_inst_def, is_terminator_def]) >>
  simp[typed_copy_effect_def, lookup_var_def, mstore_memory_nondecreasing] >>
  conj_tac
  >- simp[mstore_def, venom_state_component_equality] >>
  conj_tac
  >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  simp[mstore_def]
QED

Theorem intcall_allocated_mstore_landing:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa s0 es si s /\
  emit_void MSTORE [ptr_op; value] si = ((),sb) /\
  eval_operand ptr_op s = SOME addr /\ eval_operand value s = SOME w /\
  fn_has_code si sb fp.jc_func /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  sa.cs_next_id <= inst.inst_id /\ alloca_inv s /\ fp.jc_lo <= b /\
  b <= w2n addr /\ w2n addr + 32 <= b + sz /\
  sa.cs_next_var <= si.cs_next_var /\
  (!n lb len. local_region ce es.scopes s n lb len ==>
     regions_disjoint b sz lb len) /\
  (!n lb len. local_region ce es0.scopes s0 n lb len ==>
     lb + len <= b \/ b + sz <= lb) ==>
  gas_marked_path F fp.jc_ctx fp.jc_func s 0
    (OK (mstore (w2n addr) w s with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  intcall_expr_cont fp ce env es0 sa s0 es sb
    (mstore (w2n addr) w s with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  `typed_copy_effect fp.jc_ctx fp.jc_func si sb s
    (mstore (w2n addr) w s with vs_inst_idx := LENGTH sb.cs_current_insts)
    (w2n addr) 32` by
    (irule intcall_mstore_effect >> fs[intcall_expr_cont_def] >>
     qexistsl_tac [`ptr_op`, `value`] >> simp[]) >>
  conj_tac >- fs[typed_copy_effect_def] >>
  `si.cs_next_var <= sb.cs_next_var` by
    (drule emitted_insts_emit_void >> simp[]) >>
  `intcall_joint_res fp ce env es si s` by fs[intcall_expr_cont_def] >>
  drule_all intcall_allocated_mstore_run >> strip_tac >>
  drule_all literal_emit_mstore_run >> strip_tac >> gvs[] >>
  irule intcall_owned_store_cont >> simp[] >>
  conj_tac
  >- fs[intcall_joint_res_def, stmt_state_rel_inst_idx] >>
  metis_tac[]
QED
