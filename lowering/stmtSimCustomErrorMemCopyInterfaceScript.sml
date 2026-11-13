Theory stmtSimCustomErrorMemCopyInterface
Ancestors
  stmtSimCustomErrorMemCopyPrimitive placeTypedCopyRecursivePath
  placeMemoryFieldsForward bodyFieldMemoryProps context compileEnv
  venomState venomExecSemantics fragGasMode fragGasPathMem
  exprSimMemUnwrap valueEncoding valueEncodingProps words list
  fragExecMem emitHelperProps exprLoweringProps

Definition typed_copy_checked_entry_def:
  typed_copy_checked_entry cenv ctx dty sty dtv stv v <=>
    !func dst src sa sb s dw sw.
      compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      val_in_memory stv v (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      w2n sw + type_memory_size stv <= s.vs_alloca_next /\
      w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      alloca_inv s /\ alloca_history func s /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?t. gas_marked_path T ctx func s 0 (OK t) /\
          val_in_memory dtv v (w2n dw) t.vs_memory /\
          typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
          ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
End

Theorem typed_copy_checked_entry_run:
  typed_copy_checked_entry cenv ctx dty sty dtv stv v /\
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  simp_tac std_ss [typed_copy_checked_entry_def] >> strip_tac >>
  first_x_assum irule >> simp[] >> qexistsl_tac [`dst`, `src`, `sw`] >> simp[]
QED

Theorem compile_with_byte_offset_checked:
  compile_with_byte_offset op off sa = (out_op,sb) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME w /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand out_op t = SOME (w + n2w off) /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all compile_with_byte_offset_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (Cases_on `off = 0`
     >- (qpat_x_assum `compile_with_byte_offset _ _ _ = _` mp_tac >>
         simp[compile_with_byte_offset_def, comp_return_def] >>
         strip_tac >> simp[emitted_insts_def, run_inst_seq_mem_ok_def]) >>
     irule attr_add_prefix_mem_ok >>
     qexistsl_tac [`out_op`, `[op; Lit (n2w off)]`] >>
     gvs[compile_with_byte_offset_def]) >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb` by
    (irule straight_path_mem >> simp[] >> qexists_tac `sa` >>
     simp[EVERY_MEM] >> gvs[EVERY_MEM]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >>
  qpat_x_assum `(_ with vs_vars := _) = s` mp_tac >>
  simp[venom_state_component_equality] >> metis_tac[lookup_var_def]
QED
