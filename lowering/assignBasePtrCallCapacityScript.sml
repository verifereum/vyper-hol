(* Concrete caller-owned return buffer; no callee simulation is assumed. *)
Theory assignBasePtrCallCapacity
Ancestors assignBasePtrLiteralPost intCallFrame allocaFrontierBound exprLowering
  context emitHelper compileEnv venomExecSemantics venomInst venomState

Theorem assign_base_call96_layout:
  !cfn cenv ret_ty ty fid default_ret sa buf sb sc.
    cenv.ce_func_info (nsid_to_string fid) = (0,96,[]) /\
    cenv.ce_func_return_type (nsid_to_string fid) = BaseT (BytesT (Dynamic 64)) /\
    compile_alloc_buffer 96 sa = (buf,sb) /\
    emit_void INVOKE
      [Label (internal_fn_label (cenv.ce_func_ids (nsid_to_string fid))
         (nsid_to_string fid) (cenv.ce_func_param_types (nsid_to_string fid))
         cenv.ce_is_ctor); buf.buf_operand] sb = ((),sc) ==>
    compile_call cfn cenv ret_ty ty (IntCall fid) [] default_ret sa =
      (LocatedValue (BaseT (BytesT (Dynamic 64))) (base_ptr buf),sc)
Proof
  rpt strip_tac >>
  simp[Once compile_call_def, compile_multi_vvs_def,
       compile_stage_intcall_args_def, comp_return_def, comp_bind_def]
QED

Theorem assign_base_invoke_no_outputs_frame:
  !fuel ctx inst s t.
    inst.inst_opcode = INVOKE /\ inst.inst_outputs = [] /\
    step_inst fuel ctx inst s = OK t ==>
    t.vs_allocas = s.vs_allocas /\
    (!x. lookup_var x t = lookup_var x s)
Proof
  rpt strip_tac >>
  gvs[Once step_inst_def, AllCaseEqs()] >>
  drule invoke_return_frame >> simp[]
QED

Theorem assign_base_call96_endpoint:
  !func cenv cx es s inst p u t ctx fuel label.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit 96w] /\ inst.inst_outputs = [p] /\
    not_local_ptr cenv es.scopes p /\ exec_alloca inst s (96w:bytes32) = OK u /\
    step_inst fuel ctx (mk_inst (inst.inst_id + 1) INVOKE [Label label; Var p] [])
      (u with vs_inst_idx := SUC s.vs_inst_idx) = OK t ==>
    ?w. eval_operand (Var p) t = SOME w /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,96) /\
      w2n w + 64 < dimword(:256)
Proof
  rpt strip_tac >>
  drule assign_base_ptr_alloca_endpoint >>
  disch_then (qspecl_then [`inst`, `p`, `96w`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_at (Pat `step_inst _ _ _ _ = _`) assign_base_invoke_no_outputs_frame >>
  simp[mk_inst_def] >> strip_tac >>
  simp[eval_operand_def, lookup_var_def] >>
  gvs[wordsTheory.dimword_def, lookup_var_def] >> decide_tac
QED

Theorem assign_base_call96_insts:
  !sa buf sb sc label.
    compile_alloc_buffer 96 sa = (buf,sb) /\
    emit_void INVOKE [Label label; buf.buf_operand] sb = ((),sc) ==>
    buf.buf_operand = Var ("%" ++ toString sa.cs_next_var) /\
    sc.cs_current_bb = sa.cs_current_bb /\
    sc.cs_next_id = sa.cs_next_id + 2 /\
    sc.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ALLOCA [Lit 96w] ["%" ++ toString sa.cs_next_var];
       mk_inst (sa.cs_next_id + 1) INVOKE
         [Label label; Var ("%" ++ toString sa.cs_next_var)] []]
Proof
  rpt gen_tac >>
  simp[compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def, emit_def] >>
  strip_tac >> gvs[]
QED
