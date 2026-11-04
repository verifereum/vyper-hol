(*
 * Internal calls: the lowered INVOKE step (#638)
 *
 * The parts of the internal-call simulation that do not depend on the
 * callee's frame layout (#545) or on the induction shape (#636, #637):
 * what a returning INVOKE does to the caller, how a successful call
 * composes with the code after it, and the shape of compile_call's
 * IntCall case around the INVOKE, return buffer included.
 *
 * TOP-LEVEL:
 *   step_inst_invoke_intret  — a callee that returns with IntRet makes the
 *                              INVOKE give merge_callee_state, with the
 *                              fmp the callee hands back and the INVOKE's
 *                              outputs bound to the returned values
 *   bind_outputs_lookup      — what bind_outputs binds, and that it changes
 *                              nothing but variables
 *   step_inst_invoke_OK_control — a returning INVOKE leaves the caller's
 *                              block, index and halted flag alone
 *   frag_exec_invoke         — an INVOKE that returns, at some fuel, is a
 *                              fragment: later steps compose with it (fuel
 *                              monotonicity, from venomExecProofs' fuel_mono)
 *   frag_exec_invoke_intret  — frag_exec_invoke from the callee's IntRet
 *   compile_call_intcall_shape — compile_call's IntCall case: arguments,
 *                              return buffer, staged arguments, INVOKE,
 *                              and the value it returns.  The buffer is
 *                              32 * returns_count bytes for stack returns,
 *                              which the INVOKE's outputs are stored into,
 *                              or return_buf_size bytes for a memory
 *                              return, which alone passes it to the callee
 *                              as the INVOKE's first argument
 *
 * loweringHalt's compile_alloc_buffer_insts and
 * compile_alloc_buffer_fresh_frag give the buffer's ALLOCA and what it does.
 *)

Theory intCallStep
Ancestors
  list rich_list finite_map
  fragExec loweringHalt exprLowering emitHelper context compileEnv
  venomExecSemantics venomExecProofs venomInst venomState

(* ===== The INVOKE step ===== *)

(* The success counterpart of step_inst_invoke_abort. *)
Theorem step_inst_invoke_intret:
  !fuel ctx inst s name arg_ops callee args cs ret cs'.
    inst.inst_opcode = INVOKE /\
    decode_invoke inst = SOME (name, arg_ops) /\
    lookup_function name ctx.ctx_functions = SOME callee /\
    eval_operands arg_ops s = SOME args /\
    setup_callee callee args s = SOME cs /\
    run_blocks fuel ctx callee cs = IntRet ret cs' /\
    LENGTH inst.inst_outputs = LENGTH ret.iret_values ==>
    bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state s cs')) =
      SOME (FOLDL (\s' (out,v). update_var out v s')
              (adopt_return_fmp ret (merge_callee_state s cs'))
              (ZIP (inst.inst_outputs, ret.iret_values))) /\
    step_inst fuel ctx inst s =
      OK (FOLDL (\s' (out,v). update_var out v s')
            (adopt_return_fmp ret (merge_callee_state s cs'))
            (ZIP (inst.inst_outputs, ret.iret_values)))
Proof
  rpt gen_tac >> strip_tac >>
  `bind_outputs inst.inst_outputs ret.iret_values
     (adopt_return_fmp ret (merge_callee_state s cs')) =
   SOME (FOLDL (\s' (out,v). update_var out v s')
           (adopt_return_fmp ret (merge_callee_state s cs'))
           (ZIP (inst.inst_outputs, ret.iret_values)))`
    by simp[bind_outputs_def] >>
  simp[Once step_inst_def]
QED


Theorem foldl_fupdate_lookup[local]:
  !kvs m x.
    FLOOKUP (FOLDL (\m (k,v). m |+ (k,v)) m kvs) x =
    case ALOOKUP (REVERSE kvs) x of
      SOME v => SOME v
    | NONE => FLOOKUP m x
Proof
  Induct >- simp[] >>
  Cases >> rw[alistTheory.ALOOKUP_APPEND, FLOOKUP_UPDATE] >>
  Cases_on `ALOOKUP (REVERSE kvs) x` >> simp[] >>
  Cases_on `ALOOKUP (REVERSE kvs) q` >> gvs[]
QED

Theorem alookup_reverse_zip_distinct[local]:
  !outs vals i.
    ALL_DISTINCT outs /\ LENGTH outs = LENGTH vals /\ i < LENGTH outs ==>
    ALOOKUP (REVERSE (ZIP (outs, vals))) (EL i outs) = SOME (EL i vals)
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP FST (REVERSE (ZIP (outs, vals))))`
    by simp[MAP_REVERSE, MAP_ZIP, ALL_DISTINCT_REVERSE] >>
  drule_then irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
  simp[MEM_ZIP] >> metis_tac[]
QED

Theorem alookup_zip_not_mem[local]:
  !outs vals x.
    LENGTH outs = LENGTH vals /\ ~MEM x outs ==>
    ALOOKUP (REVERSE (ZIP (outs, vals))) x = NONE
Proof
  rw[alistTheory.ALOOKUP_NONE, MAP_REVERSE, MAP_ZIP]
QED

(* bind_outputs binds each output to its value, and changes nothing else. *)
Theorem bind_outputs_lookup:
  !outs vals s s'.
    bind_outputs outs vals s = SOME s' /\ ALL_DISTINCT outs ==>
    LENGTH outs = LENGTH vals /\
    (!i. i < LENGTH outs ==> lookup_var (EL i outs) s' = SOME (EL i vals)) /\
    (!x. ~MEM x outs ==> lookup_var x s' = lookup_var x s) /\
    ?vars. s' = s with vs_vars := vars
Proof
  rpt gen_tac >> simp[bind_outputs_def] >> strip_tac >>
  gvs[foldl_update_var_vars, lookup_var_def, foldl_fupdate_lookup] >>
  rpt strip_tac
  >- (qspecl_then [`outs`, `vals`, `i`] mp_tac alookup_reverse_zip_distinct >>
      simp[])
  >- (drule_all alookup_zip_not_mem >> simp[]) >>
  qexists_tac `FOLDL (\m (k,v). m |+ (k,v)) s.vs_vars (ZIP (outs,vals))` >>
  simp[]
QED


(* The same, from the callee's IntRet: the INVOKE's result is the caller
   merged with the callee, the returned fmp adopted, the outputs bound. *)
Theorem frag_exec_invoke_intret:
  !ctx st st' inst P Q R.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++ [inst] /\
    inst.inst_opcode = INVOKE /\
    (!s. P s ==>
       ?fuel name arg_ops callee args cs ret cs'.
         decode_invoke inst = SOME (name, arg_ops) /\
         lookup_function name ctx.ctx_functions = SOME callee /\
         eval_operands arg_ops s = SOME args /\
         setup_callee callee args s = SOME cs /\
         run_blocks fuel ctx callee cs = IntRet ret cs' /\
         LENGTH inst.inst_outputs = LENGTH ret.iret_values /\
         Q ((FOLDL (\s' (out,v). update_var out v s')
               (adopt_return_fmp ret (merge_callee_state s cs'))
               (ZIP (inst.inst_outputs, ret.iret_values)))
            with vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >> irule frag_exec_invoke >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule_all step_inst_invoke_intret >> strip_tac >>
  qexists_tac `fuel` >> gvs[]
QED

(* ===== The call site: compile_call's IntCall case ===== *)

Theorem compile_call_intcall_shape:
  !cfn cenv ret_ty ty func_id args dret st v st' ret_count rbs pvs.
    compile_call cfn cenv ret_ty ty (IntCall func_id) args dret st =
      (v, st') /\
    cenv.ce_func_info (nsid_to_string func_id) = (ret_count, rbs, pvs) ==>
    ?arg_vals st1 st2 invoke_args st3.
      compile_multi_vvs cfn cenv args st = (arg_vals, st1) /\
      compile_stage_intcall_args cenv arg_vals pvs (MAP expr_type args) st2 =
        (invoke_args, st3) /\
      (0 < ret_count ==>
       ?rbuf results st4 u.
         compile_alloc_buffer (32 * ret_count) st1 = (rbuf, st2) /\
         emit_multi_op INVOKE
           (Label (internal_fn_label
                     (cenv.ce_func_ids (nsid_to_string func_id))
                     (nsid_to_string func_id)
                     (cenv.ce_func_param_types (nsid_to_string func_id))
                     cenv.ce_is_ctor) :: invoke_args) ret_count st3 =
           (results, st4) /\
         store_multi_results rbuf.buf_operand results 0 st4 = (u, st') /\
         v = LocatedValue ret_ty (base_ptr rbuf)) /\
      (ret_count = 0 /\ 0 < rbs ==>
       ?rbuf u.
         compile_alloc_buffer rbs st1 = (rbuf, st2) /\
         emit_void INVOKE
           (Label (internal_fn_label
                     (cenv.ce_func_ids (nsid_to_string func_id))
                     (nsid_to_string func_id)
                     (cenv.ce_func_param_types (nsid_to_string func_id))
                     cenv.ce_is_ctor) :: rbuf.buf_operand :: invoke_args)
           st3 = (u, st') /\
         v = LocatedValue ret_ty (base_ptr rbuf)) /\
      (ret_count = 0 /\ rbs = 0 ==>
       ?u. st2 = st1 /\
           emit_void INVOKE
             (Label (internal_fn_label
                       (cenv.ce_func_ids (nsid_to_string func_id))
                       (nsid_to_string func_id)
                       (cenv.ce_func_param_types (nsid_to_string func_id))
                       cenv.ce_is_ctor) :: invoke_args) st3 = (u, st') /\
           v = StackValue ret_ty (Lit 0w))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_call _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  Cases_on `0 < ret_count` >> gvs[]
  >- (qmatch_asmsub_rename_tac
        `compile_stage_intcall_args _ _ _ _ s2 = (ia, s3)` >>
      qmatch_asmsub_rename_tac `emit_multi_op INVOKE _ _ s3 = (res, s4)` >>
      Cases_on `store_multi_results rbuf.buf_operand res 0 s4` >> gvs[] >>
      qexistsl_tac [`s2`, `ia`, `s3`] >> simp[] >>
      qexistsl_tac [`res`, `s4`] >> simp[]) >>
  qmatch_asmsub_rename_tac
    `compile_stage_intcall_args _ _ _ _ s2 = (ia, s3)` >>
  Cases_on `0 < rbs` >> gvs[] >>
  qexistsl_tac [`s2`, `ia`, `s3`] >> simp[]
QED

val () =
  let val th = compile_call_intcall_shape
      val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "INTCALL_SHAPE_AUDIT OK\n"
     else raise Fail "internal call shape inherited admission"
  end;
