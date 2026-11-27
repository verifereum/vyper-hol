(*
 * The two boundaries of the internal call's full case, the INVOKE and the
 * callee's return, at the joint judgment's (DF H, lo) pointer ghost: the
 * source and memory relations bodyIntCallSeams states there, plus the
 * storage domain and the pointer facts the joint path carries across them.
 *
 * TOP-LEVEL:
 *   intcall_entry_full -- the caller at the INVOKE
 *   intcall_callee_exit_full -- how the callee's run ends
 *)
Theory bodyFullIntCallDefs
Ancestors
  bodyFullPostsMods bodyIntCallSeams bodyPtrDefs ptrDiscipline intCallCallee compileVyper compileUnit
  exprLowering immSectionDead vyperStorageFootprint vyperInterpreter
  vyperState vyperAST venomState venomExecSemantics list
  contextCodegenRel contextRawReachable

val _ = Parse.hide "body";

(* Source, caller frame and two-phase argument staging at the INVOKE, plus:
   - Source: the storage the call reaches is well formed on H's domain.
   - Pointer: the caller's ghost invariant at t with its own scopes, the
     ghost of sa's variables and the bytes vv_post keeps unchanged since
     s0, and t's allocations;
   - Return buffer: a located vv's pointer is an untainted variable whose
     provenance is the call's own ALLOCA of the buffer's size;
   - INVOKE: the operands are untainted; at the callee's package, its
     arguments are related whatever t's tainted bytes hold, and each
     memory parameter's pointer, and the return buffer's when it is
     passed, lies inside the site its operand's provenance gives. *)
Definition intcall_entry_full_mods_def:
  intcall_entry_full_mods (DF, lo, d) H mods src tops ctx func cenv cx tenv name es sa sb
      vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn <=>
    (
    ~MEM (src,name) cx.stk /\
    (?dflts s1 vs t1 sd dvs td.
       lookup_callable_function cx.in_deploy name tops =
         SOME (mut,nr,args,dflts,ret,ss) /\
       eval_exprs cx es s1 = (INL vs,t1) /\
       eval_exprs (cx with stk updated_by CONS (src,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
       bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv) /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    call_evaluation_safe (cx with stk updated_by CONS (src,name))
      (int_calls_stmts ss) /\
    es1.scopes = [penv] /\
    gas_admissible (intcall_rest_at cx src name mut nr ss prev rtv) expr_vv_res_ok es1 /\
    stmt_state_rel H ctx func cenv cx (es1 with scopes := prev) t /\
    expr_sim_inv_mods mods cenv cx tenv (es1 with scopes := prev) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es0.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es0 (es1 with scopes := prev) s0 t /\
    (!n lo sz aid off asz.
       local_region cenv prev t n lo sz /\
       FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
       sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
       regions_disjoint lo sz off asz) /\
    ?st2 supplied_ops st2a default_ops invoke_args st3 rc rbs pvs lbl arg_ops bb inst argv.
      cenv.ce_func_info (nsid_to_string (src,name)) = (rc,rbs,pvs) /\
      compile_stage_intcall_args compile_expr cenv es pvs
        (TAKE (LENGTH es + LENGTH (omitted_defaults cenv (nsid_to_string (src,name)) (LENGTH es)))
           (cenv.ce_func_param_types (nsid_to_string (src,name))))
        st2 = (supplied_ops,st2a) /\
      compile_stage_intcall_args compile_expr (cenv_without_defaults cenv (nsid_to_string (src,name)))
        (omitted_defaults cenv (nsid_to_string (src,name)) (LENGTH es)) (DROP (LENGTH es) pvs)
        (DROP (LENGTH es)
           (TAKE (LENGTH es + LENGTH (omitted_defaults cenv (nsid_to_string (src,name)) (LENGTH es)))
              (cenv.ce_func_param_types (nsid_to_string (src,name)))))
        st2a = (default_ops,st3) /\
      invoke_args = supplied_ops ++ default_ops /\
      lbl = internal_fn_label (cenv.ce_func_ids (nsid_to_string (src,name)))
              (nsid_to_string (src,name))
              (cenv.ce_func_param_types (nsid_to_string (src,name)))
              cenv.ce_is_ctor /\
      (rc = 0 /\ rbs = 0 ==>
       st2 = sa /\ arg_ops = invoke_args /\
       (?u. emit_void INVOKE (Label lbl :: invoke_args) st3 = (u,sb)) /\
       vv = StackValue (cenv.ce_func_return_type (nsid_to_string (src,name)))
              (Lit 0w)) /\
      (0 < rc \/ 0 < rbs ==>
       ?rbuf aid off.
         compile_alloc_buffer (if 0 < rc then 32 * rc else rbs) sa =
           (rbuf,st2) /\
         vv = LocatedValue
                (cenv.ce_func_return_type (nsid_to_string (src,name)))
                (base_ptr rbuf) /\
         eval_operand rbuf.buf_operand t = SOME (n2w off) /\
         FLOOKUP t.vs_allocas aid = SOME (off,rbuf.buf_size) /\
         aid = sa.cs_next_id /\
         (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
                inst.inst_id = aid) /\
         sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
         (0 < rc ==>
          arg_ops = invoke_args /\
          ?results st4 u.
            emit_multi_op INVOKE (Label lbl :: invoke_args) rc st3 =
              (results,st4) /\
            store_multi_results rbuf.buf_operand results 0 st4 = (u,sb)) /\
         (rc = 0 ==>
          arg_ops = rbuf.buf_operand :: invoke_args /\
          (?u. emit_void INVOKE (Label lbl :: rbuf.buf_operand :: invoke_args)
                 st3 = (u,sb)) /\
          HD argv = n2w off /\ type_memory_size rtv <= rbuf.buf_size /\
          w2n (HD argv) + type_memory_size rtv <= t.vs_alloca_next)) /\
      ~t.vs_halted /\ t.vs_current_bb = st3.cs_current_bb /\
      t.vs_inst_idx = LENGTH st3.cs_current_insts /\
      lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      decode_invoke inst = SOME (lbl,arg_ops) /\
      eval_operands arg_ops t = SOME argv /\
      (?callee entered. gas_invoke_entry (ctx,func) t callee entered) /\
      !callee setup use_trans nkeys imm_len dflts lbl' ce params has_rb is_nr key
       trans view ctor imm_len' ss' rt.
        lookup_function lbl ctx.ctx_functions = SOME callee /\
        setup_callee callee argv t = SOME setup /\
        set_internal_package_target cenv.ce_target
          (package_internal_fn_unit mods use_trans (nkeys : string -> num)
             cenv.ce_is_ctor imm_len
             (src,(mut,nr,rr,name,args,(dflts : expr list),ret,ss))) =
          (lbl',ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len',ss',rt) ==>
        lbl' = lbl /\
        (has_rb <=> rc = 0 /\ 0 < rbs) /\
        (ce.ce_is_ctor ==> IS_SOME (FLOOKUP t.vs_labels "runtime_begin")) /\
        state_rel H func ce cx (es1 with scopes := []) t /\
        internal_immutable_regions ce cx es1 t.vs_alloca_next /\
        internal_args_rel ce params penv (if has_rb then 1 else 0) argv
          t.vs_alloca_next t.vs_memory /\
        (!i po psz.
           i < LENGTH params /\ ~SND (EL i params) /\
           FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
           ?aid off asz.
             FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
             (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
                    inst.inst_id = aid) /\
             sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
             off <= w2n (EL ((if has_rb then 1 else 0) + i) argv) /\
             w2n (EL ((if has_rb then 1 else 0) + i) argv) + psz <=
               off + asz) /\
        (has_rb ==> !i po psz.
           i < LENGTH params /\ ~SND (EL i params) /\
           FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
           regions_disjoint (w2n (HD argv)) (type_memory_size rtv)
             (w2n (EL (1 + i) argv)) psz) /\
        (ce.ce_is_ctor ==> !i po psz nm tv iv io.
          i < LENGTH params /\ ~SND (EL i params) /\
          FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
          FLOOKUP ce.ce_module_vars (ce.ce_module,nm) =
            SOME (ImmutableLoc io) /\
          FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of
                     NONE => FEMPTY
                   | SOME imms => get_source_immutables ce.ce_module imms) nm =
            SOME (tv,iv) ==>
          regions_disjoint io (type_memory_size tv)
            (w2n (EL ((if has_rb then 1 else 0) + i) argv)) psz) /\
        (has_rb /\ ce.ce_is_ctor ==> !nm tv iv io.
          FLOOKUP ce.ce_module_vars (ce.ce_module,nm) =
            SOME (ImmutableLoc io) /\
          FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of
                     NONE => FEMPTY
                   | SOME imms => get_source_immutables ce.ce_module imms) nm =
            SOME (tv,iv) ==>
          regions_disjoint io (type_memory_size tv)
            (w2n (HD argv)) (type_memory_size rtv)) /\
        t.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
        alloca_room ctx callee setup /\ fmp_room ctx callee setup
    ) /\
    storage_well_formed_on cx es1 (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx (es1 with scopes := prev) G tn t /\
    alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!inst. active_inst func inst t ==>
       frag_reachable ctx func s0 func inst t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\
    (!ty p buf. vv = LocatedValue ty p /\ p.ptr_buf = SOME buf ==>
       ?x off aid.
         p.ptr_operand = Var x /\ op_taint tn (Var x) = {} /\
         FLOOKUP G x = SOME (off,buf.buf_size) /\
         eval_operand p.ptr_operand t = SOME (n2w off) /\
         FLOOKUP t.vs_allocas aid = SOME (off,buf.buf_size) /\
         aid = sa.cs_next_id /\ aid < sb.cs_next_id /\
         lo <= off /\ off + buf.buf_size <= t.vs_alloca_next) /\
    !bb inst lbl arg_ops argv.
      lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      decode_invoke inst = SOME (lbl,arg_ops) /\
      eval_operands arg_ops t = SOME argv ==>
      EVERY (\op. op_taint tn op = {}) arg_ops /\
      (!b bsz. MEM (SOME (b,bsz)) (MAP (op_prov G) arg_ops) ==>
         ?aid. FLOOKUP t.vs_allocas aid = SOME (b,bsz) /\
           sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
           lo <= b /\ b + bsz <= t.vs_alloca_next) /\
      !callee setup use_trans nkeys imm_len dflts lbl' ce params has_rb is_nr key
       trans view ctor imm_len' ss' rt.
        lookup_function lbl ctx.ctx_functions = SOME callee /\
        setup_callee callee argv t = SOME setup /\
        set_internal_package_target cenv.ce_target
          (package_internal_fn_unit mods use_trans (nkeys : string -> num)
             cenv.ce_is_ctor imm_len
             (src,(mut,nr,rr,name,args,(dflts : expr list),ret,ss))) =
          (lbl',ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len',ss',rt) ==>
        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
           internal_args_rel ce params penv (if has_rb then 1 else 0) argv
             t.vs_alloca_next mem) /\
        (!i off sz.
           i < LENGTH params /\ ~SND (EL i params) /\
           FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
           ?b bsz aid.
             op_prov G (EL ((if has_rb then 1 else 0) + i) arg_ops) =
               SOME (b,bsz) /\
             FLOOKUP t.vs_allocas aid = SOME (b,bsz) /\
             sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
             lo <= b /\ b + bsz <= t.vs_alloca_next /\
             b <= w2n (EL ((if has_rb then 1 else 0) + i) argv) /\
             w2n (EL ((if has_rb then 1 else 0) + i) argv) + sz <= b + bsz) /\
        (has_rb ==>
         ?b bsz aid. op_prov G (HD arg_ops) = SOME (b,bsz) /\
           FLOOKUP t.vs_allocas aid = SOME (b,bsz) /\
           aid = sa.cs_next_id /\ aid < sb.cs_next_id /\
           lo <= b /\ b + bsz <= t.vs_alloca_next /\
           b <= w2n (HD argv) /\
           w2n (HD argv) + type_memory_size rtv <= b + bsz)
End

Definition intcall_entry_full_def:
  intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name es sa sb
      vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn <=>
    (
    ~MEM (NONE,name) cx.stk /\
    (?dflts s1 vs t1 sd dvs td.
       lookup_callable_function cx.in_deploy name tops =
         SOME (mut,nr,args,dflts,ret,ss) /\
       eval_exprs cx es s1 = (INL vs,t1) /\
       eval_exprs (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
       bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv) /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    call_evaluation_safe (cx with stk updated_by CONS (NONE,name))
      (int_calls_stmts ss) /\
    es1.scopes = [penv] /\
    gas_admissible (intcall_rest cx name mut nr ss prev rtv) expr_vv_res_ok es1 /\
    stmt_state_rel H ctx func cenv cx (es1 with scopes := prev) t /\
    expr_sim_inv cenv cx tenv (es1 with scopes := prev) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es0.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es0 (es1 with scopes := prev) s0 t /\
    (!n lo sz aid off asz.
       local_region cenv prev t n lo sz /\
       FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
       sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
       regions_disjoint lo sz off asz) /\
    ?st2 supplied_ops st2a default_ops invoke_args st3 rc rbs pvs lbl arg_ops bb inst argv.
      cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
      compile_stage_intcall_args compile_expr cenv es pvs
        (TAKE (LENGTH es + LENGTH (omitted_defaults cenv (nsid_to_string (NONE,name)) (LENGTH es)))
           (cenv.ce_func_param_types (nsid_to_string (NONE,name))))
        st2 = (supplied_ops,st2a) /\
      compile_stage_intcall_args compile_expr (cenv_without_defaults cenv (nsid_to_string (NONE,name)))
        (omitted_defaults cenv (nsid_to_string (NONE,name)) (LENGTH es)) (DROP (LENGTH es) pvs)
        (DROP (LENGTH es)
           (TAKE (LENGTH es + LENGTH (omitted_defaults cenv (nsid_to_string (NONE,name)) (LENGTH es)))
              (cenv.ce_func_param_types (nsid_to_string (NONE,name)))))
        st2a = (default_ops,st3) /\
      invoke_args = supplied_ops ++ default_ops /\
      lbl = internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
              (nsid_to_string (NONE,name))
              (cenv.ce_func_param_types (nsid_to_string (NONE,name)))
              cenv.ce_is_ctor /\
      (rc = 0 /\ rbs = 0 ==>
       st2 = sa /\ arg_ops = invoke_args /\
       (?u. emit_void INVOKE (Label lbl :: invoke_args) st3 = (u,sb)) /\
       vv = StackValue (cenv.ce_func_return_type (nsid_to_string (NONE,name)))
              (Lit 0w)) /\
      (0 < rc \/ 0 < rbs ==>
       ?rbuf aid off.
         compile_alloc_buffer (if 0 < rc then 32 * rc else rbs) sa =
           (rbuf,st2) /\
         vv = LocatedValue
                (cenv.ce_func_return_type (nsid_to_string (NONE,name)))
                (base_ptr rbuf) /\
         eval_operand rbuf.buf_operand t = SOME (n2w off) /\
         FLOOKUP t.vs_allocas aid = SOME (off,rbuf.buf_size) /\
         aid = sa.cs_next_id /\
         (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
                inst.inst_id = aid) /\
         sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
         (0 < rc ==>
          arg_ops = invoke_args /\
          ?results st4 u.
            emit_multi_op INVOKE (Label lbl :: invoke_args) rc st3 =
              (results,st4) /\
            store_multi_results rbuf.buf_operand results 0 st4 = (u,sb)) /\
         (rc = 0 ==>
          arg_ops = rbuf.buf_operand :: invoke_args /\
          (?u. emit_void INVOKE (Label lbl :: rbuf.buf_operand :: invoke_args)
                 st3 = (u,sb)) /\
          HD argv = n2w off /\ type_memory_size rtv <= rbuf.buf_size /\
          w2n (HD argv) + type_memory_size rtv <= t.vs_alloca_next)) /\
      ~t.vs_halted /\ t.vs_current_bb = st3.cs_current_bb /\
      t.vs_inst_idx = LENGTH st3.cs_current_insts /\
      lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      decode_invoke inst = SOME (lbl,arg_ops) /\
      eval_operands arg_ops t = SOME argv /\
      (?callee entered. gas_invoke_entry (ctx,func) t callee entered) /\
      !callee setup use_trans nkeys imm_len dflts lbl' ce params has_rb is_nr key
       trans view ctor imm_len' ss' rt.
        lookup_function lbl ctx.ctx_functions = SOME callee /\
        setup_callee callee argv t = SOME setup /\
        set_internal_package_target cenv.ce_target
          (package_internal_fn tops use_trans (nkeys : string -> num)
             cenv.ce_is_ctor imm_len
             (mut,nr,rr,name,args,(dflts : expr list),ret,ss)) =
          (lbl',ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len',ss',rt) ==>
        lbl' = lbl /\
        (has_rb <=> rc = 0 /\ 0 < rbs) /\
        (ce.ce_is_ctor ==> IS_SOME (FLOOKUP t.vs_labels "runtime_begin")) /\
        state_rel H func ce cx (es1 with scopes := []) t /\
        internal_immutable_regions ce cx es1 t.vs_alloca_next /\
        internal_args_rel ce params penv (if has_rb then 1 else 0) argv
          t.vs_alloca_next t.vs_memory /\
        (!i po psz.
           i < LENGTH params /\ ~SND (EL i params) /\
           FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
           ?aid off asz.
             FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
             (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
                    inst.inst_id = aid) /\
             sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
             off <= w2n (EL ((if has_rb then 1 else 0) + i) argv) /\
             w2n (EL ((if has_rb then 1 else 0) + i) argv) + psz <=
               off + asz) /\
        (has_rb ==> !i po psz.
           i < LENGTH params /\ ~SND (EL i params) /\
           FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) ==>
           regions_disjoint (w2n (HD argv)) (type_memory_size rtv)
             (w2n (EL (1 + i) argv)) psz) /\
        (ce.ce_is_ctor ==> !i po psz nm tv iv io.
          i < LENGTH params /\ ~SND (EL i params) /\
          FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po psz) /\
          FLOOKUP ce.ce_module_vars (ce.ce_module,nm) =
            SOME (ImmutableLoc io) /\
          FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of
                     NONE => FEMPTY
                   | SOME imms => get_source_immutables ce.ce_module imms) nm =
            SOME (tv,iv) ==>
          regions_disjoint io (type_memory_size tv)
            (w2n (EL ((if has_rb then 1 else 0) + i) argv)) psz) /\
        (has_rb /\ ce.ce_is_ctor ==> !nm tv iv io.
          FLOOKUP ce.ce_module_vars (ce.ce_module,nm) =
            SOME (ImmutableLoc io) /\
          FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of
                     NONE => FEMPTY
                   | SOME imms => get_source_immutables ce.ce_module imms) nm =
            SOME (tv,iv) ==>
          regions_disjoint io (type_memory_size tv)
            (w2n (HD argv)) (type_memory_size rtv)) /\
        t.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
        alloca_room ctx callee setup /\ fmp_room ctx callee setup
    ) /\
    storage_well_formed_on cx es1 (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx (es1 with scopes := prev) G tn t /\
    alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!inst. active_inst func inst t ==>
       frag_reachable ctx func s0 func inst t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\
    (!ty p buf. vv = LocatedValue ty p /\ p.ptr_buf = SOME buf ==>
       ?x off aid.
         p.ptr_operand = Var x /\ op_taint tn (Var x) = {} /\
         FLOOKUP G x = SOME (off,buf.buf_size) /\
         eval_operand p.ptr_operand t = SOME (n2w off) /\
         FLOOKUP t.vs_allocas aid = SOME (off,buf.buf_size) /\
         aid = sa.cs_next_id /\ aid < sb.cs_next_id /\
         lo <= off /\ off + buf.buf_size <= t.vs_alloca_next) /\
    !bb inst lbl arg_ops argv.
      lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      decode_invoke inst = SOME (lbl,arg_ops) /\
      eval_operands arg_ops t = SOME argv ==>
      EVERY (\op. op_taint tn op = {}) arg_ops /\
      (!b bsz. MEM (SOME (b,bsz)) (MAP (op_prov G) arg_ops) ==>
         ?aid. FLOOKUP t.vs_allocas aid = SOME (b,bsz) /\
           sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
           lo <= b /\ b + bsz <= t.vs_alloca_next) /\
      !callee setup use_trans nkeys imm_len dflts lbl' ce params has_rb is_nr key
       trans view ctor imm_len' ss' rt.
        lookup_function lbl ctx.ctx_functions = SOME callee /\
        setup_callee callee argv t = SOME setup /\
        set_internal_package_target cenv.ce_target
          (package_internal_fn tops use_trans (nkeys : string -> num)
             cenv.ce_is_ctor imm_len
             (mut,nr,rr,name,args,(dflts : expr list),ret,ss)) =
          (lbl',ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len',ss',rt) ==>
        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
           internal_args_rel ce params penv (if has_rb then 1 else 0) argv
             t.vs_alloca_next mem) /\
        (!i off sz.
           i < LENGTH params /\ ~SND (EL i params) /\
           FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
           ?b bsz aid.
             op_prov G (EL ((if has_rb then 1 else 0) + i) arg_ops) =
               SOME (b,bsz) /\
             FLOOKUP t.vs_allocas aid = SOME (b,bsz) /\
             sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
             lo <= b /\ b + bsz <= t.vs_alloca_next /\
             b <= w2n (EL ((if has_rb then 1 else 0) + i) argv) /\
             w2n (EL ((if has_rb then 1 else 0) + i) argv) + sz <= b + bsz) /\
        (has_rb ==>
         ?b bsz aid. op_prov G (HD arg_ops) = SOME (b,bsz) /\
           FLOOKUP t.vs_allocas aid = SOME (b,bsz) /\
           aid = sa.cs_next_id /\ aid < sb.cs_next_id /\
           lo <= b /\ b + bsz <= t.vs_alloca_next /\
           b <= w2n (HD argv) /\
           w2n (HD argv) + type_memory_size rtv <= b + bsz)
End

Theorem intcall_entry_full_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  cenv.ce_module = NONE /\ immutable_section_layout_mods [(NONE,tops)] cenv ==>
  (intcall_entry_full_mods (DF,lo,d) H [(NONE,tops)] NONE tops ctx func cenv cx tenv
     name es sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn <=>
   intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv
     name es sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn)
Proof
  strip_tac >>
  asm_simp_tac bool_ss
    [intcall_entry_full_mods_def, intcall_entry_full_def, package_internal_fn_unit_singleton,
     GSYM intcall_rest_singleton_def, expr_sim_inv_mods_singleton]
QED

(* intcall_callee_exit, and at an IntRet, with the ghost gt the callee
   ends with: the storage the callee leaves is well formed on H's domain;
   its storage, transient and immutables taint is in DF H's dead bytes, and
   the fixed region [0, lo) is tainted only where the immutables section
   is dead; it taints no byte in [lo, t's frontier) outside the call's own
   allocations (ids in [n,m)) that the caller's taint tn did not hold; and
   the return buffer rb, if any, holds the returned value whatever its
   tainted bytes hold. *)
Definition intcall_callee_exit_full_mods_def:
  intcall_callee_exit_full_mods mods (DF, lo) H func cenv cx mut nr rtv rc
      (rb:bytes32 option) (n:num) (m:num) (t:venom_state) (tn:taint) res
      (ee:evaluation_state) (gt : (string |-> num # num) # taint) r <=>
    intcall_callee_exit_mods mods H func cenv cx mut nr rtv rc rb n m t res ee r /\
    !v ir s'.
      res = INL v /\ r = IntRet ir s' ==>
      (?ee'. unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),ee') /\
             storage_well_formed_on cx ee' (FST H)) /\
      stor_taint_ok_at (DF H) (SND gt) s' /\
      (!i. i < lo /\ i IN (SND gt).t_mem ==>
           imm_section_dead_mods (cenv with ce_modules := mods)
             (mem_bytes_at 0 lo s'.vs_memory) i) /\
      (!i. lo <= i /\ i < t.vs_alloca_next /\ i IN (SND gt).t_mem /\
           (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
                          n <= aid /\ aid < m ==> i < off \/ off + asz <= i) ==>
           i IN tn.t_mem) /\
      (!p. rb = SOME p ==>
           !mem. mem_agree_outside (SND gt).t_mem s'.vs_memory mem ==>
                 val_in_memory rtv v (w2n p) mem)
End

Definition intcall_callee_exit_full_singleton_def:
  intcall_callee_exit_full (DF, lo) H func cenv cx mut nr rtv rc
      rb n m t tn res ee gt r <=>
    intcall_callee_exit_full_mods [(NONE,cx_tops cx)] (DF, lo) H func cenv cx
      mut nr rtv rc rb n m t tn res ee gt r
End

Triviality intcall_exit_dead_singleton:
  imm_section_dead_mods (cenv with ce_modules := [(NONE,tops)]) sec i <=>
  imm_section_dead tops sec i
Proof
  irule imm_section_dead_mods_singleton >> simp[]
QED

Theorem intcall_callee_exit_full_def =
  PURE_REWRITE_RULE
    [intcall_callee_exit_full_mods_def, GSYM intcall_callee_exit_singleton_def,
     intcall_exit_dead_singleton] intcall_callee_exit_full_singleton_def;
