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
  bodyIntCallSeams bodyPtrDefs ptrDiscipline intCallCallee compileVyper
  exprLowering immSectionDead vyperStorageFootprint vyperInterpreter
  vyperState vyperAST venomState venomExecSemantics list
  contextCodegenRel contextRawReachable

val _ = Parse.hide "body";

(* intcall_entry at H, plus:
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
Definition intcall_entry_full_def:
  intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name es sa sb
      vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn <=>
    intcall_entry H tops ctx func cenv cx tenv name es sa sb vv s0 es0
      (mut,nr,args,ret,ss,rr) prev penv rtv es1 t /\
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
      !callee setup use_trans nkeys imm_len lbl' ce params has_rb is_nr key
       trans view ctor imm_len' ss' rt.
        lookup_function lbl ctx.ctx_functions = SOME callee /\
        setup_callee callee argv t = SOME setup /\
        set_internal_package_target cenv.ce_target
          (package_internal_fn tops use_trans (nkeys : string -> num)
             cenv.ce_is_ctor imm_len
             (mut,nr,rr,name,args,([] : expr list),ret,ss)) =
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

(* intcall_callee_exit, and at an IntRet, with the ghost gt the callee
   ends with: the storage the callee leaves is well formed on H's domain;
   its storage, transient and immutables taint is in DF H's dead bytes, and
   the fixed region [0, lo) is tainted only where the immutables section
   is dead; it taints no byte in [lo, t's frontier) outside the call's own
   allocations (ids in [n,m)) that the caller's taint tn did not hold; and
   the return buffer rb, if any, holds the returned value whatever its
   tainted bytes hold. *)
Definition intcall_callee_exit_full_def:
  intcall_callee_exit_full (DF, lo) H func cenv cx mut nr rtv rc
      (rb:bytes32 option) (n:num) (m:num) (t:venom_state) (tn:taint) res
      (ee:evaluation_state) (gt : (string |-> num # num) # taint) r <=>
    intcall_callee_exit H func cenv cx mut nr rtv rc rb n m t res ee r /\
    !v ir s'.
      res = INL v /\ r = IntRet ir s' ==>
      (?ee'. unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),ee') /\
             storage_well_formed_on cx ee' (FST H)) /\
      stor_taint_ok_at (DF H) (SND gt) s' /\
      (!i. i < lo /\ i IN (SND gt).t_mem ==>
           imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo s'.vs_memory) i) /\
      (!i. lo <= i /\ i < t.vs_alloca_next /\ i IN (SND gt).t_mem /\
           (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
                          n <= aid /\ aid < m ==> i < off \/ off + asz <= i) ==>
           i IN tn.t_mem) /\
      (!p. rb = SOME p ==>
           !mem. mem_agree_outside (SND gt).t_mem s'.vs_memory mem ==>
                 val_in_memory rtv v (w2n p) mem)
End
