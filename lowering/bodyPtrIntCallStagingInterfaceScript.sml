(* Typed design probes only.  The quotations below are NOT theorems.
   No execution or existence claim is registered by elaborating them. *)
Theory bodyPtrIntCallStagingInterface
Ancestors
  bodyIntCallSeams bodyIntCallSource bodyPtrPreds bodyPtrDefs
  bodyPtrIntCallEntryContracts bodyPtrIntCallStagingFrame
  bodyPtrIntCallArgumentLayout bodyPtrIntCallWordStore
  bodyPtrIntCallArrayHeader bodyPtrIntCallConcreteFields
  bodyPtrIntCallStaticArrayCopy bodyPtrIntCallFixedCopy
  compileVyper exprLowering exprLoweringProps compileEnv
  fragGasPathPtr finite_map list pred_set

val staging_seam_interface = ``
  !tops ctx func cenv cx tenv ty ann name es dflt es0 sa sb vv s0
   mut nr args ret ss rr d PG G0 tn0 Q R.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args [] ret ss) tops /\
    (~MEM (NONE,name) cx.stk ==> body_exprs_ptr_ok cx es) /\
    compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa = (vv,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sa x) /\
    gas_admissible (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt))
      expr_vv_res_ok es0 /\
    stmt_state_rel ctx func cenv cx es0 s0 /\
    ghost_inv d cenv cx es0 G0 tn0 s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!res ee gt r. expr_exit res r ==> R res ee gt r) /\
    (!prev penv rtv es1 t G tn.
      intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
        (mut,nr,args,ret,ss,rr) prev penv rtv es1 t /\
      ghost_inv d cenv cx (es1 with scopes := prev) G tn t /\
      ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
      (!bb inst lbl arg_ops argv.
        lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb t.vs_inst_idx = SOME inst /\
        decode_invoke inst = SOME (lbl,arg_ops) /\
        eval_operands arg_ops t = SOME argv ==>
        EVERY (\op. op_taint tn op = {}) arg_ops /\
        EVERY (\op. !b n. op_prov G op = SOME (b,n) ==>
          (?aid. sa.cs_next_id <= aid /\
             FLOOKUP t.vs_allocas aid = SOME (b,n)) /\
          intcall_site_outside (intcall_protected cenv es0 sa s0) (b,n)) arg_ops /\
        !callee setup use_trans nkeys imm_len lbl' ce params has_rb is_nr key
         trans view ctor imm_len' ss' rt.
          lookup_function lbl ctx.ctx_functions = SOME callee /\
          setup_callee callee argv t = SOME setup /\
          set_internal_package_target cenv.ce_target
            (package_internal_fn tops use_trans (nkeys : string -> num)
               cenv.ce_is_ctor imm_len
               (mut,nr,rr,name,args,([] : expr list),ret,ss)) =
            (lbl',ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len',ss',rt) ==>
          intcall_entry_memory ce params penv (if has_rb then 1 else 0)
            (MAP (op_prov G) arg_ops) (tn with t_var := FEMPTY) setup /\
          intcall_entry_return ce has_rb
            (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE)
            (MAP (op_prov G) arg_ops) setup) ==>
      gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
        (intcall_rest cx name mut nr ss prev rtv) (es1,t,G,tn) Q R) ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt))
      (es0,s0,G0,tn0) Q R``;

(* A prefix consists of actual operands, their evaluated words, declared
   semantic types, source values and passing flags.  Return-site data is
   separate: it has capacity/provenance but no input value.  This quotation
   exposes the proposed invariant, not an assumption supplying its proof. *)
val staging_prefix_interface = ``
  !cenv cx d es0 sa s0 G0 tn0 sc ee s G tn ops ws tvs vs flags rb.
    ghost_inv d cenv cx ee G tn s /\
    ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
    s.vs_current_bb = sc.cs_current_bb /\
    s.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~s.vs_halted /\
    LENGTH ops = LENGTH ws /\ LENGTH ops = LENGTH tvs /\
    LENGTH ops = LENGTH vs /\ LENGTH ops = LENGTH flags /\
    eval_operands ops s = SOME ws /\
    EVERY (\op. op_taint tn op = {}) ops /\
    (!i. i < LENGTH ops ==>
      (!x. EL i ops = Var x ==> not_fresh_at sc x) /\
      value_has_type (EL i tvs) (EL i vs) /\
      if EL i flags then
        (!b m. mem_word_at b m = EL i ws ==>
          val_in_memory (EL i tvs) (EL i vs) b m)
      else ?b n aid.
        op_prov G (EL i ops) = SOME (b,n) /\
        sa.cs_next_id <= aid /\ aid < sc.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,n) /\
        b <= w2n (EL i ws) /\
        w2n (EL i ws) + type_memory_size (EL i tvs) <= b+n /\
        b+n <= s.vs_alloca_next /\
        intcall_site_outside (intcall_protected cenv es0 sa s0) (b,n) /\
        (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
          val_in_memory (EL i tvs) (EL i vs) (w2n (EL i ws)) m)) /\
    (!op cap. rb = SOME (op,cap) ==>
      op_taint tn op = {} /\
      (!x. op = Var x ==> not_fresh_at sc x) /\
      ?w b n aid. eval_operand op s = SOME w /\
        op_prov G op = SOME (b,n) /\
        sa.cs_next_id <= aid /\ aid < sc.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,n) /\
        b <= w2n w /\ w2n w + cap <= b+n /\ b+n <= s.vs_alloca_next /\
        intcall_site_outside (intcall_protected cenv es0 sa s0) (b,n))``;

(* Execution boundary for a single already-evaluated argument: allocation,
   unwrap and store remain in their actual compiler order.  Aggregate and
   bytestring stores must prove a counted path satisfying this post; this
   quotation deliberately does not assert that such a path exists. *)
val staging_memory_step_interface = ``
  !D ctx func PG ce cx ty vv sa sb src buf G tn s tv v
   e es0 ee raw se s0 d G0 tn0 stv dtv.
    stmt_state_rel ctx func ce cx ee s /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    local_ptrs_reserved ce sa /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sa x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sa x) /\
    vv_at ce cx (expr_type e) se sa ee raw vv s /\
    read_result cx raw ee = (INL v,ee) /\
    ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
    (!a op. vv = StackValue a op /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e op G s) /\
    (!a p. vv = LocatedValue a p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand G s) /\
    ghost_inv d ce cx ee G tn s /\
    ghost_kept ce es0 se G0 tn0 s0 G tn /\
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv /\
    evaluate_type (get_tenv cx) ty = SOME dtv /\ tv = dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    arg_type_fits (vv_type vv) ty /\
    type_memory_bytes ce ty = type_memory_size dtv /\
    s.vs_alloca_next + MAX 32 (type_memory_size dtv) + 64 < dimword (:256) /\
    FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
    (do buf <- compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty));
        src <- unwrap_value ce vv;
        (if is_word_type ty then emit_void MSTORE [buf.buf_operand;src]
         else if is_bytestring_type ty then
           do compile_store_bytestring src buf.buf_operand; comp_return () od
         else compile_store_memory ce src buf.buf_operand ty (vv_type vv));
        comp_return (src,buf) od) sa = ((src,buf),sb) ==>
    ?H tf z w b n.
      gas_path_ptr D 0 ctx func PG G tn s 0 H tf (OK z) /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      eval_operand buf.buf_operand z = SOME w /\
      op_prov H buf.buf_operand = SOME (b,n) /\
      op_taint tf buf.buf_operand = {} /\
      b <= w2n w /\ w2n w + type_memory_size tv <= b+n /\
      (!m. mem_agree_outside tf.t_mem z.vs_memory m ==>
        val_in_memory tv v (w2n w) m)``;

(* Empty-list continuation: no runtime instruction is inserted by the
   compiler, so every existing endpoint predicate is retained unchanged. *)
Theorem intcall_empty_stage_continuation[local]:
  compile_stage_intcall_args cfn ce [] flags tys sa = (ops,sb) /\
  P sa s G tn ==> ops = [] /\ P sb s G tn
Proof
  simp[compile_stage_intcall_args_def, comp_return_def] >> metis_tac[]
QED

(* Producer matrix / remaining proof obligations (not additional axioms):
 *
 * SOURCE TYPES: body_intcall_source_selection gives LIST_REL widening from
 * expr_type to the declared parameters; bind_arguments_lookup_index and
 * intcall_bound_argument_layout give the bound entry's semantic type and
 * declared slot size.  For a nested call the physical post_value_type can
 * differ from expr_type.  ifexp_intcall_copy_source and
 * ifexp_intcall_read_physical_typed expose that distinction.  Composing
 * these facts to arg_type_fits (vv_type vv) ty is STILL a proof obligation,
 * not a consequence of footprint <= capacity alone.
 *
 * ALLOCATION: assign_base_ptr_alloc_buffer_counted_path is the counted
 * runtime producer.  assign_base_ptr_alloc_buffer_counted_separated adds
 * separation.  intcall_separated_site_outside converts that to the fixed
 * original caller protected set.  Margin/headroom and freshness have to be
 * discharged from compiler/state relations.  No address-age lower bound is
 * used in the prefix invariant (allocation sites can be reused).
 *
 * STACK: unwrap_value must be composed with the argument's pointer IH.
 * Existing unwrap pointer lemmas cover particular located-value cases;
 * abiEncodeMaterialize.materialize_unwrap_owned_sim is a useful boundary,
 * not a wholesale generic stage theorem.  The final word's empty taint and
 * represented declared word are required before extending the prefix.
 *
 * WORD STORE: intcall_store_word_counted covers typed memory-to-word
 * copying, not the direct eager MSTORE with an already unwrapped scalar.
 * Direct MSTORE uses the scalar store path/encoding lemmas and the clean
 * unwrapped word.  The allocation precedes unwrap and must survive it.
 *
 * BYTESTRING: compile_store_bytestring_robust_gas_path_ptr in
 * bodyPtrIfExpBytesPost transports from physical to declared bytes/string
 * type, preserving robust representation and outside bytes/taint.  It
 * needs clean length-header and rounded-length coverage of BOTH buffers.
 * ptr_buf_ok supplies source capacity, not clean padding; the header and
 * rounding obligations remain to be derived from robust representation.
 *
 * AGGREGATE: intcall_static_array_fast_counted handles the equal-layout
 * ABI-static array fast path.  intcall_dynamic_array_header_counted handles
 * only the dynamic array HEADER prefix, not its element loop.
 * intcall_tuple_fields_conditional and intcall_struct_fields_conditional
 * retain child-copy callbacks.  Those callbacks and the dynamic/non-fast
 * array loop still require a recursive typed-copy proof.  This is missing
 * proof infrastructure, NOT evidence of an external omitted premise.
 *
 * FRAME: a subsequent expression's ghost_kept retains older nonlocal
 * sites; its concrete vv_post frame is also needed for robustness.
 * intcall_located_robust_confined_write is for a single confined write,
 * not by itself a theorem framing an arbitrary following expression.
 * Stability of prefix op evaluations and of provenance uses not_fresh_at.
 *
 * PACKAGING: use actual eval_operands and setup_callee to map the prefix
 * into intcall_entry_memory; return allocation has no input value and
 * instead maps into intcall_entry_return.  This file elaborates both
 * has_rb cases and the per-argument passing flag; it proves neither the
 * fold nor the final source-frame continuation.
 *)
