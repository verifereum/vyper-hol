(* Independent quotation/typechecking boundary for eager internal arguments. *)
Theory bodyPtrIntCallStageInterface
Ancestors
  exprLowering loweringPosts bodyPtrDefs exprSimHyps
  bodyPtrIntCallConfinement gasSummaryComposePtr vyperTypeSystem
  valueCopyBytes memoryLayoutDefs

(* Shared suffix proposition S (interface only; not a proof certificate).
!d ctx PG func cenv cx env e es sa a vv s0 ee tv s G tn Gi ti
 flag ty op b rty dtv P.
 compile_expr cenv (expr_type e) e sa = (vv,a) /\
 expr_body_pre cenv cx env e es /\
 vv_post ctx func cenv cx e es sa a s0 ee tv vv s /\
 ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
 ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es sa Gi ti s0 G tn /\
 stmt_state_rel ctx func cenv cx ee s /\
 (~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts) /\
 fn_has_code sa b func /\ fn_inst_ids_distinct func /\
 local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv a /\
 sa.cs_next_var <= a.cs_next_var /\ sa.cs_next_id <= a.cs_next_id /\
 MAP FDOM es.scopes = MAP FDOM ee.scopes /\
 ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
 (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x. vv_operand vv = Var x ==> not_fresh_at a x) /\
 (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
   ptr_buf_ok cenv e op0 G s) /\
 (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
   ptr_buf_ok cenv e p.ptr_operand G s) /\
 evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
 evaluate_type (get_tenv cx) ty = SOME dtv /\
 type_widens_to (get_tenv cx) (post_value_type cenv e) ty /\
 (!v. read_result cx tv ee = (INL v,ee) ==>
   value_has_type rty v /\ value_has_type dtv v /\
   val_wf rty v /\ val_wf dtv v) /\
 (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
   ~is_word_type (post_value_type cenv e) ==>
   type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
   type_memory_size rt < 2**64) /\
 type_memory_bytes cenv ty = type_memory_size dtv /\
 MAX 32 (type_memory_bytes cenv ty) < 2**64 /\
 acyclic_struct_metadata cenv.ce_struct_fields /\
 sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
 (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
   ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
     sz = type_memory_size rt) fields) /\
 P SUBSET intcall_protected cenv ee a s /\
 (if flag then unwrap_value cenv vv a = (op,b)
  else ?buf a1 src a2.
   compile_alloc_buffer (MAX 32 (type_memory_bytes cenv ty)) a = (buf,a1) /\
   unwrap_value cenv vv a1 = (src,a2) /\ op = buf.buf_operand /\
   (if is_word_type ty then emit_void MSTORE [op;src] a2 = ((),b)
    else if is_bytestring_type ty then
      comp_ignore_bind (compile_store_bytestring src op) (comp_return ()) a2 = ((),b)
    else compile_store_memory cenv src op ty (vv_type vv) a2 = ((),b))) ==>
 ?v H un z w.
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx tv)
    (ee,s,G,tn) [] (INL v) ee H un (OK z) /\
  z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = LENGTH b.cs_current_insts /\
  ~z.vs_halted /\ stmt_state_rel ctx func cenv cx ee z /\
  ghost_inv d cenv cx ee H un z /\ ghost_kept cenv es sa Gi ti s0 H un /\
  eval_operand op z = SOME w /\ op_taint un op = {} /\
  (if flag then
    expr_val_rel cx (post_value_type cenv e) v op z /\
    ptr_val_ok cx (post_value_type cenv e) v op H un z
   else ?base cap.
    cap = MAX 32 (type_memory_bytes cenv ty) /\ w = n2w base /\
    op_prov H op = SOME (base,cap) /\ base+cap < dimword(:256) /\
    FLOOKUP z.vs_allocas a.cs_next_id = SOME (base,cap) /\
    a.cs_next_id < b.cs_next_id /\ intcall_site_outside P (base,cap) /\
    (!m. mem_agree_outside un.t_mem z.vs_memory m ==>
      val_in_memory dtv v base m)) /\
  (!x. not_fresh_at a x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint un (Var x) = op_taint tn (Var x)) /\
  (!aid site. aid < a.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME site ==>
    FLOOKUP z.vs_allocas aid = SOME site) /\
  (!ft fv p base cap.
    val_wf ft fv /\ base <= p /\ p+type_memory_size ft <= base+cap /\
    ((?aid. aid < a.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (base,cap)) \/
     (?name. local_region cenv ee.scopes s name base cap)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ft fv p m) ==>
    !m. mem_agree_outside un.t_mem z.vs_memory m ==> val_in_memory ft fv p m)
*)

(* Premise map for S (interface delivery, not a proof of S).

   Call-site convention: sa/s0/Gi/ti precede the head expression; a/s/G/tn
   are its NORMAL expr_vv_sim_ptr endpoint; ee/tv are its source endpoint.
   The list caller retains the actual marked eval_expr prefix.  It must not
   choose a different endpoint from an erased S1 existential.  The suffix
   starts with read_result cx tv, not eval_expr and not an identity source.

   Inputs, in order of the conjuncts in S:
   - compile_expr and expr_body_pre are the head compiler equation and head
     typing/safety hypothesis of the list induction.  The literal ty in
     compile_expr is expr_type e, NOT the destination parameter type.
   - vv_post, ptr_vv_ok, ghost_inv, both ptr_buf_ok clauses and ghost_kept
     are exactly the normal continuation fields of expr_vv_sim_ptr_def.
     stmt_state_rel follows from vv_post_def.  The cursor equalities are
     that same continuation's cursor fields; its nonhalt follows from
     vv_post/state_rel (the expression normal endpoint).
   - fn_has_code sa b func is the enclosing stage-code hypothesis.  Split
     it at the compiler endpoints, using the compiler prefix equations.
     Distinct ids, no dynamic alloca, not ctor, and reserved return buf/pc
     are unchanged enclosing expr_vv_sim_ptr invocation hypotheses.
     local_ptrs_reserved at a follows from its monotonic next_var lemma;
     next_var/next_id monotonicity and operand freshness are compile_expr
     properties.  MAP FDOM equality follows from vv_post's locals_kept.
   - rty is a SOURCE witness at post_value_type; dtv is a DESTINATION
     witness at the parameter type ty.  They need not be equal.  For the
     ordinary post=annotation case, memory_rhs_read_annotation_typed gives
     value_runtime_typed from the successful composed eval_expr/read_result
     prefix.  Unfold value_runtime_typed for the evaluation witness and
     value_has_type.  For an aggregate internal call at a narrower physical
     post type use ifexp_intcall_read_physical_typed instead.  The successful
     prefix comes from the retained head path composed with the read, and
     is not an extra universal assumption about all source values.
     value_has_type_val_wf supplies val_wf.  Destination evaluation and
     annotation-to-destination widening are the bound-parameter typing
     facts. post_value_type_widens followed by type_widens_to transitivity
     gives post-to-destination widening; type_widens_to_value_has_type gives
     destination value_has_type, then value_has_type_val_wf gives its wf.
     The universal read implication in S is the continuation form of these
     facts; deterministic reads identify its v with the prefix's value.
   - Both memory-layout equalities are expr_sim_inv_memory_size.  The
     destination <2**64 bound is the bound parameter's fn_allocs_ok fact,
     via body_inv_internal_subst_allocs_ok and fn_allocs_ok_body (with the
     callee layout agreement), not merely a <dimword bound.  MAX 32 keeps
     it <2**64.  For nonword source, type_widens_to_def and
     arg_type_fits_memory_bytes_mono bound its bytes by destination bytes;
     reflexive widening is immediate.  Hence the conditional source bound.
   - sfields_tenv_consistent and the field distinctness/size clauses are
     literal expr_sim_inv_def conjuncts.  Acyclicity is an enclosing body
     compile-environment construction obligation, NOT a consequence of
     vv_holds or of expr_vv_sim_ptr. It is a literal body_inv_def conjunct
     (as used in bodySimStmtCases). StageSeam retains body_inv for the
     caller compile environment when instantiating S.
   - P is chosen by the list invariant as a subset of the protected set
     at this head endpoint.  The conditional compiler equation is precisely
     the eager staging head suffix.  It allocates at a, unwraps at a1 and
     stores at a2; none of these endpoints is silently identified with a.

   Producer-only annotation boundary proposed for C1.3.1 (NOT proved here):
   !ce aty e si vv sj.
     compile_expr ce aty e si = (vv,sj) ==>
     vv_type vv =
       (case e of Call ann (IntCall fid) args drv =>
          ce.ce_func_return_type (nsid_to_string fid)
        | _ => expr_type e)
   Concrete argument: unfold compile_expr_body once; ret_ty=expr_type e.
   Literal/name/subscript/attribute wrappers return at ret_ty; IfExp's
   StackValue and LocatedValue alternatives, StructLit, Pop, FlagMember,
   TopLevelName all explicitly retain ret_ty.  The specialized names
   AddMod/MulMod/PowMod paths take ret_ty.  Builtin/type-builtin dispatch
   wrappers likewise return at ret_ty.  In compile_call, IntCall alone
   uses call_ty=ce.ce_func_return_type; other call targets retain ret_ty.
   This is compiler output annotation, independent of runtime vv_holds.
   The proof is finite constructor/dispatch case analysis, not a new
   semantic invariant or an annotation certificate demanded of StageList.

   Branch map for using S's inputs in its producer proof:
   1. flag=T: no destination exists.  StackValue unwrap is the existing
      stack_unwrap_counted; LocatedValue is dispatched by location and
      wordness using the marked read toolkit.  For non-memory locations
      intcall_stage_source_shape supplies lowered=annotation at a.  For
      memory word reads use the typed word marked read; for memory nonword
      reads unwrap is identity on the operand.  ptr_vv_ok is at POST type
      in every case.  Nonword StackValue annotation is not inferred from
      vv_holds.  The compiler boundary above supplies it where needed.
      Result is the flag=T ptr_val_ok/expr_val_rel at post_value_type.
   2. flag=F, common allocation: compile_alloc_buffer supplies a fresh
      Var destination and whole allocation site (base,MAX 32 bytes).
      ghost_inv bounds its end strictly below dimword; ALLOCA preserves
      old registers and sites. intcall_stage_alloc_vv_post transports the
      source post from a to a1. Transport ptr_vv_ok/ptr_buf_ok and ghost
      facts as well; unwrap the ORIGINAL vv at a1, never recompile at a1.
      Old source allocation sites and locals are disjoint from this NEW
      whole site, giving both copy separation and intcall_site_outside P.
   3. Word destination: post-to-destination widening makes source a word
      of the same type (type constructor cases/type_widens_to_def).
      StackValue has no read instruction; LocatedValue uses the marked
      word read for its location.  ptr_val_ok after reading supplies clean
      source data.  One MSTORE into the fresh >=32-byte site writes a clean
      word. value_has_type dtv v and its word encoding yield the robust
      destination representation; the store's taint update is confined to
      the new site, so old robust values and ghost_kept survive.
   4. Bytestring destination: widening forces a bytestring source of the
      same kind.  LocatedValue memory uses its ptr_buf_ok site and robust
      source; storage/code sources use their existing marked materializing
      reads. StackValue uses stack_unwrap_counted with ptr_vv_ok's robust
      source. The value typing splits v into BytesV/StringV and gives the
      length bounds. robust_bytestring_header yields the untainted header
      and n=32+32*((len+31) DIV 32); source and fresh destination capacities
      cover n. compile_store_bytestring_robust_gas_path_ptr supplies the
      counted path, robust dtv destination and exterior representation
      frame. No vv_type typing hypothesis is needed for this store.
   5. Aggregate destination: return_source_word_widens_eq excludes word
      source; type_widens_from_bytestring excludes bytestring source.
      Thus post is the annotation except for IntCall, where it is the
      declared call type. For LocatedValue the annotation follows also
      from vv_holds' non-bytestring case. For StackValue it follows ONLY
      from the proposed compiler boundary above. In BOTH cases set the
      canonical store's sty=post_value_type cenv e and stv=rty, rewriting
      vv_type vv by this equality. This resolves the StackValue annotation
      issue without adding unconditional vv_type evaluation/widening to S.
      After the marked unwrap, ptr_val_ok supplies robust val_in_memory;
      ptr_buf_ok supplies whole-site capacity/provenance. Fresh allocation
      gives destination Var, clean operand, ptr_covers and source/dest
      separation. Size/layout/widening/typing/metadata are mapped above.
      Apply compile_store_memory_aggregate_counted_ptr, whose typed branch
      uses widened_assign_typed_store_counted_ptr. No local typed-copy
      implementation is proposed. Its typed_copy_state_frame and taint
      exterior clauses preserve old sites, ghost_kept, and robust values.

   This delivery freezes literal S for the conditional list interface.
   It certifies syntax and a proposed premise derivation, not the suffix
   theorem, annotation boundary, or any counted execution proof. C1.3.1
   owns those proofs; StageSeam owns the enclosing construction obligations.
*)

(* Parse/typecheck the shared proposition only: this creates no HOL constant
   and claims no theorem. Keep the comment above synchronized with this check. *)
val _ = if type_of ``
!d ctx PG func cenv cx env e es sa a vv s0 ee tv s G tn Gi ti
 flag ty op b rty dtv P.
 compile_expr cenv (expr_type e) e sa = (vv,a) /\
 expr_body_pre cenv cx env e es /\
 vv_post ctx func cenv cx e es sa a s0 ee tv vv s /\
 ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
 ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es sa Gi ti s0 G tn /\
 stmt_state_rel ctx func cenv cx ee s /\
 (~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts) /\
 fn_has_code sa b func /\ fn_inst_ids_distinct func /\
 local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv a /\
 sa.cs_next_var <= a.cs_next_var /\ sa.cs_next_id <= a.cs_next_id /\
 MAP FDOM es.scopes = MAP FDOM ee.scopes /\
 ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
 (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x. vv_operand vv = Var x ==> not_fresh_at a x) /\
 (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
   ptr_buf_ok cenv e op0 G s) /\
 (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
   ptr_buf_ok cenv e p.ptr_operand G s) /\
 evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
 evaluate_type (get_tenv cx) ty = SOME dtv /\
 type_widens_to (get_tenv cx) (post_value_type cenv e) ty /\
 (!v. read_result cx tv ee = (INL v,ee) ==>
   value_has_type rty v /\ value_has_type dtv v /\
   val_wf rty v /\ val_wf dtv v) /\
 (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
   ~is_word_type (post_value_type cenv e) ==>
   type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
   type_memory_size rt < 2**64) /\
 type_memory_bytes cenv ty = type_memory_size dtv /\
 MAX 32 (type_memory_bytes cenv ty) < 2**64 /\
 acyclic_struct_metadata cenv.ce_struct_fields /\
 sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
 (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
   ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
     sz = type_memory_size rt) fields) /\
 P SUBSET intcall_protected cenv ee a s /\
 (if flag then unwrap_value cenv vv a = (op,b)
  else ?buf a1 src a2.
   compile_alloc_buffer (MAX 32 (type_memory_bytes cenv ty)) a = (buf,a1) /\
   unwrap_value cenv vv a1 = (src,a2) /\ op = buf.buf_operand /\
   (if is_word_type ty then emit_void MSTORE [op;src] a2 = ((),b)
    else if is_bytestring_type ty then
      comp_ignore_bind (compile_store_bytestring src op) (comp_return ()) a2 = ((),b)
    else compile_store_memory cenv src op ty (vv_type vv) a2 = ((),b))) ==>
 ?v H un z w.
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx tv)
    (ee,s,G,tn) [] (INL v) ee H un (OK z) /\
  z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = LENGTH b.cs_current_insts /\
  ~z.vs_halted /\ stmt_state_rel ctx func cenv cx ee z /\
  ghost_inv d cenv cx ee H un z /\ ghost_kept cenv es sa Gi ti s0 H un /\
  eval_operand op z = SOME w /\ op_taint un op = {} /\
  (if flag then
    expr_val_rel cx (post_value_type cenv e) v op z /\
    ptr_val_ok cx (post_value_type cenv e) v op H un z
   else ?base cap.
    cap = MAX 32 (type_memory_bytes cenv ty) /\ w = n2w base /\
    op_prov H op = SOME (base,cap) /\ base+cap < dimword(:256) /\
    FLOOKUP z.vs_allocas a.cs_next_id = SOME (base,cap) /\
    a.cs_next_id < b.cs_next_id /\ intcall_site_outside P (base,cap) /\
    (!m. mem_agree_outside un.t_mem z.vs_memory m ==>
      val_in_memory dtv v base m)) /\
  (!x. not_fresh_at a x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint un (Var x) = op_taint tn (Var x)) /\
  (!aid site. aid < a.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME site ==>
    FLOOKUP z.vs_allocas aid = SOME site) /\
  (!ft fv p base cap.
    val_wf ft fv /\ base <= p /\ p+type_memory_size ft <= base+cap /\
    ((?aid. aid < a.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (base,cap)) \/
     (?name. local_region cenv ee.scopes s name base cap)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ft fv p m) ==>
    !m. mem_agree_outside un.t_mem z.vs_memory m ==> val_in_memory ft fv p m)
`` = bool then () else raise Fail "suffix interface is not boolean";
