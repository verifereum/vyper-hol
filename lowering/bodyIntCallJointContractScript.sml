(* The contract of the joint reachable induction over an internal callee's
   body (seam 2, intcall_callee_body_sim): the usual simulation carried
   together with a resource invariant, I below.  DRAFT: definitions and
   frozen leaf statements only; every leaf is cheated.

   TOP-LEVEL definitions:
   - intcall_frame: the parameters fixed for one callee body;
   - intcall_frame_ok: the fixed spatial, graph and return hypotheses;
   - intcall_joint_res: the resource conjunction I(ce,env,es,sa,s);
   - intcall_expr_cont: I and the frame clauses at an expression endpoint;
   - intcall_expr_producer, intcall_forced_producer, intcall_map_producer:
     value, forced-value (lower_value) and mapping-place producers;
   - intcall_stmt_exit, intcall_stmts_producer: the statement-list producer
     and its exit post (a single statement is the list [st]).
   Leaves (cheated): L-agg intcall_aggregate_producer_step, L-pure
   intcall_pure_producer_step, L-call intcall_effect_producer_step,
   L-force intcall_forced_producer_from_value, L-stmt
   intcall_stmt_producer_step, L-ind intcall_joint_producers (the
   induction assembling the other five).  The seam itself is proved from
   L-ind. *)

Theory bodyIntCallJointContract
Ancestors
  bodySim stmtSimReturn exprSimMapDefs intCallFrame intCallCallee
  fragGasFocus vyperTypeCallGraphSoundness supportedExprs bodyIntCallWindowForcing
Libs
  monadsyntax

(* ===== Fixed parameters ===== *)

(* Fixed for one callee body, as E0014 section 1 lists them: the program,
   the Venom context and the function being run, the pushed source context,
   the call graph (edges, owner = HD cx.stk, ancestors), the alloca
   frontier lo at the INVOKE, the caller's staged allocations, the
   protected windows P below lo, the memory origin (the caller's INVOKE
   state t) and the operand origin (the prologue landing), the root
   compile env, the source return type and its value type, the return-PC
   operand and its word, the return buffer (word, capacity) and the
   reserved operands. *)
Datatype:
  intcall_frame = <|
    jc_tops : toplevel list;
    jc_ctx : venom_context;
    jc_func : ir_function;
    jc_cx : evaluation_context;
    jc_edges : ((num option # identifier) # (num option # identifier)) list;
    jc_owner : num option # identifier;
    jc_ancestors : (num option # identifier) list;
    jc_lo : num;
    jc_staged : num -> num -> bool;
    jc_prot : num -> num -> bool;
    jc_morig : venom_state;
    jc_oorig : venom_state;
    jc_root_ce : compile_env;
    jc_ret_ty : type;
    jc_ret_tv : type_value;
    jc_rpc : operand;
    jc_pc : bytes32;
    jc_rb : (bytes32 # num) option;
    jc_reserved : operand -> bool
  |>
End

(* The hypotheses on the fixed parameters alone: P lies below lo and clear
   of every staged allocation; the graph witnesses of call_evaluation_safe
   for owner; the return PC, the root return buffer's pointer and the
   immutable base are reserved, and the return PC holds pc at the operand
   origin; the return buffer's capacity is the return value's size and P
   misses it; the source return type evaluates to ret_tv. *)
Definition intcall_frame_ok_def:
  intcall_frame_ok fp <=>
    (!a k. fp.jc_prot a k ==> a + k <= fp.jc_lo) /\
    (!b z. fp.jc_staged b z ==>
           !a k. fp.jc_prot a k ==> regions_disjoint a k b z) /\
    fp.jc_cx.stk = fp.jc_owner :: fp.jc_ancestors /\
    call_stack_follows (call_edge_rel fp.jc_edges) fp.jc_cx.stk /\
    irreflexive (TC (call_edge_rel fp.jc_edges)) /\
    functions_follow_call_graph fp.jc_edges fp.jc_cx /\
    evaluate_type (get_tenv fp.jc_cx) fp.jc_ret_ty = SOME fp.jc_ret_tv /\
    fp.jc_reserved fp.jc_rpc /\
    eval_operand fp.jc_rpc fp.jc_oorig = SOME fp.jc_pc /\
    (!x sz. fp.jc_root_ce.ce_return_buf = SOME (PtrVar x sz) ==>
            fp.jc_reserved x) /\
    (!x. fp.jc_root_ce.ce_imm_alloca = SOME x ==> fp.jc_reserved x) /\
    (!bw cap. fp.jc_rb = SOME (bw,cap) ==>
       cap = type_memory_size fp.jc_ret_tv /\
       !a k. fp.jc_prot a k ==> regions_disjoint a k (w2n bw) cap)
End

(* ===== The resource conjunction I ===== *)

(* I(ce,env,es,sa,s) of E0014 section 1, at the current compile env,
   typing, source state, compile state and Venom state.  The write-region
   authorization W(p,k) is written out: lo <= p, or [p,p+k) inside a staged
   allocation.  fresh_vars_wrt is E0076's addition (forcing needs it). *)
Definition intcall_joint_res_def:
  intcall_joint_res fp ce env es sa s <=>
    stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
    expr_sim_inv ce fp.jc_cx env es /\
    ce_locals_declared ce env /\ locals_alloc_ok ce env /\
    local_ptrs_reserved ce sa /\ fresh_vars_wrt sa s /\
    allocas_above fp.jc_lo s /\
    (!a k. fp.jc_prot a k ==>
           mem_bytes_at a k s.vs_memory = mem_bytes_at a k fp.jc_morig.vs_memory) /\
    (!op. fp.jc_reserved op ==> eval_operand op s = eval_operand op fp.jc_oorig) /\
    (!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at sa x) /\
    (!n p k. local_region ce es.scopes s n p k ==>
             fp.jc_lo <= p \/
             ?b z. fp.jc_staged b z /\ b <= p /\ p + k <= b + z) /\
    eval_operand fp.jc_rpc s = SOME fp.jc_pc /\
    ret_pc_ok ce sa s /\ return_buf_frame fp.jc_rb ce sa s /\
    same_frame fp.jc_root_ce ce /\
    (!bw cap. fp.jc_rb = SOME (bw,cap) /\ ce.ce_is_ctor ==>
       !nm tv iv io.
         FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
         FLOOKUP (case ALOOKUP es.immutables fp.jc_cx.txn.target of
                    NONE => FEMPTY
                  | SOME imms => get_source_immutables ce.ce_module imms) nm =
           SOME (tv,iv) ==>
         regions_disjoint io (type_memory_size tv) (w2n bw) cap)
End

(* At an expression's normal endpoint u (source state ee, compile state
   sb), from its entry s (source es, compile sa): I again, the position,
   old variables and allocations kept, the frontier monotone, and every
   allocation made before sa and clear of the live locals untouched (the
   frame vv_post and expr_post carry).  The last clause is how an
   aggregate's initialized prefix above lo survives its later children
   (E0076's Protected = P or prefix). *)
Definition intcall_expr_cont_def:
  intcall_expr_cont fp ce env es sa s ee sb u <=>
    intcall_joint_res fp ce env ee sb u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
           lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
             FLOOKUP u.vs_allocas aid = SOME b) /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    (!aid off sz.
       FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region ce es.scopes s n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz s.vs_memory)
End

(* ===== Expression producers ===== *)

(* Value producer: compile_expr against eval_expr.  The value holds at
   post_value_type (vv_post's type, not the compile type ty); its operand
   was handed out before sb; a memory value of a non-word, non-bytestring
   type lies in a slot [a,a+k) that W authorizes (what
   protected_value_forcing asks of its input). *)
Definition intcall_expr_producer_def:
  intcall_expr_producer fp e <=>
    !ce env es sa sb s ty vv.
      intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
      expr_body_pre ce fp.jc_cx env e es /\
      supportedExprs$supported_expr fp.jc_tops e /\
      calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
      compile_expr ce ty e sa = (vv,sb) /\
      fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
      gas_admissible (eval_expr fp.jc_cx e) expr_vv_res_ok es /\
      intcall_joint_res fp ce env es sa s /\ ~s.vs_halted /\
      s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
        (eval_expr fp.jc_cx e) (es,s)
        (\res ee u. ?tv. res = INL tv /\
           vv_holds ce fp.jc_cx (post_value_type ce e) tv vv ee u /\
           (~expr_has_effect e ==> vv_storage_live fp.jc_cx vv ee u) /\
           (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
           (~is_word_type (post_value_type ce e) /\
            ~is_bytestring_type (post_value_type ce e) /\
            (case vv of StackValue _ _ => T
                      | LocatedValue _ p => p.ptr_location = LocMemory) ==>
            !tv'. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) =
                    SOME tv' ==>
              ?w a k. eval_operand (vv_operand vv) u = SOME w /\
                a <= w2n w /\ w2n w + type_memory_size tv' <= a + k /\
                a + k < dimword (:256) /\
                (fp.jc_lo <= a \/
                 ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) /\
           intcall_expr_cont fp ce env es sa s ee sb u)
        (\res ee r. expr_exit res r)
End

(* Forced-value producer: lower_value against eval_expr then read_result,
   the operand related at post_value_type. *)
Definition intcall_forced_producer_def:
  intcall_forced_producer fp e <=>
    !ce env es sa sb s ty op.
      intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
      expr_body_pre ce fp.jc_cx env e es /\
      supportedExprs$supported_expr fp.jc_tops e /\
      calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
      lower_value compile_expr ce ty e sa = (op,sb) /\
      fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
      gas_admissible (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
        expr_res_ok es /\
      intcall_joint_res fp ce env es sa s /\ ~s.vs_halted /\
      s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
        (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) (es,s)
        (\res ee u. ?v. res = INL v /\
           expr_val_rel fp.jc_cx (post_value_type ce e) v op u /\
           (!x. op = Var x ==> not_fresh_at sb x) /\
           (~is_word_type (post_value_type ce e) /\
            ~is_bytestring_type (post_value_type ce e) ==>
            !tv'. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) =
                    SOME tv' ==>
              ?w a k. eval_operand op u = SOME w /\
                a <= w2n w /\ w2n w + type_memory_size tv' <= a + k /\
                a + k < dimword (:256) /\
                (fp.jc_lo <= a \/
                 ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) /\
           intcall_expr_cont fp ce env es sa s ee sb u)
        (\res ee r. expr_exit res r)
End

(* Mapping-place producer: an expression naming a mapping
   (expr_map_pre, not well_typed_expr), with expr_map_sim's certificate. *)
Definition intcall_map_producer_def:
  intcall_map_producer fp e <=>
    !ce env es sa sb s ty vv.
      intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
      expr_map_pre ce fp.jc_cx env e es /\
      supported_place_expr fp.jc_tops e /\
      calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
      compile_expr ce ty e sa = (vv,sb) /\
      fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
      gas_admissible (eval_expr fp.jc_cx e) expr_map_res_ok es /\
      intcall_joint_res fp ce env es sa s /\ ~s.vs_halted /\
      s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
        (eval_expr fp.jc_cx e) (es,s)
        (\res ee u. ?tr slot kt vt tp p.
           res = INL (HashMapRef tr slot kt vt) /\
           storage_mapping_region fp.jc_cx tr slot (HashMapT kt vt) /\
           vv = LocatedValue tp p /\ p.ptr_location = slot_loc tr /\
           eval_operand p.ptr_operand u = SOME slot /\
           intcall_expr_cont fp ce env es sa s ee sb u)
        (\res ee r. expr_exit res r)
End

(* ===== Statement producer ===== *)

(* How a statement list leaves the body: an abort expr_exit allows, or a
   return: an IntRet related at the root env (intret_q: state_rel with the
   scopes cleared, intret_vals_match, no adopted fmp) with the declared
   number of stack values, P and the reserved operands at their origins,
   and in memory mode the value in the return buffer. *)
Definition intcall_stmt_exit_def:
  intcall_stmt_exit fp (res : unit + exception) (ee : evaluation_state) r <=>
    expr_exit res r \/
    ?v ir u.
      res = INR (ReturnException v) /\ r = IntRet ir u /\
      intret_q fp.jc_func fp.jc_root_ce fp.jc_cx fp.jc_ret_tv v
        (ee with scopes := []) r /\
      LENGTH ir.iret_values = fp.jc_root_ce.ce_returns_count /\
      (!a k. fp.jc_prot a k ==>
             mem_bytes_at a k u.vs_memory = mem_bytes_at a k fp.jc_morig.vs_memory) /\
      (!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op fp.jc_oorig) /\
      (!bw cap. fp.jc_rb = SOME (bw,cap) ==>
                val_in_memory fp.jc_ret_tv v (w2n bw) u.vs_memory)
End

(* Statement-list producer.  Typed at the source return type, compiled at
   the body's compile type (BoolT for a void function, as
   compile_internal_function does), with a second typing at
   bare_global_assignable = FEMPTY for no-immutable-write reasoning.  The
   normal post is stmt_post's, with its compile env ce'' shared with I and
   a post typing env'' (env' on normal completion), and a monotone
   frontier. *)
Definition intcall_stmts_producer_def:
  intcall_stmts_producer fp ss <=>
    !bindings ce ce' env env' lctx es sa sb s.
      intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
      supported_stmts fp.jc_tops bindings ss /\
      (!target. supported_stmts_expr_exists
         (expr_abi_decode_target_root target) ss ==>
         occurs_abi_decode_target target fp.jc_tops) /\
      type_stmts env fp.jc_ret_ty ss = SOME env' /\
      IS_SOME (type_stmts (env with bare_global_assignable := FEMPTY)
                 fp.jc_ret_ty ss) /\
      EVERY (stmt_exprs_ok ce) ss /\
      calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_stmts ss) /\
      stmts_env ce lctx
        (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty) ss sa =
        (ce',sb) /\
      fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
      ~block_is_terminated sa /\
      gas_admissible (eval_stmts fp.jc_cx ss) (stmt_res_ok lctx) es /\
      intcall_joint_res fp ce env es sa s /\ ~s.vs_halted /\
      s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
        (eval_stmts fp.jc_cx ss) (es,s)
        (\res ee u. ?ce'' env''.
           stmt_lands lctx sb res u /\ ~u.vs_halted /\
           (res = INL () ==>
              ~block_is_terminated sb /\ ce'' = ce' /\ env'' = env') /\
           cenv_top_ext ce ce'' ee.scopes /\
           intcall_joint_res fp ce'' env'' ee sb u /\
           (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
                  lookup_var x u = SOME w) /\
           (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                    FLOOKUP u.vs_allocas aid = SOME b) /\
           s.vs_alloca_next <= u.vs_alloca_next)
        (intcall_stmt_exit fp)
End

(* ===== Leaves (frozen statements, cheated) ===== *)

(* L-agg (C1.3.14.2.3), a step of the induction on expr_size: tuple
   literals (MakeArray NONE), array literals (MakeArray (SOME _)), struct
   literals, attributes and subscripts (every place_type case: tuple and
   struct literal-index, ValPT array, MapPT), given the producers of every
   smaller expression. *)
Theorem intcall_aggregate_producer_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  ((?a t n args. e = Builtin a (MakeArray t n) args) \/
   (?a nm fields. e = StructLit a nm fields) \/
   (?a base fld. e = Attribute a base fld) \/
   (?a base idx. e = Subscript a base idx)) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED

(* L-pure (C1.3.14.3), the same step for every other non-call form: names,
   literals, top-level names, flag members, ternaries, the other builtins
   and type builtins.  Children that are internal calls are covered by the
   smaller-expression premise (supported_pure_expr admits none). *)
Theorem intcall_pure_producer_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  ~(?a t n args. e = Builtin a (MakeArray t n) args) /\
  ~(?a nm fields. e = StructLit a nm fields) /\
  ~(?a base fld. e = Attribute a base fld) /\
  ~(?a base idx. e = Subscript a base idx) /\
  ~(?a tgt args dflt. e = Call a tgt args dflt) /\
  ~(?a tgt. e = Pop a tgt) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED

(* L-call (C1.3.15): calls (internal, external, send) and pops, given the
   smaller expressions' producers and, by call-graph descent
   (callable_graph_descent), the statement producer of every frame whose
   owner has fewer call descendants under the same edges. *)
Theorem intcall_effect_producer_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (!fp' ss.
     fp'.jc_edges = fp.jc_edges /\
     CARD {z | TC (call_edge_rel fp.jc_edges) fp'.jc_owner z} <
     CARD {z | TC (call_edge_rel fp.jc_edges) fp.jc_owner z} ==>
     intcall_stmts_producer fp' ss) /\
  ((?a tgt args dflt. e = Call a tgt args dflt) \/ (?a tgt. e = Pop a tgt)) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED

(* L-force: the forced-value sibling of any expression from its value
   producer, by protected_value_forcing at the value's endpoint. *)
Theorem intcall_forced_producer_from_value:
  intcall_expr_producer fp e ==> intcall_forced_producer fp e
Proof
  cheat
QED

(* L-stmt (C1.3.16): a single statement (the list [st]) of any form, given
   the producers of every expression and of every smaller statement list
   (If and For bodies), and a list from its statements. *)
Theorem intcall_stmt_producer_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) ==>
  (!st. (!ss. list_size stmt_size ss < stmt_size st ==>
              intcall_stmts_producer fp ss) ==>
        intcall_stmts_producer fp [st]) /\
  (!ss. (!st. MEM st ss ==> intcall_stmts_producer fp [st]) ==>
        intcall_stmts_producer fp ss)
Proof
  cheat
QED

(* L-ind: the induction, on the owner's call-descendant count, then on
   expr_size and stmt_size, from the five steps above.  The seam
   intcall_callee_body_sim (bodyIntCallSeams) is proved from it: its proof
   initializes I at the prologue landing, applies this, and turns
   intcall_stmt_exit into intcall_callee_exit. *)
Theorem stmt_size_le_list_size[local]:
  !ss st. MEM st ss ==> stmt_size st <= list_size stmt_size ss
Proof
  Induct >> rw[] >> res_tac >> simp[]
QED

Theorem intcall_joint_producers_count[local]:
  !n fp. CARD {z | TC (call_edge_rel fp.jc_edges) fp.jc_owner z} = n ==>
    (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
         intcall_map_producer fp e) /\
    !ss. intcall_stmts_producer fp ss
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  `!fp' ss. fp'.jc_edges = fp.jc_edges /\
     CARD {z | TC (call_edge_rel fp.jc_edges) fp'.jc_owner z} <
     CARD {z | TC (call_edge_rel fp.jc_edges) fp.jc_owner z} ==>
     intcall_stmts_producer fp' ss` by (
    rpt strip_tac >>
    first_x_assum (qspec_then
      `CARD {z | TC (call_edge_rel fp.jc_edges) fp'.jc_owner z}` mp_tac) >>
    impl_tac >- gvs[] >>
    disch_then (qspec_then `fp'` mp_tac) >> gvs[]) >>
  `!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e` by (
    measureInduct_on `expr_size e` >>
    `intcall_expr_producer fp e /\ intcall_map_producer fp e` by (
      Cases_on `(?a t n args. e = Builtin a (MakeArray t n) args) \/
                (?a nm fields. e = StructLit a nm fields) \/
                (?a base fld. e = Attribute a base fld) \/
                (?a base idx. e = Subscript a base idx)`
      >- (irule intcall_aggregate_producer_step >> fs[]) >>
      Cases_on `(?a tgt args dflt. e = Call a tgt args dflt) \/
                (?a tgt. e = Pop a tgt)`
      >- (irule intcall_effect_producer_step >> fs[]) >>
      irule intcall_pure_producer_step >> fs[]) >>
    simp[] >> irule intcall_forced_producer_from_value >> simp[]) >>
  `!ss. (!st. MEM st ss ==> intcall_stmts_producer fp [st]) ==>
        intcall_stmts_producer fp ss` by
    metis_tac[intcall_stmt_producer_step] >>
  `!st. intcall_stmts_producer fp [st]` by (
    measureInduct_on `stmt_size st` >>
    mp_tac intcall_stmt_producer_step >> impl_tac >- simp[] >>
    strip_tac >> first_x_assum irule >> rpt strip_tac >>
    first_x_assum irule >> rpt strip_tac >>
    first_x_assum irule >>
    drule stmt_size_le_list_size >> simp[]) >>
  simp[]
QED

Theorem intcall_joint_producers:
  !fp ss. intcall_stmts_producer fp ss
Proof
  metis_tac[intcall_joint_producers_count]
QED
