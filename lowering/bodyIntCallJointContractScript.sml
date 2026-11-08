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
   intcall_stmt_producer_step, L-asm intcall_callee_body_joint.
   intcall_joint_producers is the induction assembling the first five. *)

Theory bodyIntCallJointContract
Ancestors
  bodySim stmtSimReturn exprSimMapDefs intCallFrame intCallCallee
  fragGasFocus vyperTypeCallGraphSoundness supportedExprs
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

(* The induction, not a leaf: on the owner's call-descendant count, then
   on expr_size and stmt_size, from the five steps above. *)
Theorem intcall_joint_producers:
  !fp ss. intcall_stmts_producer fp ss
Proof
  cheat
QED

(* L-asm (C1.3.10/C1.3.11 and C1.4): intcall_callee_body_sim with
   intcall_entry, cenv_module_pins, intcall_rest, intcall_callee_src and
   intcall_callee_exit unfolded (bodyIntCallSeams is not an ancestor) and
   without its body_stmts_ok premise, which the joint induction replaces.
   Its proof initializes I at the prologue landing, uses
   intcall_joint_producers, and turns intcall_stmt_exit into the exit. *)
Theorem intcall_callee_body_joint:
  !tops ctx func cenv cx tenv name es sa sb vv s0 es0 mut args ret ss rr
   prev penv rtv es1 t callee entered rc rbs pvs.
    body_inv tops ctx cenv cx /\
    (cenv.ce_module = NONE /\
     cenv.ce_module_var_type = build_var_type_map tops /\
     cenv.ce_module_vars =
       add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
         tops 0 (add_module_var_locations tops FEMPTY) /\
     cenv.ce_flag_member_id = FST (build_flag_info tops (K (K 0)) (K 0)) /\
     cenv.ce_flag_n_members = SND (build_flag_info tops (K (K 0)) (K 0)) /\
     cenv.ce_method_id =
       (\s tys. w2n (calldata_method_id
                      (function_selector s (vyper_to_abi_types (type_env tops) tys))))) /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,F,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
    (~MEM (NONE,name) cx.stk /\
    (?s1 results t1 s2 vs t2.
       eval_expr_results cx es s1 = (INL results,t1) /\
       read_results cx results s2 = (INL vs,t2) /\
       bind_arguments (get_tenv cx) args vs = SOME penv) /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    call_evaluation_safe (cx with stk updated_by CONS (NONE,name))
      (int_calls_stmts ss) /\
    es1.scopes = [penv] /\
    gas_admissible ((do rv <- finally
         (try (do eval_stmts (cx with stk updated_by CONS (NONE,name)) ss;
                  return NoneV
               od) handle_function)
         (do pop_function prev;
             unlock_if_nr cx F (is_view_mut mut)
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
    od)) expr_vv_res_ok es1 /\
    stmt_state_rel ctx func cenv cx (es1 with scopes := prev) t /\
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
    locals_kept cenv es0 s0 t /\
    (!n lo sz aid off asz.
       local_region cenv prev t n lo sz /\
       FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
       sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
       regions_disjoint lo sz off asz) /\
    ?arg_vals st1 st2 invoke_args st3 rc rbs pvs lbl arg_ops bb inst argv.
      cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
      compile_multi_vvs compile_expr cenv es sa = (arg_vals,st1) /\
      compile_stage_intcall_args cenv arg_vals pvs (MAP expr_type es) st2 =
        (invoke_args,st3) /\
      lbl = internal_fn_label (cenv.ce_func_ids (nsid_to_string (NONE,name)))
              (nsid_to_string (NONE,name))
              (cenv.ce_func_param_types (nsid_to_string (NONE,name)))
              cenv.ce_is_ctor /\
      (rc = 0 /\
       cenv.ce_func_return_type (nsid_to_string (NONE,name)) = NoneT ==>
       st2 = st1 /\ arg_ops = invoke_args /\
       (?u. emit_void INVOKE (Label lbl :: invoke_args) st3 = (u,sb)) /\
       vv = StackValue (cenv.ce_func_return_type (nsid_to_string (NONE,name)))
              (Lit 0w)) /\
      (0 < rc \/
       cenv.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT ==>
       ?rbuf aid off.
         compile_alloc_buffer (if 0 < rc then 32 * rc else rbs) st1 =
           (rbuf,st2) /\
         vv = LocatedValue
                (cenv.ce_func_return_type (nsid_to_string (NONE,name)))
                (base_ptr rbuf) /\
         eval_operand rbuf.buf_operand t = SOME (n2w off) /\
         FLOOKUP t.vs_allocas aid = SOME (off,rbuf.buf_size) /\
         aid = st1.cs_next_id /\
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
      !callee setup use_trans nkeys imm_len lbl' ce params has_rb is_nr key
       trans view ctor imm_len' ss' rt.
        lookup_function lbl ctx.ctx_functions = SOME callee /\
        setup_callee callee argv t = SOME setup /\
        set_internal_package_target cenv.ce_target
          (package_internal_fn tops use_trans (nkeys : string -> num)
             cenv.ce_is_ctor imm_len
             (mut,F,rr,name,args,([] : expr list),ret,ss)) =
          (lbl',ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len',ss',rt) ==>
        lbl' = lbl /\
        (has_rb <=>
           rc = 0 /\
           cenv.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT) /\
        (ce.ce_is_ctor ==> IS_SOME (FLOOKUP t.vs_labels "runtime_begin")) /\
        state_rel func ce cx (es1 with scopes := []) t /\
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
        alloca_room ctx callee setup /\ fmp_room ctx callee setup) /\
    gas_invoke_entry (ctx,func) t callee entered /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) ==>
    !bb inst lbl arg_ops argv.
      lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      decode_invoke inst = SOME (lbl,arg_ops) /\
      eval_operands arg_ops t = SOME argv ==>
      gas_outcome F (cx_tops cx) (ctx,callee)
        (try (do eval_stmts (cx with stk updated_by CONS (NONE,name)) ss;
                 return NoneV
              od) handle_function)
        (es1,entered) (\res ee r. F)
        (\res ee r.
           expr_exit res r \/
           ?v ir s'.
             res = INL v /\ r = IntRet ir s' /\
             state_rel func cenv cx (ee with scopes := []) s' /\
             intret_vals_match rtv v ir.iret_values /\
             LENGTH ir.iret_values = rc /\ ir.iret_adopt_fmp = NONE /\
             (!b sz. b + sz <= t.vs_alloca_next /\
                     (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
                                    sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
                                    regions_disjoint b sz off asz) ==>
                     mem_bytes_at b sz s'.vs_memory = mem_bytes_at b sz t.vs_memory) /\
             (!p. (if rc = 0 /\
                      cenv.ce_func_return_type (nsid_to_string (NONE,name)) <> NoneT
                   then SOME (HD argv) else NONE) = SOME p ==>
                  val_in_memory rtv v (w2n p) s'.vs_memory))
Proof
  cheat
QED
