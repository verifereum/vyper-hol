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
   The induction's steps are one leaf theory each, bodyIntCallJoint{Agg,
   Pure,Call,Force,Stmt}; bodyIntCallJointInd assembles them into
   intcall_joint_producers, from which the seam itself is proved. *)

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

(* The caller's compile env agrees with every function's
   build_compile_env for tops on the module-level fields the callee's
   package env takes from tops: the module, module-variable types and
   locations (immutables included), flag metadata and method ids.  body_inv pins the other module-level
   fields this way. *)
Definition cenv_module_pins_def:
  cenv_module_pins tops cenv <=>
    cenv.ce_module = NONE /\
    cenv.ce_module_var_type = build_var_type_map tops /\
    cenv.ce_module_vars =
      add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
        tops 0 (add_module_var_locations tops FEMPTY) /\
    cenv.ce_flag_member_id = FST (build_flag_info tops (K (K 0)) (K 0)) /\
    cenv.ce_flag_n_members = SND (build_flag_info tops (K (K 0)) (K 0)) /\
    cenv.ce_method_id =
      (\s tys. w2n (calldata_method_id
                     (function_selector s (vyper_to_abi_types (type_env tops) tys))))
End

Theorem build_compile_env_module_pins:
  cenv_module_pins tops
    (build_compile_env tops vis mut fname args ret fbody use_trans)
Proof
  simp[cenv_module_pins_def, compileVyperTheory.build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[])
QED

(* A supported program declares no memberless struct: the interim
   condition trunk's supported_program carries until the checker's
   rejection of memberless structs (what Vyper rejects) reaches it.  Held
   here; it is proved once supported_declaration_headers' StructDecl clause
   requires fields <> []. *)
Theorem supported_program_struct_fields_nonempty:
  supported_program tops /\ supported_struct_fields tops id = SOME fs ==>
  fs <> []
Proof
  cheat
QED

(* The hypotheses on the fixed parameters alone: P lies below lo and clear
   of every staged allocation; the graph witnesses of call_evaluation_safe
   for owner; the return PC, the root return buffer's pointer and the
   immutable base are reserved, every reserved operand is a variable the
   prologue defined at the operand origin, and the return PC holds pc
   there; no supported struct is memberless (the interim condition trunk's
   supported_program carries until the checker's rejection reaches it); the return buffer's capacity is the return value's size and P
   misses it; the source return type evaluates to ret_tv.  The root env
   returns internally (RET to the return PC, as the prologue sets it), with
   the stack-return count of the declared return type, and a return buffer
   exactly when that count is 0 and the type isn't void; its module-level
   fields are the ones build_compile_env takes from tops. *)
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
    fp.jc_root_ce.ce_return_pc = SOME (PtrVar fp.jc_rpc 0) /\
    cenv_module_pins fp.jc_tops fp.jc_root_ce /\
    fp.jc_root_ce.ce_returns_count =
      returns_stack_count
        (\name. MAP (FST o SND)
                 (get_struct_fields fp.jc_root_ce.ce_struct_fields name))
        fp.jc_ret_ty /\
    (IS_SOME fp.jc_rb <=>
       fp.jc_root_ce.ce_returns_count = 0 /\ fp.jc_ret_ty <> NoneT) /\
    (!x sz. fp.jc_root_ce.ce_return_buf = SOME (PtrVar x sz) ==>
            fp.jc_reserved x) /\
    (!x. fp.jc_root_ce.ce_imm_alloca = SOME x ==> fp.jc_reserved x) /\
    (!op. fp.jc_reserved op ==>
          ?x w. op = Var x /\ lookup_var x fp.jc_oorig = SOME w) /\
    (!id fs. supportedTypes$supported_struct_fields fp.jc_tops id = SOME fs ==>
             fs <> []) /\
    (!bw cap. fp.jc_rb = SOME (bw,cap) ==>
       cap = type_memory_size fp.jc_ret_tv /\
       w2n bw + cap <= fp.jc_lo /\
       (!b z. fp.jc_staged b z ==> regions_disjoint (w2n bw) cap b z) /\
       !a k. fp.jc_prot a k ==> regions_disjoint a k (w2n bw) cap)
End

(* ===== The resource conjunction I ===== *)

(* I(ce,env,es,sa,s) of E0014 section 1, at the current compile env,
   typing, source state, compile state and Venom state.  The write-region
   authorization W(p,k) is written out: lo <= p, or [p,p+k) inside a staged
   allocation. *)
Definition intcall_expr_res_def:
  intcall_expr_res fp ce env es sa s <=>
    stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
    expr_sim_inv ce fp.jc_cx env es /\
    locals_alloc_ok ce env /\
    local_ptrs_reserved ce sa /\
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

(* I at a statement boundary: every compile-env local is declared in the
   typing.  An AnnAssign's initializer is compiled after its name is
   declared on the compile side only, so expressions get intcall_expr_res. *)
Definition intcall_joint_res_def:
  intcall_joint_res fp ce env es sa s <=>
    intcall_expr_res fp ce env es sa s /\ ce_locals_declared ce env
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
    intcall_expr_res fp ce env ee sb u /\ ~u.vs_halted /\
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
       mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz s.vs_memory) /\
    locals_kept ce es s u
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
      intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
      s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
        (eval_expr fp.jc_cx e) (es,s)
        (\res ee u. ?tv. res = INL tv /\
           vv_holds ce fp.jc_cx (post_value_type ce e) tv vv ee u /\
           vv_at ce fp.jc_cx (post_value_type ce e) sa sb ee tv vv u /\
           (post_value_type ce e <> expr_type e ==>
            vv_own ce fp.jc_cx (post_value_type ce e) sa sb ee tv vv u) /\
           (~expr_has_effect e ==> vv_storage_live fp.jc_cx vv ee u) /\
           (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
           (post_value_type ce e <> NoneT /\
            ~is_word_type (post_value_type ce e) /\
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
      intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
      s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
        (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) (es,s)
        (\res ee u. ?v. res = INL v /\
           expr_val_rel fp.jc_cx (post_value_type ce e) v op u /\
           expr_val_at ce fp.jc_cx (post_value_type ce e) sa sb ee v op u /\
           (post_value_type ce e <> expr_type e ==>
            expr_val_own ce fp.jc_cx (post_value_type ce e) sa sb ee v op u) /\
           (!x. op = Var x ==> not_fresh_at sb x) /\
           (post_value_type ce e <> NoneT /\
            ~is_word_type (post_value_type ce e) /\
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
      intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
      s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
        (eval_expr fp.jc_cx e) (es,s)
        (\res ee u. ?tr slot kt vt tp p.
           res = INL (HashMapRef tr slot kt vt) /\
           storage_mapping_region fp.jc_cx tr slot (HashMapT kt vt) /\
           vv = LocatedValue tp p /\ p.ptr_location = slot_loc tr /\
           eval_operand p.ptr_operand u = SOME slot /\
           (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
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
