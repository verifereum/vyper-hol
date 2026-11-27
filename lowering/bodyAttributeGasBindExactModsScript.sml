(* Specialize the Attribute bind to the raw-expression simulation posts. *)
Theory bodyAttributeGasBindExactMods
Ancestors
  bodyAttributeGasBindMods bodyFullPostsMods

(* The success packet of expr_vv_sim_full_mods, parameterized by the
   expression, end of compilation, and lowered value. *)
fun raw_post e sb vv =
  ``\(H:(bool # 256 word # type_value) list # num list) (tv:eval_result) ee G tn t.
    vv_post_mods H ctx func cenv cx ^e es sa ^sb s0 ee tv ^vv t /\
    vv_store_bound cx (post_value_type cenv ^e) (lowered_value_type cenv ^e)
      ee tv ^vv t /\
    t.vs_current_bb = ^sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH ^sb.cs_current_insts /\
    alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    ptr_vv_ok cx (post_value_type cenv ^e) tv ^vv ee G tn t /\
    (!v. tv = Value v /\ ~is_word_type (post_value_type cenv ^e) /\
          ~is_bytestring_type (post_value_type cenv ^e) ==>
          vv_own cenv cx (post_value_type cenv ^e) sa ^sb ee tv ^vv t /\
          (!t' p. ^vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
    (cenv.ce_is_ctor /\ vv_location ^vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val,ee) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type cenv ^e) = SOME rt /\
                  eval_operand (vv_operand ^vv) t = SOME w ==>
                  w2n w + type_memory_size rt <= lo /\
                  (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                         val_in_memory rt val (w2n w) mem)) /\
    (!t' op. ^vv = StackValue t' op /\ ~is_word_type (post_value_type cenv ^e) ==>
             ptr_buf_ok cenv ^e op G t) /\
    (!t' p. ^vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv ^e p.ptr_operand G t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

fun sum_post post =
  ``\H (res:eval_result + exception) ee G tn t.
     ?tv. res = INL tv /\ ^post H tv ee G tn t``;

val child_post = raw_post ``obj:expr`` ``sm:compile_state`` ``bvv:vyper_value``;
val field_post = raw_post ``Attribute ann obj fld`` ``sb:compile_state`` ``vv:vyper_value``;
val exit_post =
  ``\(H:(bool # 256 word # type_value) list # num list)
      (res:eval_result + exception) ee (gt:(string |-> num # num) # taint) r.
    expr_exit res r /\ halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

val bind_exact =
  ``gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_expr cx obj) (es,s0,G0,tn0) ^(sum_post child_post) ^exit_post /\
  (!xs raw ee s G tn.
    eval_expr cx obj (es with gas_obs := xs) = (INL raw,ee) /\
    ee.gas_obs = [] /\ ~s.vs_halted /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> ^child_post H raw ee G tn s) ==>
    ?raw' t G' tn'.
      select_result cx (expr_type obj) raw (AttrSubscript fld) ee = (INL raw',ee) /\
      !H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
        ^field_post H raw' ee G' tn' t) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_expr cx (Attribute ann obj fld)) (es,s0,G0,tn0)
    ^(sum_post field_post) ^exit_post``;

Theorem attribute_vv_outcome_bind_exact_mods:
  ^(rhs (concl (DEPTH_CONV BETA_CONV bind_exact)))
Proof
  ACCEPT_TAC (BETA_RULE (Q.INST [`Child` |-> `^child_post`, `Field` |-> `^field_post`]
    attribute_vv_outcome_bind_mods))
QED
