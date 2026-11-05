Theory bodyIntCallJointSingleton
Ancestors
  exprSimAggregateSource exprSimWordArgs vyperState
  exprSimSource exprSimHypsDefs vyperTypeSystem

(* Materialise the sole child on its actual evaluation endpoint. *)
Theorem joint_eval_make_tuple_singleton:
  compatible_bound bnd 1 /\
  eval_expr cx e es = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) ==>
  eval_expr cx (Builtin ann (MakeArray NONE bnd) [e]) es =
    (INL (Value (ArrayV (TupleV [v]))),ee)
Proof
  rpt strip_tac >>
  `eval_exprs cx [e] es = (INL [v],ee)` by
    simp[eval_exprs_cons_action, bind_def, eval_exprs_nil, return_def] >>
  drule_at (Pos last) aggregate_eval_make_tuple >> simp[]
QED

(* The bound is supplied by the parent's typing, not by a new precondition. *)
Theorem joint_typed_eval_make_tuple_singleton:
  expr_sim_pre ce cx env (Builtin ann (MakeArray NONE bnd) [e]) es /\
  eval_expr cx e es = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) ==>
  eval_expr cx (Builtin ann (MakeArray NONE bnd) [e]) es =
    (INL (Value (ArrayV (TupleV [v]))),ee)
Proof
  rpt strip_tac >> irule joint_eval_make_tuple_singleton >>
  gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  metis_tac[]
QED

(* Representation audit for the allocating MsgGas parent (not a simulation).

   Source: joint_typed_eval_make_tuple_singleton uses only the actual child
   evaluation and read_result at ee.  It is independent of observation tails
   and ctor mode.  expr_sim_pre_body_pre (exprSimSource) supplies the input of
   make_tuple_evaluated_layout; expr_body_pre_builtin_arg supplies child typing.
   For e = Builtin ga (Env MsgGas) args, layout gives ann = TupleT [ga].

   Concrete endpoint from joint_tuple_word_suffix_path:
     r = (mstore (w2n p) w (update_var x p u))
           with vs_inst_idx := LENGTH sb.cs_current_insts.
   Here p MUST be the pointer from literal_alloc_buffer_run, not a new
   existential pointer selected by another simulation.

   Encoding: val_in_memory_def reduces the singleton TupleTV encoding to
   val_in_memory child_tv (IntV (&w2n w)) (w2n p) r.vs_memory.
   mstore_establishes_val_in_memory_prim (valueEncodingProps) establishes this
   once val_to_w256 (IntV (&w2n w)) = w is rewritten.  No tuple-specific local
   helper is required.  Encoding alone is NOT vv_post.

   Exact remaining vv_post sequents at r (loweringPosts):
   1. stmt_state_rel at ee: suffix_frame supplies this once the SAME u has
      its state relation, same allocation and local separation.
   2. vv_holds: buf operand still evaluates to p at r, evaluated parent type
      is TupleTV [child_tv], and source Value reads to itself at ee.
   3. vv_at: val_wf of the tuple, plus SAME allocation id sa.cs_next_id,
      sa.cs_next_id < sb.cs_next_id, its pointer/size at r, footprint bound,
      and disjointness from ALL local_region ce ee.scopes r regions.
      Reused ALLOCA must retain this allocation id; freshness of its address
      is not a premise.  aggregate_alloca_slice_excludes_local is exported.
   4. every not_fresh_at sa variable value is preserved from original s0.
   5. every original allocation map entry is preserved from s0.
   6. every old, nonlocal allocation window is preserved from s0 (exact
      local-separation guard uses es.scopes and s0, not ee and r).
   7. locals_kept ce es s0 r.
   Plus the producer's stronger hs and initialized-immutable byte equalities
   must compose from s0, not merely from u.  Suffix frame already handles
   initialized immutable type_memory_size windows in BOTH ctor modes.

   These are outstanding construction sequents, not assumed consequences of
   the existing existential aggregate simulation.  No ordinary-success proof
   would discharge gas_outcome's exempt alternative; enclosing source outcome
   transport must retain that branch separately. *)
