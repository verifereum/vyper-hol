(* Full allocation capacity, rather than the shortened live array, bounds
   the value returned by pop. *)
Theory bodyMemPopLocalFacts
Ancestors
  exprSimPop exprSimMemDefs bodyMemoryDefs exprSimProps exprSimDefs
  compileEnv context venomState instIdxIndep exprLoweringProps exprLowering
  list words arithmetic vyperAST

Theorem pop_local_result_capacity:
  !w len n esz sz frontier.
    0 < len /\ len <= n /\ 32 + n * esz <= sz /\
    w2n (w:bytes32) + sz <= frontier /\ frontier < dimword (:256) ==>
    esz = 0 \/
    w2n (w + 32w + (n2w len - 1w) * n2w esz) + esz <= frontier
Proof
  rpt strip_tac >>
  `len * esz <= n * esz` by simp[] >>
  `w2n (w + 32w + (n2w len - 1w) * n2w esz) =
   w2n w + 32 + (len - 1) * esz` by
    (irule pop_ptr_w2n >> decide_tac) >>
  `w2n w + 32 + (len - 1) * esz + esz <= w2n w + sz` by
    (irule pop_elem_fits >> simp[] >> qexists_tac `n` >> simp[]) >>
  decide_tac
QED

Theorem pop_local_vv_post_mem:
  vv_post ctx func cenv cx (Pop ann (NameTarget id)) es sa sb s0
    es' tv (LocatedValue ann (mk_ptr op LocMemory)) t /\
  stmt_state_rel ctx func cenv cx es s0 /\
  evaluate_type (get_tenv cx) ann = SOME etv /\
  eval_operand op t =
    SOME (w + 32w + (n2w len - 1w) * n2w (type_memory_size etv)) /\
  0 < len /\ len <= n /\ 32 + n * type_memory_size etv <= sz /\
  w2n w + sz <= s0.vs_alloca_next /\ t.vs_alloca_next = s0.vs_alloca_next ==>
  vv_store_bound cx (expr_type (Pop ann (NameTarget id)))
    (lowered_value_type cenv (Pop ann (NameTarget id)))
    es' tv (LocatedValue ann (mk_ptr op LocMemory)) t
Proof
  rpt strip_tac >>
  `s0.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  `type_memory_size etv = 0 \/
   w2n (w + 32w + (n2w len - 1w) * n2w (type_memory_size etv)) +
     type_memory_size etv <= t.vs_alloca_next` by
    (irule pop_local_result_capacity >> metis_tac[]) >>
  simp[expr_type_def, lowered_value_type_def] >>
  irule (SRULE [expr_type_def]
    (Q.INST [`e` |-> `Pop ann (NameTarget id)`] vv_store_bound_capacity)) >>
  fs[expr_type_def, mk_ptr_def] >> metis_tac[]
QED
