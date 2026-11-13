Theory bodyPtrIfExpUnwrapNoop
Ancestors
  bodyPtrDefs exprLowering context compileEnv loweringHalt fragGasPathPtr

(* This boundary covers precisely the return branches. In particular, the
   non-word test is on the LocatedValue's own type, not its annotation. *)
Theorem unwrap_value_noop_endpoint:
  !cenv vv sc src sn.
    ((?ty op. vv = StackValue ty op) \/
     (?ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\
             p.ptr_location = LocMemory)) /\
    unwrap_value cenv vv sc = (src,sn) ==>
    sn = sc /\ src = vv_operand vv
Proof
  rpt strip_tac >>
  gvs[unwrap_value_def, comp_return_def, vv_operand_def]
QED

(* R retains the entire source frame (vv_post, ptr_vv_ok, both buffer
   clauses, ghost_inv and original-sa ghost_kept) without restating it.
   Destination coverage and lookup are explicit: subsequent active unwrap
   branches will need to preserve these at the post-allocation cutoff. *)
Theorem unwrap_value_noop_counted_frame:
  !D lo ctx fn PG cenv vv sc src sn G tn s out n a R.
    ((?ty op. vv = StackValue ty op) \/
     (?ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\
             p.ptr_location = LocMemory)) /\
    unwrap_value cenv vv sc = (src,sn) /\ ~s.vs_halted /\
    R sc G tn s /\ ptr_covers G tn out s n /\ lookup_var out s = a ==>
    sn = sc /\ src = vv_operand vv /\
    gas_path_ptr D lo ctx fn PG G tn s 0 G tn (OK s) /\
    R sn G tn s /\ ptr_covers G tn out s n /\ lookup_var out s = a
Proof
  rpt gen_tac >> disch_tac >>
  `sn = sc /\ src = vv_operand vv` by
    metis_tac[unwrap_value_noop_endpoint] >> gvs[] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

(* Direct consumer of compile_alloc_buffer_vv_source_frame. All premises
   below are outputs of that theorem except the unwrap equation/branch
   guard; lookup is compared with the same allocated machine endpoint. *)
Theorem unwrap_value_noop_vv_source_frame:
  !D ctx fn PG cenv cx e es sa sc s0 es' tv vv s d G0 tn0 G tn
   out n src sn.
    ((?ty op. vv = StackValue ty op) \/
     (?ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\
             p.ptr_location = LocMemory)) /\
    unwrap_value cenv vv sc = (src,sn) /\
    ~s.vs_halted /\ ptr_covers G tn out s n /\
    ghost_inv d cenv cx es' G tn s /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    vv_post ctx fn cenv cx e es sa sc s0 es' tv vv s /\
    ptr_vv_ok cx (expr_type e) tv vv es' G tn s /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
        ptr_buf_ok cenv e op G s) /\
    (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G s) ==>
    sn = sc /\ src = vv_operand vv /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK s) /\
    ptr_covers G tn out s n /\
    ghost_inv d cenv cx es' G tn s /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    vv_post ctx fn cenv cx e es sa sn s0 es' tv vv s /\
    ptr_vv_ok cx (expr_type e) tv vv es' G tn s /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
        ptr_buf_ok cenv e op G s) /\
    (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G s)
Proof
  rpt gen_tac >> disch_tac >>
  `sn = sc /\ src = vv_operand vv` by
    metis_tac[unwrap_value_noop_endpoint] >> gvs[] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED
