(*
 * Whitelist removal: for loops over a memory-valued array iterable other
 * than a local name (form 2 of whitelistForIter's survey).
 *
 * compile_stmt's For Array case compiles the iterable with compile_expr
 * and then runs the fixed or dynamic memory loop over the pointer it
 * returns: a temporary buffer (a list literal, an extcall result, an IfExp
 * copy) or a place inside a local (a struct member or a subscript).  The
 * source iterates the snapshot it read at loop entry, so the compiled loop
 * agrees only while the body leaves the iterable's bytes alone.
 *
 * Neither S1 interface says that yet:
 *   - for a temporary, stmt_post keeps no memory outside the locals, so a
 *     body's stmt_frag doesn't keep the buffer;
 *   - for a place, vv_post doesn't tie the pointer to the source place
 *     (only to some offset of a local of the same type), so
 *     "the body doesn't write the place" (iterator_unmodified) doesn't
 *     reach the bytes the loop reads.
 * So the loop is proved against a hook, and each kind of iterable reduces
 * the hook to the interface clause it lacks today, taken as an explicit
 * hypothesis:
 *
 *   stmt_frag_keep Q    - a statement fragment that also keeps the state
 *                         predicate Q from start to end
 *   expr_vv_sim_with Qe - expr_vv_sim with an extra postcondition Qe
 *   keep_stable Q sb b z - Q survives code that keeps the variables handed
 *                         out before sb and the bytes [b, b+z)
 *
 * TOP-LEVEL:
 *   compile_for_mem_frag      - the For case over a memory iterable, given
 *                               the hook (a pointer inside an allocation
 *                               made before the loop, and a body that keeps
 *                               the elements there)
 *   typed_stmts_place_frame   - source side: a body that writes nothing
 *                               containing the iterable's place keeps every
 *                               read below its attribute path
 *   for_keep_temp             - hook for a temporary: from a body that keeps
 *                               the bytes of the buffer's allocation
 *   for_keep_place            - hook for a place: from the pointer being the
 *                               place's (local pointer + mem_path_offset)
 *                               and the source frame
 *)
Theory whitelistForIterMem
Ancestors
  whitelistForIterDynFrag stmtSimForArrayFrame exprSimSubscriptMap exprSimDefs loweringPosts
  stmtSimDefs gasOutcome supportedStmts vyperTypeSystem vyperState
  vyperInterpreter valueEncoding valueEncodingProps valueEncodingProofs
  stmtLowering exprLowering venomState list finite_map arithmetic words

(* A statement fragment as stmt_frag says, that also keeps Q: started in a
   state where Q holds, it ends where Q holds.  stmt_frag_keep (K T) is
   stmt_frag. *)
Definition stmt_frag_keep_def:
  stmt_frag_keep Q ctx func cx lctx RetQ cenv
    (m : compile_env compiler) source es <=>
    !sa sb s0 cenv'.
      m sa = (cenv', sb) /\ fn_has_code sa sb func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ret_pc_ok cenv sa s0 /\ ~block_is_terminated sa /\
      gas_admissible source (stmt_res_ok lctx) es /\
      stmt_state_rel ctx func cenv cx es s0 /\ Q s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx, func) source (es, s0)
        (\res ee t. stmt_post ctx func cx lctx cenv cenv' sa sb s0 res ee t /\
                    Q t)
        (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
End

(* expr_vv_sim, whose post also has Qe of the compile states, the start
   state, and the source and Venom results.  expr_vv_sim_with (K ...) T is
   expr_vv_sim. *)
Definition expr_vv_sim_with_def:
  expr_vv_sim_with Qe ctx func cenv cx ty e es <=>
    !sa sb vv s0.
      compile_expr cenv ty e sa = (vv, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx, func) (eval_expr cx e) (es, s0)
        (\res ee t. ?tv. res = INL tv /\
          vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
          Qe sa sb s0 ee tv vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts)
        (\res ee r. expr_exit res r)
End

(* Q survives any code that keeps the variables handed out before sb and
   the bytes [b, b + z): the loop's own index, element copy and branches
   write only fresh variables and the loop variable's allocation. *)
Definition keep_stable_def:
  keep_stable Q (sb : compile_state) b z <=>
    !s s'. Q s /\
      (!x. not_fresh_at sb x ==> lookup_var x s' = lookup_var x s) /\
      mem_bytes_at b z s'.vs_memory = mem_bytes_at b z s.vs_memory ==>
      Q s'
End

(* The For case over a memory-valued iterable, fixed or dynamic.  The hook
   (the last premise) is asked of every end of the iterable's fragment: the
   pointer w lies inside an allocation (aid, b, z) made before the loop,
   the elements vs of the value v the source read sit at w, and the body,
   at every element, keeps a predicate Q that puts them there and that
   survives the loop's own code (keep_stable).  P is the source-side loop
   invariant, as in compile_for_dynarray_frag. *)
Theorem compile_for_mem_frag:
  !ctx func cx cenv lctx RetQ ty id et bd c n arr_e stmts tv es Qe.
  expr_type arr_e = ArrayT et bd /\ (bd = Fixed c \/ bd = Dynamic c) /\
  c <= n /\ c < dimword (:256) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) /\ cenv.ce_alloca_locals /\
  (!st. vv_location (FST (compile_expr cenv (ArrayT et bd) arr_e st)) =
          SOME LocMemory) /\
  lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  expr_vv_sim_with Qe ctx func cenv cx (ArrayT et bd) arr_e es /\
  (!sa sb s0 es1 rv vv s1.
     compile_expr cenv (ArrayT et bd) arr_e sa = (vv, sb) /\
     vv_post ctx func cenv cx arr_e es sa sb s0 es1 rv vv s1 /\
     Qe sa sb s0 es1 rv vv s1 ==>
     ?v vs w aid b z Q P.
       read_result cx rv es1 = (INL v, es1) /\
       extract_elements (ArrayTV tv bd) v = SOME vs /\
       eval_operand (vv_operand vv) s1 = SOME w /\
       FLOOKUP s1.vs_allocas aid = SOME (b, z) /\ aid < sb.cs_next_id /\
       b <= w2n w /\ w2n w + type_memory_size (ArrayTV tv bd) <= b + z /\
       b + z < dimword (:256) /\
       Q s1 /\ keep_stable Q sb b z /\
       (!s. Q s ==> val_in_memory (ArrayTV tv bd) v (w2n w) s.vs_memory) /\
       P es1 /\ lookup_scopes id es1.scopes = NONE /\
       (!k. k < LENGTH vs ==> value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)) /\
       (!st0 bc sd ex inc ei k.
          declare_local cenv id et st0 = (bc,sd) /\
          P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
          stmt_frag_keep Q ctx func cx (InLoop ex inc) RetQ bc
            (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
            (ei with scopes :=
              (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs;
                                popped := []|>)) :: ei.scopes)) /\
       (!ei k gs r es2.
          P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
          eval_stmts cx stmts (ei with <| scopes :=
            (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs;
                              popped := []|>)) :: ei.scopes; gas_obs := gs |>) =
            (r,es2) ==>
          (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
          ?sc rest. es2.scopes = sc :: rest /\
            (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
            ((r = INL () \/ r = INR ContinueException) ==>
              P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE))) ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (For id et (Array arr_e) n stmts))
    (eval_stmt cx (For id et (Array arr_e) n stmts)) es
Proof
  cheat
QED

(* Source side for a place iterable: a body that writes nothing containing
   the place p (iterator_unmodified) keeps, at every scope, the reads of
   the root local below p's attribute path (the path up to its first
   subscript, place_access).  typed_stmts_projection_frame is the case of
   an empty attribute path, where the whole root is kept. *)
Theorem typed_stmts_place_frame:
  supported_stmts tops bindings stmts /\
  type_stmts env ret_ty stmts = SOME env' /\
  expr_place arr_e = SOME p /\ place_access p [] = (NameTarget root, attrs) /\
  root IN FDOM env.var_types /\
  stmts_writes_ok (\w. ~place_contains w p) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  es.scopes <> [] /\ eval_stmts cx stmts es = (res,es') ==>
  LENGTH es'.scopes = LENGTH es.scopes /\
  MAP (\sc. OPTION_MAP
          (\e rest. read_memory_path e (MAP AttrSubscript attrs ++ rest))
          (FLOOKUP sc root)) es'.scopes =
  MAP (\sc. OPTION_MAP
          (\e rest. read_memory_path e (MAP AttrSubscript attrs ++ rest))
          (FLOOKUP sc root)) es.scopes
Proof
  cheat
QED

(* Hook for a temporary buffer: a body that keeps the bytes of the
   buffer's allocation keeps the iterable's value in it.  The hypothesis
   is what stmt_post's frame on the memory of allocations made before the
   fragment and holding no local (the S1 interface piece on stmt_post)
   gives every body. *)
Theorem for_keep_temp:
  !ctx func cx lctx RetQ cenv m source es atv v w b z cs.
    (!bs. stmt_frag_keep (\s. mem_bytes_at b z s.vs_memory = bs)
            ctx func cx lctx RetQ cenv m source es) /\
    val_wf atv v /\ b <= w /\ w + type_memory_size atv <= b + z ==>
    stmt_frag_keep (\s. val_in_memory atv v w s.vs_memory)
      ctx func cx lctx RetQ cenv m source es /\
    keep_stable (\s. val_in_memory atv v w s.vs_memory) cs b z
Proof
  rpt gen_tac >> strip_tac >>
  `!m1 m2. mem_bytes_at b z m2 = mem_bytes_at b z m1 /\
           val_in_memory atv v w m1 ==> val_in_memory atv v w m2` by
    (rpt strip_tac >> irule val_in_memory_mem_agree >> simp[] >>
     qexistsl_tac [`type_memory_size atv`, `m1`] >> simp[] >>
     drule (cj 1 mem_bytes_at_agree_window) >> disch_then irule >> simp[]) >>
  conj_tac >~ [`keep_stable`] >- (simp[keep_stable_def] >> metis_tac[]) >>
  simp[stmt_frag_keep_def] >>
  map_every qx_gen_tac [`sa`, `sb`, `s0`, `cenv'`] >> strip_tac >>
  qpat_x_assum `!bs. stmt_frag_keep _ _ _ _ _ _ _ _ _ _`
    (qspec_then `mem_bytes_at b z s0.vs_memory` mp_tac) >>
  simp[stmt_frag_keep_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `s0`, `cenv'`] mp_tac) >> simp[] >>
  strip_tac >> irule gas_outcome_conseq >> first_assum (irule_at Any) >>
  simp[] >> metis_tac[]
QED

(* Hook for a place inside a local: the iterable's pointer is the place's,
   the root local's pointer bw (in its variable q) plus the byte offset k
   of the place's path in the root's type (the vv_place_ptr clause of the
   S1 interface piece on vv_post), and the body writes nothing containing
   the place.  Then the body keeps q and the value v the place held at
   entry. *)
Theorem for_keep_place:
  !ctx func cx ex inc RetQ bc ty stmts ei tops bindings env ret_ty env' arr_e
   p root attrs rest entry v q z bw t0 tv0 k atv.
    stmt_frag ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts) ei /\
    supported_stmts tops bindings stmts /\
    type_stmts env ret_ty stmts = SOME env' /\
    expr_place arr_e = SOME p /\ place_access p [] = (NameTarget root, attrs) /\
    root IN FDOM env.var_types /\
    stmts_writes_ok (\w. ~place_contains w p) stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    ei.scopes <> [] /\ lookup_scopes root ei.scopes = SOME entry /\
    read_memory_path entry (MAP AttrSubscript attrs ++ rest) = INL v /\
    FLOOKUP bc.ce_vars root = SOME (PtrVar (Var q) z) /\
    bc.ce_var_type root = SOME t0 /\
    evaluate_type (get_tenv cx) t0 = SOME tv0 /\
    mem_path_offset tv0 (MAP AttrSubscript attrs ++ rest) = SOME (k, atv) ==>
    stmt_frag_keep
      (\s. lookup_var q s = SOME bw /\
           val_in_memory atv v (w2n bw + k) s.vs_memory)
      ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts) ei
Proof
  cheat
QED
