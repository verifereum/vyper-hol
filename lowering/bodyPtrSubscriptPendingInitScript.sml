(* Initialization boundary probes: no global pending-state predicate. *)
Theory bodyPtrSubscriptPendingInit
Ancestors
  bodyPtrSubscriptNamedRoot bodyPtrSubscriptCapturedInitProbe
  bodyPtrDefs loweringPosts vyperState vyperInterpreter
  valueEncoding exprSimDefs ptrDiscipline finite_map

(* With no pending items and no certified historical owners, this is the
   entire represented-root obligation. Initial entry.popped is unrestricted. *)
Theorem empty_pending_current_roots:
  ghost_inv d cenv cx es G tn s ==>
  !id entry p sz.
    lookup_scopes id es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
    ptr_covers G tn p s sz /\
    !w mem. lookup_var p s = SOME w /\
      mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem
Proof
  simp[ghost_inv_def] >> metis_tac[]
QED

Theorem current_root_read:
  lookup_scopes id es.scopes = SOME entry ==>
  read_result cx (PlaceR (MemoryPlace id [])) es = (INL entry.value,es)
Proof
  simp[read_result_def, read_place_def, bind_def, get_scopes_def,
       lift_option_type_def, lift_sum_def, read_memory_path_def,
       evaluate_subscripts_def, return_def]
QED

(* Capture adds a root read/address certificate without changing any frame
   component. named_root_preparation provides the address from state_rel;
   it is not reconstructed from arbitrary bytes or a historical child. *)
Theorem current_root_capture:
  expr_body_pre cenv cx env (Name ann id) es /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s ==>
  ?entry p sz a.
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) ann = SOME entry.type /\
    value_has_type entry.type entry.value /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME ann /\
    lookup_var p s = SOME a /\ type_memory_size entry.type <= sz /\
    read_result cx (PlaceR (MemoryPlace id [])) es = (INL entry.value,es) /\
    ptr_covers G tn p s sz /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory entry.type entry.value (w2n a) mem) /\
    ghost_inv d cenv cx es G tn s
Proof
  strip_tac >> drule_all named_root_preparation >> strip_tac >>
  qexistsl_tac [`entry`, `p`, `sz`, `a`] >> simp[current_root_read]
QED

(* The ordinary normal post's OWN read and robust representation are on one
   endpoint. No statement about other captures or complete owners follows. *)
Theorem ordinary_memory_endpoint:
  vv_post ctx func cenv cx e es sa sb s0 ee result (LocatedValue ty p) s /\
  ptr_vv_ok cx (expr_type e) result (LocatedValue ty p) ee G tn s /\
  p.ptr_location = LocMemory /\ post_value_type cenv e = expr_type e /\
  ~is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  ty = expr_type e /\ ?v w.
    read_result cx result ee = (INL v,ee) /\
    eval_operand p.ptr_operand s = SOME w /\
    ptr_mem_ok cx (expr_type e) v p.ptr_operand G tn s /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory tv v (w2n w) mem)
Proof
  strip_tac >> drule_all captured_memory_post >> strip_tac >>
  gvs[ptr_vv_ok_def] >> gvs[ptr_mem_ok_def] >> metis_tac[]
QED

(* Interface verdict (C1.mutual.init).

   The checked boundary ordinary_memory_endpoint consumes exactly two clauses
   of expr_vv_sim_ptr's NORMAL post (vv_post and ptr_vv_ok), on the SAME
   ee,s,G,tn. It retains ptr_mem_ok, so its provenance/val_store_size coverage
   implication is not weakened to plain val_in_memory. It gives no address
   for another source place, no scope identity, and no representation of an
   enclosing historical owner. Its successful own read is unconditional once
   the displayed endpoint/type/location premises hold.

   A HOL-typed singleton *observation* interface, before owner augmentation,
   is the following explanatory lambda (NOT a new predicate definition):

     \(ee:evaluation_state) G tn (s:venom_state).
       ?v w. read_result cx (PlaceR (MemoryPlace id path)) ee = (INL v,ee) /\
         eval_operand op s = SOME w /\
         ptr_mem_ok cx ty v op G tn s

   The types of G, tn, op, ty, id and path are inferred from ptr_mem_ok
   and read_result, as in the checked applications above.
   For a general producer the ordinary normal post would have to be conjoined
   with this observation for EVERY incoming classified pending item, and an
   origin certificate for its own returned PlaceR. Both must use that post's
   ee,s,G,tn, not a second existential path. This observation alone is too
   weak for owner_path_pop_header: it represents the selected result, not its
   full historical parent. A full-parent certificate must additionally retain
   the actual first-success owner, its type/value/address, robust memory
   representation, and the typed offset connecting it to op. Lookup order
   and the scope in which id was resolved are essential extra fields.

   empty_pending_current_roots initializes precisely the root component:
   with pending=[] and certified_history=[] there are no other universally
   quantified obligations. It deliberately retains arbitrary entry.popped.
   current_root_capture checks the non-vacuous singleton case: source lookup,
   successful own read, pointer address, full current entry representation
   and coverage all coexist with the UNCHANGED ghost_inv. It uses the actual
   typed Name precondition and stmt_state_rel, not only ghost_inv.

   DECISION: full-parent certificates must be retained when evaluating a
   root/selector, OR stored in a separate reachable-owner table. The ordinary
   vv endpoint cannot reconstruct them after returning only a child. These
   checked facts do not choose between those two equivalent storage designs.
   Missing producer obligations are (a) origin/typed-offset/scope identity for
   a returned non-root, (b) preservation or refresh of incoming certificates,
   (c) full owner initialization when Pop creates historical children. They
   are not projections of ordinary safety. Global mutual closure therefore
   remains blocked pending the subsequent bind/list feasibility probes.
*)
