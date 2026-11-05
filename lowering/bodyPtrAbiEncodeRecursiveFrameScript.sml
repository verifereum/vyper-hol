(* Explicit relational interfaces for a child encoder's protected resources.
   No predicate is introduced: each child must discharge these frame premises. *)
Theory bodyPtrAbiEncodeRecursiveFrame
Ancestors
  bodyPtrAbiEncodeCursorFrame bodyPtrDefs exprLoweringProps emitHelperProps
  robustCopyTransportPtr typedCopyRobustTransportPtr
  ptrDiscipline venomState venomExecSemantics compileEnv
  words finite_map arithmetic pred_set list valueEncodingProofs

Theorem abi_encode_older_frame_then:
  (!q. not_fresh_at st q ==>
    lookup_var q t = lookup_var q s /\ FLOOKUP H q = FLOOKUP G q /\
    op_taint un (Var q) = op_taint tn (Var q)) /\
  (!q. not_fresh_at mid q ==>
    lookup_var q u = lookup_var q t /\ FLOOKUP J q = FLOOKUP H q /\
    op_taint vn (Var q) = op_taint un (Var q)) /\
  st.cs_next_var <= mid.cs_next_var ==>
  (!q. not_fresh_at st q ==>
    lookup_var q u = lookup_var q s /\ FLOOKUP J q = FLOOKUP G q /\
    op_taint vn (Var q) = op_taint tn (Var q))
Proof
  strip_tac >> rpt strip_tac >>
  `not_fresh_at mid q` by (fs[not_fresh_at_def] >> decide_tac) >>
  metis_tac[]
QED

Theorem abi_encode_ptr_covers_transport:
  lookup_var q t = lookup_var q s /\ FLOOKUP H q = FLOOKUP G q /\
  op_taint un (Var q) = op_taint tn (Var q) /\ ptr_covers G tn q s n ==>
  ptr_covers H un q t n
Proof
  simp[ptr_covers_def]
QED

Theorem abi_encode_older_frame_covers:
  (!q. not_fresh_at st q ==>
    lookup_var q t = lookup_var q s /\ FLOOKUP H q = FLOOKUP G q /\
    op_taint un (Var q) = op_taint tn (Var q)) /\
  not_fresh_at st p /\ ptr_covers G tn p s n ==>
  ptr_covers H un p t n
Proof
  metis_tac[abi_encode_ptr_covers_transport]
QED

Theorem abi_encode_clean_window_exterior:
  un.t_mem SUBSET tn.t_mem UNION writes /\
  (!i. a <= i /\ i < a+n ==> i NOTIN writes) /\
  (!i. a <= i /\ i < a+n ==> i NOTIN tn.t_mem) ==>
  (!i. a <= i /\ i < a+n ==> i NOTIN un.t_mem)
Proof
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem abi_encode_exterior_memory_window:
  mem_agree_outside writes mem mem' /\
  (!i. a <= i /\ i < a+n ==> i NOTIN writes) ==>
  mem_bytes_at a n mem' = mem_bytes_at a n mem
Proof
  strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `j < n` >>
  `a+j NOTIN writes` by (first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (a+j) 1 mem = mem_bytes_at (a+j) 1 mem'` by
    metis_tac[mem_agree_outside_def] >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

(* A recursive child preserves precisely the saved head/cursor/offset operands;
   its own length operand is new and must be supplied clean by the child. *)
Theorem abi_encode_cursor_suffix_entry:
  (!q. not_fresh_at saved q ==>
    lookup_var q t = lookup_var q s /\ FLOOKUP H q = FLOOKUP G q /\
    op_taint un (Var q) = op_taint tn (Var q)) /\
  not_fresh_at saved head /\ not_fresh_at saved cursor /\ not_fresh_at saved offset /\
  lookup_var head s = SOME (n2w h) /\ lookup_var cursor s = SOME (n2w p) /\
  lookup_var offset s = SOME (n2w off) /\
  ptr_covers G tn head s 32 /\ ptr_covers G tn cursor s 32 /\
  op_taint tn (Var offset) = {} ==>
  lookup_var head t = SOME (n2w h) /\ lookup_var cursor t = SOME (n2w p) /\
  lookup_var offset t = SOME (n2w off) /\
  ptr_covers H un head t 32 /\ ptr_covers H un cursor t 32 /\
  op_taint un (Var offset) = {}
Proof
  strip_tac >>
  `ptr_covers H un head t 32 /\ ptr_covers H un cursor t 32` by
    (conj_tac >> irule abi_encode_older_frame_covers >>
     goal_assum $ drule_at Any >> qexists_tac `saved` >> simp[]) >>
  metis_tac[]
QED
