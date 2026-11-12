(* Captured-result endpoint probe. No global invariant is defined. *)
Theory bodyPtrSubscriptCapturedInitProbe
Ancestors
  loweringPosts bodyPtrDefs bodyPtrSubscriptOwnerPop
  bodyPtrSubscriptHistoryLayoutProbe exprSimVVFrame
  valueEncodingProps vyperState list

Theorem captured_memory_holds:
  vv_holds cenv cx ty result (LocatedValue ty' p) es s /\
  p.ptr_location = LocMemory /\ ~is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  ty' = ty /\ ?v w.
    read_result cx result es = (INL v,es) /\
    eval_operand p.ptr_operand s = SOME w /\
    val_in_memory tv v (w2n w) s.vs_memory
Proof
  simp[vv_holds_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem captured_memory_post:
  vv_post ctx func cenv cx e es sa sb s0 ee result (LocatedValue ty p) s /\
  p.ptr_location = LocMemory /\ post_value_type cenv e = expr_type e /\
  ~is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  ty = expr_type e /\ ?v w.
    read_result cx result ee = (INL v,ee) /\
    eval_operand p.ptr_operand s = SOME w /\
    val_in_memory tv v (w2n w) s.vs_memory
Proof
  strip_tac >> irule captured_memory_holds >> gvs[vv_post_def] >>
  qexists_tac `cenv` >> simp[]
QED

(* Feasibility report, source checked 2026-11-06.

   1. INITIALIZATION (not all-history initialization).
   bodyPtrDefs:296-326's expr_vv_sim_ptr has ONE gas_outcome_ptr normal post
   containing vv_post. Applying captured_memory_post to that same normal
   endpoint (ee,t,G,tn), with result=PlaceR(MemoryPlace id path), yields
     ?v w. read_result cx (PlaceR(MemoryPlace id path)) ee = (INL v,ee) /\
           eval_operand p.ptr_operand t = SOME w /\
           val_in_memory tv v (w2n w) t.vs_memory.
   Thus this is an EXISTING successful read, not merely conditional on one.
   It works if read_memory_path selected initial popped history as well as
   the current entry. No empty-history assumption is needed. In contrast,
   vv_at (loweringPosts:356-374) supplies val_wf and containment only
   conditional on successful read and evaluated type. It does not give
   source-place address identity or future representation.
   Empty trusted=[] plus opaque=entry.popped provides NO shielding via
   HistoryPrefix: its successful-read premise is false on []. Initialization
   of the captured read comes from vv_holds, not from prefix shielding.

   2. ONE CURRENT OR HISTORICAL POP (exact proposed observation, not a theorem).
   Fix captured result r, type tvc, and evaluated address wc. At source E and
   target T the initial formula is
     read_result cx r E = (INL vc,E) /\
     val_in_memory tvc vc (w2n wc) T.vs_memory.
   After the actual pop_place transition E -> E' and target length-header
   store T' = mstore (base+k) (n2w(LENGTH vs-1)) T, the required observation is
     !vc'. read_result cx r E' = (INL vc',E') ==>
           val_in_memory tvc vc' (w2n wc) T'.vs_memory.
   When read_result is unchanged, a sufficient explicit frame is
     !addr. w2n wc <= addr /\ addr < w2n wc+type_memory_size tvc ==>
       (if addr < LENGTH T'.vs_memory then EL addr T'.vs_memory else 0w) =
       (if addr < LENGTH T.vs_memory then EL addr T.vs_memory else 0w).
   Existing val_in_memory_mem_agree consumes this (with typing/wf).
   This sufficient reserved-window frame is NOT necessary: captured parent
   and historical children overlap reserved capacity. If captured r denotes
   the changed owner, vc' differs and owner_path_pop_header reconstructs it
   instead. If r denotes a child just removed, current_path_pop_header gives
   its LAST representation at the old address; record_pop/read_popped must
   separately relate that child to r. For a historical-owner Pop, replace_popped
   updates the first successful suffix owner; owner_path_pop_header applies
   only given THAT owner's representation, not from the one captured read
   alone. No representation of a larger ancestor follows from a child read.

   Nested-row test: HistoryLayoutProbe.first_pop_history_layout represents
   current [[7,8]] at b and captured row [9,10] at b+128. The next historical
   row Pop stores 1 at b+128. The old-row unchanged-value/frame claim is
   false (its header is now 1, not 2); shortened_history_layout instead
   represents [9] at b+128 and 10 at b+192. Its already checked
   pop_header_store_observations proves the scalar at b+192 and first row
   words unchanged. Thus a restricted read-sensitive invariant is necessary;
   neither immutable captured values nor disjoint reserved owners suffice.

   3. SAME-WITNESS e2 CALLBACK (missing strengthened contract).
   For every captured r,tvc,wc and e2 start E1,T1,G1,tn1 satisfying the
   ordinary input premises of expr_sim_ptr_def, plus
     ?vc. read_result cx r E1=(INL vc,E1) /\
          val_in_memory tvc vc (w2n wc) T1.vs_memory,
   the proposed callback needs gas_outcome_ptr of eval_expr cx e2 from
   (E1,T1,G1,tn1), with ALL the existing expr_sim_ptr normal post clauses
   conjoined with
     !vc'. read_result cx r E2=(INL vc',E2) ==>
           val_in_memory tvc vc' (w2n wc) T2.vs_memory.
   Here E2,T2,G2,tn2 are exactly that callback's normal endpoint; one must
   not combine a second existential execution to obtain this observation.
   This formula is only a requirement for feasibility analysis: r must in
   addition carry real retained-place identity or non-owned/owned buffer
   classification. Arbitrary r,wc satisfying the initial formula can alias
   changed unrelated bytes and are not justified protected observations.

   bodyPtrDefs:expr_sim_ptr_def and expr_vv_sim_ptr_def contain no such
   captured-r quantifier. Their expr_post/vv_post only represent e2's own
   result; their old-allocation frame (loweringPosts:386-390) excludes the
   local regions containing historical rows. locals_kept and ghost_kept
   preserve address/provenance facts, not these bytes. vv_holds_vars_frame
   (exprSimVVFrame:44-55) requires unchanged memory AND unchanged source es;
   it cannot handle this Pop. The frozen premise body_expr_ptr_ok cx e2
   therefore supplies an ordinary counted callback, not this strengthened
   post. compile_subscript's base-before-index, length-after-index sequence
   is recorded in ConsumerContract:166-175. First required extra step is
   exactly this refreshed representation at the index endpoint.

   VERDICT: initialization of the captured result's OWN read is available
   on e1's counted witness. All initial history need not be represented.
   However that observation alone cannot initialize larger historical owners
   that a later Pop can select. General e2 effect closure is NOT authorized:
   request ancestor strategy review for a restricted producer induction with
   explicit address/ownership classification and current/history read update
   rule. Ordinary callback projection is insufficient. No concrete frozen
   target counterexample is established by this diagnostic.
*)
