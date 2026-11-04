(* Arithmetic interface probes for allocation-relative pointer transport.
   No state relation is defined by this diagnostic. *)
Theory lowerDloadRelocationBoundary
Ancestors
  arithmetic words

Theorem site_translation_comparisons:
  !b c sz x y:num.
    b <= x /\ x <= b + sz /\ b <= y /\ y <= b + sz ==>
    ((c + (x - b) = c + (y - b)) <=> (x = y)) /\
    ((c + (x - b) < c + (y - b)) <=> (x < y)) /\
    c <= c + (x - b) /\ c + (x - b) <= c + sz
Proof
  rpt strip_tac >> decide_tac
QED

Theorem site_translation_word_value:
  !b c sz x:num.
    b <= x /\ x <= b + sz /\ c + sz < dimword (:256) ==>
    w2n (n2w (c + (x - b)) : 256 word) = c + (x - b)
Proof
  rpt strip_tac >> simp[] >>
  `c + (x - b) < dimword (:256)` by decide_tac >>
  simp[LESS_MOD]
QED

(* C1.10 INTERFACE PROPOSAL -- NOT A DEFINITION OR A PROVED SIMULATION.

   Existing alloca_remap_rel cannot be used unchanged: it equates alloca
   domains and memory lengths, uses strict containment for pointers, and
   compares allocation bytes without the source taint mask. LowerDload adds
   private sites, permits one-past comparisons, and leaves new-site bytes
   tainted. A new paired-frame predicate is therefore necessary if this
   simulation route is retained. The following is input for strategy review.

   Proposed HOL signature (all auxiliary names below are schematic):

     ld_pair : num -> venom_context -> venom_context -> venom_state ->
       call_frame list -> (num # num) option list ->
       (string,num # num) fmap -> taint -> ir_function -> instruction ->
       venom_state -> venom_state ->
       ((num # num), (num # num # num)) fmap ->
       (string,num # num) fmap -> (num # num) option list ->
       (((string,num # num) fmap # (num # num) option list) list) ->
       num -> num -> bool

   Parameters, in order: lo,C,C',vs0,stk,PG,G,tn,fn,inst,s,t,A,H,Q,K,
   frame_serial,phase. A maps allocation identity (frame serial, source
   inst_id) to (source base,target base,size). H maps current source variable
   names to identities; Q gives parameter identities; K stores suspended
   callers' H,Q pairs in the same order as stk. The serial is a fresh
   activation identity, NOT call depth (siblings reuse depth). phase is an
   expansion position, with zero meaning a synchronized original boundary.
   A contains only allocations belonging to active or suspended frames;
   discarded callee records are removed on return, never used for live bytes.

   Required conjuncts, to be made precise by the strategist before defining:

   1. frame_reachable vs0 C stk PG G tn fn inst s; length K = length stk.
      The target control point is the pass image of this source point at
      phase zero, or the indicated ALLOCA/ADD/CODECOPY/MLOAD expansion point.
      Previous labels agree. Target variables introduced by the pass are
      unrestricted except for the expansion-phase scratch/data-offset facts.
   2. Current source alloca map entries have A entries with identity
      (frame_serial,aid), equal size and recorded source base; the target
      map has the corresponding original aid at the recorded target base.
      Its extra entries are exactly already-executed private DLOAD sites.
      Apply the analogous condition to each suspended caller's saved maps.
      Zero-sized identities remain distinct even when all three numbers in
      their A records coincide. For a reused original site, reuse its A
      entry rather than extending the frontier a second time.
   3. FDOM H = FDOM G. If H(v)=k and A(k)=(b,c,n), then G(v)=(b,n).
      Q erases via A's source projection to PG; likewise saved H,Q erase to
      cf_prov,cf_params. H propagates the SELECTED identity through
      ASSIGN/ADD/SUB/PHI, not an inverse lookup by (b,n). PARAM uses Q.
      All syntactic pointer-derived variables that currently have values
      must have identities; this completeness needs a separate proof from
      fn_ptr_ok (it must not be assumed from FDOM H = FDOM G alone).
   4. Original variable domains agree. For every bound original v with no
      H entry, word_agree_except (op_taint tn (Var v)) (s.vars v) (t.vars v).
      With H(v)=k and A(k)=(b,c,n), require the modular equation
         t.vars v = s.vars v + n2w c - n2w b : bytes32.
      Do NOT require unsigned containment except at accesses/comparisons.
      Parameter vectors obey the corresponding Q relation. No provenance
      is fabricated for scalar values or returned values.
   5. For i < lo outside tn.t_mem, read_byte i s.memory = read_byte i t.memory.
      For every active/suspended A(k)=(b,c,n) and j<n, if b+j NOTIN tn.t_mem,
      read_byte (b+j) s.memory = read_byte (c+j) t.memory.
      No memory length equality, no condition on discarded/reclaimed sites,
      and no condition on private scratch contents at phase zero. Private
      scratch intervals are disjoint from all positive-size observable
      A intervals and the fixed region. Source live intervals and target
      live intervals are separately disjoint and below their frontiers.
   6. Non-memory state: contexts, data section, labels, code, fmp,
      call_entry_fmp, initial_fmp, return_pc_token, prev_hashes, halted,
      returndata, logs, outcomes, pending_deletions agree at synchronized
      points. Accounts agree outside tn.t_stor in the current address's
      storage, all other account fields agree; transient at current address
      agrees outside tn.t_trans and all other addresses agree; immutables
      have equal domains and word_agree_except with key_taint tn.t_imm.
      Requests are paired with their snapshot mask captured when issued
      (not the current tn); dead_wf/taint_within permit using the existing
      request_agree_except D instead if D is added to the signature.
      This choice is an OPEN interface issue for review, not an assertion
      that current-mask agreement implies historical agreement.
   7. t.alloca_next = s.alloca_next + 32*q for an existential q bounded by
      ctx_dload_count C; each saved frame has its own saved q/frontiers.
      Charge scratch to distinct DLOAD ids in distinct active functions.
      callee_first must justify that no active function repeats. All live
      endpoints are <= their frame frontier and the target frontier is
      < dimword(:256), derived from source dload_headroom_ok. This includes
      the strict endpoint bound needed for one-past word comparisons.

   Coverage/feasibility table (paper checks, not preservation theorems):

   Initial entry: s=t modulo entry PC; A contains identity mappings for
   initial vs_allocas, H=FEMPTY,Q=[],K=[]. Existing initial sites need their
   own serial even though no source variable yet carries them. Initial
   bytes equal. q=0. Must check initial map validity from o1_run_state_ok.

   New original ALLOCA: append (serial,aid)->(s.next,t.next,size); advance
   both frontiers by size. Newly allocated bytes need not agree: new_site_bytes
   taints them. Already allocated ALLOCA just returns recorded bases.
   Keeping zero sites explicit makes this operation independent of size.

   Private DLOAD scratch: only target map/frontier grows by 32, q increments
   once per site; identity relation on source variables unchanged. Scratch
   starts at target frontier and hence misses all mapped live regions.
   Expansion-phase facts must specify scratch CODECOPY bytes before MLOAD;
   no boundary memory equality for scratch is needed. At DLOADBYTES use the
   existing destination identity; there is no scratch allocation.

   Caller push: setup_callee clears vs_allocas and vars but INHERITS the
   frontier (it does not reset it to fmp). Save H,Q and caller maps in K;
   Q'=MAP identity_of_operand ops, H'=FEMPTY. Keep caller A entries live.
   New activation gets fresh serial; source frame_reachable supplies PG'.
   INVOKE taint rule forbids tainted arguments; pointer arguments relocate.

   Caller pop: merge_callee_state copies memory/accounts/etc, but restores
   saved caller vars/params/allocas/alloca_next. Delete callee A/scratch;
   restore saved H,Q and q; remove return-output H entries as frame_reachable
   removes cf_prov outputs. Returned pointer escape must be excluded by
   ptr_use_ok, rather than assuming returned words are scalar. Source
   taint's memory/storage components persist, saved variable taint restores.

   Revert forwarding: access_ok intentionally supplies NO read/write site
   containment. Prove target remains syntactically in_revert_forward and
   use that disjunct of inst_mem_ok_in_fn, retaining the frontier bound.
   No later synchronized continuation is needed after REVERT/Abort; only
   RETURNDATACOPY's next REVERT boundary must be covered. Do not transport
   exempt accesses using ordinary relocation bounds.

   Arithmetic representability: site_translation_comparisons includes
   closed endpoints and equality/order. To use it for words need both
   b+sz < dimword(:256) and c+sz < dimword(:256), and actual operands in
   those closed intervals; site_translation_word_value proves target
   representability. General ADD/SUB uses modular equations, not this fact.

   Outstanding diagnostic issues: initial alloca-map wellformedness,
   provenance completeness (including PARAM/PHI), returned-value exclusion,
   historical request masks, distinct active-function scratch charging, and
   target-prefix phase coverage require explicit reviewed boundaries. This
   proposal alone does not lower the parent simulation's design risk.
*)
