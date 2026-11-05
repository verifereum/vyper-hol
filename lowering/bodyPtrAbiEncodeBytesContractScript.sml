(* Explicit bytes instance of the recursive encoder resource interface. *)
Theory bodyPtrAbiEncodeBytesContract
Ancestors
  bodyPtrAbiEncodeBytesPhases bodyPtrAbiEncodeBytesMemory
  bodyPtrAbiEncodeRecursiveFrame bodyPtrAbiEncodeCursorFrame bodyPtrDefs
  abiEncoderMemory abiDecoderContract abiEncoderRounding abiEncoderInput abiEncoderBytes
  valueEncodingProps
  compileEnv exprLoweringProps emitHelperProps venomState venomExecSemantics
  ptrDiscipline words arithmetic finite_map pred_set

Theorem abi_encode_bytes_frame_projection:
  abi_encode_read_frame st
    (mcopy db sb (32+cnt) (mstore (db+rounded) 0w s)) G
    (tn with t_mem := tn.t_mem DIFF {i | db+rounded <= i /\ i < db+rounded+32}
       DIFF {i | db <= i /\ i < db+(32+cnt)}) t H un /\
  cnt <= rounded ==>
  (!q. not_fresh_at st q ==>
    lookup_var q t = lookup_var q s /\ FLOOKUP H q = FLOOKUP G q /\
    op_taint un (Var q) = op_taint tn (Var q)) /\
  mem_agree_outside {i | db <= i /\ i < db+(32+rounded)} s.vs_memory t.vs_memory /\
  (!i. ~(db <= i /\ i < db+(32+rounded)) ==> (i IN un.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  `abi_decode_frame db (32+rounded) s
    (mcopy db sb (32+cnt) (mstore (db+rounded) 0w s))` by
    (irule abi_encoder_bytes_write_frame >> simp[]) >>
  qpat_x_assum `abi_encode_read_frame _ _ _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [abi_encode_read_frame_def] >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `!q. not_fresh_at st q ==> _` mp_tac >>
      simp_tac (srw_ss()) [mcopy_def, mstore_def, write_memory_with_expansion_def,
        lookup_var_def, op_taint_def, LET_THM]) >>
  conj_tac
  >- (simp_tac (srw_ss()) [mem_agree_outside_def] >> rpt strip_tac >>
      fs[abi_decode_frame_def] >> sym_tac >> first_x_assum irule >> decide_tac) >>
  fs[] >> rpt strip_tac >> simp[] >> decide_tac
QED

Theorem abi_encode_bytes_contract_path:
  !total.
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) st = (out,en) /\
  abi_encoder_input (AbiBytestring maxlen) at (contractABI$BytesV bs) (w2n a) cap s.vs_memory /\
  (w2n a+cap <= w2n b \/ w2n b+(32+contractABI$ceil32 (LENGTH bs)) <= w2n a) /\
  not_fresh_at st dst /\ not_fresh_at st src /\
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
  ptr_covers G tn dst s total /\ ptr_covers G tn src s (32+LENGTH bs) /\
  (!i. w2n a <= i /\ i < w2n a+(32+LENGTH bs) ==> i NOTIN tn.t_mem) /\
  LENGTH bs+31 < dimword(:256) /\ 32+LENGTH bs < dimword(:256) /\
  32+LENGTH bs <= total /\ contractABI$ceil32 (LENGTH bs)+32 <= total /\
  w2n b+contractABI$ceil32 (LENGTH bs) < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?p t H un. out = Var p /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    lookup_var p t = SOME (n2w (LENGTH (enc at (contractABI$BytesV bs)))) /\
    op_taint un (Var p) = {} /\ not_fresh_at en p /\
    ptr_covers H un dst t total /\
    (!i. w2n b <= i /\ i < w2n b+LENGTH (enc at (contractABI$BytesV bs)) ==> i NOTIN un.t_mem) /\
    mem_bytes_at (w2n b) (LENGTH (enc at (contractABI$BytesV bs))) t.vs_memory =
      enc at (contractABI$BytesV bs) /\
    abi_decode_frame (w2n b) (LENGTH (enc at (contractABI$BytesV bs))) s t /\
    fresh_vars_wrt limit_st t /\ t.vs_inst_idx = s.vs_inst_idx+10 /\
    (!q. not_fresh_at st q ==> lookup_var q t = lookup_var q s /\
      FLOOKUP H q = FLOOKUP G q /\ op_taint un (Var q) = op_taint tn (Var q)) /\
    mem_agree_outside
      {i | w2n b <= i /\ i < w2n b+(32+contractABI$ceil32 (LENGTH bs))}
      s.vs_memory t.vs_memory /\
    (!i. ~(w2n b <= i /\ i < w2n b+(32+contractABI$ceil32 (LENGTH bs))) ==>
      (i IN un.t_mem <=> i IN tn.t_mem))
Proof
  gen_tac >> strip_tac >>
  `mload (w2n a) s = n2w (LENGTH bs) /\ 32+LENGTH bs <= cap /\
   (at = Bytes NONE \/ at = String)` by
    (fs[abi_encoder_input_bytes_iff, mem_word_at_eq_mload]) >>
  drule_all abi_encode_bytes_checked_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `w2n a+(32+LENGTH bs) <= w2n b \/
   w2n b+(32+contractABI$ceil32 (LENGTH bs)) <= w2n a` by decide_tac >>
  qpat_assum `abi_encode_read_frame st _ G _ t H un`
    (mp_then Any mp_tac abi_encode_bytes_memory_result) >>
  disch_then (qspecl_then [`maxlen`, `cap`, `at`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `LENGTH bs <= contractABI$ceil32 (LENGTH bs)` by simp[abi_encoder_ceil32_bounds] >>
  drule_all abi_encode_bytes_frame_projection >> strip_tac >>
  `LENGTH (enc at (contractABI$BytesV bs)) = 32+contractABI$ceil32 (LENGTH bs)` by
    metis_tac[abi_encoder_bytes_encoding] >>
  qexistsl_tac [`p`, `t`, `H`, `un`] >> asm_rewrite_tac []
QED

(* Recursive resource-interface audit (C1.4.17.6.6).
   This is a call-site table, NOT a theorem asserting invariant closure.
   References are to the current source definitions, not an S1 path lift.

   Notation used only in this comment:
   E = LENGTH (enc at av), C = reserved output capacity, B = source base,
   K = source-read capacity, D = destination base.  A child uses E_i,K_i.
   All nonempty windows additionally need no-wrap and coverage.  For every
   call at compiler state r, saved Vars must be not_fresh_at r; the counted
   child must preserve lookup_var, provenance and op_taint of all such Vars.
   A common limit state must bound the final cs_next_var and remain fresh.
   Protected windows must be disjoint from the ENTIRE reserved child output
   and every actual child ALLOCA site, including reused sites.  Allocation
   growth by itself does not establish the reused-site disjointness.

   Branch/call table: defs/abiEncoderScript.sml 180-382
   * AbiPrimWord (251-253): K>=32, E=32, C>=32; load source word then store
     destination word; no scratch.  window_word_contract (WindowLeaves)
     supplies semantics only; existing counted primitive boundaries supply
     edges, not the complete recursive frame post automatically.
   * AbiCopy sz (276-279): K>=sz, E=sz, C>=sz; MCOPY uses Lit(n2w sz),
     returned length is literal.  sz=0 is still an emitted MCOPY; whether its
     operands need coverage follows the zero-access instruction rule, not
     the empty-complex return rule.  Source/destination may be endpoints.
   * AbiBytestring (255-274): n=LENGTH bs, K>=32+n, E=32+round_up_32 n,
     C>=E; zero last word at D+round_up_32 n then copy 32+n bytes.  Even n=0
     accesses 32 bytes on both sides.  abi_encode_bytes_contract_path above gives
     same-endpoint counted semantics, full destination coverage and exterior
     memory/taint plus older-variable frame, for Var src/dst.  Its source
     capacity is not E and need not include padding.
   * AbiComplex [] (304-305): E=0, K can be 0, no instruction, return Lit 0.
     No provenance may be demanded merely to return that literal.
   * AbiComplex nonempty (307-337): H=SUM member head sizes.  If dynamic,
     allocate 32-byte dyn_ptr, initialize H, traverse members, reload cursor;
     otherwise use Lit 0 as dyn_ptr, traverse and return Lit(n2w H).
     Member i source = B+span(TAKE i infos), where span sums mem_sz, and
     K_i<=mem_sz_i with span+K_i<=K.  head offset h sums abi_sz.  elem_src
     is ALWAYS ADD-produced Var, even offset zero.  Child dst is described
     next.  Remainder recursion keeps original dst/src and cursor, NOT a
     sliced source operand.  Protect source, completed head/tails and cursor.
   * Static child (236-238): ADD-produced static_loc at D+h, recurse there
     with child_ptr.  Can choose C_i=E_i (or a proven disjoint larger slice),
     need h+E_i<=C.  No dyn_ptr read, so Lit 0 passed by static complex is
     inert.  E_i=0 still emits address ADD but must not require memory access.
   * Dynamic child (240-247): load off from 32-byte dyn_ofst_ptr, child_dst
     is ADD-produced Var at D+off, recurse, then store off at D+h and
     off+E_i back to cursor.  Need off+E_i<=C, h+32<=C, clean off and E_i,
     coverage of child suffix and saved head slot/cursor after recursion.
     Choose C_i=E_i to avoid reserving a suffix overlapping protected siblings;
     choosing C-off needs a separate proof of all protected disjointness.
     Child exterior frame protects cursor and head when disjoint from child
     output and child scratch sites.  Source K_i comes from parent window.
   * AbiDynArray entry (281-302): ALWAYS allocate parent_dyn_ptr (32 bytes),
     initialize zero, MLOAD source count N, MSTORE destination count, run
     loop, then load/update/load parent cursor.  Thus K>=32 and C>=32 even
     N=0.  Parent cursor must be protected across the complete loop.
   * Static-element loop (191-225): allocate i_ptr (32 bytes); index j;
     source child B+32+j*msz with K_j<=msz and 32+j*msz+K_j<=K;
     destination D+32+j*asz with E_j=asz.  Need C>=32+N*asz.
     Calls static_info, not recursive to_buf: admissibility must select
     PrimWord or Copy.  Both child addresses are ADD-produced Vars.
     Preserve clean count, root operands, i_ptr and parent_dyn_ptr; increment
     index, JMP, reload count at exit, return 32+N*asz.  Empty loop still
     initializes/loads cursor and branches, but never reads a child.
   * Dynamic-element loop (339-382): allocate i_ptr and dyn_ptr (32 each).
     off_j=N*asz+SUM tails(TAKE j avs), child source as above, destination
     D+32+off_j; head slot D+32+j*asz.  Need
       32+off_j+E_j<=C, 32+j*asz+32<=C, and C>=E(array).
     Recurse on ADD-produced Var/Var with C_j=E_j; preserve head slot,
     i_ptr, dyn_ptr, parent_dyn_ptr, completed encoded prefix and source.
     Suffix stores off_j, off_j+E_j, j+1 then backedge; exit returns
     32+off_N.  Register only actual ALLOCA sites, excluding outer cursors.

   Semantic interfaces actually available:
   abiEncoderWindowScript.sml window_input rules 8-54 and *_iff theorems
   give EXACT K_i bounds above, without pointer provenance or taint facts.
   abiEncoderWindowContractScript.sml abi_encoder_window_pre (9-29) asks
   disjointness only for LIVE E, NOT reserved C; its alloca reuse clauses
   range over actual opcode ALLOCA and require sz=32.  window_strong_contract
   (207-213) produces window_strong_result; projections
   window_strong_result_effect/growth/sizes (247-267) give registered effects
   on window_alloca_sites, growth, 32-byte sizes, but NOT counted pointer paths.
   abiEncoderWindowComplexScript.sml window_complex_strong_contract (378):
     (!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> window_strong_contract ei)
     ==> window_strong_contract (AbiComplex infos).
   abiEncoderWindowArrayScript.sml window_array_strong_contract (372):
     window_strong_contract ei ==>
     window_strong_contract (AbiDynArray ei asz msz active).
   abiEncoderWindowChildScript.sml window_dynamic_child_call (331-357)
   threads prefix, child result, suffix code and saved values, but requires
   an S1 window_strong_contract and returns window_phase, NOT gas_path_ptr.
   Its Lit(n2w(D+off)) in window_pre is a specification operand, not the
   actual compiler's recursive destination.
   abiEncoderWindowArrayInvariantScript.sml window_array_inv (135-149)
   tracks semantic prefix, count, index/cursor values and root resources;
   window_array_transition_source/cursor_frame (81-103) transport memory
   windows.  Neither interface carries ghost coverage, memory cleanliness,
   saved provenance/taint, nor a common freshness limit across the backedge.

   Target entry / operand audit:
   defs/exprLoweringScript.sml 3362-3394 has three staging branches:
   singleton word allocates/stores 32-byte tmp (Var); tuple staging allocates
   type_memory_bytes cenv (TupleT arg_tys) (Var); singleton nonword unwraps.
   unwrap_value (965-978) returns an existing LocMemory operand unchanged.
   compile_name_vv (1490-1498) explicitly supplies Lit(n2w offset) for MemLoc
   and the arbitrary stored operand ptr_op for PtrVar.  Thus Var-only source
   is NOT justified for top-level recursive entry.  Operand datatype cases
   must be handled generically or eliminated by an existing validity premise;
   no unverified claim that PtrVar can contain only Vars is made here.
   All internal to_buf callers produce Var destinations; complex and array
   recursion produce Var sources.  static child passes its source through.
   The only literal recursive control operand is inactive complex dyn_ptr;
   other literals are sizes/offsets/zeros, not memory pointers created here.
   defs/builtinAbiScript.sml 44-71 allocates
     T=32+32*word_size(maxlen+mid_size), mid_size=0 or 4,
   then ADD-produces destination at buffer+32+mid_size.  Available reserved
   capacity is C=T-(32+mid_size), not T or actual E.  Need E<=maxlen<=C.
   Method-id MSTORE at buffer+32 covers 32 bytes and may overlap data start;
   it precedes recursion.  Final length MSTORE needs preserved buffer operand
   and coverage, not merely the encoder's live E-byte write footprint.

   Missing implications for strategist refinement, NOT target falsehood:
   (1) General operand (in particular MemLoc literal) input coverage/cleanliness
       boundary, including zero-capacity branch; Var-only bytes is insufficient.
   (2) Child window extraction must combine semantic K_i witnesses with root
       coverage, clean source, no-wrap and E_i output slices; live E_i capacity
       avoids unnecessarily protecting the whole remaining output suffix.
   (3) Actual scratch allocation/reuse must establish source/output/protected
       disjointness and saved cursor coverage, excluding outer cursor sites.
   (4) Prefix+IH+suffix contract closure: older-variable ghost preservation,
       clean output/length, exact exterior memory/taint frame on actual sites,
       and alloca resources must hold on ONE counted endpoint.
   (5) Array loop invariant needs counted header/backedge/exit paths, j<=N,
       clean count/index/cursors, root capacity, frame and common limit-state
       freshness in addition to S1's semantic invariant; validate both loops.
   (6) Staging establishes window_input/admissibility/source capacity and the
       literal pointer case; top-level output reservation covers full lowered
       bytestring type even when runtime encoding is short or zero.
   No induction skeleton or new predicate is introduced by this diagnostic.
*)

(* Zero-footprint / scratch reuse audit (C1.4.17.6.9).
   Exact existing checked boundaries are reused, not duplicated:
   fragExecPtr.ptr_inst_ok_mcopy_zero (431-452) proves
     eval_operand dst s=SOME a /\ eval_operand src s=SOME b /\
     op_taint tn dst={} /\ op_taint tn src={} /\ ~ctx_has_dalloca ctx
     ==> ptr_inst_ok D 0 fuel ctx fn G tn
           (mk_inst id MCOPY [dst;src;Lit 0w] []) s.
   Thus zero Copy needs evaluated clean addresses but NO provenance, even
   when they are literals.  access_ok's range obligations guard len<>0;
   MCOPY's taint_ok still requires clean operands.  Empty complex instead
   emits no instruction.  Neither case establishes positive footprint.

   Representative reused-32-byte boundary: instantiate n=32 in
   allocationPtr.reused_alloca_ptr_covers (185-207).  Its exact premises are
   FLOOKUP s.vs_allocas id=SOME(b,n) and b+n<dimword(:256); the conclusion
   gives coverage n for out in update_var out (n2w b) s under step_prov and
   step_taint, AND preserves any old ptr_covers G tn p s sz with p<>out.
   allocationPtr.reused_alloca_step (154) identifies that precise endpoint;
   reused_alloca_ghost (164) gives no new_site_bytes, G update only at out,
   and t_var update only at out to {}; reused_alloca_memory_taint (221)
   gives exact t_mem equality.  These are already general in n, so adding a
   special 32-byte theorem would duplicate them.  Memory is unchanged by
   update_var; subsequent MSTORE initialization, not ALLOCA reuse itself,
   is where protected memory/taint disjointness becomes necessary.

   Actual-site table (compiler defs/abiEncoderScript.sml):
   constructor/phase             scratch sites                 protected
   complex dynamic (311-317)     dyn_ptr, size 32                source, head/tails
   array entry (285-300)         parent_dyn_ptr, size 32         source, output
   static array loop (195-217)   i_ptr, size 32                  parent cursor
   dynamic array loop (342-374)  i_ptr,dyn_ptr, size 32 each     parent cursor
   recursive element            only its actual ALLOCA sites   outer cursors,
                                                                source,prefix
   primitive/Copy/bytes/empty    none                           source,prefix
   At each site split FLOOKUP s.vs_allocas id into NONE and SOME(b,32).
   NONE: allocationPtr.fresh_alloca_new_site_bytes/fresh_alloca_ghost,
   fresh_alloca_ptr_covers and fresh_alloca_taint_below_frontier provide the
   new-site facts; fresh_alloca_old_region_disjoint (123-133) excludes any
   old registered region using alloca_inv s.  An arbitrary protected window
   additionally needs its bytes below the initial frontier (or registered
   region coverage).  SOME: use the representative reuse boundaries above;
   later stores require regions_disjoint(protected,(b,32)) explicitly.
   Saved pointer variables must differ from out; compiler freshness, not
   allocation disjointness, must discharge that variable inequality.

   Comparison with semantic resource contracts:
   abiEncoderWindowContract.abi_encoder_window_pre (9-29) already assumes
   every reused actual ALLOCA site in frag_ids has sz=32 and is disjoint
   from source (sb,cap) and LIVE output (d,E).  It says nothing about arbitrary
   outer protected windows or extra reserved output beyond E.  The stronger
   reserved-capacity/protected invariant must either add these hypotheses or
   reserve only live E and derive cursor separation from registered sites.
   window_strong_result_effect/growth/sizes supply actual-site effects,
   growth and 32-byte sizes at the endpoint, NOT pointer ghosts or taint.
   abi_encoder_window_effect_parent (97-109) protects registered (p,n) if
   FLOOKUP s.vs_allocas parent=SOME(p,n), parent NOTIN child ids, alloca_inv t,
   registered child effect, and disjointness from child live output hold.
   alloca_site_registered_disjoint is the used distinct-site separation rule.
   window_array_body_sites (abiEncoderWindowArray 101-116) proves child body
   sites exclude parent/index/dynamic-cursor sites from the actual code and
   counter bounds: mid, mid+2, st are all NOTIN body sites.  Its premises
   include owner=mid+(if active then 5 else 2), body_end+6=loop_end,
   st<=mid and loop_end<=en plus abi_encoder_array_loop_code.  This is a
   concrete available exclusion interface, not a claim that arbitrary
   recursive fragments cannot reuse a parent's site.

   Remaining caller implications: establish matching code/counter bounds
   and registered outer cursor before applying site exclusion; transport
   alloca_inv and the allocation registrations at the counted endpoint;
   supply live-output disjointness for each protected cursor/prefix/source;
   thread clean cursor cells through initialization and child writes using
   the exterior taint frame (semantic effect_parent alone is insufficient).
   No new proof or frozen-definition change is required for this diagnostic.
*)

(* Same-endpoint contract proposal (C1.4.17.6.10, diagnostic ONLY).
   Nothing below is a theorem or a new HOL predicate. P/R/W below are textual
   abbreviations for the displayed formulae, to specify the proposed statements
   without installing an opaque recursive predicate. All free variables in each
   proposed statement are universally quantified, except endpoint witnesses.

   Resource pre P(st,en,src,dst,ei,at,av,B,K,D,C,s,G,tn,limit):
     abi_encoder_window_pre ctx fn st en (Var dst) src ei at av B K D s /\
     en.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
     ~ctx_has_dalloca ctx /\ op_taint tn src = {} /\
     op_taint tn (Var dst) = {} /\ not_fresh_at st dst /\
     D < dimword(:256) /\ B < dimword(:256) /\
     B+K <= dimword(:256) /\ D+C <= dimword(:256) /\
     LENGTH (enc at av) <= C /\ LENGTH (enc at av) < dimword(:256) /\
     (0 < C ==> ptr_covers G tn dst s C) /\
     (0 < K ==> ?q. src = Var q /\ ptr_covers G tn q s K) /\
     (!i. B <= i /\ i < B+K ==> i NOTIN tn.t_mem).
   C is capacity retained by the ghost frame; only E=LENGTH(enc at av)
   is writable. Choose C=E for recursive children. K is the semantic read
   window, not encoded size. Literal src at K=0 is permitted. Semantic pre
   already supplies the evaluated addresses, source/output disjointness,
   alloca_inv/room, code/distinct IDs, and reused scratch separation from
   source and LIVE output. P does not assert their closure under execution.

   Write set W(st,en,D,E,t) is the following set expression, not a definition:
     {i | D <= i /\ i < D+E} UNION
     {i | ?id b n. id IN window_alloca_sites fn (frag_ids st en) /\
                    FLOOKUP t.vs_allocas id = SOME(b,n) /\ b <= i /\ i < b+n}.
   Using the ENDPOINT allocation map includes fresh and reused scratch and
   avoids claiming exterior equality outside live output alone.

   Resource post R(st,en,out,at,av,D,C,s,G,tn,t,H,un,limit):
     window_strong_result ctx fn st en out at av D s t /\
     gas_path_ptr gasD 0 ctx fn PG G tn s 0 H un (OK t) /\
     op_taint un out = {} /\
     (!q. out = Var q ==> not_fresh_at en q) /\
     fresh_vars_wrt limit t /\
     (!q. not_fresh_at st q ==>
       lookup_var q t = lookup_var q s /\ FLOOKUP H q = FLOOKUP G q /\
       op_taint un (Var q) = op_taint tn (Var q)) /\
     (0 < C ==> ptr_covers H un dst t C) /\
     (!i. D <= i /\ i < D+LENGTH(enc at av) ==> i NOTIN un.t_mem) /\
     mem_agree_outside W(st,en,D,LENGTH(enc at av),t) s.vs_memory t.vs_memory /\
     (!i. i NOTIN W(st,en,D,LENGTH(enc at av),t) ==>
       (i IN un.t_mem <=> i IN tn.t_mem)).
   Exact proposed to_buf statement after textual expansion:
     compile_abi_encode_to_buf (Var dst) src ei st = (out,en) /\ P(...) ==>
       ?t H un. R(...).
   window_strong_result supplies semantic bytes/length, control endpoint,
   registered actual-site effects, alloca growth/room/invariant, sizes and
   extend_sim at THIS t. It is a required output to prove along the counted
   run, not an independently chosen semantic witness. PG and gasD are arbitrary.
   A generic ghost_inv is deliberately not asserted: callers reconstruct their
   own older-frame invariant from the displayed frame and new clean values.

   Required extra arithmetic checks before this proposal becomes executable:
   the bytes instance needs len+31<dimword, 32+len<dimword and the strict
   D+ceil32(len)<dimword. Derive from E<=C, D+C<=dimword and E<dimword
   (E=32+ceil32(len)); len<=ceil32(len). Positive PrimWord/Copy windows
   similarly have strict address bounds from positive coverage. K=0 uses
   evaluated clean addresses, never positive provenance. If window_input
   does not justify a minimal K, retain its witness and explicitly prove
   the root covers that K; do not infer it from E.

   Exact proposed child statement, using P/R expansion above:
     compile_abi_encode_child (Var dst) src ei dyn h dp st = (out,en) /\
     abi_encode_child_prefix (Var dst) h dp st = (ops,ready) /\
     compile_abi_encode_to_buf (SND(SND ops)) src ei ready = (len,child_end)
   is the DYNAMIC decomposition only. Do not require it when dyn=F.
   Dynamic pre at s: P with destination D+off and capacity E for the
   recursive call is to be established at the prefix endpoint prepared;
   at entry require evaluated clean dp at slot, ptr_covers dp 32, clean
   mem_word_at slot=n2w off, h+32<=C, off+E<=C, off+E<dimword,
   D+C<=dimword, and regions_disjoint(slot,32)(D,C).
   The parent source is disjoint from (D,C) and (slot,32). Prefix produces
   head/offset/child-destination Vars and preserves all P resources. The
   child post R is consumed to run the suffix at THE SAME t; suffix returns
   eval_operand out=n2w E, stores n2w off at D+h and n2w(off+E) at slot.
   Child scratch sites must exclude dp's registered site. The union write
   set is child W UNION [D+h,D+h+32) UNION [slot,slot+32). Post is counted
   path, freshness, older ghost frame, root C coverage, clean child output,
   clean head/cursor and exterior memory/taint outside this union. It cannot
   be R at destination D: child does not encode a complete parent at D.
   Static pre instead uses h+E<=C and child P at D+h after ONE ADD;
   dp is unused and has no resource premise. Post is R for child bytes at
   D+h with enlarged write-set relative to parent; return length E, not h+E.

   Exact member-traversal transition schema (one constructor per step):
     compile_abi_encode_complex_elems (Var dst) src (DROP k infos)
       (abi_encoder_member_span (TAKE k infos))
       (SUM(MAP (\(_,az,_,_). az) (TAKE k infos))) dp st = (out,en)
     /\ window_structural_members_inv ctx fn infos at ats avs k src (Var dst)
          dp site slot B K D st en s
     /\ the resource part of P for root infos, with current source window
     /\ clean prefix windows in window_member_prefix infos ats avs k D s.vs_memory
     /\ (EXISTS (\(_,_,_,dyn). dyn) infos ==> clean dp operand,
          ptr_covers dp 32, clean [slot,slot+32), slot registered at site)
     /\ common-limit freshness and final bound
     ==> ?t H un. counted path s/G/tn -> t/H/un /\
          window_member_prefix infos ats avs (LENGTH infos) D t.vs_memory /\
          clean completed head and tail windows /\
          (EXISTS (\(_,_,_,dyn). dyn) infos ==>
             mem_word_at slot t.vs_memory =
               n2w(window_member_tail infos ats avs (LENGTH infos))) /\
          older ghost frame, root C coverage, limit freshness /\
          registered effects, growth, alloca resources and exterior
          memory/taint outside root live output UNION actual scratch
          UNION (if dynamic then [slot,slot+32) else EMPTY).
   Here 'clean window', 'ptr_covers dp' mean respectively the explicit
   universal byte formula in P and dp=Var q /\ ptr_covers G tn q s 32.
   The semantic invariant's st/en parameter denotes REMAINING code; use
   the remaining-pre transport boundary rather than pretending the compiled
   suffix is compile_to_buf for the whole infos. Traversal returns Lit 0,
   NOT the total encoded length, so op_taint out={} is trivial; no length
   lookup post belongs to this statement. Nonempty complex reloads dp (or
   returns literal head size) afterwards to produce the to_buf length.

   Constructor premise/post map and unresolved caller implications:
   - PrimWord: window_input gives K>=32, E=32; counted load/store plus
     semantic leaf yield R with empty scratch set. Must prove source clean
     load and preserve same t; semantic existence alone is insufficient.
   - Copy: E=sz; for sz>0 take semantic K>=sz and slice to sz for MCOPY.
     For sz=0 use ptr_inst_ok_mcopy_zero on evaluated clean addresses.
     Both cases return Lit(n2w sz); exterior/older frame has no scratch.
   - Bytes: accepted abi_encode_bytes_contract_path gives same t, bytes,
     clean result and exterior frame, but NOT yet window_strong_result.
     Prove semantic control, effects, resource/growth/extend projections on
     that precise endpoint. Do not claim accepted bytes theorem equals R.
   - Empty complex: s=t, H=G, un=tn, reflexive counted path, Lit 0; C=E=0
     needs no provenance. Resource/semantic reflexivity supplies the rest.
   - Static child: ADD gives D+h and Var, slice C_i=E_i; source K_i comes
     from parent window witness, not from E_i. E_i=0 still executes ADD.
   - Dynamic child: prefix yields saved head/offset and child dst, then R
     preserves them by abi_encode_cursor_suffix_entry. Registered distinct
     sites protect cursor; W disjointness plus exterior taint protects its
     clean cell. Child live output disjointness protects head slot/prefix.
   - Member cons: ADD source B+span; semantic window yields independent
     K_i<=ms_i and span+K_i<=K. Slice coverage/cleanliness via Slice leaf;
     if K_i>0 use Operand leaf; if zero use clean evaluated endpoint.
     Current head/tail writes are disjoint from prior prefix by semantic
     structural layout, NOT merely by allocation separation. Actual scratch
     disjointness from prior output follows parent pre/live bounds and fresh
     frontier, but must be proved. Apply child then recurse at k+1.
   - Member nil: k=LENGTH infos, no instruction or write. Keep entire
     prefix and cursor, return Lit 0. No source read is authorized.
   - Complex nonempty: allocate/init cursor iff dynamic, preserve source
     and root output using actual-site resource hypotheses; enter k=0;
     after traversal load cursor or return head size. This is the closure
     of R, not just the member prefix result. C may exceed E but stores
     touch only E; old-var frame preserves C coverage without reserving C
     against scratch writes. Exterior frame advertises actual scratch too.

   Induction parameters: mutual compiler recursion supplies to_buf IHs for
   child infos; member list induction/generalization must retain k, full
   infos/ats/avs, B,K,D,C, dp/site/slot, st/en, limit, and G/tn. Endpoint
   states and counters must remain universally quantified. Compose with
   gas_path_ptr_then and older_frame_then, deriving semantic projections
   during execution, not by joining existential results afterwards.

   Review request: the formulae are an interface proposal, not validated
   recursive closure. Assign executable proof leaves for base R instances,
   same-endpoint bytes semantic resource completion, static/dynamic child
   closure, member-cons/nil transport and complex entry/exit. Array closure
   stays separate (.11). In particular the semantic structural member
   invariant alone does NOT imply clean prefixes, ghost source slices,
   clean registered cursor cells, or counted endpoints; those are explicit
   additional maintained resources, not consequences silently attributed
   to window_strong_contract. No frozen-target falsehood is claimed.
*)
