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
