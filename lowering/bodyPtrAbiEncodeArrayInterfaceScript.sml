(* Finite array/interface diagnostic, C1.4.17.6.11.
   No execution theorem, admitted skeleton or new predicate is installed here.
   This leaf records the interface to be reviewed before array implementation. *)
Theory bodyPtrAbiEncodeArrayInterface
Ancestors
  bodyPtrAbiEncodeBytesContract bodyPtrAbiEncodeOperand bodyPtrAbiEncodeSlice
  abiEncoderWindowArray abiEncoderWindowArrayInvariant abiEncoderWindowArrayLoop
  abiEncoderWindowArrayEntry abiEncoderWindowArrayExit

(* Proposed invariant I(active,j,s,G,tn), by textual expansion only:

   window_array_inv ctx fn owner ids ei asz msz active ty avs src (Var dst)
     (Var ip) isite islot dp dsite dslot count_op label B K D j s /\
   j <= LENGTH avs /\ LENGTH avs < dimword(:256) /\
   E = LENGTH(enc (Array NONE ty) (ListV avs)) /\ E <= C /\
   D+C <= dimword(:256) /\ B+K <= dimword(:256) /\ E < dimword(:256) /\
   ptr_covers G tn dst s C /\
   (?q. src=Var q /\ ptr_covers G tn q s K) /\
   (!i. B <= i /\ i < B+K ==> i NOTIN tn.t_mem) /\
   op_taint tn count_op = {} /\
   ptr_covers G tn ip s 32 /\
   (!i. islot <= i /\ i < islot+32 ==> i NOTIN tn.t_mem) /\
   (active ==> ?q. dp=Var q /\ ptr_covers G tn q s 32 /\
      (!i. dslot <= i /\ i < dslot+32 ==> i NOTIN tn.t_mem)) /\
   window_array_cursor T owner (Var pp) psite pb 0 B K D E s /\
   ptr_covers G tn pp s 32 /\
   (!i. pb <= i /\ i < pb+32 ==> i NOTIN tn.t_mem) /\
   psite NOTIN ids /\ isite <> psite /\
   (active ==> dsite <> psite /\ dsite <> isite) /\
   fresh_vars_wrt limit s /\ ~ctx_has_dalloca ctx /\
   (!i. D <= i /\ i < D+32 ==> i NOTIN tn.t_mem) /\
   (!i. D+32 <= i /\ i < D+32+j*asz ==> i NOTIN tn.t_mem) /\
   (active ==>
     (!i. D+32+LENGTH avs*asz <= i /\
          i < D+32+LENGTH avs*asz+
                SUM(MAP (abi_member_tail_size ty) (TAKE j avs)) ==>
          i NOTIN tn.t_mem)).

   Variables E,C,K and root compilation bounds are fixed across iterations;
   label is hdr/body/exit according to boundary. At an array entry, K>=32
   and E>=32 even if avs=[]; so unlike zero-footprint complex, Var sources
   and positive root provenance follow from the Operand boundary. owner
   must be AFTER cursor setup, so saved count/ip/dp/pp/root variables are
   all not_fresh_at owner; require them explicitly before using old-frame
   transport. ids is the loop's ACTUAL allocation sites, not its instruction
   IDs. It excludes psite, but includes isite/dsite where enabled.

   In addition to I, each whole-phase result must provide the following
   relational F(a,s,G,tn,t,H,un,sites,writes):
     (!q. not_fresh_at a q ==>
        lookup_var q t=lookup_var q s /\ FLOOKUP H q=FLOOKUP G q /\
        op_taint un (Var q)=op_taint tn (Var q)) /\
     abi_encoder_registered_effect sites writes s t /\
     window_alloca_growth s t /\ alloca_inv t /\ alloca_room ctx fn t /\
     abi_encoder_extend_sim ctx fn s t /\ t.vs_labels=s.vs_labels /\
     (!id b n. id IN sites /\ FLOOKUP t.vs_allocas id=SOME(b,n) ==> n=32) /\
     mem_agree_outside W s.vs_memory t.vs_memory /\
     (!i. i NOTIN W ==> (i IN un.t_mem <=> i IN tn.t_mem)).
   W expands exactly as in BytesContract: union of listed output intervals
   and endpoint registered regions for sites. F has no existential semantic
   witness. Prefix semantics, control, freshness, and cleanliness must hold
   at the SAME t as gas_path_ptr. The old-frame parameter a is phase-specific:
   use owner around a whole iteration, ready around the recursive child;
   never protect header/body temporary variables as older than owner.

   Boundary statements to implement, all free parameters universally quantified:

   HEADER:
     I(active,j,s,G,tn) at hdr /\ header block code lookup /\
     body/exit block lookups /\ phi_prefix_length body_insts=0 /\
     phi_prefix_length exit_insts=0 /\
     (!x. not_fresh_at owner x ==> x<>iv /\ x<>cmp /\ x<>done)
     ==> ?t H un. gas_path_ptr gasD 0 ctx fn PG G tn s 0 H un (OK t) /\
         I(active,j,t,H,un) at (if j<LENGTH avs then body else exit) /\
         t=jump_to (if j<LENGTH avs then body else exit)
              (abi_encode_array_header_state iv cmp done j (LENGTH avs) s) /\
         F(owner,s,G,tn,t,H,un,{},[]).
   Code is exactly abi_encode_array_header_insts id (Var ip) count_op
   iv cmp done body exit, as in window_array_header_step. MLOAD index
   needs ip coverage/clean cell; LT and ISZERO give clean booleans; JNZ
   needs clean done operand. jump_to has no PHIs by these premises; derive
   the pointer jump edge and ghost endpoint, not just semantic transition.

   STATIC ROUND:
     I(F,j,s,G,tn) at body /\ j<LENGTH avs /\ loop body code /\
     final compiler bound <= limit /\ static_info element resource contract
     ==> ?t H un. counted path s/G/tn -> t/H/un /\
         I(F,SUC j,t,H,un) at hdr /\
         F(owner,s,G,tn,t,H,un,{isite},[(D+32+j*asz,asz)]).
   The actual sequence is index MLOAD, src ADD32/MUL/ADD, dst ADD32/MUL/ADD,
   static_info, index ADD1/MSTORE/JMP. Admissibility must prove ei is
   PrimWord or Copy: static_info otherwise returns zero without encoding.
   Source child window K_j<=msz and 32+j*msz+K_j<=K comes from
   window_array_root_live_pre; output E_j=asz. Slice root coverage to E_j,
   and source coverage/cleanliness to K_j. Arithmetic products must not
   wrap; window/source bound proves j*msz, output bound proves j*asz.
   With asz=0 the endpoint ADDs still run and Copy may emit zero MCOPY;
   do not infer positive access from an ADD-produced Var. Return to hdr
   after index store; j+1<=N<dimword ensures clean correct counter.

   DYNAMIC ROUND:
     I(T,j,s,G,tn) at body /\ j<LENGTH avs /\ loop body code /\
     final compiler bound <= limit /\ child resource contract R for ei
     ==> ?t H un. counted path s/G/tn -> t/H/un /\
         I(T,SUC j,t,H,un) at hdr /\
         F(owner,s,G,tn,t,H,un,
           body_sites UNION {isite;dsite},
           [(D+32+j*asz,32);(D+32+off_j,E_j)]).
   off_j=N*asz+SUM(MAP (abi_member_tail_size ty) (TAKE j avs)),
   E_j=LENGTH(enc ty (EL j avs)), child destination D+32+off_j.
   Prefix: clean index, source slice, covered head slot, clean cursor load,
   covered tail destination. Apply R with C_j=E_j, independent K_j.
   Suffix: MSTORE head offset, ADD child length to off_j, MSTORE dp,
   ADD1/MSTORE ip, JMP hdr. Child older frame is at ready, preserving
   head_pos, dyn_ofst, ip, dp, count and parent pointer. Clean length
   and off_j yield clean next cursor. Child scratch site exclusions must
   prove isite,dsite,psite NOTIN body_sites using window_array_body_sites
   with its actual owner/counter/code equalities; name freshness alone
   does not imply allocation-site exclusion. Source/prefix/cursor bytes
   are disjoint from child output and actual scratch. Frame memory AND
   taint with W, not just abi_encoder_registered_effect.

   LOOP (both cases, after setup):
     I(active,j,s,G,tn) at hdr /\ header premises /\
     (!k u J vn. k<N /\ I(active,k,u,J,vn) at body ==>
        ?v L wn. counted round path /\ I(active,SUC k,v,L,wn) at hdr /\
                 corresponding F)
     ==> ?t H un. counted path s/G/tn -> t/H/un /\
         I(active,N,t,H,un) at exit /\ cumulative F.
   Prove by complete induction on N-j, composing header, round, IH.
   The terminal header executes too. For N=0 there is no round or element
   read, but all setup, header and exit accesses still execute. The resource
   interface must keep limit fixed while counters/temporary values repeat;
   fresh_vars_wrt limit means variables at/above limit remain absent, not
   that body temporaries below limit are absent on every iteration.

   ENTRY:
     to_buf P for AbiDynArray ei asz msz active /\ compile decomposition
     ==> ?s1 G1 tn1. counted entry path /\ I(active,0,s1,G1,tn1) at hdr /\
         F(st,s,G,tn,s1,G1,tn1,entry_sites,[(D,32)]).
   Entry allocates pp32, writes zero, loads source count, stores destination
   count; allocates ip32 and writes zero; active additionally allocates
   dp32 and writes N*asz. Then JMP header. Must establish pp/ip/dp registered
   distinct sites, clean cells, covered pointers, count/root saved Vars,
   owner/compiler-code counters and resource bounds. Fresh allocations
   are outside old windows; reuse must use the actual-site precondition.
   Source count is a clean MLOAD even when N=0. No child provenance is
   needed until the loop takes a body edge. Initial prefix=count only.

   EXIT/PARENT FINISH:
     I(active,N,s,G,tn) at exit /\ actual exit+finish code /\
     final compiler bound <= limit
     ==> ?t H un. counted path /\ root R for AbiDynArray at t /\
         mem_word_at pb t.vs_memory=n2w E.
   Static exit reloads source count, multiplies by asz, adds 32.
   Dynamic exit ALSO emits a source count MLOAD (unused), then loads dp,
   adds 32. Preserve clean source/count across every body for that load.
   Both then MLOAD pp (zero), ADD size, MSTORE pp, MLOAD pp. Coverage pp32
   and clean cell are needed independently of output coverage. pp zero
   must survive loop effects: psite exclusion, registered alloca_inv and
   live-output disjointness give memory preservation; exterior taint frame
   gives clean cell. Finish adds psite to the scratch effect/write set.
   Semantic array_prefix_complete supplies bytes only once the prefix at
   N is shown at the very same counted endpoint. Root R is BytesContract's
   proposed expansion, not an already established theorem.

   Mutual assembly / missing proof assignments:
   - Compiler mutual recursion supplies child to_buf resource contracts,
     never runtime iterations. Use N-j induction internally for loops.
   - Distinguish compile_abi_encode_static_info from recursive to_buf;
     establish its admissible base contract once using primitive/Copy.
   - Prove root P entry -> I0 and I_N -> root R separately from rounds.
   - Full parent results remain same-endpoint primitive/Copy/empty/bytes,
     child, member, complex, static-array, dynamic-array and final mutual
     encoder contract. No step here establishes any of those results.
   - Missing caller implications include actual code/ID/phi bounds, byte
     cleanliness of structural prefixes, all K_j slices, arithmetic strict
     no-wrap, parent-site exclusion, and actual allocation effects. These
     require executable proof leaves, not a further unbounded comment audit.
   Source references: defs/abiEncoder 191-224,281-302,339-382;
   WindowArrayInvariant 106-149,191-204; WindowArrayLoop 274-366;
   WindowArray 101-116,296-310. No claim of frozen-target falsehood.
*)
