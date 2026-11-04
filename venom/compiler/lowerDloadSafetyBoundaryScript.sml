(* Safety-only observation boundaries for the LowerDload memory contract. *)
Theory lowerDloadSafetyBoundary
Ancestors
  o1PassContract unitTransformDefs unitShapeDefs lowerDloadRelocationBoundary
  ptrDiscipline finite_map list fcgDefs

Theorem lower_dload_initial_allocations:
  o1_run_state_ok s ==>
  s.vs_allocas = FEMPTY /\ s.vs_vars = FEMPTY /\ s.vs_memory = [] /\
  ~s.vs_halted /\ s.vs_fmp = s.vs_initial_fmp
Proof
  simp[o1_run_state_ok_def, o1_initial_state_ok_def]
QED

Theorem shape_retpc_operand_boundary:
  fn_shape_ok fn /\ retpc_var fn x /\ MEM inst (fn_insts fn) /\
  MEM (Var x) inst.inst_operands ==>
  inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PHI \/
  (MEM inst.inst_opcode [RET; RETFMP; DRET] /\
   ?front. inst.inst_operands = front ++ [Var x] /\ ~MEM (Var x) front)
Proof
  strip_tac >>
  `opaque_use_ok fn` by gvs[fn_shape_ok_def] >>
  drule_all opaque_use_ok_retpc_use >>
  simp[retpc_use_ok_def]
QED

(* C1.11.a consumer inventory (semantic definitions, not proof consumers).

   vs_requests: consume_call_outcome -> record_request appends rq (or leaves
   the list alone for computed precompiles); merge_callee_state copies it.
   No semantic helper selects from it or tests its length/content. It may
   be omitted from a safety-only relation; no historical taint mask needed.

   vs_logs: LOG appends an event; extract_venom_result appends new logs;
   consume_call_outcome/adopt_outcome appends oracle logs on success;
   merge_callee_state copies. No semantic consumer branches on old logs or
   imports them into accounts, transient state, operands or call input.
   make_venom_call_state/make_venom_create_state create fresh subcontexts,
   not subcontexts seeded with vs_logs. Omit historical logs for safety.

   vs_pending_deletions: consume_call_outcome/adopt_outcome_deletions prepend
   the oracle's co_toDelete on successful nonstatic calls; merge copies.
   Never inspected by a Venom instruction (no finalization inside run_context).
   May be omitted for safety, not for observational equivalence.

   vs_outcomes: consume_call_outcome calls take_outcome, which inspects the
   head on noncomputed calls, choosing success, returndata, account state
   and transient state. This field MUST remain related (equality suffices).
   Computed precompiles leave it unchanged. Equal outcomes alone is not
   enough: request target/data/static and relevant snapshot state still
   require their own input boundaries. Historical requests are not inputs
   to take_outcome. No numerical pointer is stored in an oracle queue by
   the LowerDload expansion.

   vs_return_pc_token: initialized from LAST args by setup_callee, read ONLY
   by RETPC_PARAM, restored from saved caller by merge_callee_state, and
   untouched by adopt_return_fmp. RETPC_PARAM places it in an ordinary
   variable, hence omission needs opaque-variable treatment, not blanket
   equality of untainted variables. shape_retpc_operand_boundary checks
   that all statically token-derived uses are ASSIGN, PHI or the UNIQUE
   final operand of RET, RETFMP or DRET. RET evaluates its operand list but discards its final
   value with FRONT; it does not compare that value to any continuation.
   Numeric token values therefore need not agree, but definedness and
   propagation through selected copy/phi still must be in the relation.
   This restriction does NOT permit ignoring PARAM: a LAST args value read
   through PARAM uses the ordinary scalar/pointer relation, not opacity.

   Initial state: lower_dload_initial_allocations proves the map is EMPTY,
   not merely wellformed; identity initialization needs no initial sites.
   o1_run_state_ok by itself gives NO numerical bound on vs_alloca_next.
   It only constrains that field via downstream reachable-state premises
   in o1_src_inv (raw/headroom) and ptr_discipline's initial lo bound. A
   target-entry proof must use those premises and entry reachability,
   rather than invent an extra initial frontier assumption.

   Sources inspected: venomExecSemantics definitions exec_alloca,
   step_inst_base, extract_venom_result, setup_callee, merge_callee_state,
   adopt_return_fmp and call/create state constructors; venomCallOracleDefs
   consume_call_outcome and venom_call_request; extCallOracle take_outcome,
   record_request, adopt_outcome and adopt_outcome_deletions. State helper
   eval_operand/eval_operands read vars/labels, never historical fields.
   Full projected-step preservation is deliberately NOT claimed here.
*)

Theorem provenance_operand_erasure:
  !e H op. op_prov (e o_f H) op = OPTION_MAP e (op_prov H op)
Proof
  Cases_on `op` >> simp[op_prov_def, FLOOKUP_o_f] >>
  rpt gen_tac >> Cases_on `FLOOKUP H s` >> simp[]
QED

Theorem provenance_arguments_erasure:
  !e H ops.
    MAP (op_prov (e o_f H)) ops = MAP (OPTION_MAP e) (MAP (op_prov H) ops)
Proof
  Induct_on `ops` >> simp[provenance_operand_erasure]
QED

Theorem provenance_phi_erasure:
  !e H prev inst.
    phi_prov prev (e o_f H) inst = OPTION_MAP e (phi_prov prev H inst)
Proof
  rpt gen_tac >> Cases_on `prev` >> simp[phi_prov_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >>
  simp[provenance_operand_erasure]
QED

Theorem provenance_return_erasure:
  !e H outs.
    e o_f (DRESTRICT H (COMPL (set outs))) =
    DRESTRICT (e o_f H) (COMPL (set outs))
Proof
  rpt gen_tac >> simp[fmap_eq_flookup] >> gen_tac >>
  Cases_on `x IN set outs` >> simp[FLOOKUP_o_f, FLOOKUP_DRESTRICT]
QED

Theorem provenance_param_erasure:
  !e Q H inst s idx.
    inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] ==>
    out_prov (MAP (OPTION_MAP e) Q) (e o_f H) inst s =
    OPTION_MAP e (out_prov Q H inst s)
Proof
  rpt strip_tac >> simp[out_prov_def] >>
  Cases_on `w2n idx < LENGTH Q` >> simp[EL_MAP]
QED

(* C1.11.b selected-identity feasibility equations.

   Represent an identity by num#num (activation serial, source aid). Choose
   a TOTAL erasure e : (num#num)->(num#num) for the currently live identities;
   e(serial,aid)=(source base,size). A total map is harmless outside selected
   identities, where it is not used. Maintain G=e o_f H and
   PG=MAP (OPTION_MAP e) Q. This does not invert e. Zero-sized identities
   can be distinct even when e maps them to the same pair.

   PARAM: the selected identity output is EL (w2n idx) Q when in bounds,
   NONE otherwise. provenance_param_erasure proves the corresponding
   out_prov equation. Scalar arguments at declared pointer positions use
   NONE, not an arbitrary site; static pointer membership need NOT imply
   dynamic identity presence. Invalid indices do not produce a successor.

   PHI: use resolve_phi prev operands to select exactly the same operand
   in H as in G. provenance_phi_erasure proves the selection equation.
   At an entry run all PHIs in parallel from H0, updating output identities
   from selected H0 operands; scalar selected alternatives stay NONE.
   No domain completeness assumption on syntactic pointer variables is valid.

   Caller push: for Var v select FLOOKUP H v, otherwise NONE, exactly
   op_prov H. provenance_arguments_erasure gives the PG erasure equation.
   Save H,Q alongside cf_prov,cf_params. This permits scalar arguments to
   declared pointer positions without inventing identities.

   Return: DRESTRICT H (COMPL (set inv.inst_outputs)); restore saved Q.
   provenance_return_erasure checks this commutes with G erasure. Returned
   results have no selected identity. That is sound only if pointer-valued
   operands cannot be ordinary return values: fn_ptr_ok/ptr_use_ok forbids
   syntactic pointer-derived variables in RET (RET has no mem access operand
   and is not pointer-preserving). The final opaque RETPC_PARAM-derived
   operand instead uses shape_retpc_operand_boundary and is discarded by RET.

   Needed completeness shape, NOT proved here: each bound original variable
   is either (a) selected H identity with modular pointer agreement, (b)
   retpc_var fn with arbitrary but defined opaque word, or (c) scalar with
   word_agree_except its source taint. If a variable is not syntactically
   pointer-derived it cannot have a selected identity. The converse fails:
   pointer-declared PARAM may receive a scalar, and selected PHI may select
   such a scalar. Thus G=e o_f H suffices for source provenance erasure but
   must be accompanied by this dynamic VALUE classification in a relation.
   ASSIGN and scalar-selected PHI preserve (c); affine ADD/SUB needs the
   existing fn_ptr_ok affine_pointer_ops restriction for (a). Opaque copies
   are handled independently of pointer identity; overlap of static classes
   requires checking the chosen priority, not demanding both word equations.

   These equations validate the proposed ghost interface only. They are not
   a provenance-completeness induction or a paired execution proof.
*)

Theorem list_precedes_transitive:
  !xs x y z.
    list_precedes x y xs /\ list_precedes y z xs ==>
    list_precedes x z xs
Proof
  simp[list_precedes_iff] >> rpt strip_tac >> gvs[] >>
  qexistsl_tac [`i`, `j'`] >> simp[] >> decide_tac
QED

Theorem list_precedes_distinct:
  !xs x y. list_precedes x y xs ==> x <> y
Proof
  simp[list_precedes_iff] >> rpt strip_tac >> gvs[]
QED

(* C1.11.c stack charging and prefix interface diagnostic.

   Strict stack invariant proposed for frame_reachable vs C stk PG G tn fn i s:
     EVERY (\f. MEM f.cf_fn C.ctx_functions) stk /\
     MEM fn C.ctx_functions /\
     (!k. k < LENGTH stk ==>
         list_precedes fn.fn_name (EL k stk).cf_fn.fn_name names) /\
     (!j k. j < k /\ k < LENGTH stk ==>
         list_precedes (EL j stk).cf_fn.fn_name
                       (EL k stk).cf_fn.fn_name names).
   Stack order is most recent caller first; function names increase with
   stack index. On call, callee_first gives callee BEFORE current caller,
   not after. list_precedes_transitive propagates this to older frames;
   list_precedes_distinct excludes recursive active-name reuse. On return
   remove the active callee and the top caller record, restoring that caller.
   Membership must come from lookup_function and context shape, not from
   list_precedes alone. A general frame_reachable stack invariant remains
   to be proved; these two checked order lemmas validate its order boundary.

   Scratch accounting: for each active frame f keep E_f, the set of DLOAD
   source ids whose private ALLOCA has already executed successfully in f.
   Charge q = SUM (MAP CARD E_f) over the active frame and suspended callers.
   Current frontier equation t.next = s.next + 32*q uses ALL these charges,
   because setup_callee inherits the current frontier. Each suspended caller
   separately stores its prefix q_at_push and its two saved frontiers.
   - first scratch at d: E_f'=E_f UNION {d}, q'=q+1;
   - reused scratch at d: E_f'=E_f, q'=q;
   - new original ALLOCA: both frontiers increase by identical size, q'=q;
   - push: E_new={}, q'=q, new frame map empty;
   - pop: restore caller saved frontiers and q_at_push, discard callee E;
     this is NOT subtraction from an arbitrary current cumulative count.
   Distinct active names and per-function distinct source ids give injection
   of charged pairs into context DLOAD occurrences, hence q<=ctx_dload_count C.
   Repeated sibling calls reuse bytes but do not accumulate active charges.
   Headroom at the matching source state gives t.next<dimword(:256).

   Target phase table (positions BEFORE executing active instruction).
   Let source inst d be active in frame_reachable at s; let p be its lowered
   start index, with fresh vars a,z and fresh ids ai,zi,ci,mi from supply.
   For DLOAD [off] [out]:
     phase 0: index p,   ALLOCA ai [32] [a]; source witness s before d.
       Frontier equation with current E, scratch may already be allocated.
     phase 1: index p+1, ADD zi [off;Label code_end] [z]; same source s.
       Scratch has recorded base c and size 32, c+32<=t.next; E includes d.
     phase 2: index p+2, CODECOPY ci [a;z;32] []; same source s.
       eval a=n2w c, eval z=n2w (off+code boundary), source offset bound
       prevents code-address wrap. Scratch disjointness/taint masks retained.
     phase 3: index p+3, MLOAD mi [a] [out]; same source s.
       Scratch now contains the 32 bytes read by source DLOAD; its read
       access is below frontier even before proving output equality.
     successor: source executes d OK s', target executes MLOAD OK t';
       compare successor indices and step_taint/provenance at phase 0.
   For DLOADBYTES [dst;off;n]:
     phase 0: p, ADD [off;Label code_end] [z], witness before source d.
     phase 1: p+1, CODECOPY [dst;z;n], same source s, computed z bound;
       dst is translated by selected identity or is fixed-region scalar;
       source access_ok supplies destination site containment when needed.
     successor: source DLOADBYTES OK s', target CODECOPY OK t', phase 0.
   Other instructions: phase 0 only. Malformed expansion envelopes are
   unchanged by supply, but context shape should exclude them; do not infer
   shape solely from the opcode. Structural origin uses C1.1 facts.

   Prefix induction required by mem_inv_raw_reachable is raw_reachable_ind
   in contextRawReachable, instantiated at the TARGET context and vs0.
   Its four rules are entry, next (including atomic successful INVOKE),
   block, and callee. A next rule with INVOKE steps an entire callee run,
   so stack-phase reasoning alone is insufficient: successful callee-run
   preservation must be a separate boundary, typically by fuel induction.
   Alternative: establish frame_reachable target coverage then prove its
   erasure covers raw_reachable, including that atomic INVOKE-next rule.
   Source-to-target terminating simulation does not imply either route.
   At every phase, prove raw_mem_ok at the active state even if its next
   step errors; an Error has no successor but the current access still
   belongs to raw_reachable. A matched source error cannot justify skipping
   target active-state safety. For source progress at the final phase need
   operand agreement/definedness, not merely successful target execution.

   Outstanding precise boundary: simultaneous target fuel/run coverage
   and prefix induction with explicit caller restoration, plus general
   active-stack order/charge preservation. No such theorem is asserted by
   this finite phase and arithmetic diagnostic.
*)

(* C1.11.d SPECIFICATION DRAFT, for architecture review only.
   Supersedes the schematic C1.10 proposal; NOTHING BELOW IS A DEFINITION.

   Exact types used in this draft (record declarations are proposals only):

   ld_site = num # num
   ld_alloc = (ld_site, num # num # num) fmap
   ld_frame = <| lf_serial:num; lf_supply:ir_supply; lf_fn:ir_function;
                 lf_src:venom_state; lf_tgt:venom_state;
                 lf_H:(string,ld_site) fmap; lf_Q:ld_site option list;
                 lf_E:num set; lf_tv:(string,num set) fmap |>

   A frame list F has active frame HD F, then most-recent saved caller.
   Saved source/target states are PRE-INVOKE snapshots, not copies of current
   memory. Only the active pair supplies current memory/accounts/taint.
   N:num is the next activation serial; all lf_serial are <N and distinct.
   Sigma:string->ir_supply is a fixed function-level supply witness. Its
   obligation is (!fn. MEM fn C.ctx_functions ==> MEM
     (FST(lower_dload_function_supply (Sigma fn.fn_name) fn))
     C'.ctx_functions), with function-name lookup uniqueness and configured
   freshness additionally established from the stage. This is an explicit
   outstanding structural obligation, not a consequence of arbitrary Sigma.

   All abbreviations below have equations; HOL type abbreviations and the
   proposed record above are meta-notation, not changes to existing types.

   erase A k = case FLOOKUP A k of SOME(b,c,n) => (b,n) | NONE => (0,0)
   charge F = SUM (MAP (\f. CARD f.lf_E) F)
   image f = FST(lower_dload_function_supply f.lf_supply f.lf_fn)

   envelope u fn s j X p <=>
     ?bb bi ub ui.
       bi < LENGTH fn.fn_blocks /\ EL bi fn.fn_blocks = bb /\
       bb.bb_label = s.vs_current_bb /\ j < LENGTH bb.bb_instructions /\
       ub = SND(lower_dload_blocks_supply u (TAKE bi fn.fn_blocks)) /\
       ui = SND(lower_dload_insts_supply ub (TAKE j bb.bb_instructions)) /\
       X = FST(lower_dload_inst_supply ui (EL j bb.bb_instructions)) /\
       p = LENGTH(FST(lower_dload_insts_supply ub
                        (TAKE j bb.bb_instructions)))
   Here u:ir_supply, fn:ir_function, s:venom_state, j,p:num,
   X:instruction list. The configured block/inst supplies, not legacy
   arithmetic ids, define both positions and private sites.

   private f d ai <=>
     ?bb j bi ub ui inst X.
       bi < LENGTH f.lf_fn.fn_blocks /\ EL bi f.lf_fn.fn_blocks = bb /\
       j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = inst /\
       inst.inst_id = d /\ inst.inst_opcode = DLOAD /\
       (?op out. inst.inst_operands=[op] /\ inst.inst_outputs=[out]) /\
       ub = SND(lower_dload_blocks_supply f.lf_supply
                                          (TAKE bi f.lf_fn.fn_blocks)) /\
       ui = SND(lower_dload_insts_supply ub (TAKE j bb.bb_instructions)) /\
       X = FST(lower_dload_inst_supply ui inst) /\
       LENGTH X = 4 /\ ai = (HD X).inst_id

   wordrel A k x y <=>
     case k of NONE => x=y
       | SOME a => ?b c n. FLOOKUP A a = SOME(b,c,n) /\
                          y = x + n2w c - n2w b
   (x,y:bytes32). Absence of identity means scalar for parameters, NOT an
   arbitrary site. For variables the no-identity case uses their taint.

   vars A f <=>
     DRESTRICT f.lf_tgt.vs_vars (set(fn_ir_vars f.lf_fn)) =
       DRESTRICT f.lf_tgt.vs_vars (FDOM f.lf_src.vs_vars) /\
     FDOM f.lf_src.vs_vars SUBSET set(fn_ir_vars f.lf_fn) /\
     (!v. v IN set(fn_ir_vars f.lf_fn) ==>
       (v IN FDOM f.lf_src.vs_vars <=> v IN FDOM f.lf_tgt.vs_vars)) /\
     FDOM f.lf_H SUBSET FDOM f.lf_src.vs_vars /\
     (!v x y. FLOOKUP f.lf_src.vs_vars v = SOME x /\
               FLOOKUP f.lf_tgt.vs_vars v = SOME y ==>
       if retpc_var f.lf_fn v then T
       else case FLOOKUP f.lf_H v of
         SOME a => wordrel A (SOME a) x y
       | NONE => word_agree_except
           (case FLOOKUP f.lf_tv v of NONE=>{} | SOME m=>m) x y) /\
     LENGTH f.lf_src.vs_params = LENGTH f.lf_tgt.vs_params /\
     (!j. j < LENGTH f.lf_src.vs_params ==>
       wordrel A (if j < LENGTH f.lf_Q then EL j f.lf_Q else NONE)
         (EL j f.lf_src.vs_params) (EL j f.lf_tgt.vs_params))

   This chooses opaque priority on the static intersection of retpc_var
   and pointer variables. No numeric relation is required for a token.
   H still has to erase to source G even for such a variable. Preservation
   must prove that no nonopaque consumer can receive an opaque value.

   maps A f <=>
     FINITE f.lf_E /\
     (!d. d IN f.lf_E ==> ?ai. private f d ai) /\
     (!aid b n. FLOOKUP f.lf_src.vs_allocas aid = SOME(b,n) ==>
       ?c. FLOOKUP A (f.lf_serial,aid) = SOME(b,c,n) /\
           FLOOKUP f.lf_tgt.vs_allocas aid = SOME(c,n)) /\
     (!ai c n. FLOOKUP f.lf_tgt.vs_allocas ai = SOME(c,n) ==>
       (?b. FLOOKUP f.lf_src.vs_allocas ai = SOME(b,n) /\
             FLOOKUP A (f.lf_serial,ai) = SOME(b,c,n)) \/
       (n=32 /\ ?d. d IN f.lf_E /\ private f d ai)) /\
     (!d ai. d IN f.lf_E /\ private f d ai ==>
       ?c. FLOOKUP f.lf_tgt.vs_allocas ai = SOME(c,32))

   slots A F = {k | ?f aid b c n.
     MEM f F /\ k=(f.lf_serial,aid) /\
     FLOOKUP f.lf_src.vs_allocas aid=SOME(b,n) /\
     FLOOKUP A k=SOME(b,c,n)}

   intervals lo s <=>
     (!aid b n. FLOOKUP s.vs_allocas aid=SOME(b,n) ==>
        lo<=b /\ b+n<=s.vs_alloca_next) /\
     (!a b n a' b' n'.
       FLOOKUP s.vs_allocas a=SOME(b,n) /\
       FLOOKUP s.vs_allocas a'=SOME(b',n') /\ a<>a' /\ 0<n /\ 0<n' ==>
       b+n<=b' \/ b'+n'<=b)

   memory lo A tn s t <=>
     (!i. i<lo /\ i NOTIN tn.t_mem ==>
          read_byte i s.vs_memory=read_byte i t.vs_memory) /\
     (!k b c n j. FLOOKUP A k=SOME(b,c,n) /\ j<n /\
                    b+j NOTIN tn.t_mem ==>
          read_byte (b+j) s.vs_memory=read_byte (c+j) t.vs_memory)

   nonghost tn s t <=>
     s.vs_call_ctx=t.vs_call_ctx /\ s.vs_tx_ctx=t.vs_tx_ctx /\
     s.vs_block_ctx=t.vs_block_ctx /\ s.vs_returndata=t.vs_returndata /\
     s.vs_outcomes=t.vs_outcomes /\ s.vs_data_section=t.vs_data_section /\
     s.vs_labels=t.vs_labels /\ s.vs_code=t.vs_code /\
     s.vs_fmp=t.vs_fmp /\ s.vs_call_entry_fmp=t.vs_call_entry_fmp /\
     s.vs_initial_fmp=t.vs_initial_fmp /\ s.vs_prev_hashes=t.vs_prev_hashes /\
     s.vs_halted=t.vs_halted /\
     FDOM s.vs_immutables=FDOM t.vs_immutables /\
     (!k x y. FLOOKUP s.vs_immutables k=SOME x /\
               FLOOKUP t.vs_immutables k=SOME y ==>
        word_agree_except (key_taint tn.t_imm k) x y) /\
     (!a. (s.vs_accounts a with storage := (t.vs_accounts a).storage) =
            t.vs_accounts a /\
       storage_agree_except
         (if a=s.vs_call_ctx.cc_address then tn.t_stor else {})
         (s.vs_accounts a).storage (t.vs_accounts a).storage) /\
     (!a. storage_agree_except
         (if a=s.vs_call_ctx.cc_address then tn.t_trans else {})
         (s.vs_transient a) (t.vs_transient a))

   No equation for logs/requests/deletions/return_pc_token. This omission
   is intentional and limited to the consumer inventory at lines 28-84.

   sync lo C vs0 stk PG G tn fn inst s t A F N <=>
     F<>[] /\ (HD F).lf_fn=fn /\ (HD F).lf_src=s /\
     (HD F).lf_tgt=t /\ (HD F).lf_tv=tn.t_var /\
     frame_reachable vs0 C stk PG G tn fn inst s /\
     active_inst fn inst s /\
     LENGTH F=SUC(LENGTH stk) /\
     G=erase A o_f (HD F).lf_H /\
     PG=MAP (OPTION_MAP (erase A)) (HD F).lf_Q /\
     ALL_DISTINCT (MAP (\f. f.lf_serial) F) /\
     EVERY (\f. f.lf_serial<N /\ maps A f /\ vars A f /\
       intervals lo f.lf_src /\ intervals lo f.lf_tgt /\
       f.lf_src.vs_prev_bb=f.lf_tgt.vs_prev_bb /\
       f.lf_src.vs_current_bb=f.lf_tgt.vs_current_bb /\
       MEM f.lf_fn C.ctx_functions) F /\
     FDOM A=slots A F /\
     (!j. j<LENGTH F ==>
       (EL j F).lf_tgt.vs_alloca_next =
       (EL j F).lf_src.vs_alloca_next + 32*charge(DROP j F)) /\
     (!j. j<LENGTH F ==>
       ?X p. envelope (EL j F).lf_supply (EL j F).lf_fn
                     (EL j F).lf_src (EL j F).lf_src.vs_inst_idx X p /\
             (EL j F).lf_tgt.vs_inst_idx=p) /\
     (!j. j<LENGTH stk ==>
       (EL j stk).cf_fn=(EL (SUC j) F).lf_fn /\
       (EL j stk).cf_state=(EL (SUC j) F).lf_src /\
       (EL j stk).cf_prov=erase A o_f (EL (SUC j) F).lf_H /\
       (EL j stk).cf_params=
         MAP (OPTION_MAP (erase A)) (EL (SUC j) F).lf_Q /\
       (EL j stk).cf_tvar=(EL (SUC j) F).lf_tv) /\
     charge F<=ctx_dload_count C /\
     memory lo A tn s t /\ nonghost tn s t

   The continuation below supplies the global interval, phase and coverage
   clauses. All names above and below are specification-only; no transport
   theorem is claimed by writing their equations.
*)

(* C1.11.d continued: exact global and phase equations.

   sites F source = {(j,aid,b,n) | ?f.
     j<LENGTH F /\ f=EL j F /\
     FLOOKUP (if source then f.lf_src.vs_allocas else f.lf_tgt.vs_allocas)
       aid=SOME(b,n)}
   (source:bool; j,aid,b,n:num).

   global lo A F <=>
     (!source j aid b n. (j,aid,b,n) IN sites F source ==>
       lo<=b /\ b+n <=
         (if source then (HD F).lf_src.vs_alloca_next
                    else (HD F).lf_tgt.vs_alloca_next)) /\
     (!source j aid b n j' aid' b' n'.
       (j,aid,b,n) IN sites F source /\
       (j',aid',b',n') IN sites F source /\
       (j,aid)<>(j',aid') /\ 0<n /\ 0<n' ==>
       b+n<=b' \/ b'+n'<=b) /\
     (!f a. MEM f F /\
       (a IN FRANGE f.lf_H \/ MEM (SOME a) f.lf_Q) ==> a IN FDOM A)

   prefix C' fn' X p h t0 t <=>
     h<LENGTH X /\ ?R.
       LENGTH R=SUC h /\ HD R=t0 /\ LAST R=t /\
       (!j. j<h ==> ?u.
         active_inst fn' (EL j X) (EL j R) /\
         step_inst 0 C' (EL j X) (EL j R)=OK u /\
         EL (SUC j) R=(u with vs_inst_idx:=SUC(p+j))) /\
       active_inst fn' (EL h X) t
   (X:instruction list; R:venom_state list; p,h:num).
   Prefix uses fuel 0 only for proper expansion prefixes, which never contain
   INVOKE. If X=[inst] then h=0 and no step is asserted. Intermediate states
   are related to the SAME sync pre-state, rather than pretending that the
   source has already executed DLOAD. This is an explicit finite execution
   equation, not an uninterpreted phase predicate. In particular it includes
   the CODECOPY bytes at phase 3 through the actual semantic update.

   pair lo names Sigma C C' vs0 fn' ti t <=>
     ?stk PG G tn fn inst s t0 A F N X p h.
       sync lo C vs0 stk PG G tn fn inst s t0 A F N /\
       global lo A F /\
       EVERY (\f. f.lf_supply=Sigma f.lf_fn.fn_name) F /\
       (!j k. j<k /\ k<LENGTH F ==>
         list_precedes (EL j F).lf_fn.fn_name
                       (EL k F).lf_fn.fn_name names) /\
       fn'=image(HD F) /\
       envelope (HD F).lf_supply fn s s.vs_inst_idx X p /\
       prefix C' fn' X p h t0 t /\ ti=EL h X
   Signature: num -> string list -> (string->ir_supply) ->
     venom_context -> venom_context -> venom_state -> ir_function ->
     instruction -> venom_state -> bool.
   This is the proposed safety relation, not a simulation definition added
   to the project. It existentially carries selected identities, finite
   expansion history, suspended callers, and a reachable source witness.
   No output/log/history equality is silently embedded in it.

   Exact phase cases implied by prefix and lower_dload_inst_supply:
     DLOAD proper envelope: LENGTH X=4, h=0,1,2,3 respectively;
     DLOADBYTES proper envelope: LENGTH X=2, h=0,1 respectively;
     unchanged envelope: LENGTH X=1 and h=0.
   Raw safety is required at EVERY h, not just at the final prefix state.
   At h=0 the frontier is sync's saved frontier; at h>0 for DLOAD it is
     t0.next + (if d IN (HD F).lf_E then 0 else 32).
   The scratch record, computed ADD and copied bytes are specified by prefix,
   not independent existential guesses. The prefix semantic consequences
   are still outstanding boundary lemmas, including the displayed frontier
   equation and its no-wrap conclusion from dload_headroom_ok.

   Ghost transition equations (not extra assumptions on the frozen theorem):
   - ALLOCA at original aid, successful fresh allocation at b,c,size n:
       A' = A |+ ((serial,aid),(b,c,n)); E'=E.
     On reuse A'=A. The exact maps clause decides reuse without inverse lookup.
   - Complete DLOAD d:
       E'=E UNION {d}; A'=A.
     H'=set_prov H inst.inst_outputs NONE; Q'=Q. Other provenance updates
     use the selected operations given below, never numeric inversion.
   - PARAM output: set_prov H outs
       (if w2n idx<LENGTH Q then EL (w2n idx) Q else NONE).
   - ASSIGN/ADD/SUB output: set_prov H outs (first_prov H operands).
   - Other non-PHI original outputs, except ALLOCA:
       set_prov H outs NONE.
   - New/reused ALLOCA output: set_prov H outs (SOME(serial,aid)).
   - PHIs: phis_prov prev H0 bb.instructions, with parallel input H0.
     These existing polymorphism-free num#num functions apply to identities
     because an identity has exactly the existing provenance pair type.
   - Call: retain all old A entries; push a new active record with
       serial=N, H=FEMPTY, Q=MAP(op_prov Hcaller) ops, E={}, tv=FEMPTY,
       fn=callee, supply=Sigma callee.fn_name,
       src/tgt=the successful enters_block results of setup_callee.
     Old active record becomes the saved PRE-INVOKE record, N'=SUC N.
     Source stk is extended by frame_reachable_call's exact record.
   - Return: discard HD F, restoring the next frame f. Restrict A to
       {k | FST k <> (HD F).lf_serial};
     H'=DRESTRICT f.lf_H (COMPL(set inv.inst_outputs)), Q'=f.lf_Q,
     E'=f.lf_E, tv'=DRESTRICT f.lf_tv (COMPL(set inv.inst_outputs)).
     Replace f's src/tgt with the corresponding bind_outputs results after
     merge_callee_state/adopt_return_fmp and increment each saved PC to its
     own next original/lowered boundary. No charge subtraction is used:
     charge(TL F) is exactly the restored saved suffix charge.
     The memory relation uses current (post-callee) tn.t_mem, not saved tv.
   These equations describe ghost choices; source step_taint and source
   frame_reachable remain authoritative for all source masks and witnesses.

   Initialization and consumer proof-obligation table:

   Entry | lower_dload_initial_allocations supplies empty maps, vars, memory;
     choose A=FEMPTY, H=FEMPTY,Q=[],E={},serial=0,N=1,F=[entry record].
     Paired enters_block/PHI and configured envelope preservation OUTSTANDING.
     Source entry raw/headroom and ptr_discipline.lo supply frontier bounds;
     never infer a frontier bound from o1_run_state_ok alone.
   Site lookup/zero sites | maps/global plus provenance_*_erasure equations;
     general selected-identity and disjointness preservation OUTSTANDING.
   Scalar/address/control consumer | vars and wordrel, taint_ok/access_ok;
     numerical operand/range transport OUTSTANDING. Word translation and
     closed-interval comparisons have checked arithmetic helpers. Nonempty
     comparison sites must be shown to select the same A identity using
     positive size and global source disjointness, not assumed from e.
   Opaque operand | shape_retpc_operand_boundary checked; ASSIGN/PHI and
     token-definedness transport OUTSTANDING. PARAM uses Q, never opacity.
   Allocation access | maps/global and source raw/headroom; frontier and
     scratch charge preservation OUTSTANDING. list_precedes transitivity
     and distinctness checked, full stack membership/order OUTSTANDING.
   Load/store/copy | memory and source masks; per-op byte/taint transport
     OUTSTANDING. All live frames use current tn.t_mem. Private scratch is
     disjoint by global and below the prefix frontier by ALLOCA semantics.
   External effects | nonghost with source taint_ok excludes tainted call
     inputs; input equality and oracle-state preservation OUTSTANDING.
     Historical observation omission has the diagnostic inventory above,
     not a checked projected-step theorem.
   Revert-forward | need transformed syntactic revert_forward_at boundary;
     OUTSTANDING. Do not demand access_ok containment of exempt accesses.
   Return | exact pop equations above; ordinary return words must agree
     because ptr_use_ok excludes pointers and taint_ok excludes taint;
     opaque final token is dropped by FRONT. Full result boundary OUTSTANDING.

   Exact target-prefix theorem requested for this relation:
     assumptions of lower_dload_stage_mem, a chosen lo from ptr_discipline,
     and the structural Sigma witness imply
       !fn' ti t. raw_reachable vs0 C' fn' ti t ==>
                   pair lo names Sigma C C' vs0 fn' ti t.
   Follow separately with
       pair ... fn' ti t ==> raw_mem_ok C' fn' ti t
   with the same source premises (in particular raw/headroom invariants).
   Both are OUTSTANDING. The first is TARGET-to-source coverage, including
   every state before a failing instruction. Source progress is not replaced
   by an assertion that matching target executions terminate.

   Required induction boundary for atomic INVOKE-next:
     Given sync at a target INVOKE, if step_inst fuel C' inv t0=OK u,
     produce a source frame_reachable return witness followed by the source
     ret rule and a new sync at the incremented caller PCs. The source
     successful-return witness has the form
       frame_reachable vs0 C (f::stk) PG G tn fn rinst s /\
       active_inst fn rinst s /\
       step_inst fsrc C rinst s=IntRet ret s_end,
     with ret.iret_values equal to the target internal return values and
     ret.iret_adopt_fmp related by equality of the optional returned FMP field.
     Use memory/nonghost on final states and the pop equation to rebuild sync.
     Prove this with the target run_defs mutual well-founded induction:
       (fuel,run_blocks), (fuel,exec_block remaining instructions),
       (fuel,step_inst), as ordered in run_defs's termination proof.
     Expansion prefixes consume only exec_block instruction rank; nested
     INVOKE consumes run_blocks fuel; block recurrence decreases fuel.
     At IntRet, establish the source reachable ret witness rather than
     demanding source run_blocks with the target's exact fuel.
     Halt/Abort/Error do not yield an atomic next successor. Their ACTIVE
     prefixes still require safety; these outcomes must not be skipped by
     the run-coverage induction. Raw callee-entry rule uses push directly.

   REVIEW GATE: This draft has exact relation equations, but no definition,
   no typechecked interface, and no preservation proof. In particular the
   atomic call boundary is a substantial additional induction, not a lemma
   certified by the previous finite phase diagnostic. C1 remains Risk 3.
*)
