# C1.20.3 — residual joint-continuation interface proposal

Status: **proposal for exact contract ruling and producer decomposition, not a proof certificate**.
Only this document is changed. No proposed theorem below has been installed in a
Script, relied upon, parsed by HOL, or claimed true by a build. The existing
`bodyFullAugAssign.body_augassign_other_full` statement remains frozen.

## Boundary and factoring

Use the existing `augassign_rhs_invoke_full` unchanged. In particular, do not
introduce another RHS simulation theorem or a second numeric endpoint theorem.
Use `gas_outcome_full_bind_all` to connect its normal bundle to proposal A below.
A is the common *operator-to-write* continuation, not a destination theorem.
B is the deploy-immutable write callback. C is the composite-place load/read/type
endpoint; D is its write callback. B and D do not depend on A or on each other.
C is required before RHS invocation; an effectful target cannot use the pure
prefix rule. These four boundaries are subject-specific proposed new scripts:

* `lowering/augAssignFullWordContinuationScript.sml`, A;
* `lowering/augAssignFullImmutableWriteScript.sml`, B;
* `lowering/augAssignFullPlaceLoadScript.sml`, C;
* `lowering/augAssignFullPlaceWriteScript.sml`, D.

All local `let` bindings in the statements are ordinary term abbreviations,
**not** proposed HOL definitions. The displayed binders are the complete
proposed interfaces; unannotated binders use ordinary HOL type inference from
the existing constants. In particular, the actual type of `Q` in A is
```sml
((bool # bytes32 # type_value) list # num list) ->
(unit + exception) -> evaluation_state -> (string, num # num) fmap ->
taint -> venom_state -> bool
```
Here `taint` is the existing record type from `ptrDiscipline`, not a new type
alias. `H` is the pair of typed storage regions and natural lock slots,
`G/G0/Gr/Gt/Gl/Gop` have type `(string, num # num) fmap`, and
`tn/tn0/tnr/tnt/tnl/tnop` have type `taint`. These types follow from
`storage_trace_horizon_def`, `op_prov_def`, and the existing `taint` datatype.
A caller supplies the canonical normal statement post as Q. B and D
return a local framed statement post, which the caller composes with its saved
entry frame. This avoids teaching either destination producer about RHS syntax.

## A. Common word operator followed by a destination callback

The captured state `u,Gr,tnr` is **the** canonical RHS endpoint. The callback
receives a different, jointly constructed operator endpoint and exact frame
facts; it must not pretend that `expr_post ... s2 ... operated` holds at the new
cursor. The RHS post in P continues to refer to u.

```sml
Theorem augassign_word_operator_continue_full:
  !DF lo d explicit ctx func PG RetQ cenv cx st0 e ty bop ptv cur rhs p
   es sa s2 s3 s_rhs0 ee u G0 tn0 Gr tnr x y op Q.
  let P = \H.
      expr_post H ctx func cenv cx e es sa s2 s_rhs0 ee rhs y u /\
      expr_store_bound cx (post_value_type cenv e) rhs y u /\
      u.vs_current_bb = s2.cs_current_bb /\
      u.vs_inst_idx = LENGTH s2.cs_current_insts /\
      alloca_history func u /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s_rhs0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee Gr tnr u /\
      ptr_val_ok cx (post_value_type cenv e) rhs y Gr tnr u /\
      (~is_word_type (post_value_type cenv e) ==>
         ptr_buf_ok cenv e y Gr u) /\
      ghost_kept_at lo cenv es sa G0 tn0 s_rhs0 Gr tnr
  in
  let R = \H res ff gt r.
      (?ex. res = INR ex /\
        (!tail. stmt_exit_ptr (RetQ H) (ff with gas_obs := tail)
          (INR ex) gt r) /\
        halt_exit H cx ff (INR ex) r /\
        (ctx_has_dalloca ctx ==> !s.
          (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
  in
    compile_binop bop x y ty NONE
      (if bop = Exp then expr_int_literal e else NONE) s2 = (op,s3) /\
    fn_has_code s2 s3 func /\ fn_inst_ids_distinct func /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
    type_bits ty MOD 8 = 0 /\
    evaluate_type (get_tenv cx) ty = SOME ptv /\ value_has_type ptv cur /\
    (?etv. evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
           value_has_type etv rhs) /\
    word_value cur /\ word_value rhs /\
    (!n. expr_int_literal e = SOME n ==> rhs = IntV n) /\
    (bop = Exp ==> ?n. expr_int_literal e = SOME n /\ 0 <= n) /\
    (bop = ShL \/ bop = ShR ==> ?i. rhs = IntV i /\ 0 <= i) /\
    expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs ee) /\
    eval_operand x u = SOME (val_to_w256 cur) /\
    eval_operand y u = SOME (val_to_w256 rhs) /\
    op_prov Gr x = NONE /\ op_taint tnr x = {} /\
    op_prov Gr y = NONE /\ op_taint tnr y = {} /\
    (!z. x = Var z ==> not_fresh_at s2 z) /\
    (!z. y = Var z ==> not_fresh_at s2 z) /\
    (!l. x <> Label l /\ y <> Label l) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> P H) /\
    local_ptrs_reserved cenv s2 /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at s2 z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at s2 z) /\
    ~u.vs_halted /\
    (!result operated Gop tnop.
       evaluate_binop
         (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
         ptv bop cur rhs = INL result /\
       word_value result /\ value_has_type ptv result /\
       encode_value ptv result = SOME [(0,val_to_w256 result)] /\
       operated = (u with vs_inst_idx := LENGTH s3.cs_current_insts)
         with vs_vars := operated.vs_vars /\
       eval_operand op operated = SOME (val_to_w256 result) /\
       (!z. not_fresh_at s2 z ==>
         lookup_var z operated = lookup_var z u /\
         FLOOKUP Gop z = FLOOKUP Gr z /\
         op_taint tnop (Var z) = op_taint tnr (Var z)) /\
       tnop.t_mem = tnr.t_mem /\ tnop.t_stor = tnr.t_stor /\
       tnop.t_trans = tnr.t_trans /\ tnop.t_imm = tnr.t_imm /\
       op_prov Gop op = NONE /\ op_taint tnop op = {} ==>
       gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
         (write_place cx p result) (ee,operated,Gop,tnop) Q R) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
      (bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ptv bop cur rhs)) (write_place cx p))
      (ee,u,Gr,tnr) Q R
```

Discharge and proof map:

1. P is exactly `augAssignFullRhs:41-53` after choosing its normal result rhs;
   the compiler-state names and operand are renamed, no conjunct discarded.
2. `storage_trace_domain` and the all-H P come from the SAME endpoint in
   `gas_outcome_full_bind_all:33-45`. This witnesses a horizon before extracting
   FMP, alloca history, or ghost resources. Do not use the unwitnessed all-H
   implication alone to choose an execution path.
3. Typing/word operands come from `aug_place_typing`,
   `expr_body_pre_word_result`, and RHS source-success preservation. Literal,
   Exp and shift side conditions are the existing AugAssign typing conditions;
   `aug_place_bop_res_ok` supplies numeric result admissibility from statement
   admissibility and actual source replay. They are not new root guards.
4. Read result x is saved before the RHS; `expr_post`'s old-register frame and
   `ghost_kept_at` supply its concrete value, provenance and taint. The lowerer
   supplies y's freshness. Word-typed RHS uses `post_value_type_word` to connect
   the physical result type, never an aggregate coercion axiom.
5. Reuse `binop_typed_numeric_witness`, `compile_binop_straight_fresh_ptr`,
   `typed_binop_scalar_member_ptr`, `compile_binop_clean_certificate_ptr`, then
   `binop_numeric_origin_ptr_continuation`. These already construct ONE operated
   state and ghosts outside H, or ONE Revert-abort endpoint outside H. Do not
   copy `augassign_toplevel_operator_endpoint_full` as a new generic endpoint;
   it is a proof recipe and still has an obsolete no-D premise on this base.
6. A normal numeric path followed by the callback path yields the bind's joint
   path. The variable-only frame transports `stmt_state_rel` and ghost facts
   for B/D using `ghost_inv_at_exterior_frame`; the source state is still ee.
   RuntimeError/Revert uses the numeric abort path, `expr_exit_INR_type`,
   `stmt_exit_ptr_def`, and `halt_exit_def` separately. It cannot be IntRet or
   Halt, so the conditional exceptional FMP clause is vacuous on that branch.
7. RHS exceptions are handled by bind_all BEFORE A and retain R verbatim.
   No new RHS wrapper is proposed. The bind certificate transport premises of
   bind_all must be discharged in final assembly using the source-specific
   existing exempt-certificate constructors; they are not omitted by writing
   an informal sequential-path argument.

## B. Deploy-immutable write callback

This is a LOCAL suffix post (entry s3/ss, source ee). Original statement frames
are composed by the consumer, not hidden in this producer. `off` is the saved
constructor destination; ee is the actual post-RHS/operator source state.

```sml
Theorem augassign_immutable_write_full:
  !DF lo d explicit ctx func PG RetQ tops cenv cx env st0 ee ss G tn
   id ty ptv off value op s3 sf lctx.
    body_inv tops ctx cenv cx /\ cx.in_deploy /\
    expr_sim_inv cenv cx env ee /\
    FLOOKUP env.bare_globals (cenv.ce_module,id) = SOME ty /\
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
    cenv.ce_module_var_type (cenv.ce_module,id) = SOME ty /\
    evaluate_type (get_tenv cx) ty = SOME ptv /\ is_word_type ty /\
    value_has_type ptv value /\ word_value value /\
    encode_value ptv value = SOME [(0,val_to_w256 value)] /\
    emit_void MSTORE [Lit (n2w off);op] s3 = ((),sf) /\
    fn_has_code s3 sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv s3 /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at s3 z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at s3 z) /\
    eval_operand op ss = SOME (val_to_w256 value) /\
    op_prov G op = NONE /\ op_taint tn op = {} /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee ss /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx ee G tn ss) /\
    return_buf_frame d cenv s3 ss /\ alloca_history func ss /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp ss) /\
    ~ss.vs_halted /\ ss.vs_current_bb = s3.cs_current_bb /\
    ss.vs_inst_idx = LENGTH s3.cs_current_insts ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
      (write_place cx (ImmutablePlace cenv.ce_module id []) value)
      (ee,ss,G,tn)
      (\H res ff G1 tn1 t.
        res = INL () /\
        stmt_post H ctx func cx lctx cenv cenv s3 sf ee ss res ff t /\
        return_buf_frame d cenv sf t /\ alloca_history func t /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        ss.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ff G1 tn1 t /\
        ghost_kept_at lo cenv ee s3 G tn ss G1 tn1)
      (\H res ff gt r. ?ex. res = INR ex /\
        (!tail. stmt_exit_ptr (RetQ H) (ff with gas_obs := tail)
          (INR ex) gt r) /\
        halt_exit H cx ff (INR ex) r /\
        (ctx_has_dalloca ctx ==> !s.
          (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
```

Consumer discharge:

* `immutable_augassign_metadata` supplies the module/type/off facts from deploy
  typing. `immutable_augassign_entry` supplies the actual source immutable and
  current value. `immutable_augassign_prefix_obs`, `immutable_augassign_forced`,
  and `immutable_augassign_rhs_admissible` are the source prefix and RHS-admissibility
  bridge for `augassign_pure_prefix_full` (obs = [], mid = es).
* The saved destination is a literal, not re-read from a potentially changed
  source environment. The old value x loaded before RHS is framed by P in A.
* After RHS, its `expr_body_pre_word_result` consequence supplies
  `expr_sim_inv ... ee`. Same-module immutable metadata is compile/environment
  metadata, unchanged by source evaluation. A's operator frame transports the
  all-H resources and return buffer from u to ss. Literal destination has empty
  provenance/taint without any new assumption.
* `immutable_augassign_write_source`, `immutable_augassign_store`,
  `immutable_augassign_local_frame`, and `immutable_augassign_alloca_sep_update`
  give source write and concrete state reconstruction. `place_store_emit_run_mem`
  is only a counted-memory recipe; the producer must execute its MSTORE once
  and construct pointer ghosts on THAT execution, not pair a second path with it.
* Preserve the source's updated immutables in ff. Do not substitute entry es.

**Unverified proof-interface obligation B1 (for ruling/de-risking):** ordinary
`ghost_inv_at_mstore_clean` assumes `lo <= off`, which cannot be imposed on a
constructor's reserved immutable section. B intentionally has NO such premise.
Its proof must show that clearing the written word's taint preserves
`imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo new_memory) i` for remaining
old tainted bytes below lo. This content-sensitive condition is in
`bodyPtrDefs:142-143`; unchanged outside-byte memory alone does not prove it.
Also check return-buffer separation and local `alloca_frame` against immutable
reserved-region separation. If these do not follow from the displayed resources,
report the exact required internal contract for ruling; do not add `lo <= off`,
`lo = 0`, or a root guard silently. No claim of a proof of B1 is made here.

## C. Composite-place read/type and counted-load endpoint

Input is the exact normal target-place endpoint, NOT a separately existential
memory result. Preserve target_post AND memory liveness AND target_ptr_ok.
`marks` is the target's mark list, not a new independently selected execution.

```sml
Theorem augassign_place_load_full:
  !DF lo d explicit ctx func PG tops bindings cenv cx env env' ret_ty st0
   ty bt bop e es sa sm s1 r loc cur_op s0 mid t G0 tn0 Gt tnt p marks.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    supported_stmt tops bindings (AugAssign ty bt bop e) /\
    ((?base fld. bt = AttributeTarget base fld) \/
     (?base key. bt = SubscriptTarget base key)) /\
    type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
    compile_get_target_ptr compile_expr cenv bt sa = (r,sm) /\
    FST (SND r) = SOME loc /\
    (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
    emit_op (case loc of LocStorage => SLOAD | LocTransient => TLOAD
                     | _ => MLOAD) [FST r] sm = (cur_op,s1) /\
    fn_has_code sm s1 func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at sm z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at sm z) /\
    (!tail. eval_target_place cx bt
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL p,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       target_post H ctx func cenv cx es sa sm s0 mid (PlaceR p) (Type ty) r t /\
       (!id path. p = MemoryPlace id path ==>
          ?entry v. lookup_scopes id mid.scopes = SOME entry /\
                    evaluate_subscripts entry.type entry.value path = INL v) /\
       t.vs_current_bb = sm.cs_current_bb /\
       t.vs_inst_idx = LENGTH sm.cs_current_insts /\
       alloca_history func t /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
       s0.vs_alloca_next <= t.vs_alloca_next /\
       ghost_inv_at (DF H) lo d cenv cx mid Gt tnt t /\
       target_ptr_ok cenv (PlaceR p) r Gt tnt t /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 Gt tnt) /\
    return_buf_frame d cenv sm t /\ ~t.vs_halted ==>
    ?cur ptv loaded Gl tnl.
      (!tail. read_place cx p (mid with gas_obs := tail) =
                 (INL cur,mid with gas_obs := tail) /\
              place_type_value cx p (mid with gas_obs := tail) =
                 (INL ptv,mid with gas_obs := tail)) /\
      evaluate_type (get_tenv cx) ty = SOME ptv /\
      value_has_type ptv cur /\ word_value cur /\ type_bits ty MOD 8 = 0 /\
      eval_operand cur_op loaded = SOME (val_to_w256 cur) /\
      op_prov Gl cur_op = NONE /\ op_taint tnl cur_op = {} /\
      ~loaded.vs_halted /\ loaded.vs_current_bb = s1.cs_current_bb /\
      loaded.vs_inst_idx = LENGTH s1.cs_current_insts /\
      alloca_history func loaded /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp loaded) /\
      loaded.vs_alloca_next = t.vs_alloca_next /\
      loaded = (t with vs_inst_idx := LENGTH s1.cs_current_insts)
        with vs_vars := loaded.vs_vars /\
      (!z. not_fresh_at sm z ==>
        lookup_var z loaded = lookup_var z t /\ FLOOKUP Gl z = FLOOKUP Gt z /\
        op_taint tnl (Var z) = op_taint tnt (Var z)) /\
      tnl.t_mem = tnt.t_mem /\ tnl.t_stor = tnt.t_stor /\
      tnl.t_trans = tnt.t_trans /\ tnl.t_imm = tnt.t_imm /\
      return_buf_frame d cenv s1 loaded /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (t,Gt,tnt) [] (OK loaded,Gl,tnl) /\
        stmt_state_rel H ctx func cenv cx mid loaded /\
        storage_well_formed_on cx mid (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx mid Gl tnl loaded /\
        target_ptr_ok cenv (PlaceR p) r Gl tnl loaded /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 Gl tnl)
```

Discharge/specialization:

* Instantiate `body_target_place_sim_full` at sa/sm and use its gas_outcome_full
  normal branch. Its own source equation, actual endpoint mid, t, Gt, tnt and
  mark list supply the displayed bundle **verbatim** (bodyFullTargetDefs:126-140).
  The concrete uniform source equation is the bind_all continuation's equation.
  Compiler decomposition is `aug_place_code_parts`; its impossible NONE branch
  is eliminated by `target_post`/`place_ptr_rel`, not by assuming successful
  compiled execution. Known memory/storage place kind selects loc.
* Memory specialization: p = MemoryPlace id path, loc = LocMemory;
  `aug_place_target_memory_live`, `aug_place_memory_type_read`,
  `aug_place_memory_read_typed`, and `aug_place_memory_access_ready` give the
  actual read, source type, and MLOAD word from target liveness and typed scopes.
* Pure storage specialization: p = StoragePlace tr slot ptv and loc agrees with
  tr. Use `aug_place_target_storage_ready`, `aug_place_storage_read_ready` and
  `storage_place_observed_read_live`. The observation was produced by THIS
  target evaluation, so a valid H observes it.
* Effectful storage specialization uses exactly the same C statement, but mid
  and mid.storage_trace are the post-index state/trace. Invoke
  `aug_place_rhs_pre_target_gas_obs` and source call-preservation to obtain the
  RHS precondition there. Never reuse es.storage_trace or an es-scopes value
  after an effectful index. No extra pure-target premise occurs in C.
* Return buffer transport is required separately: target_post frames allocations
  and old registers, while the full target bundle does not explicitly list
  `return_buf_frame`; the consumer must derive it from its saved entry frame
  before calling C. This is an explicit discharge obligation, not a conjunct
  falsely attributed to target_place_sim_full.
* C constructs the one fresh MLOAD/SLOAD/TLOAD step and the step_prov/step_taint
  ghosts together; use ptr_inst_ok_mload/sload/tload and load ghost rules, not
  an existential counted-memory path followed by an independent pointer path.

**Unverified interface obligations C1/C2:** clean loaded-word taint requires
memory encoding independence or observed storage key-taint bounds; it is not
implied by target_ptr_ok alone. The intended derivation is from target_post's
state relation plus ghost_inv_at and actual place observation. Confirm this at
the producer probe before adopting C. Separately confirm that the exact
memory-liveness conjunct and source target typing suffice to derive the same
ptv for all H, without adding an es=mid or purity hypothesis. These are proposed
proof obligations, not reasons to edit foreign MappingScratch.

## D. Composite-place write callback (including static failure)

This callback starts AFTER RHS and numeric execution. The saved pointer's
relation must be transported to ee/ss, and its provenance retained. The input
explicitly excludes immutable destinations: B owns that route. It does not
exclude static execution. In particular, no nonstatic guard may be added to a
frozen root to make the SSTORE/TSTORE success recipe usable.

```sml
Theorem augassign_place_write_full:
  !DF lo d explicit ctx func PG RetQ tops cenv cx env st0 lctx ee ss G tn
   p loc ty ptv value dst op w s3 sf.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env ee /\
    ((?id path. p = MemoryPlace id path) \/
     (?tr slot tv. p = StoragePlace tr slot tv)) /\
    (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
    emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                       | _ => MSTORE) [dst;op] s3 = ((),sf) /\
    fn_has_code s3 sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv s3 /\ acyclic_struct_metadata cenv.ce_struct_fields /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at s3 z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at s3 z) /\
    eval_operand dst ss = SOME w /\
    place_ptr_rel cenv cx ss (PlaceR p) w (SOME loc) (Type ty) /\
    target_ptr_ok cenv (PlaceR p) (dst,SOME loc,SOME (value_type_place (Type ty)))
      G tn ss /\
    (!z. dst = Var z ==> not_fresh_at s3 z) /\
    is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
    value_has_type ptv value /\ word_value value /\
    eval_operand op ss = SOME (val_to_w256 value) /\
    op_prov G op = NONE /\ op_taint tn op = {} /\
    (!id path entry t0.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (loc = LocMemory ==> w2n w + 32 <= ss.vs_alloca_next) /\
    gas_admissible (write_place cx p value) (stmt_res_ok lctx) ee /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       storage_place_observed H p /\
       stmt_state_rel H ctx func cenv cx ee ss /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx ee G tn ss) /\
    return_buf_frame d cenv s3 ss /\ alloca_history func ss /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp ss) /\
    ~ss.vs_halted /\ ss.vs_current_bb = s3.cs_current_bb /\
    ss.vs_inst_idx = LENGTH s3.cs_current_insts ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
      (write_place cx p value) (ee,ss,G,tn)
      (\H res ff G1 tn1 t.
        res = INL () /\
        stmt_post H ctx func cx lctx cenv cenv s3 sf ee ss res ff t /\
        return_buf_frame d cenv sf t /\ alloca_history func t /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        ss.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ff G1 tn1 t /\
        ghost_kept_at lo cenv ee s3 G tn ss G1 tn1)
      (\H res ff gt r. ?ex. res = INR ex /\
        (!tail. stmt_exit_ptr (RetQ H) (ff with gas_obs := tail)
          (INR ex) gt r) /\
        halt_exit H cx ff (INR ex) r /\
        (ctx_has_dalloca ctx ==> !s.
          (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
```

Discharge/specialization:

* dst = FST r, with r from C. Save it through RHS using old-register and
  `ghost_kept_at` frames, and through the operator using A's explicit frame.
  The original target_post relation is transported to the **post-RHS** source
  state using the existing AugAssign saved-place/alias and source frame rules.
  Merely keeping the concrete operand is not enough to claim place_ptr_rel.
* Memory specialization uses target liveness, RHS typed-scope preservation,
  local_ptrs_rel, `place_store_word_alloca_frame`'s recipe, and the same local
  region to derive the <= frontier premise. The entry-type compatibility
  premise is exactly the one in `place_store_word_run_mem:171-174`, not an
  arbitrary new source invariant.
* Storage/transient specialization uses the place observation from C and trace
  prefix monotonicity through RHS. `place_store_word_run_mem` reconstructs the
  post on every observing horizon for ONE concrete store. Its theorem is a
  counted-memory recipe only; D must build the pointer/ghost path on that same
  concrete store. State/encoding and key-taint facts must use the selected bank.
* Suffix gas_admissibility is derived by replay of target/read/type/RHS/operator
  success in the original admissible statement. It cannot be inferred from
  the lowerer's output, or replaced by an assumed successful write_place.
* Static source failure is an actual Abort case. Keep it in D; do not feed it
  to the success-only `place_store_word_run_mem`. Compare source write_place's
  RuntimeError and the static backend write fault. Exempt/error certificate
  handling must follow gas_outcome_full, not a fabricated normal endpoint.

**Unverified interface obligations D1/D2:** confirm exact saved-place relation
transport and source lock/alias facts after an effectful RHS. In particular,
`storage_place_observed` is NOT source lock freedom. If existing source safety
and admissibility do not establish precisely the backend/source write branch
alignment in D, request an exact internal premise ruling rather than silently
assuming unlocked/nonstatic. Confirm `target_ptr_ok` for the reconstructed r is
statement-identical to the actual r (SND (SND r) is supplied by target_post).
No composite write result has been proved by this proposal.

## Final consumer graph and joins

```
canonical augassign_rhs_invoke_full ----\
canonical numeric/scalar producers -----> A ----\
canonical immutable metadata/store ---> B ------> C1.20.2 frozen root assembly
canonical target_place_sim_full -------> C ----/       |
canonical placeStore/counting recipes -> D -----------/
```

B, C, D are independent producer candidates. A consumes B/D only as the shown
callback premise; it does not import their theories. Final assembly supplies
normal-Q post-strengthening to compose B/D's local statement post, its original
saved alloca/register frame, ghost_kept transitivity, and the root landing cursor.
This is source/frame composition at the already chosen endpoint, not pairing
existential S1/memory/pointer results. The final Q is exactly the one expanded
from `stmt_frag_full`, including alloca_history then conditional actual FMP.
R is exactly the full statement exception callback shown above.

For deploy immutable use the existing pure prefix theorem with obs=[], then
bind the canonical RHS and A with B. For memory and pure-storage composite
places use target_place_sim_full followed by C and the same RHS/A/D sequence.
For effectful storage compose target simulation using bind_all, then C at mid,
then RHS/A/D; carry the target's actual trace and source endpoint. The target's
exception callback is still expression-typed: change only its success type via
expr_exit_INR_type, retain same-H halt_exit, and exclude IntRet by cases on the
expression exit when upgrading the conditional Halt resource.

Width-general plain top-level word destinations must continue to use the
existing scalar/topword producer boundary and its assigned owner. This packet
does not transfer that ownership or certify those branches. Runtime immutable
branches remain eliminated by existing typing classification, not by a new
unsupported-target hypothesis. Existing local and local-field roots remain
owned by their current leaves.

## Exact approval/de-risking request

1. Approve or amend the four displayed new internal interfaces and script/output
   boundaries. They are NEW helper contracts, not automatically authorized by
   callback-port approval d26b4f43. No exported/root statement change is sought.
2. Already approved portions: same-H halt_exit, expression Halt to statement
   Halt/IntRet resource transport, normal-Q conditional FMP, physical
   post_value_type in the RHS store bound. These facts do NOT authorize an
   arbitrary new alias/lock/dead-section premise.
3. Assign proof probes for B1, C1/C2, D1/D2 before claiming the affected producer
   is risk 1-2. In particular decide whether B1 needs a reusable immutable
   section ghost boundary, and whether D needs a source-success-first callback
   rather than the stronger whole-write outcome displayed here. Do not infer
   formal validity from this document or from the retained memory recipes.
4. Validate producer names/types and the final consumer discharge map on current
   canonical sources before installing theorem declarations. The typography
   type descriptions above are not declarations. All four theorem headers are
   proposals, not frozen contracts; the approved version must be recorded before
   proving or relying on it.
5. Keep foreign MappingScratch qualification owner-routed. It is not needed to
   review these source contracts and must not be repaired here. Do not start a
   second family run, touch sibling source, or release another owner's wait.

## Source/evidence ledger

* `augAssignFullRhs:9-58`: exact canonical RHS Q/R, fresh session read
  TO_assignment_cases-L0040-20261116T132824426721Z_m0024_t002.
* `bodyFullTargetDefs:91-143`: exact target-place normal/exception bundle,
  TO_assignment_cases-L0040-20261116T132824426721Z_m0024_t003.
* `augAssignFullOperator:9-57`: existing joint numeric endpoint, conditional FMP,
  TO_assignment_cases-L0040-20261116T132824426721Z_m0025_t001.
* `gasOutcomeFullCompose:29-62`: bind_all including certificate premises,
  TO_assignment_cases-L0040-20261116T132824426721Z_m0025_t002.
* `bodyImmutableAugAssignFacts:8-118`: metadata/entry/load,
  TO_assignment_cases-L0040-20261116T132824426721Z_m0025_t003.
* `bodyImmutableAugAssignExec:10-91`: pure-prefix/replay/admissibility,
  TO_assignment_cases-L0040-20261116T132824426721Z_m0025_t004.
* `bodyImmutableAugAssignStore:160-205`: concrete immutable reconstruction,
  TO_assignment_cases-L0040-20261116T132824426721Z_m0026_t004.
* `augAssignPlaceWordStoreMemory:161-221`: success-only counted-memory recipe,
  TO_assignment_cases-L0040-20261116T132824426721Z_m0028_t003.
* `augAssignFullSourcePrefix:13-33`: existing pure prefix, not for effectful
  indices, TO_assignment_cases-L0040-20261116T132824426721Z_m0029_t004.
* `bodyPtrDefs:128-146,197-214`: ghost invariant and kept frame,
  TO_assignment_cases-L0040-20261116T132824426721Z_m0030_t002.
* `stmtSimAugAssignPlaceMemory:1293-1333`: actual target endpoint readiness,
  TO_assignment_cases-L0040-20261116T132824426721Z_m0031_t003.
* Narrow source lookup confirms canonical target_post definition and its exact
  r type: TO_assignment_cases-L0040-20261116T132824426721Z_m0032_t004.
* Entry diagnostic only: augAssignFullRhsTheory restored from cache and holbuild
  finished 3.432s; TO_assignment_cases-L0040-20261116T132824426721Z_m0030_t001.
  This does not parse or certify any proposal in this document.

## Bounded self-audit (current source, 2026-11-16)

This audit finishes the interface-design artifact; it does **not** approve any
new contract or discharge the labelled mathematical probes.

* A's P was compared conjunct-by-conjunct with
  `augAssignFullRhsScript.sml:41-53`: expr_post uses the actual RHS input source
  `es`, compiler states `sa/s2`, input concrete state `s_rhs0`, actual output
  source `ee`, RHS value/operand `rhs/y`, and concrete endpoint `u`. Its kept
  frame refers to `es/sa/G0/tn0/s_rhs0`, not to the post-operator cursor.
  The output R at :54-58 matches A/B/D's full exceptional callback. The
  existing numeric continuation :39-57 provides a single concrete/ghost
  endpoint outside H and a variable-only normal frame. A still owes the
  small source `bop_result`/`evaluate_binop` bridge and the bind certificates;
  neither is supplied by separately existential simulations.
* Immutable address lowering is exact, not guessed from Assign:
  `defs/exprLoweringScript.sml:2075-2084` returns
  `(Lit (n2w off), SOME LocCode, OPTION_MAP ValPT ...)` for the saved immutable.
  `defs/stmtLoweringScript.sml:900-923` selects default MLOAD/MSTORE for LocCode
  and emits the store as `[dst_op;res_op]`. Thus B's
  `emit_void MSTORE [Lit (n2w off);op]` is the actual AugAssign suffix; it is
  NOT `compile_imm_store_word`'s ADD-based suffix. The constructor metadata
  fact also supplies `off + type_memory_size ptv < dimword(:256)`; its
  derivation at B's use is `immutable_augassign_metadata:20-21`.
* B1 remains a real probe, not an asserted missing external precondition.
  `ghost_inv_at:142-143` tests `imm_section_dead` using the NEW memory section.
  `immSectionDead:27-48,60-67` shows why that predicate is content-sensitive
  for bytestrings/dynamic arrays. B writes a word-typed immutable, so the
  promising argument is typed declaration-region separation: it cannot alter
  another immutable's length/header, and its own word layout has no dead
  bytes. The document does not claim that boundary has already been proved.
  Ordinary `lo <= off` store framing remains inapplicable in general.
* C's all-H target bundle matches `bodyFullTargetDefs:126-140`. In particular
  target memory liveness, conditional actual FMP, target_ptr_ok and ghost_kept
  are retained. `loweringPosts:719-738` confirms the r type, place readability,
  register/allocation frame, and locals_kept; it does NOT return
  return_buf_frame explicitly. The separate input frame in C must be derived
  by the consumer from its saved frame and target_post (allocated return
  region separation, saved pointer/PC registers). That discharge remains an
  explicit verification item and must not be erased by alleging the bundle
  contains it.
* D's r reconstruction is exact: target_post fixes
  `SND (SND r) = SOME (value_type_place (Type ty))`, and C fixes its loc. The
  original first operand is retained by register frames. For memory,
  `place_ptr_rel:683-691` uses saved base registers plus compile/type metadata;
  for storage :692-694 it uses the saved slot, location and evaluated type.
  These are the exact facts a producer must frame, rather than assuming that
  operand equality alone gives source write readiness. The success-only
  counted-memory recipe :161-194 contains the same entry-type compatibility
  and frontier conditions as D, but no static-error proof or pointer ghost
  proof. Hence D1/D2, selected-bank taint, static/source lock alignment and
  actual post-RHS scope liveness are still de-risking items, not completed
  callbacks. If a whole-write interface is unjustified, the strategist should
  choose a source-success-first callback before seeking approval, rather than
  add an unexplained lock/nonstatic premise.
* No new `.sml` file, statement, semantic definition, admission, or foreign
  supplier edit was made. The canonical RHS target was checked with holbuild
  (nothing to rebuild, 1.525s); this is entry/interface evidence only. The
  four proposals are deliberately still unparsed documentation. Exact
  header approval and proof-probe decomposition are the next decisions.

Audit evidence: TO_assignment_cases-L0040-20261116T132824426721Z_m0040_t001
through m0040_t007; m0041_t003/m0041_t004; m0042_t002/m0042_t003/m0042_t004;
m0043_t004/m0043_t005/m0043_t006; m0044_t002/m0044_t003;
m0047_t001/m0047_t003; m0049_t001; m0050_t001/m0050_t002/m0050_t005.
