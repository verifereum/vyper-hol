# Initialized-loop suffix: conditional proof-point capture

## Status and source identity

This is **diagnostic data, not a proved helper or a Consumer delivery**. The
obligation `body_for_local_array_full_from_contracts[initialized_loop_suffix]`
was actually reached. The source-packet, compiler-packet and common-loop
predecessors were left suspended. Their resulting assumptions below are
conditional local goals, not imported theorems. No `Finalise` was run.

Source: `bodyFullForArrayLocalCaptureContext/Consumer.reconstructed.txt`, blob
`2970c304716a8db3019f7f0b490e31c98bce8270`, reconstructed from base blob
`5a295bb9c0d27cebf180e7355caefe7dd3edac34` and the committed lossless patch.
The archive, not a private worktree Consumer, is the source of this capture.
Replay retained source lines 1-25, 37-529, 637-782, 1669-1701 and 2012-2014;
only the diagnostic theory name and printer differed. The two temporary replay
scripts are not part of this publication.

Original default build: batch `cd009688-03e5-43e1-96dc-411b8a72b51e`,
`TO_statement_cases-L0050-20261116T223006792810Z_m0013_t001`.
The deliberate diagnostic failure printed CAPTURE-BEGIN through CAPTURE-END,
including all 134 assumptions, the free-variable types, and the conclusion.
Original readbacks: `m0015_t001`, `m0017_t003`, `m0022_t002`, `m0023_t001`,
`m0023_t002` under that same tool-output prefix. The last printer took
2456.176 ms at the ordinary 2500 ms limit. A later attempt to serialize the
whole sequent in one tactic timed out (batch
`2314e7fd-984a-47f7-936c-7229909d491f`, `m0025_t001`); it did not prove or
invalidate the suffix and did not produce a usable raw-file artifact.
This publication transcribes the persisted observation instead of replaying
that runtime proof again.

## Types of the captured free variables

The table is the printer's free-variable inventory, grouped only to save space.
Here `horizon` is *documentary notation* for
`(bool # 256 word # type_value) list # num list`, and `ghost` for
`string |-> num # num`; these are not new HOL definitions or type declarations.
`exception` in the Exit type is `vyperState$exception`.

```text
Exit : horizon -> vyperState$exception -> evaluation_state -> ghost # taint -> exec_result -> bool
Done : horizon -> evaluation_state -> ghost -> taint -> venom_state -> bool
Inv : horizon -> eval_result list -> evaluation_state -> ghost -> taint -> venom_state -> bool
Head : string -> string -> operand -> string -> instruction -> 256 word -> 256 word ->
       horizon -> eval_result list -> evaluation_state -> ghost -> taint -> venom_state -> bool
DF : horizon -> dead
RetQ : horizon -> value -> evaluation_state -> ghost # taint -> exec_result -> bool
arr_base, dst : 256 word
shadow_sb0, shadow_sb1, sdecl, sdecl', sj, sb1, sb0, scopy,
shadow_start, shadow_finish, start, finish : compile_state
bc_out, bc, cenv', cenv : compile_env
tail_code : instruction list
Gentry, G0 : ghost
tnentry, tn0 : taint
cc, s0 : venom_state
ainst : instruction
p, ov, tov, ep, incr_lbl, nv, cond_lbl, idx, dv, exit_lbl, body_lbl,
ap, name, id : string
j3, joff, j4, i1, i2, i3, j1, j2, az, lo, n : num
bound_op : operand
st0, es : evaluation_state
lctx : loop_ctx
vs : value list
av : array_value
ent : scope_entry
env_b, env : typing_env
d : (256 word # num) option
shadow_ctx, ctx : venom_context
PG : (num # num) option list
func, shadow_func : ir_function
ret_ty, typ : type
bindings : (string # type) list
tops : toplevel list
cx : evaluation_context
bd : bound
tv : type_value
stmts : stmt list
entry, handler, body_outcome, body_fragment, dynamic_entry, dynamic_prefix, fixed : ind
```

The seven `ind` variables are assumption-label markers, **not** runtime entry
labels, semantic resources, or executable witnesses. Their marked propositions
are universally closed contracts, expanded below. No type is identified between
ordinary and shadow states.

## Raw sequent (factored transcription)

`A0` through `A133` name the assumptions in the original printer order.
Whitespace is compressed; Unicode logical notation is rendered in ordinary HOL
ASCII. The seven long labelled propositions are factored into the exact
quotation expansions in the next section; none is omitted. `C` is the unchanged
conclusion. These names are documentary, not constants installed into HOL.
Abbrev markers are retained as observed. For a lemma statement they become their
underlying equalities; the label markers similarly unwrap to their propositions.

```text
A0:
 !rs ee s G tn.
   ~s.vs_halted /\
   (!H. valid_horizon cx st0 H ee.storage_trace ==> Inv H rs ee G tn s) /\
   gas_admissible (eval_for cx tv id stmts rs) (stmt_res_ok lctx) ee ==>
   gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_for cx tv id stmts rs) (ee,s,G,tn)
     (\H res ee G tn t. res = INL () /\ Done H ee G tn t)
     (\H res ee gt r. ?ex. res = INR ex /\ Exit H ex ee gt r)
A1:
 Abbrev (Exit = (\H ex ee gt r.
   (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
   halt_exit H cx ee (INR ex) r /\
   (ctx_has_dalloca ctx ==>
    !s. r = Halt s \/ (?ir. r = IntRet ir s) ==> allocas_below_fmp s)))
A2:
 Abbrev (Done = (\H ee G tn s.
   stmt_lands lctx finish (INL ()) s /\ ~s.vs_halted /\
   ~block_is_terminated finish /\ cenv_top_ext cenv cenv ee.scopes /\
   stmt_state_rel H ctx func cenv cx ee s /\
   storage_well_formed_on cx ee (FST H) /\
   return_buf_frame d cenv finish s /\ alloca_history func s /\
   s0.vs_alloca_next <= s.vs_alloca_next /\
   ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
   (!x w. not_fresh_at start x /\ lookup_var x s0 = SOME w ==>
          lookup_var x s = SOME w) /\
   (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
             FLOOKUP s.vs_allocas aid = SOME bl) /\
   !x. not_fresh_at start x ==>
       FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)))
A3: Abbrev (Inv = Head idx p bound_op cond_lbl ainst arr_base dst)
A4: fn_has_code shadow_sb0 shadow_sb1 shadow_func
A5: gas_shadow_state sb1 shadow_sb1
A6: gas_shadow_state sb0 shadow_sb0
A7: stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty (MAP gas_shadow_stmt stmts)
      shadow_sb0 = (bc_out,shadow_sb1)
A8: stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty stmts sb0 = (bc_out,sb1)
A9: lookup_block body_lbl func.fn_blocks = SOME
      <|bb_label := body_lbl; bb_instructions := sb0.cs_current_insts ++ tail_code|>
A10: bd = Dynamic (bound_length bd) ==>
     not_fresh_at scopy tov /\ tov <> p /\ tov <> idx /\ joff <> j3 /\ joff <> j4
A11: !x. bound_op = Var x ==>
     x <> dv /\ x <> ov /\ (bd = Dynamic (bound_length bd) ==> x <> tov) /\
     x <> ep /\ x <> idx /\ x <> nv
A12: copy_old_operand scopy bound_op
A13: copy_old_operand start (Var ap)
A14: start.cs_next_var <= sb0.cs_next_var
A15: scopy.cs_next_var <= sb0.cs_next_var
A16: start.cs_next_var <= scopy.cs_next_var
A17: cs_extends scopy sb0
A18: cs_extends start scopy
A19: !H. valid_horizon cx st0 H es.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s0,G0,tn0) [] (OK cc,Gentry,tnentry) /\
     Inv H (MAP Value vs) (es with gas_obs := []) Gentry tnentry cc
A20: ~cc.vs_halted
A21: not_fresh_at sb0 ap
A22: not_fresh_at sb0 p
A23: not_fresh_at sb0 idx
A24: !x. not_fresh_at start x ==> not_fresh_at sb0 x /\ x <> idx /\ x <> nv
A25: !x. not_fresh_at start x ==>
     not_fresh_at scopy x /\ x <> dv /\ x <> ov /\ x <> ep /\
     (bd = Dynamic (bound_length bd) ==> x <> tov)
A26: declare_local cenv id typ sdecl = (bc,sdecl')
A27: finish.cs_current_insts = []
A28: finish.cs_current_bb = exit_lbl
A29: not_fresh_at scopy ap
A30: not_fresh_at scopy ep
A31: not_fresh_at scopy p
A32: not_fresh_at scopy idx
A33: bd = Dynamic (bound_length bd) ==> ap <> tov
A34: ~MEM ap [idx;dv;ov;ep;nv]
A35: bd = Dynamic (bound_length bd) ==>
     ALL_DISTINCT [idx;dv;ov;tov;ep;nv;p] /\ !scs. not_local_ptr cenv scs tov
A36: ALL_DISTINCT [idx;dv;ov;ep;nv;p]
A37: !scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs dv /\
           not_local_ptr cenv scs ov /\ not_local_ptr cenv scs ep /\
           not_local_ptr cenv scs nv
A38: bc with <|ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
              ce_dynarray_capacity := cenv.ce_dynarray_capacity|> = cenv
A39: !nm. nm <> id ==> FLOOKUP bc.ce_vars nm = FLOOKUP cenv.ce_vars nm
A40: FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv typ))
A41: ainst.inst_outputs = [p]
A42: ainst.inst_opcode = ALLOCA
A43: MEM ainst (fn_insts func)
A44: ~block_is_terminated sb1 ==>
     sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
     sj.cs_current_insts = sb1.cs_current_insts ++
       [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb1 sj func
A45: ~block_is_terminated sb0
A46: local_ptrs_reserved bc sb0
A47: local_ptrs_reserved bc scopy
A48: fn_has_code sb0 sb1 func
A49: compile_stmts bc (InLoop exit_lbl incr_lbl) ret_ty stmts sb0 = ((),sb1)
A50: fn_has_code scopy sb0 func
A51: same_blocks scopy sb0
A52: sb0.cs_current_insts = scopy.cs_current_insts ++ emitted_insts scopy sb0
A53: sb0.cs_current_bb = body_lbl
A54: compile_iter_elem_copy cenv (Var ep) (Var p) (type_memory_bytes cenv typ)
       LocMemory F typ typ scopy = ((),sb0)
A55: scopy.cs_current_insts =
     [mk_inst j3 MUL [Var idx;Lit (n2w (type_memory_bytes cenv typ))] [ov]] ++
     (case bd of Fixed m => []
      | Dynamic c => [mk_inst joff ADD [Lit 32w;Var ov] [tov]]) ++
     [mk_inst j4 ADD [Var ap;case bd of Fixed m => Var ov | Dynamic c => Var tov] [ep]]
A56: scopy.cs_current_bb = body_lbl
A57: lookup_block incr_lbl func.fn_blocks = SOME
     <|bb_label := incr_lbl; bb_instructions :=
       [mk_inst i1 ADD [Var idx;Lit 1w] [nv];
        mk_inst i2 ASSIGN [Var nv] [idx]; mk_inst i3 JMP [Label cond_lbl] []]|>
A58: lookup_block cond_lbl func.fn_blocks = SOME
     <|bb_label := cond_lbl; bb_instructions :=
       [mk_inst j1 EQ [Var idx;bound_op] [dv];
        mk_inst j2 JNZ [Var dv;Label exit_lbl;Label body_lbl] []]|>
A59:
 Abbrev (Head = (\idx p bound_op cond_lbl ainst arr_base dst H rs ee G tn s.
   LENGTH rs <= LENGTH vs /\
   rs = MAP Value (DROP (LENGTH vs - LENGTH rs) vs) /\
   expr_sim_inv cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee s /\
   storage_well_formed_on cx ee (FST H) /\ dead_lo_ok H (DF H) lo cenv cx /\
   return_buf_frame d cenv start s /\ alloca_history func s /\
   s0.vs_alloca_next <= s.vs_alloca_next /\ allocas_from lo s /\
   ghost_inv_at (DF H) lo d cenv cx ee G tn s /\ ~s.vs_halted /\
   s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
   LENGTH vs < dimword (:256) /\
   lookup_var idx s = SOME (n2w (LENGTH vs - LENGTH rs)) /\
   eval_operand bound_op s = SOME (n2w (LENGTH vs)) /\
   FLOOKUP G idx = NONE /\ op_prov G bound_op = NONE /\
   op_taint tn (Var idx) = {} /\ op_taint tn bound_op = {} /\
   lookup_scopes name ee.scopes = SOME ent /\ ent.type = ArrayTV tv bd /\
   ent.value = ArrayV av /\ vs = array_elements ent.type av /\
   eval_operand (Var ap) s = SOME arr_base /\ lookup_var p s = SOME dst /\
   ptr_covers G tn p s (type_memory_bytes cenv typ) /\
   FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,type_memory_bytes cenv typ) /\
   w2n dst + type_memory_bytes cenv typ < dimword (:256) /\
   w2n dst + type_memory_bytes cenv typ <= s.vs_alloca_next /\
   (!nm b len. local_region cenv ee.scopes s nm b len ==>
       regions_disjoint (w2n dst) (type_memory_bytes cenv typ) b len) /\
   (!x w. not_fresh_at start x /\ lookup_var x s0 = SOME w ==>
          lookup_var x s = SOME w) /\
   (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==>
             FLOOKUP s.vs_allocas aid = SOME bl) /\
   (!x. not_fresh_at start x ==>
        FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
   lookup_scopes id ee.scopes = NONE /\ ret_pc_ok cenv start s))
A60: compile_stmt cenv lctx ret_ty
       (For id typ (Array (Name (ArrayT typ bd) name)) n stmts) start = ((),finish)
A61: cenv' = cenv
A62: !c lc a b. compile_stmts c lc ret_ty stmts a = ((),b) ==>
     cs_extends a b /\ a.cs_next_var <= b.cs_next_var
A63: type_memory_bytes cenv typ + 64 < dimword (:256)
A64: type_memory_bytes cenv typ = type_memory_size tv
A65: type_memory_bytes cenv typ < 2 ** 64
A66: cenv.ce_alloca_locals
A67: Abbrev (vs = array_elements (ArrayTV tv bd) av)
A68: storage_trace_domain cx st0 es.storage_trace
A69: s0.vs_inst_idx = LENGTH start.cs_current_insts
A70: s0.vs_current_bb = start.cs_current_bb
A71: ~s0.vs_halted
A72: !H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H) /\ ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0
A73: !fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_no_wrap inst s
A74: ctx_has_dalloca ctx ==> allocas_below_fmp s0
A75: alloca_history func s0
A76: return_buf_frame d cenv start s0
A77: gas_admissible
       (eval_stmt cx (For id typ (Array (Name (ArrayT typ bd) name)) n stmts))
       (stmt_res_ok lctx) es
A78: ~block_is_terminated start
A79: !x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x
A80: ret_pc_ok cenv start s0
A81: local_ptrs_reserved cenv start
A82: fn_inst_ids_distinct func
A83: !H. dead_lo_ok H (DF H) lo cenv cx
A84: fn_has_code shadow_start shadow_finish shadow_func
A85: fn_has_code start finish func
A86: MEM shadow_func shadow_ctx.ctx_functions
A87: MEM func ctx.ctx_functions
A88: gas_shadow_function func shadow_func
A89: ctx_inst_ids_distinct ctx
A90: gas_shadow_context ctx shadow_ctx
A91: gas_shadow_state finish shadow_finish
A92: gas_shadow_state start shadow_start
A93: stmt_env cenv lctx ret_ty
       (gas_shadow_stmt (For id typ (Array (Name (ArrayT typ bd) name)) n stmts))
       shadow_start = (cenv',shadow_finish)
A94: stmt_env cenv lctx ret_ty
       (For id typ (Array (Name (ArrayT typ bd) name)) n stmts) start = (cenv',finish)
A95: lookup_scopes id es.scopes = NONE
A96: FLOOKUP cenv.ce_vars id = NONE
A97: body_for_full_ok cx tv id stmts (MAP Value vs)
A98: !gs. eval_iterator cx (Array (Name (ArrayT typ bd) name))
       (es with gas_obs := gs) = (INL (MAP Value vs),es with gas_obs := gs)
A99: FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var ap) az)
A100: LENGTH vs < dimword (:256)
A101: LENGTH vs <= n
A102: ent.value = ArrayV av
A103: well_formed_type_value (ArrayTV tv bd)
A104: value_has_type (ArrayTV tv bd) (ArrayV av)
A105: ent.type = ArrayTV tv bd
A106: evaluate_type (get_tenv cx) typ = SOME tv
A107: lookup_scopes name es.scopes = SOME ent
A108: ~supported_stmts_expr_exists expr_internal_call_root stmts
A109: supported_stmts tops bindings stmts
A110: type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b
A111: iterator_unmodified (Array (Name (ArrayT typ bd) name)) stmts
A112: id NOTIN FDOM env.var_types
A113: FLOOKUP env.var_types name = SOME (ArrayT typ bd)
A114: ~ctx_has_dalloca ctx
A115: frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ cenv ret_ty
A116: call_evaluation_safe cx
        (int_calls_stmt (For id typ (Array (Name (ArrayT typ bd) name)) n stmts))
A117: stmt_exprs_ok cenv (For id typ (Array (Name (ArrayT typ bd) name)) n stmts)
A118: type_stmt env ret_ty (For id typ (Array (Name (ArrayT typ bd) name)) n stmts) = SOME env
A119: locals_alloc_ok cenv env
A120: ce_locals_declared cenv env
A121: expr_sim_inv cenv cx env es
A122: !target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
        (For id typ (Array (Name (ArrayT typ bd) name)) n stmts) ==>
        occurs_abi_decode_target target tops
A123: supported_stmt tops bindings
        (For id typ (Array (Name (ArrayT typ bd) name)) n stmts)
A124: body_inv tops ctx cenv cx
A125: body_iterator_full_ok cx (Array (Name (ArrayT typ bd) name))
A126: !s'3' vs t' s'4' t''.
        eval_iterator cx (Array (Name (ArrayT typ bd) name)) s'3' = (INL vs,t') /\
        check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' = (INL (),t'') ==>
        body_for_full_ok cx tv id stmts vs
A127: entry :- close(local_round_entry_revised)
A128: handler :- close(local_handled_round_contract)
A129: body_outcome :- close(local_body_outcome_contract)
A130: body_fragment :- close(local_body_fragment_contract)
A131: dynamic_entry :- close(dynamic_entry_contract)
A132: dynamic_prefix :- close(dynamic_prefix_contract)
A133: fixed :- close(fixed_entry_contract)

C:
 gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
   (cx_tops cx) cx st0
   (eval_stmt cx (For id typ (Array (Name (ArrayT typ bd) name)) n stmts))
   (es,s0,G0,tn0)
   (\H res ee G tn t. ?cenv''.
      stmt_lands lctx finish res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated finish /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' finish t /\ alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx ee G tn t /\
      (!x w. not_fresh_at start x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
              FLOOKUP t.vs_allocas aid = SOME b) /\
      !x. not_fresh_at start x ==>
          FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x))
   (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r)
```

### Expansion of the seven labelled assumptions

`close(q)` means universal closure of **all** free variables of the specified
quotation, exactly `boolSyntax.list_mk_forall (free_vars q,q)` from archived
lines 454-458. The types are those parsed in the archived header (lines 1-25).
It does not mean an additional hypothesis about a quotation variable. The
following source ranges in the **integrated, immutable source blob identified
above** give complete literal expansions (including every premise) of the
seven long propositions, without making this note a second copy of the shared
contracts. They are incorporated as part of this factored raw sequent:

| Raw assumption | Quotation in Consumer.reconstructed.txt | Exact inclusive source lines |
|---|---|---|
| A127, entry | `local_round_entry_revised` | 325-452 |
| A128, handler | `local_handled_round_contract` | 283-321 |
| A129, body_outcome | `local_body_outcome_contract` | 232-281 |
| A130, body_fragment | `local_body_fragment_contract` | 210-230 |
| A131, dynamic_entry | `dynamic_entry_contract` | 153-208 |
| A132, dynamic_prefix | `dynamic_prefix_contract` | 94-151 |
| A133, fixed | `fixed_entry_contract` | 37-92 |

These source slices are self-contained in the published package, not references
to uncommitted source or to missing theorem objects. Alpha-renaming bound
variables or changing the pretty-printer's quantifier order is immaterial to
this representation; **no premise of those seven quotations is dropped**.
The free variables `fixed` etc. occur only in the label markers. To recover the
unfactored original display, splice each closed quotation after its marker.
The later failed-writer log also prints all seven propositions in full, in the
reverse assumption order (fixed first, entry seventh); that is corroboration
of the same sequent, not a successful capture-file write.

## Extracted `local_initialized_loop_suffix` interface

The conservative extraction is the following completely specified statement,
written with textual macros A0-A133 and C expanded exactly as above and with
the types in the inventory. `EVERY I` is the ordinary list conjunction, not a
new predicate. All parameters below are universally quantified at the outer
level; the closure of each contract is *inside* its corresponding A127-A133.

```text
local_initialized_loop_suffix:
 !Exit Done arr_base dst shadow_sb0 shadow_sb1 bc_out tail_code Gentry tnentry
  Inv cc sdecl sdecl' ainst sj bc sb1 p sb0 j3 ov joff tov j4 ep scopy incr_lbl
  i1 nv i2 i3 cond_lbl j1 idx bound_op dv j2 exit_lbl body_lbl Head st0 G0 tn0
  s0 shadow_start shadow_finish lctx start cenv' finish ap az vs av ent env_b
  DF lo d shadow_ctx PG func shadow_func RetQ ret_ty env es bindings tops ctx
  cenv cx typ bd name n tv id stmts.
  EVERY I
   [A0;A1;A2;A3;A4;A5;A6;A7;A8;A9;
    A10;A11;A12;A13;A14;A15;A16;A17;A18;A19;
    A20;A21;A22;A23;A24;A25;A26;A27;A28;A29;
    A30;A31;A32;A33;A34;A35;A36;A37;A38;A39;
    A40;A41;A42;A43;A44;A45;A46;A47;A48;A49;
    A50;A51;A52;A53;A54;A55;A56;A57;A58;A59;
    A60;A61;A62;A63;A64;A65;A66;A67;A68;A69;
    A70;A71;A72;A73;A74;A75;A76;A77;A78;A79;
    A80;A81;A82;A83;A84;A85;A86;A87;A88;A89;
    A90;A91;A92;A93;A94;A95;A96;A97;A98;A99;
    A100;A101;A102;A103;A104;A105;A106;A107;A108;A109;
    A110;A111;A112;A113;A114;A115;A116;A117;A118;A119;
    A120;A121;A122;A123;A124;A125;A126;A127;A128;A129;
    A130;A131;A132;A133] ==> C
```

An eventual HOL declaration must textually expand the A/C macros, unwrap
Abbrev to equality and erase only label markers, not their propositions.
`entry`, `handler`, `body_outcome`, `body_fragment`, `dynamic_entry`,
`dynamic_prefix`, `fixed` disappear because their label markers have been
erased. There are no unspecified hypotheses or ellipses in this extraction.
No such theorem is claimed here.
All 134 propositions are retained conservatively: minimization of the runtime
context has **not** been proved. This is deliberately not an eighth semantic
cut and must not become an extra root hypothesis. A helper prover may remove
irrelevant premises only by actually proving the resulting stronger helper.

The smaller natural proof boundary appears to be A0, A19, A20 together with the
abbreviation expansions, the iterator/type/gas facts and initial frame/ghost
context. This is a **proof direction**, not a verified replacement statement.
In particular, do not silently assume that the conditional A19 follows from
A72, or replace it by independent memory and pointer runs.

## Complete premise-discharge map

This map accounts for every captured assumption. It identifies its origin and
who must eventually supply it, not certification that the supplier is complete.

| Assumptions | Actual origin / required discharge in the Consumer |
|---|---|
| A0 | Archived `initialized_packet`, lines 1691-1699: suspended `common_loop`. The round/loop assembly must prove this exact outcome callback for Inv/Done/Exit; this capture does not prove it. |
| A1-A3 | Definitional abbreviations introduced at lines 1670-1690: Exit, Done, Inv, respectively. No semantic premise is added when these are expanded. |
| A4-A8 | The body-shadow tail of suspended `code_packet`, lines 774-779. The packet helper must derive both stmts_env equations and the code/state linkage from the actual root ordinary and shadow compilations A93/A94, A91/A92. **No independent shadow code_ready witness is allowed.** |
| A9-A18 | Compiler packet lines 760-773: same-block/code-tail fact, dynamic temporary and old-operand conditions, cs_extends/counters. Packet helper obligation, not a conclusion of this diagnostic. |
| A19-A20 | Selected existential initialization endpoint from compiler packet lines 753-759: the very same cc,Gentry,tnentry (and arr_base,dst) for every valid H. Fixed/dynamic initialization proofs must provide it. The path and Inv conjunct cannot be split between independently chosen runs. |
| A21-A25 | Compiler packet lines 747-752: old-register freshness/caller frame facts. Supplied by packet/freshness proofs from the compiler counters, not global runtime simplification. |
| A26-A28 | Packet lines 745-746: declaration and exit state fields. |
| A29-A37 | Packet lines 734-744: freshness, non-local-pointer and generated-register distinctions, including exactly the conditional Dynamic clauses. |
| A38-A40 | Packet lines 730-733: compile-environment update/projections. |
| A41-A44 | Packet lines 723-729: allocation instruction and body jump extension, with the existing nontermination guard retained. |
| A45-A54 | Packet lines 714-722: body/copy compile and code facts, local-pointer reservation, same-block and emitted-instruction facts. |
| A55-A58 | Packet lines 698-713: concrete copy, condition and increment blocks. |
| A59 | Head abbreviation introduced at lines 663-693; fully expanded above. This is a definitionally introduced local abbreviation, not a loop-invariant theorem. |
| A60-A61 | Derived at runtime lines 651-658 from the actual ordinary stmt_env equation A94. The proof normalizes declare_stmt_local/comp_bind etc.; the source segment was replayed, not assumed as a global theorem. |
| A62 | Runtime lines 646-650, compile_stmt_ci_mono projection: compiler extension and next-var monotonicity, not a body induction. |
| A63 | Runtime lines 644-645: dimension/size arithmetic using A65. |
| A64 | Runtime lines 642-643: expr_sim_inv_memory_size from typing/context. |
| A65 | Runtime lines 640-641: stmt_exprs_ok/alloc_limits_stmt. |
| A66 | Runtime line 639: body_inv gives ce_alloca_locals. |
| A67 | Runtime line 638: local abbreviation for the array elements; expand as equality. |
| A68 | Supplied by gas_outcome_full_initial_domain, archived lines 526-527. This witnesses the initial trace domain; it is not an unwitnessed all-H vacuity argument. |
| A69-A94 | Initial runtime binders/antecedents of stmt_frag_full_def at lines 525-527, including actual ordinary/shadow compilation, one initial machine/ghost tuple, frame/alloca history, no-wrap, dead-lo, validity-conditioned relation and gas admissibility. These remain caller obligations of the unchanged fragment contract. |
| A95-A113 | Source packet chosen at lines 504-524; source_packet Resume is suspended in this selective replay. Its iterator, scope, type, size and freshness facts must be proved by that source-packet obligation in final assembly. A98 is the exact iterator equation for every gas tail. |
| A114 | Archived line 503: body_inv_no_dalloca from A124. Not an inference from alloca_inv. |
| A115-A125 | Original fragment antecedents after specializing the Name Array iterator and source normalization, archived lines 463-501. A118 already has env' eliminated to env via the source packet. |
| A126 | Original body-for premise specialized using the evaluated type from source packet; bound/type/check arguments are normalized but not strengthened. |
| A127 | Seventh universally closed antecedent, label entry. Eventually the revised local round-entry supplier; the literal quotation and all premises remain unchanged. |
| A128 | Sixth antecedent, label handler. Eventually handled-round/scope-pop transport. |
| A129 | Fifth antecedent, label body_outcome. Eventually body full-fragment elimination at the actual ordinary/shadow code pair, retaining halt_exit and conditional allocation. |
| A130 | Fourth antecedent, label body_fragment. Eventually the existing body-statement full callback at the extended environment. |
| A131 | Third antecedent, label dynamic_entry. Eventually checked dynamic-entry supplier, not a proved fact in this replay. |
| A132 | Second antecedent, label dynamic_prefix. Preserved unfinished dynamic prefix remains a proof obligation. |
| A133 | First antecedent, label fixed. Eventually fixed initialization supplier. Parsed conditional contract does not establish supplier-instance acceptance. |

Every assumption has an origin; none is marked as logically discharged merely
because it appears in this table. The unresolved source_packet/code_packet/
common_loop proof obligations are explicitly conditional. The final join must
also connect the seven closed antecedents to their actual checked suppliers.

## Intended suffix proof and reuse boundary

The source iterator is known by A98 for *all* gas tails; A106 supplies successful
type evaluation and A101 supplies the bound. Thus the For prelude can be routed
to `eval_for cx tv id stmts (MAP Value vs)` at the gas-cleared source state.
A19 supplies its selected zero-prefix target path, A20 supplies non-haltedness,
and the same A19 supplies Inv at that endpoint. Apply A0 there after deriving
the recursive gas-admissibility obligation from A77. Transport Done to the
root continuation using A61 and its frame/history/freshness conjuncts; unwrap
Exit to the root exceptional callback without losing halt_exit. This paragraph
is an argument to be proved, not a claim that the required compositions have
already been checked.

Existing reusable interfaces identified by search (do not duplicate them):
`gasOutcomeFullGuardedTheory.gas_outcome_full_zero_prefix_guarded`,
`gasOutcomeFullTheory.gas_outcome_full_post_mono`, and
`gasOutcomeFullComposeTheory.gas_outcome_full_post_source`.
The helper proof should use the named joint combinators rather than manually
unfolding the good/bad-storage outcome arms. No second body induction is needed.

The one endpoint cc and one Gentry,tnentry are selected outside `!H` in the
compiler packet. `lo` remains arbitrary. A73 and A74 remain precisely initial
stepped-state resources; no allocation safety is inferred from alloca_inv or a
vacuous all-H implication. Ordinary and shadow state equalities are never
asserted. The exceptional predicate A1 retains both halt_exit and the existing
conditional allocation conjunct even though the root C requests only its
pointer/halting projection.

## Publication audit boundary

Only this markdown artifact is intended for publication. No Consumer,
LocalContracts quotation, frozen public header or supplier source is changed.
No new theorem, definition, semantic assumption or admission is introduced.
There is no helper build/check success claim: this leaf owns capture and
interface extraction only. The ordinary default diagnostic build reached this
proof point and then deliberately failed; the later serialization timeout is
not a Consumer proof result. The future helper and assembled Consumer still
require their owners' ordinary builds and source-integrity checks.
