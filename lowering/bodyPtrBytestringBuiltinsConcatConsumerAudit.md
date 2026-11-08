# Conditional Concat consumer / frame comparison (C1.image.exclusion)

This is a source/interface diagnostic, not a theorem of image exclusion or target
falsehood. Checked comparison fixtures are TerminalPairProbe, TerminalInstallProbe,
and CheckerBoundaryProbe. Their builds were independently successful.

## First absence use and complete local interface

`ConcatConditional.concat_vv_ptr_of_context_header_free` (lines 8-17):

    (!f. lookup_function f.fn_name ctx.ctx_functions = SOME f ==>
         concat_header_free f) ==>
    expr_vv_sim_ptr d ctx PG func cenv cx out_ty
      (Builtin ann (Concat n) args) es

It unfolds expr_vv_sim_ptr, obtains actual function lookup from
stmt_state_rel_function_lookup, applies compile_concat_mandatory_header to
compile_expr and fn_has_code, and closes by contradiction with header absence.
There is NO gas path, ghost transition, selected runtime instruction, or operand
simulation invoked in this proof. Absence is used to make the entire initial
frame impossible, before considering execution. In particular it is inaccurate
to describe this proof as failing a pointer check at its fourth instruction.

The local antecedent after unfolding is precisely bodyPtrDefs 298-311:
* compile_expr cenv out_ty (Builtin ann (Concat n) args) sa = (vv,sb);
* fn_has_code sa sb func; fn_inst_ids_distinct func;
* local_ptrs_reserved cenv sa; ~ctx_has_dalloca ctx; ~cenv.ce_is_ctor;
* old-variable requirements for ce_return_buf and ce_return_pc;
* gas_admissible (eval_expr cx expression) expr_vv_res_ok es;
* stmt_state_rel ctx func cenv cx es s0;
* ghost_inv d cenv cx es G0 tn0 s0; ~s0.vs_halted;
* current block = sa.current block, instruction index = LENGTH sa.current insts.

`ConcatConditional.concat_body_ptr_of_context_header_free` (19-32) supplies
absence under body_inv tops ctx cenv cx and expr_body_pre cenv cx env expression
es, constructs the vv judgment above, then uses expr_sim_ptr_of_vv. It does NOT
use the target's body_exprs_ptr_ok operand hypothesis at all.

`ConcatCompatibility.compile_concat_mandatory_header` (27-59) has only:

    compile_expr cenv out_ty (Builtin ann (Concat n) args) sa = (vv,sb) /\
    fn_has_code sa sb func ==> ~concat_header_free func

It exposes the dispatch's allocation/ADD/allocation/store prefix, uses ci_mono
and cs_extends through compile_concat's children, and fn_has_code_split to
place that prefix in the function. No execution or semantic premise is used.

## What the matcher remembers

concat_header_free (ConcatCompatibility 8-17) universally quantifies label, bb,
prefix, suffix, four ids, bytes, and b/data/off variable names. It forbids linked
full instruction records with allocation size n2w bytes, ADD b 32, ALLOCA64 off,
MSTORE off 0. It DOES NOT remember that b/data/off originated at this Concat site,
the result vv, requested/annotated type, n, args, or any later continuation.
The mandatory-header proof instantiates these arbitrary names with the actual
fresh output names and ids. The predicate itself remains generic window absence.
Consequently retaining actual record names does not distinguish the checked
Attribute/Empty collision: its records have exactly the same required linking.

## Premise table

| Layer | Actual Concat use | Checked collision / remaining gap |
|---|---|---|
| Compilation | Dispatch 3199-3217 allocates output size 32+ceil(n/32)*32, ADD32, ALLOCA64 and zero store BEFORE compiling any argument. Later reads off and stores final length. | Attribute compiles mismatched StructLit B with A annotation to ALLOCA32, ADD32; Empty Bytes[1] supplies ALLOCA64, zero store. Same four-record shape, no same source origin or full continuation. n=0 also makes a real Concat first allocation 32. |
| Function code | fn_has_code and inst-id distinctness are initial vv premises. stmt_state_rel includes lookup through alloca_room. | Local list and standalone well-formed function exist. Original real source compilation has the prefix but runtime installation is rejected at unrelated INVOKE. No installed membership proved. |
| Body frame | body_inv 61-88 supplies actual successful runtime/deploy lowering, support, function metadata, built struct map, acyclic metadata, module-code relation, cenv target and alloca-locals, key uniqueness etc. | Support alone checked. No actual successful unit or body_inv for collision. body_inv does NOT say expression being simulated occurs in source code. |
| Expression pre | expr_body_pre 148-160 supplies expr_sim_inv, well_typed_expr of the simulated expression, byte widths, allocation limits, call safety/module conditions, no EVM-run, ABI target occurrence and dynamic compatibility. | Does not give well-typedness of every installed expression. Existing ConcatAdmissionProbe proves well-typed literal Concat/body pre separately, but not its code installed in same context. |
| Operand ptr validity | Frozen target supplies body_exprs_ptr_ok when arity valid. It can yield child judgments under suitable child preconditions. | Conditional consumer ignores it. Collision's Attribute value is not itself an actual Concat argument at the matched prefix. No child judgment for it was proved. |
| Buffer coverage | expr_vv_sim_ptr normal post requires ptr_buf_ok for any returned LocatedValue at LocMemory (bodyPtrDefs 322-323); expr_sim_ptr normal post also requires it for nonword results. ptr_buf_ok 224-230 requires full lowered-type extent in provenance allocation. | Attribute value is base+32 from size32 allocation, annotated Bytes[1] of size64: it cannot satisfy that coverage using its allocation provenance. But coverage is a POST condition of a judgment for THAT Attribute, not a precondition on arbitrary instructions contained in func. No such judgment is used at the conditional contradiction. |
| Continuation | Real Concat has compile_concat child processing, MLOAD off, MSTORE output length. | Child-list witness continues with argument staging and INVOKE; isolated checker witness ends STOP. Neither establishes equality to full real Concat compilation. |

## Ghost / runtime distinction

The fourth instruction writes zero to a separately allocated 64-byte offset cell;
CheckerBoundaryProbe proves the whole four-instruction window plus STOP satisfies
fn_ptr_ok_check and wf_function. The known actual unsafe Concat step is elsewhere:
ConcatRunProbe.concat_probe_prefix_destination and _second_store show the second
fixed-bytes literal is MSTOREd at destination 289 with provenance (256,64), id11.
concat_probe_prefix_unsafe_store proves ~access_ok outside revert-forward. The
32-byte store overhangs 320. This detached execution is not an admissible frame.
ConcatFrameProbe explicitly demonstrates failed installed lookup for its synthetic
function in the empty-program unit. These facts are not a frozen counterexample.

## Outcome / exact gap

There is no locally justified replacement exclusion boundary from this audit.
The four-record predicate deliberately erases the distinguishing continuation.
Bad Attribute coverage does not repair it: simulation of that Attribute is not a
premise at the Concat use, and header emission precedes all Concat operands.

Two possible future interfaces require strategist selection, not assumption:
1. A stronger actual-code origin/continuation impossibility theorem under body_inv,
   fn_has_code for FULL Concat, expr_body_pre, and (if actually needed) operand
   judgments. Its proof must allow accidental supported header collisions.
2. An actual installed/frame counterexample whose code includes the full failing
   Concat continuation, with the existing literal operand judgments, correct gas
   admissibility, stmt_state_rel and ghost_inv. Current fixtures do not provide it.

Do not rename global absence or infer this missing implication from ptr_buf_ok.
No new invariant or conditional simulation theorem was introduced here.
