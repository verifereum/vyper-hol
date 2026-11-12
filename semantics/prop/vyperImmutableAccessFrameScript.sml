(*
 * What expr_accesses says about the running contract's immutables at run
 * time: an expression with no risky call (no external call, send,
 * raw_call, create or call-family builtin, in it or in an internal
 * function it reaches) changes the immutable id of module src only if its
 * accesses write StateRef (src,id).
 *
 * The function premise ties the accesses analysis to the code that runs,
 * as in vyperStorageAccessFrame: an internal call the expression reaches
 * is looked up in mods, and the function the evaluator calls is the one
 * function_accesses reads (or the empty constructor lookup_function
 * synthesizes).
 *
 * TOP-LEVEL:
 *   eval_expr_unwritten_immutable
 *)

Theory vyperImmutableAccessFrame
Ancestors
  vyperSubscriptOverlap vyperInterpreter vyperState vyperContext
  vyperStorageAccessFrame vyperLocalAccessFrame
  vyperTypeInvariants vyperTypeCallStackSoundness vyperTypeCallGraphSoundness
  vyperTypeCallGraph list

(* Why it holds (a reader may ignore this): immutables change only through
   an ImmutablePlace written by Assign, AugAssign, Append or Pop (inside an
   expression only Pop), and such a place is resolved from a target rooted
   at TopLevelNameTarget (src,id), whose accesses_target emits
   WriteAcc (StateRef (src,id)).  A write to another immutable updates
   another key of the same module's map (set_immutable), or another
   module's map (set_source_immutables keeps the others).  Internal calls
   keep cx.txn.target, and a reached callee's own accesses are in
   expr_accesses through reached_functions, as in
   vyperStorageAccessFrame's evaluate_finite_frame. *)

Theorem eval_expr_unwritten_immutable:
  !cx e st res st' env mods src id.
    eval_expr cx e st = (res,st') /\
    well_typed_expr env e /\ env_consistent env cx st /\
    state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    (!src fn ts mut nr args dflts ret body.
       MEM (src,fn) (reached_functions mods e) /\
       get_module_code cx src = SOME ts /\
       lookup_callable_function cx.in_deploy fn ts =
         SOME (mut,nr,args,dflts,ret,body) ==>
       ALOOKUP mods src = SOME ts /\
       (find_function fn ts = SOME (dflts,body) \/
        (dflts = [] /\ body = []))) /\
    ~MEM RiskyAcc (expr_accesses mods e) /\
    ~MEM (WriteAcc (StateRef (src,id))) (expr_accesses mods e) ==>
    FLOOKUP (case ALOOKUP st'.immutables cx.txn.target of
               NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) id =
    FLOOKUP (case ALOOKUP st.immutables cx.txn.target of
               NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) id
Proof
  cheat
QED
