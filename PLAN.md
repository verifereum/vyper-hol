# Fix vyperEvalPreservesImmutablesDomTheory

## Problem
Build fails at line 1227 with "Couldn't infer type for overloaded name Call" because the `Call` constructor was extended from 2 to 3 arguments in commit 97e41a6 (`AST: add default arguments and default return values (#49)`).

### Root cause changes:
1. **Call constructor**: `Call call_target (expr list)` → `Call call_target (expr list) (expr option)` (new `drv` default return value field)
2. **lookup_callable_function return type**: Changed from 4-tuple `(mutability # args # ret # body)` to 5-tuple `(mutability # args # dflts # ret # body)`
3. **ExtCall semantics**: New recursive call `eval_expr cx (THE drv)` when `returnData = []` and `IS_SOME drv` - this generates an additional induction hypothesis

## Changes needed

### 1. Simple pattern fixes (add `_` or `drv`)
- [ ] Line 1220/1227: `Call Send es` → `Call Send es _`
- [ ] Lines 1418-1419: `Call (ExtCall ...) es` → `Call (ExtCall ...) es drv`
- [ ] Line 1516: `Call (IntCall ...) es` → `Call (IntCall ...) es _`

### 2. case_Send_imm_dom IH update
- [ ] Check if the IH conditions (lines 1222-1225) changed shape from evaluate_ind
- [ ] Update IH to match new induction principle

### 3. case_ExtCall_imm_dom overhaul
- [ ] Add IH for the new `drv` recursive call: `eval_expr cx (THE drv)` preserves immutables dom
- [ ] Update proof to handle the new code path (`returnData = []` and `IS_SOME drv`)
- [ ] Reference: `vyperScopePreservingExprScript.sml` lines 229-368 shows how this was handled

### 4. case_IntCall_imm_dom tuple type fix
- [ ] Lines 1531, 1557-1559: Update tuple type from `function_mutability # (string # type) list # type # stmt list` to `function_mutability # (string # type) list # (num |-> expr) # type # stmt list` (or whatever the actual new type is)
- [ ] IH conditions (lines 1477-1516) may need updating for new tuple structure

### 5. Main induction (immutables_dom_mutual)
- [ ] Check if `evaluate_ind` generates additional cases for `drv` recursive call
- [ ] May need new `>-` entries in the case dispatch (lines 1582-1649)

## Strategy
1. Start HOL session, check actual IH shapes interactively
2. Fix patterns and IHs
3. Fix proofs
4. Verify build passes with holmake
