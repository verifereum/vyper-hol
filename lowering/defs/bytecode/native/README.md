# Native bytecode parity runner

## Overview

The parity theories in `../eval/` prove, by `EVAL`, that `compile_vyper`
produces exactly the deployment and runtime bytes of the pinned Python
compiler for each of the 101 fixtures in `../python-o1-no-asm-opt/`. They are
kernel-checked and slow, which is why the rollup is opt-in.

This directory runs the same check as compiled Standard ML. The equations
`EVAL` uses for `compile_vyper` are printed by EmitML and compiled. The
result is trusted rather than kernel-checked. It runs all 101 fixtures in
about a second, so it can run on every change; the `EVAL` theories remain the
proof.

## Files

- `compilerNativeEmitScript.sml`: the generator, a theory script that
  produces no theorems. It writes `compilerNativeML.sml` (a holbuild extra
  output, not checked in).
- `compilerNativeRuntime.sml`: native implementations of the HOL primitives
  the generated code calls (numbers, integers, words, characters, finite
  maps, sets).
- `compilerNativeParity.sml`: the runner. It compiles each fixture natively
  and compares the bytes with its oracle file.

## Use

```sh
holbuild build --skip-checkpoints --skip-proof-steps compilerNativeEmitTheory
holbuild executable bytecode_parity_native
cd lowering/defs/bytecode
./native/bytecode_parity_native.exe python-o1-no-asm-opt            # all fixtures
./native/bytecode_parity_native.exe python-o1-no-asm-opt add_arg.hex  # one
```

Each fixture prints `PASS` or `FAIL` with its time. The exit status is
non-zero unless every selected fixture matches.

## What the generator exports

It starts from `compile_vyper (K SOME) (o1_policy all_capabilities)` and the
fixture programs. From there it follows the constants of `EVAL`'s compset:
about 1600 constants and 105 datatypes. For each constant it takes the
compset's rewrite rules that read as definitions: an unconditional equation
whose left side applies the constant to variables, constructors and literals.

The rest of the pipeline makes those equations printable and executable in
Standard ML:

- **Equation choice.** When a constant's compset rules are not all of that
  form, its stored definition is used instead. Examples are numeral patterns
  such as `TAKE`'s `NUMERAL (BIT1 n)` and side conditions. Without this
  switch the function would be partial in ML.
- **Patterns.** Patterns on `SUC` become a guard, because natives are
  arbitrary-precision integers.
- **Record literals.** `<| f := v; ... |>` is a chain of updates on `ARB`;
  it becomes a constructor application.
- **Parentheses.** Nested `case` and `fn` expressions that end a case arm
  are wrapped so that EmitML prints parentheses. Without them a following
  arm would parse as part of the nested expression.
- **Strict evaluation.** Native code is strict where `EVAL` is not.
  - `EVAL` can carry a quantified condition or an `ARB` placeholder
    unevaluated in a value it later discards. Native code would have to
    evaluate it.
  - So the generator rewrites with proved restatements. `FDOM m SUBSET s`
    becomes `FEVERY`, and bounded quantifiers become `EXISTS`/`EVERY`. A
    proved computable equation covers `lower_dload_invalidates_layout`.
  - Any `ARB` left becomes a default value of its type.
  - A quantifier still left at run time raises `Stuck` and names its
    definition.

## Trust

Mismatches and failures are reliable: a `FAIL` means the native compiler
disagreed with the oracle or stopped. A `PASS` relies on:

- EmitML printing the equations faithfully;
- the runtime implementing each primitive as its HOL definition;
- the approximations below.

The approximations:

- Finite maps are association lists with distinct keys, newest first. Direct
  map equality is extensional (`hn_fmap_eq`). Equality on records that
  contain maps compares these lists. So two equal maps built in different
  orders compare unequal, where HOL says they are equal.
- `ARB` is a fixed default value; in HOL it is unspecified.
- Natives are total where `EVAL` might stop. For example, `hn_fmap_eq`
  decides map equality that `EVAL` may leave unevaluated.

For these reasons the native run is a fast regression check, and the `EVAL`
parity theories are still needed for a proof.
