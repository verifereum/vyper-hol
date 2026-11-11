(* Numeric gas interfaces for calls in the fetched EVM semantics. *)
Theory asmCallGasArithmetic
Ancestors
  vfmExecution arithmetic

Theorem call_gas_refunded_overhead:
  call_gas value gas L mc oc = (dg, stipend) ==>
  sc + dg + mc <= stipend + sc + mc + oc
Proof
  simp[call_gas_def] >> rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem call_gas_budget_reserve:
  call_gas value gas L mc oc = (dg, stipend) /\
  mc + oc + 6400 <= B /\ B <= L /\ sc <= 100 ==>
  sc + dg + mc <= L /\
  (L - B) DIV 64 <= L - (sc + dg + mc)
Proof
  strip_tac >>
  `~(L < mc + oc)` by decide_tac >>
  gvs[call_gas_def] >>
  qmatch_goalsub_abbrev_tac `x DIV 64` >>
  `x + mc + oc = L` by (simp[Abbr `x`] >> decide_tac) >>
  `L - (mc + (oc + x DIV 64)) = x - x DIV 64` by
    (simp[Abbr `x`] >> decide_tac) >>
  asm_rewrite_tac[] >>
  `6400 <= x` by (simp[Abbr `x`] >> decide_tac) >>
  `100 <= x DIV 64` by
    (qspec_then `64` (qspecl_then [`6400`, `x`] mp_tac) DIV_LE_MONOTONE >> simp[]) >>
  `x DIV 64 <= x` by simp[DIV_LESS_EQ] >>
  `MIN gas (x - x DIV 64) <= x - x DIV 64` by simp[] >>
  `(L - B) DIV 64 <= (x - 6400) DIV 64` by
    (irule DIV_LE_MONOTONE >> simp[] >> simp[Abbr `x`] >> decide_tac) >>
  `(x - 6400) DIV 64 = x DIV 64 - 100` by
    (mp_tac (Q.INST [`n` |-> `64`, `q` |-> `100`, `m` |-> `x`] DIV_SUB) >> simp[]) >>
  decide_tac
QED
