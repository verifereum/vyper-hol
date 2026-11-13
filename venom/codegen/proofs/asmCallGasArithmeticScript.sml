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

(* Expansion charges depend on rounded words, not the old allocation. *)
Theorem memory_cost_word_mono:
  word_size a <= word_size b ==> memory_cost a <= memory_cost b
Proof
  strip_tac >>
  `word_size a * word_size a <= word_size b * word_size b` by
    (irule LESS_MONO_MULT2 >> simp[]) >>
  `word_size a * word_size a DIV 512 <= word_size b * word_size b DIV 512` by
    (irule DIV_LE_MONOTONE >> simp[]) >>
  gvs[memory_cost_def, vfmConstantsTheory.memory_cost_per_word_def]
QED

Theorem memory_expansion_cost_bound:
  endpoint <= H ==>
  memory_expansion_cost old (word_size endpoint * 32) <= memory_cost H
Proof
  strip_tac >>
  Cases_on `word_size endpoint * 32 <= old`
  >- simp[memory_expansion_cost_def, MAX_DEF] >>
  `word_size endpoint <= word_size H` by
    (simp[vfmConstantsTheory.word_size_def] >> irule DIV_LE_MONOTONE >> simp[]) >>
  `word_size (word_size endpoint * 32) = word_size endpoint` by
    simp[vfmConstantsTheory.word_size_def, ADD_DIV_ADD_DIV] >>
  `memory_cost (word_size endpoint * 32) <= memory_cost H` by
    (irule memory_cost_word_mono >> simp[]) >>
  simp[memory_expansion_cost_def, MAX_DEF] >> decide_tac
QED

Theorem call_memory_expansion_cost_bound:
  (az = 0 \/ ao + az <= H) /\ (rs = 0 \/ ro + rs <= H) ==>
  memory_expansion_cost old
    (if 0 < SND (max_expansion_range (ao,az) (ro,rs))
     then word_size (FST (max_expansion_range (ao,az) (ro,rs)) +
                     SND (max_expansion_range (ao,az) (ro,rs))) * 32
     else 0) <= memory_cost H
Proof
  strip_tac >>
  Cases_on `az = 0` >> Cases_on `rs = 0` >>
  gvs[max_expansion_range_def] >>
  rpt IF_CASES_TAC >> simp[] >>
  metis_tac[memory_expansion_cost_bound, MULT_COMM]
QED

(* CREATE's bounded initcode and its single memory range. *)
Theorem create_upfront_cost_bound:
  sz <= 2 * max_code_size /\ (sz = 0 \/ off + sz <= H) ==>
  32000 + (if two then 8 else 2) * word_size sz +
    memory_expansion_cost old
      (if 0 < sz then word_size (off + sz) * 32 else 0) <=
    44288 + memory_cost H
Proof
  strip_tac >>
  `word_size sz <= 1536` by
    (gvs[vfmConstantsTheory.word_size_def,
         vfmConstantsTheory.max_code_size_def] >>
     qspec_then `32` (qspecl_then [`sz + 31`, `49183`] mp_tac)
       DIV_LE_MONOTONE >> simp[]) >>
  `memory_expansion_cost old
      (if 0 < sz then word_size (off + sz) * 32 else 0) <= memory_cost H` by
    (Cases_on `sz = 0`
     >- simp[memory_expansion_cost_def, memory_cost_def,
             vfmConstantsTheory.word_size_def, MAX_DEF] >>
     simp[] >> metis_tac[memory_expansion_cost_bound, MULT_COMM]) >>
  Cases_on `two` >> gvs[] >> decide_tac
QED

Theorem create_forwarded_gas_reserve:
  k <= B /\ B <= L ==>
  (L - B) DIV 64 <=
    (L - k) - ((L - k) - (L - k) DIV 64)
Proof
  strip_tac >>
  `(L - k) DIV 64 <= L - k` by simp[DIV_LESS_EQ] >>
  `(L - k) - ((L - k) - (L - k) DIV 64) = (L - k) DIV 64` by decide_tac >>
  asm_rewrite_tac[] >> irule DIV_LE_MONOTONE >> simp[]
QED
