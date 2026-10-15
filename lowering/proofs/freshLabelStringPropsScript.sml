(* Decimal label strings: digit facts and unique final separator.
 * TOP-LEVEL: decimal_suffix_inj -- unrestricted prefixes, decimal suffixes.
 * Helpers: isDigit_HEX_decimal, toString_digits, separator_prefix_inj.
 * No compiler-state or admitted label facts are used here.
 *)
Theory freshLabelStringProps
Ancestors
  ASCIInumbers numposrep arithmetic list rich_list string

(* ===== Decimal digits ===== *)

Theorem isDigit_HEX_decimal:
  !n. n < 10 ==> isDigit (HEX n)
Proof
  simp[GSYM MEM_COUNT_LIST] >> gen_tac >> EVAL_TAC >>
  strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem toString_digits:
  EVERY isDigit (toString n)
Proof
  rw[num_to_dec_string_def, n2s_def, EVERY_MAP] >>
  irule EVERY_MONOTONIC >> qexists_tac `$> 10` >> simp[] >>
  metis_tac[isDigit_HEX_decimal, GREATER_DEF, n2l_BOUND,
            DECIDE ``0n < 10``]
QED

(* ===== Separator cancellation ===== *)

(* Reading from the digit end, the first separator fixes the split.
   The tails a and b are unrestricted; in particular they may contain sep. *)
Theorem separator_prefix_inj:
  !d e a b sep.
    ~MEM sep d /\ ~MEM sep e /\
    d ++ sep::a = e ++ sep::b ==>
    d = e /\ a = b
Proof
  Induct_on `d` >> rpt gen_tac >> Cases_on `e` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem decimal_suffix_inj:
  !a b d e.
    EVERY isDigit d /\ EVERY isDigit e /\
    a ++ "_" ++ d = b ++ "_" ++ e ==>
    a = b /\ d = e
Proof
  rpt gen_tac >> strip_tac >>
  `~isDigit #"_"` by EVAL_TAC >>
  `~MEM #"_" d /\ ~MEM #"_" e` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `_ = _` (mp_tac o AP_TERM ``REVERSE : string -> string``) >>
  PURE_REWRITE_TAC[REVERSE_APPEND, REVERSE_DEF, APPEND] >> strip_tac >>
  `REVERSE d = REVERSE e /\ REVERSE a = REVERSE b` by
    (irule separator_prefix_inj >> qexists_tac `#"_"` >>
     fs[MEM_REVERSE, APPEND_ASSOC]) >>
  gvs[]
QED
