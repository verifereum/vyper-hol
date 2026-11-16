# Fixed-path proof reuse and fallback disposition (C1.5.5.1.a)

This is an inert diagnostic note, not a new theorem, supplier, or Consumer
qualification. The compatibility filename does not imply a remaining fixed
residual. E0133 observed closure of `fixed_init`, including the reduced
19-premise assembly. No duplicate fixed-residual lemma is requested.

## Exact interface and retained source

`bodyFullForArrayLocalCaptureContext/raw-goals.txt` contains all free-variable
types, all 19 assumptions and the exact conclusion, in equivalent ASCII HOL
spelling, from m1042_t001. No premise is silently removed from that record.
`Consumer.base-and-patch.txt` is a lossless archive of the complete retained
Consumer using base commit 7fa477c887c95a0650b8fc18888caf726dfadf0f and blob
5a295bb9c0d27cebf180e7355caefe7dd3edac34. Its patch includes all subsequent
diagnostic edits; production Consumer was not modified for this publication.

Current archived source locations:
- 1356-1444: fixed_init setup and local facts.
- 1445-1455: application of the approved `fixed` antecedent by matching actual
  compiler, state, ghost, lookup and scope premises already in context.
- 1456-1480: retain 19 assumptions, discard only the rest, solve conjunction.
- 1481-1488: original already-closing premise proof retained in a comment.
- 1489-1531: selected endpoint/ghost witnesses and Head assembly.
- 1533: post-QED execution marker.

## Premise origins and discharge map

Assumption numbers refer to raw-goals.txt.

| Assumptions | Origin in retained fixed_init or inherited context | Use |
| --- | --- | --- |
| 0,1,2 | existing initial target pc/index/nonhalted facts; preserved by selection at 1470-1472 | direct matching |
| 3 | existing no-dalloca fact, selected at 1470 | direct matching; no alloca_inv shortcut |
| 4 | valid horizon witness obtained at 1389-1392 and live in context at selection | existential conclusion witnessed by H |
| 5 | inherited alloca_history, selected at 1469 | direct matching |
| 6 | established 1442-1444 using ent.type and abbreviation vs | direct matching |
| 7 | inherited ent.value, selected at 1468 | direct matching |
| 8 | established 1438-1441 from LENGTH vs = n (1359-1363) | direct matching |
| 9 | established 1401-1404 from local_ptrs_reserved | Var injectivity simplification then matching |
| 10 | established 1405-1408 from ret_pc_ok | direct matching |
| 11,12 | inherited return-buffer reservation and local_ptrs_reserved facts, selected 1463-1464 | direct matching |
| 13 | established 1435-1437 from not-fresh exclusion at 1409-1413 | direct matching |
| 14 | established 1431-1434 from generated-name equations | direct matching |
| 15 | inherited LENGTH bound, selected 1461 | direct matching |
| 16,17 | inherited typed memory size equality and bound, selected 1459-1460 | decide_tac derives type_memory_size tv < dimword (:256) |
| 18 | inherited distinct instruction IDs, selected 1458 | direct matching |

The solver is the retained conjunction proof: `rpt conj_tac`, matching facts,
linear arithmetic with the two size facts only, simplification of Var
injectivity, and the existing horizon witness. It neither strengthens the
seven cuts nor introduces a semantic assumption. There is no new exported
helper interface here.

## Observed execution and limits

- m1042_t001 captured the typed reduced sequent before solving.
- m1044_t001 ran the retained solver on those 19 premises and proceeded past
  fixed_init. m1045_t001 records
  `FIXED-INIT-AND-REDUCED-ASSEMBLY-CLOSED` from the post-QED marker.
- Neither `reduced-fixed-residual`, the old `fixed-residual`, nor `head-leaf`
  fallback was reached in that executed fixed_init path. This statement is
  limited to that prefix; it asserts nothing about common_round or shadow
  body linkage.
- m1050_t005 records the later dynamic_init MLOAD stage-equation failure at
  1547-1550. The Consumer build does not pass. Other suspended obligations
  remain owed; no theorem was finalised by this diagnostic.

Full evidence identifiers share prefix
`TO_statement_cases-L0016-20261116T193214352355Z_`.
Current readback and source comparison evidence:
`TO_statement_cases-L0016-20261116T200109121105Z_m1065_t002` (current diff),
`m1065_t003` (archive), `m1065_t004` (typed raw sequent), `m1065_t005` (marker),
`m1066_t002` (retained fixed_init source), `m1066_t004` (later failure).

Package acceptance would certify these observations and provenance only.
Ordinary helper builds/checks and assembled Consumer qualification remain
separate obligations. The seven LocalContracts quotations and frozen public
headers have not been edited by this archival work.
