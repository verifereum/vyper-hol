(* Representation transport shared by compatibility and ambient interfaces. *)
structure typedCopyRobustLib =
struct
open HolKernel boolLib bossLib
open bodyPtrDefsTheory valueEncodingPropsTheory representationCleanPtrTheory
     valueCopyBytesTheory loweringPostsTheory exprSimDefsTheory exprSimPropsTheory

val source =
  qpat_x_assum `_ /\ _` strip_assume_tac >>
  `val_in_memory stv v (w2n a) s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  qspecl_then [`tenv`, `sty`, `stv`] mp_tac bytestring_type_value >>
  asm_rewrite_tac[] >> strip_tac >>
  (conj_tac >-
     (gvs[valueEncodingTheory.val_in_memory_def, venomStateTheory.mload_def,
           valueEncodingTheory.mem_word_at_def] >> metis_tac[]) >>
   gvs[] >> FIRST [drule robust_val_in_memory_bytes_clean,
                   drule robust_val_in_memory_string_clean] >> simp[]);

fun destination copied_window =
  `32 <= n /\ 32+len <= n` by
    (qspec_then `32` mp_tac arithmeticTheory.DIVISION >>
     (impl_tac >- decide_tac) >>
     disch_then (qspec_then `len+31` strip_assume_tac) >>
     qpat_x_assum `n = _` SUBST1_TAC >> decide_tac) >>
  rpt gen_tac >> disch_tac >>
  `mem_bytes_at (w2n b+0) 32 m = mem_bytes_at (w2n a+0) 32 s.vs_memory` by
    (irule copied_window >>
     qexistsl_tac [`n`, `sf`, `tn.t_mem`, `tnf.t_mem`] >>
     asm_rewrite_tac[] >> gvs[]) >>
  `mem_bytes_at (w2n b+32) len m = mem_bytes_at (w2n a+32) len s.vs_memory` by
    (irule copied_window >>
     qexistsl_tac [`n`, `sf`, `tn.t_mem`, `tnf.t_mem`] >>
     asm_rewrite_tac[] >> gvs[]) >>
  `val_in_memory stv v (w2n a) s.vs_memory` by
    (qpat_x_assum `!m. mem_agree_outside tn.t_mem _ m ==> _` irule >>
     simp[mem_agree_outside_def]) >>
  `val_in_memory dtv v (w2n a) s.vs_memory` by
    (irule bytestring_val_in_memory_transfer >> conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`sty`, `dty`, `tenv`, `stv`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `!m. mem_agree_outside tn.t_mem _ m ==> _` kall_tac >>
  qpat_x_assum `val_in_memory stv v _ _` kall_tac >>
  qspecl_then [`tenv`, `dty`, `dtv`] mp_tac bytestring_type_value >>
  asm_rewrite_tac[] >> strip_tac >>
  gvs[valueEncodingTheory.val_in_memory_def,
      valueEncodingTheory.mem_word_at_def, GSYM valueEncodingTheory.mem_bytes_at_def];

fun robust (execution, exterior, copied_window, ambient) =
  rpt gen_tac >> disch_tac >>
  `mload (w2n a) s = n2w len /\
   (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
   (!i. w2n a+32 <= i /\ i < w2n a+32+len ==> i NOTIN tn.t_mem)` by source >>
  qpat_x_assum `_ /\ _` strip_assume_tac >>
  drule_all execution >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`]
    (qx_choose_then `Gf` (qx_choose_then `tnf` (qx_choose_then `sf` strip_assume_tac)))) >>
  drule exterior >> disch_then drule >>
  disch_then (assume_tac o SIMP_RULE bool_ss [AND_IMP_INTRO]) >>
  ambient >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> asm_rewrite_tac[] >>
  (conj_tac >- destination copied_window >> gvs[] >>
   rpt strip_tac >> qpat_x_assum `!ft fv p m. _` irule >> asm_rewrite_tac[]);
end
