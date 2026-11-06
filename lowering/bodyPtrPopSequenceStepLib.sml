structure bodyPtrPopSequenceStepLib =
struct
open HolKernel Parse boolLib bossLib;
open bodyPtrPopSequenceStepTheory bodyPtrPopEmptyTaintTheory;

(* Check empty-taint observations before evaluating access and step facts.
   Never unfold symbolic lookups into one comparison per populated register. *)
val pop_sequence_step_tac =
  ho_match_mp_tac pop_inst_seq_ptr_cons_exists >>
  (conj_tac >- (
    rewrite_tac[ptrSafeRunTheory.ptr_inst_ok_def] >>
    (conj_tac >- (rewrite_tac[ptrDisciplineTheory.access_ok_def] >>
      CONV_TAC (computeLib.RESTR_EVAL_CONV [``contextCodegenRel$in_revert_forward``]) >> simp[])) >>
    (conj_tac >- (irule pop_taint_ok_empty >>
      (conj_tac >- (simp[] >> rpt (ho_match_mp_tac pop_fupdate_taint_empty) >> simp[])) >>
      simp[])) >> EVAL_TAC >> simp[])) >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``fragGasSeqPtr$inst_seq_ptr``]) >> simp[];
end
