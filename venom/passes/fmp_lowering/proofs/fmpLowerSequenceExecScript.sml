(* Straight-line operational composition of the production indexed walker.
 * The point invariant includes the concrete ledger/coverage and fresh-name
 * conditions required by local simulations. The rule does not establish them
 * from static plan acceptance, and does not model block control flow. *)
Theory fmpLowerSequenceExec
Ancestors
  fmpLowerIndexedProps fmpLowerRestoreExec analysisSimDefs analysisSimProofsBase list

(* The local obligations are separate for restore execution and the original
 * instruction's expansion. In particular the latter sees the restored state,
 * not the pre-restore interpreter FMP. A successful local step excludes
 * terminators, calls and PHIs unless a caller supplies their own semantics. *)
Theorem fmp_lower_indexed_exec:
  !insts k supply restores code leftover supply' s.
  fmp_lower_indexed infos ctx runner label k supply restores insts =
    SOME (code,leftover,supply') /\
  invariant k supply restores s /\
  (!j inst sp plan bases later prefix sp0 head sp1 st.
    MEM inst insts /\
    fmp_select_point_restores (label,j) plan = (bases,later) /\
    fmp_emit_restores runner sp bases = (prefix,sp0) /\
    fmp_lower_inst infos ctx runner sp0 inst = SOME (head,sp1) /\
    invariant j sp plan st ==>
    ?restored next.
      run_insts fuel ctx prefix st = OK restored /\
      run_insts fuel ctx head restored = OK next /\
      invariant (SUC j) sp1 later next) ==>
  ?final.
    run_insts fuel ctx code s = OK final /\
    invariant (k + LENGTH insts) supply' leftover final
Proof
  Induct >- simp[fmpLowerDefsTheory.fmp_lower_indexed_def, run_insts_def] >>
  rpt gen_tac >> simp[fmp_lower_indexed_cons] >> rpt strip_tac >>
  `?restored next.
     run_insts fuel ctx prefix s = OK restored /\
     run_insts fuel ctx head restored = OK next /\
     invariant (SUC k) s1 later next` by metis_tac[MEM] >>
  `?final. run_insts fuel ctx tail next = OK final /\
     invariant (SUC k + LENGTH insts) supply' leftover final` by
    (first_x_assum irule >> metis_tac[MEM]) >>
  qexists_tac `final` >>
  fs[run_insts_append, arithmeticTheory.ADD_CLAUSES]
QED

(* Concrete instantiation at a DALLOCA reclaim point. This connects the local
 * execution boundary to the actual indexed walker and its supply threading. *)
Theorem fmp_lower_indexed_restored_dalloca:
  fmp_lower_indexed infos ctx runner label k supply restores [inst] =
    SOME (code,leftover,supply') /\
  fmp_select_point_restores (label,k) restores = ([target],later) /\
  fmp_emit_restores runner supply [target] = (prefix,sp) /\
  inst.inst_opcode = DALLOCA /\ inst.inst_operands = [size_op] /\
  inst.inst_outputs = [out] /\
  fresh_ir_var sp = (plus31,s1) /\
  fresh_ir_var s1 = (mask,s1a) /\ fresh_ir_var s1a = (aligned,s2) /\
  fresh_inst_id s2 = (ai,s3) /\ fresh_inst_id s3 = (ni,s3a) /\
  fresh_inst_id s3a = (mi,s4) /\ fresh_inst_id s4 = (bi,s5) /\
  lookup_var target s = SOME value /\
  eval_operand size_op s = SOME sz /\ size_op <> Var runner /\
  ALL_DISTINCT [plus31;mask;aligned;runner;out] ==>
  run_insts fuel ctx code s =
    OK (update_var runner (value + n2w (ceil32 (w2n sz)))
         (update_var out value
           (update_var aligned (n2w (ceil32 (w2n sz)))
             (update_var mask (~31w)
               (update_var plus31 (sz + 31w) (update_var runner value s))))))
Proof
  strip_tac >>
  `fmp_lower_inst_shape infos ctx inst` by
    simp[fmpLowerDefsTheory.fmp_lower_inst_shape_def] >>
  drule_all fmpLowerExecTheory.fmp_lower_dalloca_code >> strip_tac >>
  fs[fmpLowerDefsTheory.fmp_lower_indexed_def] >> gvs[] >>
  drule_all fmp_emit_restore_single >> strip_tac >>
  simp[run_insts_append] >>
  irule fmpLowerExecTheory.dalloca_expansion_exec >>
  simp[eval_operand_restore, venomStateTheory.lookup_var_def,
       venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Relocation frontier. The raw run allocates from the raw FMP, which starts
 * at raw0; the lowered run allocates from the runner, which starts at fmp0.
 * Restores only lower the runner, so the lowered frontier lo is bounded by
 * the raw one shifted down by raw0 - fmp0, not equal to it. *)
Definition fmp_frontier_rel_def:
  fmp_frontier_rel fmp0 raw0 lo (raw_fmp:bytes32) <=>
    fmp0 <= raw0 /\ fmp0 <= lo /\ raw0 <= w2n raw_fmp /\
    lo - fmp0 <= w2n raw_fmp - raw0
End

Theorem fmp_frontier_rel_le:
  fmp_frontier_rel fmp0 raw0 lo raw_fmp ==> lo <= w2n raw_fmp
Proof
  simp[fmp_frontier_rel_def]
QED

Theorem fmp_frontier_rel_dalloca:
  fmp_frontier_rel fmp0 raw0 lo raw_fmp /\
  w2n raw_fmp + n < dimword (:256) ==>
  lo + n < dimword (:256) /\
  raw_fmp + n2w n = n2w (w2n raw_fmp + n) /\
  w2n (raw_fmp + n2w n) = w2n raw_fmp + n /\
  fmp_frontier_rel fmp0 raw0 (lo + n) (raw_fmp + n2w n)
Proof
  strip_tac >> drule fmp_frontier_rel_le >> strip_tac >>
  `raw_fmp + n2w n = n2w (w2n raw_fmp + n)` by
    simp[GSYM wordsTheory.word_add_n2w] >>
  gvs[fmp_frontier_rel_def]
QED

Theorem fmp_restore_frontier:
  fmp_frontier_rel fmp0 raw0 lo raw_fmp /\ fmp0 <= newtop /\ newtop <= lo ==>
  fmp_frontier_rel fmp0 raw0 newtop raw_fmp
Proof
  simp[fmp_frontier_rel_def]
QED

(* P9b no-wrap. A raw DALLOCA that does not wrap is matched by the lowered
 * expansion from a runner at a related frontier, which does not wrap either. *)
Theorem dalloca_relocate_exec:
  inst.inst_opcode = DALLOCA /\ inst.inst_operands = [size_op] /\
  inst.inst_outputs = [out] /\
  eval_operand size_op s_raw = SOME sz /\
  eval_operand size_op s_low = SOME sz /\
  lookup_var runner s_low = SOME (n2w lo) /\
  ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
  w2n s_raw.vs_fmp + ceil32 (w2n sz) < dimword (:256) /\
  fmp_frontier_rel fmp0 raw0 lo s_raw.vs_fmp ==>
  step_inst_base inst s_raw =
    OK (update_var out s_raw.vs_fmp
      (s_raw with vs_fmp := n2w (w2n s_raw.vs_fmp + ceil32 (w2n sz)))) /\
  run_insts fuel ctx
    [mk_inst ai ADD [Lit 31w;size_op] [plus31];
     mk_inst ni NOT [Lit 31w] [mask];
     mk_inst mi AND [Var plus31;Var mask] [aligned];
     mk_inst bi BUMP [Var runner;Var aligned] [out;runner]] s_low =
    OK (update_var runner (n2w (lo + ceil32 (w2n sz)))
         (update_var out (n2w lo)
           (update_var aligned (n2w (ceil32 (w2n sz)))
             (update_var mask (~31w)
               (update_var plus31 (sz + 31w) s_low))))) /\
  lo + ceil32 (w2n sz) < dimword (:256) /\
  fmp_frontier_rel fmp0 raw0 (lo + ceil32 (w2n sz))
    (n2w (w2n s_raw.vs_fmp + ceil32 (w2n sz)))
Proof
  strip_tac >>
  drule_all fmp_frontier_rel_dalloca >> strip_tac >>
  rpt conj_tac
  >- simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs]
  >- (drule_all fmpLowerExecTheory.dalloca_expansion_exec >>
      simp[wordsTheory.word_add_n2w])
  >- simp[]
  >> gvs[]
QED

val _ = List.app (fn (name,th) =>
  if null (Thm.hyp th) andalso
     List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected dependency in " ^ name))
  (DB.thms "fmpLowerSequenceExec");
