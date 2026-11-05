(* Set-level boundaries only; no whole-run confinement is assumed here. *)
Theory bodyPtrIntCallConfinement
Ancestors bodyPtrDefs decoderGhostFramePtr ptrSafeRun ptrDiscipline
  finite_map pred_set list

Definition intcall_site_outside_def:
  intcall_site_outside P (b:num,n:num) <=>
    DISJOINT P {i | b <= i /\ i < b + n}
End

Definition intcall_prov_outside_def:
  intcall_prov_outside P PG G <=>
    (!site. MEM (SOME site) PG ==> intcall_site_outside P site) /\
    (!x site. FLOOKUP G x = SOME site ==> intcall_site_outside P site)
End

Definition intcall_mem_frame_def:
  intcall_mem_frame P (tn0:taint) (tn:taint) <=>
    tn.t_mem INTER P SUBSET tn0.t_mem
End

Definition intcall_protected_def:
  intcall_protected cenv (es:evaluation_state) sa (s0:venom_state) =
    {i | (?aid off sz.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                 off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz) \/
    (?n b sz. local_region cenv es.scopes s0 n b sz /\
      b <= i /\ i < b + sz /\
      (!k. dynarray_len_at cenv n k ==> i < b + k \/ b + k + 32 <= i))}
End

Theorem intcall_mem_frame_refl:
  intcall_mem_frame P tn tn
Proof
  simp[intcall_mem_frame_def, INTER_SUBSET]
QED

Theorem intcall_mem_frame_trans:
  intcall_mem_frame P tn0 tn1 /\ intcall_mem_frame P tn1 tn2 ==>
  intcall_mem_frame P tn0 tn2
Proof
  simp[intcall_mem_frame_def] >> SET_TAC[]
QED

Theorem intcall_ghost_kept_frame:
  ghost_kept cenv es sa G0 tn0 s0 G tn <=>
  (!x. not_fresh_at sa x ==>
       FLOOKUP G x = FLOOKUP G0 x /\
       op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  intcall_mem_frame (intcall_protected cenv es sa s0) tn0 tn
Proof
  simp[ghost_kept_def, intcall_mem_frame_def, intcall_protected_def,
       SUBSET_DEF, IN_INTER, GSPECIFICATION] >> metis_tac[]
QED

Theorem intcall_mem_frame_step:
  new_site_bytes s t SUBSET COMPL P /\
  written_taint tn inst s SUBSET COMPL P ==>
  intcall_mem_frame P tn (step_taint inst s t tn)
Proof
  strip_tac >> drule_all step_taint_memory_bound >>
  simp[intcall_mem_frame_def, SUBSET_DEF, IN_INTER, IN_UNION,
       IN_COMPL] >> metis_tac[]
QED

Theorem intcall_prov_outside_invoke:
  intcall_prov_outside P PG G ==>
  intcall_prov_outside P (MAP (op_prov G) ops) FEMPTY
Proof
  simp[intcall_prov_outside_def, MEM_MAP] >> rpt strip_tac >>
  rename1 `SOME site = op_prov G op` >>
  Cases_on `op` >> gvs[op_prov_def] >> metis_tac[]
QED

Theorem intcall_mem_frame_invoke:
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  intcall_mem_frame P tn0
    (SND (ghost_blocks fuel ctx callee (MAP (op_prov G) ops) FEMPTY
            (tn with t_var := FEMPTY) cs)) ==>
  intcall_mem_frame P tn0 (SND (ghost_step fuel ctx PG G tn inst s))
Proof
  strip_tac >> drule_all ghost_step_invoke >>
  disch_then (fn th => rewrite_tac[th]) >>
  gvs[intcall_mem_frame_def]
QED

Theorem intcall_mem_frame_reset:
  intcall_mem_frame P tn0 (tn with t_var := FEMPTY) <=>
  intcall_mem_frame P tn0 tn
Proof
  simp[intcall_mem_frame_def]
QED
