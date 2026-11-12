Theory bodyIntCallCompilerInterval
Ancestors
  exprLoweringProps fragExec compileEnv

(* A fixed variable-counter floor is retained across composition.  Only
   consumed instruction ids are constrained; pre-existing code is arbitrary. *)
Definition intcall_compiler_interval_def:
  intcall_compiler_interval k a b <=>
    ci_mono a b /\
    !func n. fn_has_code a b func /\
      a.cs_next_id <= n /\ n < b.cs_next_id ==>
      ?inst. MEM inst (fn_insts func) /\ inst.inst_id = n /\
        (inst.inst_opcode = ALLOCA ==>
          !out. MEM out inst.inst_outputs ==>
            ?j. k <= j /\ out = STRING #"%" (toString j))
End

Theorem intcall_compiler_interval_refl:
  intcall_compiler_interval k a a
Proof
  simp[intcall_compiler_interval_def, ci_mono_refl]
QED

Theorem intcall_compiler_interval_trans:
  intcall_compiler_interval k a b /\
  intcall_compiler_interval k b c ==>
  intcall_compiler_interval k a c
Proof
  rw[intcall_compiler_interval_def]
  >- (gvs[ci_mono_def] >>
      irule cs_extends_trans >> qexists `b` >> simp[]) >>
  `fn_has_code a b func /\ fn_has_code b c func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  Cases_on `n < b.cs_next_id`
  >- (qpat_x_assum `!func n. fn_has_code a b func /\ _ ==> _`
        (qspecl_then [`func`, `n`] mp_tac) >> simp[]) >>
  qpat_x_assum `!func n. fn_has_code b c func /\ _ ==> _`
    (qspecl_then [`func`, `n`] mp_tac) >> simp[]
QED

Theorem intcall_compiler_interval_floor:
  k' <= k /\ intcall_compiler_interval k a b ==>
  intcall_compiler_interval k' a b
Proof
  rw[intcall_compiler_interval_def] >>
  first_x_assum drule_all >> strip_tac >>
  qexists `inst` >> simp[] >> rpt strip_tac >>
  gvs[] >>
  qpat_x_assum `!out. MEM out _ ==> _`
    (qspec_then `out` mp_tac) >> simp[] >>
  strip_tac >> qexists `j` >> simp[]
QED

Theorem intcall_compiler_interval_bind:
  (!a. intcall_compiler_interval k a (SND (mf a))) /\
  (!v a. intcall_compiler_interval k a (SND (mg v a))) ==>
  intcall_compiler_interval k s (SND (comp_bind mf mg s))
Proof
  strip_tac >> simp[comp_bind_def, pairTheory.UNCURRY] >>
  Cases_on `mf s` >> gvs[] >>
  irule intcall_compiler_interval_trans >>
  qexists `SND (mf s)` >> simp[]
QED

Theorem intcall_compiler_interval_ignore_bind:
  (!a. intcall_compiler_interval k a (SND (mf a))) /\
  (!a. intcall_compiler_interval k a (SND (mg a))) ==>
  intcall_compiler_interval k s (SND (comp_ignore_bind mf mg s))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule intcall_compiler_interval_bind >> simp[]
QED
