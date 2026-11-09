Theory bodyIntCallCompilerFloor
Ancestors
  bodyIntCallCompilerEmit bodyIntCallCompilerInterval compileEnv exprLoweringProps

Theorem intcall_interval_next_var:
  intcall_compiler_interval k a b ==> a.cs_next_var <= b.cs_next_var
Proof
  simp[intcall_compiler_interval_def, ci_mono_def]
QED

Theorem intcall_interval_bind_floor:
  (!a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (mf a))) /\
  (!v a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (mg v a))) /\
  k <= s.cs_next_var ==>
  intcall_compiler_interval k s (SND (comp_bind mf mg s))
Proof
  strip_tac >> Cases_on `mf s` >> rename1 `mf s = (v,b)` >>
  `intcall_compiler_interval k s b` by metis_tac[pairTheory.SND] >>
  `k <= b.cs_next_var` by
    (drule intcall_interval_next_var >> simp[]) >>
  simp[comp_bind_def] >> irule intcall_compiler_interval_trans >>
  qexists `b` >> simp[]
QED

Theorem intcall_interval_ignore_bind_floor:
  (!a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (mf a))) /\
  (!a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (mg a))) /\
  k <= s.cs_next_var ==>
  intcall_compiler_interval k s (SND (comp_ignore_bind mf mg s))
Proof
  strip_tac >> simp[comp_ignore_bind_def] >>
  irule intcall_interval_bind_floor >> simp[]
QED
