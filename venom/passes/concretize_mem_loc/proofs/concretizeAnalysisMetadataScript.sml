Theory concretizeAnalysisMetadata
Ancestors
  concretizeAnalysisSizes concretizeMemLocDefs venomInst list finite_map

Theorem unique_mems_used_every:
  !xs. EVERY P xs ==> EVERY P (unique_mems_used xs)
Proof
  recInduct unique_mems_used_ind >> simp[unique_mems_used_def] >>
  rpt strip_tac >> gvs[] >> first_x_assum irule >>
  gvs[EVERY_MEM, MEM_FILTER]
QED

Theorem imported_mems_used_every:
  (!inst name args callee.
    MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label name :: args /\
    lookup_function name ctx.ctx_functions = SOME callee ==>
    EVERY P callee.fn_mems_used) ==>
  EVERY P (imported_mems_used ctx fn)
Proof
  strip_tac >> simp[imported_mems_used_def] >>
  irule unique_mems_used_every >>
  simp[EVERY_FLAT, EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[callee_mems_used_def] >>
  Cases_on `lookup_function s ctx.ctx_functions` >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >> gvs[EVERY_MEM]
QED

Theorem apply_context_layout_mems_every:
  static_alloca_items fn = SOME items /\
  EVERY (\(a,s). P (a,THE (FLOOKUP layout.cl_positions a),s)) items /\
  EVERY P (imported_mems_used ctx fn) ==>
  EVERY P (apply_context_concretize_layout ctx layout fn).fn_mems_used
Proof
  strip_tac >> simp[apply_context_concretize_layout_def] >>
  irule unique_mems_used_every >> simp[EVERY_MAP] >>
  gvs[EVERY_MEM] >> PairCases >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem imported_mems_used_excludes:
  (!inst name args callee.
    MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label name :: args /\
    lookup_function name ctx.ctx_functions = SOME callee ==>
    ~EXISTS (\(a,p,s). a = aid) callee.fn_mems_used) ==>
  ~EXISTS (\(a,p,s). a = aid) (imported_mems_used ctx fn)
Proof
  simp[GSYM EVERY_NOT_EXISTS] >> strip_tac >>
  irule imported_mems_used_every >> first_assum ACCEPT_TAC
QED

Theorem context_import_exclusion_size:
  (!inst name args callee.
    MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label name :: args /\
    lookup_function name ctx.ctx_functions = SOME callee ==>
    ~EXISTS (\(a,p,s). a = aid) callee.fn_mems_used) ==>
  context_alloca_size fn (imported_mems_used ctx fn) aid = get_alloca_size fn aid
Proof
  metis_tac[imported_mems_used_excludes, context_alloca_size_local]
QED

Theorem context_import_size_valid:
  !imports aid pos sz. EVERY (\(a,p,s). size_of a = SOME s) imports /\
  MEM (aid,pos,sz) imports ==> context_alloca_size fn imports aid = sz
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  simp[context_alloca_size_def, FIND_thm] >>
  rpt strip_tac >> gvs[] >> IF_CASES_TAC >> gvs[EVERY_MEM] >>
  first_x_assum drule >> simp[] >>
  rewrite_tac[GSYM context_alloca_size_def] >> metis_tac[]
QED
