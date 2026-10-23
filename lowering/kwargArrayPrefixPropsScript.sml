(* Typed payload facts only: execution and allocation framing are separate. *)
Theory kwargArrayPrefixProps
Ancestors typedKwargBufferProps valueEncoding list arithmetic

Theorem elems_in_memory_indexed:
  !vs addr tv mem.
    elems_in_memory vs addr tv mem <=>
    !j. j < LENGTH vs ==>
      val_in_memory tv (EL j vs) (addr + j * type_memory_size tv) mem
Proof
  Induct_on `vs`
  >- simp[val_in_memory_def]
  >> rpt gen_tac >> simp[val_in_memory_def] >> eq_tac
  >- (rpt strip_tac >> Cases_on `j` >> gvs[] >>
      first_x_assum drule >> asm_simp_tac std_ss [EL, TL, HD, MULT_CLAUSES, AC ADD_ASSOC ADD_COMM])
  >> strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[])
  >> rpt strip_tac >> first_x_assum (qspec_then `SUC j` mp_tac) >>
  asm_simp_tac std_ss [EL, TL, HD, MULT_CLAUSES, AC ADD_ASSOC ADD_COMM]
QED

Theorem kwarg_array_prefix_indexed:
  kwarg_array_prefix tv vs addr i mem <=>
  i <= LENGTH vs /\
  (!j. j < i ==>
    val_in_memory tv (EL j vs) (addr + j * type_memory_size tv) mem)
Proof
  simp[kwarg_array_prefix_def, elems_in_memory_indexed, LENGTH_TAKE] >>
  Cases_on `i <= LENGTH vs` >> simp[] >>
  metis_tac[EL_TAKE]
QED

Theorem kwarg_array_prefix_transfer:
  kwarg_array_prefix tv vs addr i mem /\
  (!j. j < i ==>
    val_in_memory tv (EL j vs) (addr + j * type_memory_size tv) mem') ==>
  kwarg_array_prefix tv vs addr i mem'
Proof
  simp[kwarg_array_prefix_indexed]
QED

Theorem kwarg_array_prefix_extend:
  i < LENGTH vs /\ kwarg_array_prefix tv vs addr i mem /\
  val_in_memory tv (EL i vs) (addr + i * type_memory_size tv) mem ==>
  kwarg_array_prefix tv vs addr (SUC i) mem
Proof
  rw[kwarg_array_prefix_indexed] >>
  Cases_on `j = i` >> gvs[] >> first_x_assum irule >> decide_tac
QED

(* val_in_memory describes payload only; it imposes no bound or val_wf test. *)
Theorem kwarg_array_prefix_dynamic_complete:
  kwarg_array_prefix tv vs (addr + 32) (LENGTH vs) mem /\
  mem_word_at addr mem = n2w (LENGTH vs) ==>
  val_in_memory (ArrayTV tv (Dynamic bound))
    (ArrayV (DynArrayV vs)) addr mem
Proof
  simp[val_in_memory_def] >> metis_tac[kwarg_array_prefix_complete]
QED

(* Check the transitive proof dependencies, including imported boundary facts. *)
val _ = List.app (fn th =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail "kwarg array prefix theorem has oracle/axiom dependencies")
  [elems_in_memory_indexed, kwarg_array_prefix_indexed,
   kwarg_array_prefix_transfer, kwarg_array_prefix_extend,
   kwarg_array_prefix_dynamic_complete];
