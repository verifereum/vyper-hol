(* Range transport is independent of successful execution.  In each opcode
   branch invert the target operand shape and range membership first; only
   then use source operand definedness and size equality.  DRET is multi-range
   and deliberately excluded from this single-access boundary. *)
Theory lowerDloadRangeTransport
Ancestors contextCodegenRel codegenRel memLocDefs venomState venomInst words list
          venomExecProofs

Theorem ld_single_access_range_transport:
  !inst s t.
    inst.inst_opcode <> DRET /\
    (!op y. MEM op inst.inst_operands /\ eval_operand op t = SOME y ==>
       ?x. eval_operand op s = SOME x) ==>
    ((!ops szop. mem_read_ops inst = SOME ops /\
                   ops.iao_max_size = SOME szop ==>
         eval_operand szop s = eval_operand szop t) ==>
     !a n. MEM (a,n) (source_memory_read_ranges inst t) ==>
       ?ops x y. mem_read_ops inst = SOME ops /\
         MEM ops.iao_ofst inst.inst_operands /\
         eval_operand ops.iao_ofst s = SOME x /\
         eval_operand ops.iao_ofst t = SOME y /\ a = w2n y /\
         MEM (w2n x,n) (source_memory_read_ranges inst s)) /\
    ((!ops szop. mem_write_ops inst = SOME ops /\
                   ops.iao_max_size = SOME szop ==>
         eval_operand szop s = eval_operand szop t) ==>
     !a n. MEM (a,n) (source_memory_write_ranges inst t) ==>
       ?ops x y. mem_write_ops inst = SOME ops /\
         MEM ops.iao_ofst inst.inst_operands /\
         eval_operand ops.iao_ofst s = SOME x /\
         eval_operand ops.iao_ofst t = SOME y /\ a = w2n y /\
         MEM (w2n x,n) (source_memory_write_ranges inst s))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- suspend "reads"
  >> suspend "writes"
QED

Resume ld_single_access_range_transport[reads]:
  rpt strip_tac >> Cases_on `inst.inst_opcode` >>
  fs[source_memory_read_ranges_def]
  >~ [`inst.inst_opcode = MLOAD`] >-
    (Cases_on `inst.inst_operands` >> fs[] >>
     rename1 `MEM (a,n) (case tail of [] => _ | _ => _)` >>
     Cases_on `tail` >> fs[] >>
     Cases_on `eval_operand h t` >> gvs[] >>
     simp[mem_read_ops_def])
  >~ [`inst.inst_opcode = ILOAD`] >-
    (Cases_on `inst.inst_operands` >> fs[] >>
     rename1 `MEM (a,n) (case tail of [] => _ | _ => _)` >>
     Cases_on `tail` >> fs[] >>
     Cases_on `eval_operand h t` >> gvs[] >>
     simp[mem_read_ops_def])
  >~ [`inst.inst_opcode = MCOPY`] >-
    (namedCases_on `inst.inst_operands` ["", "dst rest"] >> fs[] >>
     namedCases_on `rest` ["", "src rest1"] >> fs[] >>
     namedCases_on `rest1` ["", "len rest2"] >> fs[] >>
     Cases_on `rest2` >> fs[] >>
     Cases_on `eval_operand dst t` >> fs[] >>
     Cases_on `eval_operand src t` >> fs[] >>
     Cases_on `eval_operand len t` >> gvs[] >>
     gvs[mem_read_ops_def] >>
     `?v. eval_operand dst s = SOME v` by metis_tac[] >>
     `?v. eval_operand src s = SOME v` by metis_tac[] >>
     simp[])
  >~ [`inst.inst_opcode = RETURN`] >-
    (namedCases_on `inst.inst_operands` ["", "off rest"] >> fs[] >>
     namedCases_on `rest` ["", "len tail"] >> fs[] >>
     Cases_on `tail` >> fs[] >>
     Cases_on `eval_operand off t` >> fs[memory_range_of_operands_def] >>
     Cases_on `eval_operand len t` >> gvs[] >>
     gvs[mem_read_ops_def] >>
     `?v. eval_operand off s = SOME v` by metis_tac[] >> simp[])
  >~ [`inst.inst_opcode = REVERT`] >-
    (namedCases_on `inst.inst_operands` ["", "off rest"] >> fs[] >>
     namedCases_on `rest` ["", "len tail"] >> fs[] >>
     Cases_on `tail` >> fs[] >>
     Cases_on `eval_operand off t` >> fs[memory_range_of_operands_def] >>
     Cases_on `eval_operand len t` >> gvs[] >>
     gvs[mem_read_ops_def] >>
     `?v. eval_operand off s = SOME v` by metis_tac[] >> simp[])
  >~ [`inst.inst_opcode = SHA3`] >-
    (namedCases_on `inst.inst_operands` ["", "off rest"] >> fs[] >>
     namedCases_on `rest` ["", "len tail"] >> fs[] >>
     Cases_on `tail` >> fs[] >>
     Cases_on `eval_operand off t` >> fs[memory_range_of_operands_def] >>
     Cases_on `eval_operand len t` >> gvs[] >>
     gvs[mem_read_ops_def] >>
     `?v. eval_operand off s = SOME v` by metis_tac[] >> simp[])
  >~ [`inst.inst_opcode = CALL`] >-
    (namedCases_on `inst.inst_operands` ["", "gas r1"] >> fs[] >>
     namedCases_on `r1` ["", "addr r2"] >> fs[] >>
     namedCases_on `r2` ["", "value r3"] >> fs[] >>
     namedCases_on `r3` ["", "off r4"] >> fs[] >>
     namedCases_on `r4` ["", "len r5"] >> fs[] >>
     namedCases_on `r5` ["", "ret r6"] >> fs[] >>
     namedCases_on `r6` ["", "cap tail"] >> fs[] >>
     Cases_on `tail` >> fs[] >>
     Cases_on `eval_operand gas t` >> fs[] >>
     Cases_on `eval_operand addr t` >> fs[] >>
     Cases_on `eval_operand value t` >> fs[] >>
     Cases_on `eval_operand ret t` >> fs[] >>
     Cases_on `eval_operand cap t` >> fs[] >>
     Cases_on `eval_operand off t` >> fs[memory_range_of_operands_def] >>
     Cases_on `eval_operand len t` >> gvs[] >>
     gvs[mem_read_ops_def] >>
     `?v. eval_operand gas s = SOME v` by metis_tac[] >>
     `?v. eval_operand addr s = SOME v` by metis_tac[] >>
     `?v. eval_operand value s = SOME v` by metis_tac[] >>
     `?v. eval_operand ret s = SOME v` by metis_tac[] >>
     `?v. eval_operand cap s = SOME v` by metis_tac[] >>
     `?v. eval_operand off s = SOME v` by metis_tac[] >> simp[])
  >~ [`inst.inst_opcode = STATICCALL`] >-
    (namedCases_on `inst.inst_operands` ["", "gas r1"] >> fs[] >>
     namedCases_on `r1` ["", "addr r2"] >> fs[] >>
     namedCases_on `r2` ["", "off r3"] >> fs[] >>
     namedCases_on `r3` ["", "len r4"] >> fs[] >>
     namedCases_on `r4` ["", "ret r5"] >> fs[] >>
     namedCases_on `r5` ["", "cap tail"] >> fs[] >>
     Cases_on `tail` >> fs[] >>
     Cases_on `eval_operand gas t` >> fs[] >>
     Cases_on `eval_operand addr t` >> fs[] >>
     Cases_on `eval_operand ret t` >> fs[] >>
     Cases_on `eval_operand cap t` >> fs[] >>
     Cases_on `eval_operand off t` >> fs[memory_range_of_operands_def] >>
     Cases_on `eval_operand len t` >> gvs[] >>
     gvs[mem_read_ops_def] >>
     `?v. eval_operand gas s = SOME v` by metis_tac[] >>
     `?v. eval_operand addr s = SOME v` by metis_tac[] >>
     `?v. eval_operand ret s = SOME v` by metis_tac[] >>
     `?v. eval_operand cap s = SOME v` by metis_tac[] >>
     `?v. eval_operand off s = SOME v` by metis_tac[] >> simp[])
  >~ [`inst.inst_opcode = DELEGATECALL`] >-
    (namedCases_on `inst.inst_operands` ["", "gas r1"] >> fs[] >>
     namedCases_on `r1` ["", "addr r2"] >> fs[] >>
     namedCases_on `r2` ["", "off r3"] >> fs[] >>
     namedCases_on `r3` ["", "len r4"] >> fs[] >>
     namedCases_on `r4` ["", "ret r5"] >> fs[] >>
     namedCases_on `r5` ["", "cap tail"] >> fs[] >>
     Cases_on `tail` >> fs[] >>
     Cases_on `eval_operand gas t` >> fs[] >>
     Cases_on `eval_operand addr t` >> fs[] >>
     Cases_on `eval_operand ret t` >> fs[] >>
     Cases_on `eval_operand cap t` >> fs[] >>
     Cases_on `eval_operand off t` >> fs[memory_range_of_operands_def] >>
     Cases_on `eval_operand len t` >> gvs[] >>
     gvs[mem_read_ops_def] >>
     `?v. eval_operand gas s = SOME v` by metis_tac[] >>
     `?v. eval_operand addr s = SOME v` by metis_tac[] >>
     `?v. eval_operand ret s = SOME v` by metis_tac[] >>
     `?v. eval_operand cap s = SOME v` by metis_tac[] >>
     `?v. eval_operand off s = SOME v` by metis_tac[] >> simp[])
  >~ [`inst.inst_opcode = CREATE`] >-
    (namedCases_on `inst.inst_operands` ["", "value r1"] >> fs[] >>
     namedCases_on `r1` ["", "off r2"] >> fs[] >>
     namedCases_on `r2` ["", "len tail"] >> fs[] >>
     Cases_on `tail` >> fs[] >>
     Cases_on `eval_operand value t` >> fs[] >>
     Cases_on `eval_operand off t` >> fs[memory_range_of_operands_def] >>
     Cases_on `eval_operand len t` >> gvs[] >>
     gvs[mem_read_ops_def] >>
     `?v. eval_operand value s = SOME v` by metis_tac[] >>
     `?v. eval_operand off s = SOME v` by metis_tac[] >> simp[])
  >~ [`inst.inst_opcode = CREATE2`] >-
    (namedCases_on `inst.inst_operands` ["", "value r1"] >> fs[] >>
     namedCases_on `r1` ["", "off r2"] >> fs[] >>
     namedCases_on `r2` ["", "len r3"] >> fs[] >>
     namedCases_on `r3` ["", "salt tail"] >> fs[] >>
     Cases_on `tail` >> fs[] >>
     Cases_on `eval_operand value t` >> fs[] >>
     Cases_on `eval_operand salt t` >> fs[] >>
     Cases_on `eval_operand off t` >> fs[memory_range_of_operands_def] >>
     Cases_on `eval_operand len t` >> gvs[] >>
     gvs[mem_read_ops_def] >>
     `?v. eval_operand value s = SOME v` by metis_tac[] >>
     `?v. eval_operand salt s = SOME v` by metis_tac[] >>
     `?v. eval_operand off s = SOME v` by metis_tac[] >> simp[]) >>
  namedCases_on `inst.inst_operands` ["", "tcop rest"] >> fs[] >>
  Cases_on `tcop` >> fs[] >> rename1 `Lit tc` >>
  Cases_on `LENGTH rest <> w2n tc + 2` >> fs[] >>
  Cases_on `eval_operands (DROP 2 (REVERSE rest)) t` >> fs[] >>
  namedCases_on `REVERSE rest` ["", "off rev1"] >> fs[] >>
  `LENGTH rest = SUC (LENGTH rev1)` by
    (qpat_x_assum `REVERSE rest = _` (mp_tac o AP_TERM ``LENGTH : operand list -> num``) >> simp[]) >>
  namedCases_on `rev1` ["", "len topics"] >> fs[] >>
  Cases_on `eval_operand off t` >> fs[memory_range_of_operands_def] >>
  Cases_on `eval_operand len t` >> gvs[] >>
  `MEM off rest /\ MEM len rest /\
   (!op. MEM op topics ==> MEM op rest)` by
    (qpat_x_assum `REVERSE rest = _` mp_tac >>
     disch_then (assume_tac o GSYM) >> metis_tac[MEM_REVERSE, MEM]) >>
  `?v. eval_operand off s = SOME v` by metis_tac[] >>
  `IS_SOME (eval_operands topics s)` by
    (`EVERY (\op. IS_SOME (eval_operand op t)) topics` by
       (irule (iffLR eval_operands_IS_SOME_EVERY) >> simp[]) >>
     rewrite_tac[eval_operands_IS_SOME_EVERY, EVERY_MEM] >>
     fs[EVERY_MEM] >> rpt strip_tac >>
     `IS_SOME (eval_operand e t)` by metis_tac[] >>
     Cases_on `eval_operand e t` >> fs[] >>
     `?v. eval_operand e s = SOME v` by metis_tac[] >> simp[]) >>
  Cases_on `eval_operands topics s` >> fs[] >>
  Cases_on `topics` >> gvs[mem_read_ops_def]
QED

Resume ld_single_access_range_transport[writes]:
  rpt strip_tac >> Cases_on `inst.inst_opcode` >>
  fs[source_memory_write_ranges_def]
  >~ [`inst.inst_opcode = MSTORE`] >- suspend "mstore"
  >~ [`inst.inst_opcode = MSTORE8`] >- suspend "mstore8"
  >~ [`inst.inst_opcode = ISTORE`] >- suspend "istore"
  >~ [`inst.inst_opcode = MCOPY`] >- suspend "mcopy_write"
  >~ [`inst.inst_opcode = CALLDATACOPY`] >- suspend "calldatacopy"
  >~ [`inst.inst_opcode = RETURNDATACOPY`] >- suspend "returndatacopy"
  >~ [`inst.inst_opcode = DLOADBYTES`] >- suspend "dloadbytes"
  >~ [`inst.inst_opcode = CODECOPY`] >- suspend "codecopy"
  >~ [`inst.inst_opcode = EXTCODECOPY`] >- suspend "extcodecopy"
  >~ [`inst.inst_opcode = CALL`] >- suspend "call_write"
  >~ [`inst.inst_opcode = STATICCALL`] >- suspend "staticcall_write"
  >~ [`inst.inst_opcode = DELEGATECALL`] >- suspend "delegatecall_write"
QED

Resume ld_single_access_range_transport[mstore]:
  namedCases_on `inst.inst_operands` ["", "dst rest"] >> fs[] >>
  namedCases_on `rest` ["", "value tail"] >> fs[] >>
  Cases_on `tail` >> fs[] >>
  Cases_on `eval_operand dst t` >> fs[fixed_source_write_range_def] >>
  Cases_on `eval_operand value t` >> gvs[] >>
  gvs[mem_write_ops_def] >>
  `?v. eval_operand dst s = SOME v` by metis_tac[] >>
  `?v. eval_operand value s = SOME v` by metis_tac[] >> simp[]
QED

Resume ld_single_access_range_transport[mstore8]:
  namedCases_on `inst.inst_operands` ["", "dst rest"] >> fs[] >>
  namedCases_on `rest` ["", "value tail"] >> fs[] >>
  Cases_on `tail` >> fs[] >>
  Cases_on `eval_operand dst t` >> fs[fixed_source_write_range_def] >>
  Cases_on `eval_operand value t` >> gvs[] >>
  gvs[mem_write_ops_def] >>
  `?v. eval_operand dst s = SOME v` by metis_tac[] >>
  `?v. eval_operand value s = SOME v` by metis_tac[] >> simp[]
QED

Resume ld_single_access_range_transport[istore]:
  namedCases_on `inst.inst_operands` ["", "dst rest"] >> fs[] >>
  namedCases_on `rest` ["", "value tail"] >> fs[] >>
  Cases_on `tail` >> fs[] >>
  Cases_on `eval_operand dst t` >> fs[fixed_source_write_range_def] >>
  Cases_on `eval_operand value t` >> gvs[] >>
  gvs[mem_write_ops_def] >>
  `?v. eval_operand dst s = SOME v` by metis_tac[] >>
  `?v. eval_operand value s = SOME v` by metis_tac[] >> simp[]
QED

Resume ld_single_access_range_transport[mcopy_write]:
  namedCases_on `inst.inst_operands` ["", "dst rest"] >> fs[] >>
  namedCases_on `rest` ["", "src rest1"] >> fs[] >>
  namedCases_on `rest1` ["", "len tail"] >> fs[] >>
  Cases_on `tail` >> fs[] >>
  Cases_on `eval_operand dst t` >> fs[sized_source_write_range_def] >>
  Cases_on `eval_operand src t` >> fs[] >>
  Cases_on `eval_operand len t` >> gvs[] >> gvs[mem_write_ops_def] >>
  `?v. eval_operand dst s = SOME v` by metis_tac[] >>
  `?v. eval_operand src s = SOME v` by metis_tac[] >> simp[]
QED

Resume ld_single_access_range_transport[calldatacopy]:
  namedCases_on `inst.inst_operands` ["", "dst rest"] >> fs[] >>
  namedCases_on `rest` ["", "src rest1"] >> fs[] >>
  namedCases_on `rest1` ["", "len tail"] >> fs[] >>
  Cases_on `tail` >> fs[] >>
  Cases_on `eval_operand dst t` >> fs[sized_source_write_range_def] >>
  Cases_on `eval_operand src t` >> fs[] >>
  Cases_on `eval_operand len t` >> gvs[] >> gvs[mem_write_ops_def] >>
  `?v. eval_operand dst s = SOME v` by metis_tac[] >>
  `?v. eval_operand src s = SOME v` by metis_tac[] >> simp[]
QED

Resume ld_single_access_range_transport[returndatacopy]:
  namedCases_on `inst.inst_operands` ["", "dst rest"] >> fs[] >>
  namedCases_on `rest` ["", "src rest1"] >> fs[] >>
  namedCases_on `rest1` ["", "len tail"] >> fs[] >>
  Cases_on `tail` >> fs[] >>
  Cases_on `eval_operand dst t` >> fs[sized_source_write_range_def] >>
  Cases_on `eval_operand src t` >> fs[] >>
  Cases_on `eval_operand len t` >> gvs[] >> gvs[mem_write_ops_def] >>
  `?v. eval_operand dst s = SOME v` by metis_tac[] >>
  `?v. eval_operand src s = SOME v` by metis_tac[] >> simp[]
QED

Resume ld_single_access_range_transport[dloadbytes]:
  namedCases_on `inst.inst_operands` ["", "dst rest"] >> fs[] >>
  namedCases_on `rest` ["", "src rest1"] >> fs[] >>
  namedCases_on `rest1` ["", "len tail"] >> fs[] >>
  Cases_on `tail` >> fs[] >>
  Cases_on `eval_operand dst t` >> fs[sized_source_write_range_def] >>
  Cases_on `eval_operand src t` >> fs[] >>
  Cases_on `eval_operand len t` >> gvs[] >> gvs[mem_write_ops_def] >>
  `?v. eval_operand dst s = SOME v` by metis_tac[] >>
  `?v. eval_operand src s = SOME v` by metis_tac[] >> simp[]
QED

Resume ld_single_access_range_transport[codecopy]:
  namedCases_on `inst.inst_operands` ["", "dst rest"] >> fs[] >>
  namedCases_on `rest` ["", "src rest1"] >> fs[] >>
  namedCases_on `rest1` ["", "len tail"] >> fs[] >>
  Cases_on `tail` >> fs[] >>
  Cases_on `eval_operand dst t` >> fs[sized_source_write_range_def] >>
  Cases_on `eval_operand src t` >> fs[] >>
  Cases_on `eval_operand len t` >> gvs[] >> gvs[mem_write_ops_def] >>
  `?v. eval_operand dst s = SOME v` by metis_tac[] >>
  `?v. eval_operand src s = SOME v` by metis_tac[] >> simp[]
QED

Resume ld_single_access_range_transport[extcodecopy]:
  namedCases_on `inst.inst_operands` ["", "addr r1"] >> fs[] >>
  namedCases_on `r1` ["", "dst rest"] >> fs[] >>
  namedCases_on `rest` ["", "src rest1"] >> fs[] >>
  namedCases_on `rest1` ["", "len tail"] >> fs[] >>
  Cases_on `tail` >> fs[] >>
  Cases_on `eval_operand addr t` >> fs[] >>
  Cases_on `eval_operand dst t` >> fs[sized_source_write_range_def] >>
  Cases_on `eval_operand src t` >> fs[] >>
  Cases_on `eval_operand len t` >> gvs[] >> gvs[mem_write_ops_def] >>
  `?v. eval_operand addr s = SOME v` by metis_tac[] >>
  `?v. eval_operand dst s = SOME v` by metis_tac[] >>
  `?v. eval_operand src s = SOME v` by metis_tac[] >> simp[]
QED
Resume ld_single_access_range_transport[call_write]:
  namedCases_on `inst.inst_operands` ["", "gas r1"] >> fs[] >>
  namedCases_on `r1` ["", "addr r2"] >> fs[] >>
  namedCases_on `r2` ["", "value r3"] >> fs[] >>
  namedCases_on `r3` ["", "off r4"] >> fs[] >>
  namedCases_on `r4` ["", "len r5"] >> fs[] >>
  namedCases_on `r5` ["", "ret r6"] >> fs[] >>
  namedCases_on `r6` ["", "cap tail"] >> fs[] >>
  Cases_on `tail` >> fs[] >>
  Cases_on `eval_operand gas t` >> fs[] >>
  Cases_on `eval_operand addr t` >> fs[] >>
  Cases_on `eval_operand value t` >> fs[] >>
  Cases_on `eval_operand off t` >> fs[] >>
  Cases_on `eval_operand len t` >> fs[] >>
  Cases_on `eval_operand ret t` >> fs[] >>
  Cases_on `eval_operand cap t` >> gvs[] >> gvs[mem_write_ops_def] >>
  `?v. eval_operand gas s = SOME v` by metis_tac[] >>
  `?v. eval_operand addr s = SOME v` by metis_tac[] >>
  `?v. eval_operand value s = SOME v` by metis_tac[] >>
  `?v. eval_operand off s = SOME v` by metis_tac[] >>
  `?v. eval_operand len s = SOME v` by metis_tac[] >>
  `?v. eval_operand ret s = SOME v` by metis_tac[] >> simp[]
QED
Resume ld_single_access_range_transport[staticcall_write]:
  namedCases_on `inst.inst_operands` ["", "gas r1"] >> fs[] >>
  namedCases_on `r1` ["", "addr r2"] >> fs[] >>
  namedCases_on `r2` ["", "off r3"] >> fs[] >>
  namedCases_on `r3` ["", "len r4"] >> fs[] >>
  namedCases_on `r4` ["", "ret r5"] >> fs[] >>
  namedCases_on `r5` ["", "cap tail"] >> fs[] >>
  Cases_on `tail` >> fs[] >>
  Cases_on `eval_operand gas t` >> fs[] >>
  Cases_on `eval_operand addr t` >> fs[] >>
  Cases_on `eval_operand off t` >> fs[] >>
  Cases_on `eval_operand len t` >> fs[] >>
  Cases_on `eval_operand ret t` >> fs[] >>
  Cases_on `eval_operand cap t` >> gvs[] >> gvs[mem_write_ops_def] >>
  `?v. eval_operand gas s = SOME v` by metis_tac[] >>
  `?v. eval_operand addr s = SOME v` by metis_tac[] >>
  `?v. eval_operand off s = SOME v` by metis_tac[] >>
  `?v. eval_operand len s = SOME v` by metis_tac[] >>
  `?v. eval_operand ret s = SOME v` by metis_tac[] >> simp[]
QED
Resume ld_single_access_range_transport[delegatecall_write]:
  namedCases_on `inst.inst_operands` ["", "gas r1"] >> fs[] >>
  namedCases_on `r1` ["", "addr r2"] >> fs[] >>
  namedCases_on `r2` ["", "off r3"] >> fs[] >>
  namedCases_on `r3` ["", "len r4"] >> fs[] >>
  namedCases_on `r4` ["", "ret r5"] >> fs[] >>
  namedCases_on `r5` ["", "cap tail"] >> fs[] >>
  Cases_on `tail` >> fs[] >>
  Cases_on `eval_operand gas t` >> fs[] >>
  Cases_on `eval_operand addr t` >> fs[] >>
  Cases_on `eval_operand off t` >> fs[] >>
  Cases_on `eval_operand len t` >> fs[] >>
  Cases_on `eval_operand ret t` >> fs[] >>
  Cases_on `eval_operand cap t` >> gvs[] >> gvs[mem_write_ops_def] >>
  `?v. eval_operand gas s = SOME v` by metis_tac[] >>
  `?v. eval_operand addr s = SOME v` by metis_tac[] >>
  `?v. eval_operand off s = SOME v` by metis_tac[] >>
  `?v. eval_operand len s = SOME v` by metis_tac[] >>
  `?v. eval_operand ret s = SOME v` by metis_tac[] >> simp[]
QED
Finalise ld_single_access_range_transport
