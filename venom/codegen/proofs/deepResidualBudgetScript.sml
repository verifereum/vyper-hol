(*
 * Helpers for deepResidualSim: the planner steps behind input emission and
 * reorder preserve the marker-tolerant residual budgets.
 *)

Theory deepResidualBudget
Ancestors
  fnPlanPrefix preparedPrefixSim generatedPrefixSim generatedReorderSim
  genericInputReady reorderSim doSwapSim codegenRel asmSem planExec
  stackPlanGen stackPlanOps stackPlanTypes stackModel blockSimHelpers
  list rich_list arithmetic

