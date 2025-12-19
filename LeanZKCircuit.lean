-- This module serves as the root of the `LeanZKCircuit` library.
-- Import modules here that should be built as part of the library.
import LeanZKCircuit.Command.Air.Lemmas.base_member_projection
import LeanZKCircuit.Command.Air.Lemmas.subcircuit_isValid

import LeanZKCircuit.Command.Air.Syntax.air_definition
import LeanZKCircuit.Command.Air.Syntax.entry

import LeanZKCircuit.Command.Air.assign_columns
import LeanZKCircuit.Command.Air.define_air
import LeanZKCircuit.Command.Air.instance_creation
import LeanZKCircuit.Command.Air.is_valid
import LeanZKCircuit.Command.Air.structure_definition
import LeanZKCircuit.Command.Air.valid_circuit

import LeanZKCircuit.Command.util

import LeanZKCircuit.Interactions

import LeanZKCircuit.OpenVM.Circuit

import LeanZKCircuit.Tactics.BitVec.bv_amicus_kerneli
import LeanZKCircuit.Tactics.BitVec.bv_amicus_kerneli
import LeanZKCircuit.Tactics.VectorEq
import LeanZKCircuit.Tactics.CompilePerf.Options
import LeanZKCircuit.Tactics.CompilePerf.SanitiseSimp
import LeanZKCircuit.Tactics.CompilePerf.TacticAnalysisWrapper
