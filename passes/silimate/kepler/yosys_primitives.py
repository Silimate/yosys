# SPDX-FileCopyrightText: 2026 Silimate
# SPDX-License-Identifier: ISC
#
# Self-contained Yosys gate primitives for kepler-formal LEC/SEC.
# Loaded via py_tech_files / SNLPyLoader::loadPrimitives (constructPrimitives).

import logging

logger = logging.getLogger(__name__)

try:
    from najaeda import naja
except ImportError:  # pragma: no cover
    import naja


def _construct_sequential(design, clk):
    inputs = []
    outputs = []
    for term in design.getBitTerms():
        if term == clk:
            continue
        if term.getDirection() == naja.SNLTerm.Direction.Input:
            inputs.append(term)
        elif term.getDirection() == naja.SNLTerm.Direction.Output:
            outputs.append(term)
    naja.SNLDesign.addClockToOutputsArcs(clk, outputs)
    naja.SNLDesign.addInputsToClockArcs(inputs, clk)


def constructAND(lib):
    cell = naja.SNLDesign.createPrimitive(lib, "$_AND_")
    naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Input, "A")
    naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Input, "B")
    naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Output, "Y")
    cell.setTruthTable(0x8)


def constructNOT(lib):
    cell = naja.SNLDesign.createPrimitive(lib, "$_NOT_")
    naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Input, "A")
    naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Output, "Y")
    cell.setTruthTable(0b01)


def constructDFF_P(lib):
    cell = naja.SNLDesign.createPrimitive(lib, "$_DFF_P_")
    clk = naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Input, "C")
    naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Input, "D")
    naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Output, "Q")
    _construct_sequential(cell, clk)


def constructDFF_N(lib):
    cell = naja.SNLDesign.createPrimitive(lib, "$_DFF_N_")
    clk = naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Input, "C")
    naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Input, "D")
    naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Output, "Q")
    _construct_sequential(cell, clk)


def constructDLATCH_P(lib):
    cell = naja.SNLDesign.createPrimitive(lib, "$_DLATCH_P_")
    en = naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Input, "E")
    naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Input, "D")
    naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Output, "Q")
    _construct_sequential(cell, en)


def constructDLATCH_N(lib):
    cell = naja.SNLDesign.createPrimitive(lib, "$_DLATCH_N_")
    en = naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Input, "E")
    naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Input, "D")
    naja.SNLScalarTerm.create(cell, naja.SNLTerm.Direction.Output, "Q")
    _construct_sequential(cell, en)


def constructPrimitives(lib):
    logger.info("Loading Kepler Yosys primitives ($_AND_/$_NOT_/$_DFF_*/$_DLATCH_*)")
    constructAND(lib)
    constructNOT(lib)
    constructDFF_P(lib)
    constructDFF_N(lib)
    constructDLATCH_P(lib)
    constructDLATCH_N(lib)
