package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.util.representation.StructuredRepresentation;

public class SetOfIntegerValues implements BaseNonRelationalValueDomain<SetOfIntegerValues>  {
    @Override
    public SetOfIntegerValues lubAux(SetOfIntegerValues setOfIntegerValues) throws SemanticException {
        return null;
    }

    @Override
    public boolean lessOrEqualAux(SetOfIntegerValues setOfIntegerValues) throws SemanticException {
        return false;
    }

    @Override
    public SetOfIntegerValues top() {
        return null;
    }

    @Override
    public SetOfIntegerValues bottom() {
        return null;
    }

    @Override
    public StructuredRepresentation representation() {
        return null;
    }
}