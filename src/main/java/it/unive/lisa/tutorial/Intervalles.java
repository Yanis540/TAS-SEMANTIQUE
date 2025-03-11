package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

public class Intervalles // instances of this class are lattice elements such that:
		// - their state (fields) hold the information contained into a single
		//   variable
		// - they provide logic for the evaluation of expressions
		implements BaseNonRelationalValueDomain<
			// java requires this type parameter to have this class
			// as type in fields/methods
			Intervalles> {

    public static final Intervalles TOP = new Intervalles(Integer.MIN_VALUE,Integer.MAX_VALUE),BOTTOM = new Intervalles(Integer.MAX_VALUE,Integer.MIN_VALUE);
    private final int min,max;
    public Intervalles(int min, int max) {
        this.min = min;
        this.max = max;
    }

    @Override
    public Intervalles lubAux(Intervalles other) throws SemanticException {
        return new Intervalles(Math.min(min, other.min), Math.max(max, other.max));
    }

    @Override
    public boolean lessOrEqualAux(Intervalles other) throws SemanticException {
        return min >= other.min && max <= other.max;
    }

    @Override
    public Intervalles top() {
        return TOP;
    }

    @Override
    public Intervalles bottom() {
        return BOTTOM;
    }

    @Override
    public StructuredRepresentation representation() {
        return new StringRepresentation("["+min+".."+max+"]");
    }

    
}
