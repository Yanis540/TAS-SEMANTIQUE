package it.unive.lisa.tutorial;

import java.util.HashSet;
import java.util.Set;

import it.unive.lisa.analysis.Lattice;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.DivisionOperator;
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.BinaryOperator;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

public class SetOfIntegerValues implements BaseNonRelationalValueDomain<SetOfIntegerValues>  {
    public static final SetOfIntegerValues BOTTOM = new SetOfIntegerValues(new HashSet<>()),TOP = new SetOfIntegerValues(null);
    public final Set<Integer> values;
    public SetOfIntegerValues(Set<Integer> values) {
        this.values = values;
    }
    public SetOfIntegerValues(int value) {
        this.values = new HashSet<>();
        this.values.add(value);
    }
    @Override
    public SetOfIntegerValues lubAux(SetOfIntegerValues setOfIntegerValues) throws SemanticException {
        HashSet<Integer> newValues = new HashSet<>(this.values);
        newValues.addAll(setOfIntegerValues.values);
        return new SetOfIntegerValues(newValues);
    }

    @Override
    public boolean lessOrEqualAux(SetOfIntegerValues setOfIntegerValues) throws SemanticException {
        return false;
    }

    @Override
    public SetOfIntegerValues top() {
        return TOP;
    }

    @Override
    public SetOfIntegerValues bottom() {
        return BOTTOM;
    }
    @Override
    public SetOfIntegerValues evalBinaryExpression(BinaryOperator operator, SetOfIntegerValues left, SetOfIntegerValues right, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if(operator instanceof AdditionOperator) {
            if(left.isTop() || right.isTop())
                return top();
            if(left.isBottom() || right.isBottom())
                return bottom();
            Set<Integer> values = new HashSet<>();
            for(int leftValue : left.values)
                for(int rightValue : right.values)
                    values.add(leftValue + rightValue);
            return new SetOfIntegerValues(values);
        }
       
        return BaseNonRelationalValueDomain.super.evalBinaryExpression(operator, left, right, pp, oracle);
    }
     @Override
    public SetOfIntegerValues evalNonNullConstant(Constant constant, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if (constant.getValue() instanceof Integer)
            return new SetOfIntegerValues((Integer) constant.getValue());
        return BaseNonRelationalValueDomain.super.evalNonNullConstant(constant, pp, oracle);
    }
    @Override
    public StructuredRepresentation representation() {
        if(this.isBottom())
            return Lattice.bottomRepresentation();
        if(this.isTop())
            return Lattice.topRepresentation();
        return new StringRepresentation(values.toString());
    }
}